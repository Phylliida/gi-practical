"""String isomorphism under a permutation group, following the recursion of
Hajiaghayi & JafariRaviz (arXiv:2611.01399), Section 6, Algorithm 5.

    Iso_G(x, y) = { g in G : x^g = y }

is returned as Coset(gens, rep): every isomorphism is h * rep for some h in
<gens> = Aut_G(x), or None if there is no isomorphism.

What is implemented as in the paper:
  * Solve / Continue with the orbit-chain rule (largest orbit first),
  * the primitive-quotient dispatcher (Maroti's form of Cameron's theorem):
    enumerate small quotients, treat natural giants and Johnson actions on
    k-sets as giants, and apply product refinement to product actions,
  * the Johnson outcome before GiantStep: a color class of the projected label
    coloring that is a Johnson (or Hamming) graph on all labels reduces Sym(q)
    to its automorphism group (scheme_step),
  * constant-size local certificates (Algorithm 3), with CheckNewWindow done by
    enumerating cosets of ker(phi_T) and solving on the window,
  * the "large known symmetry" branch (full certificates generate Alt(q)),
  * LiftAndContinue and CombineExact.

Branching economy (not in the paper; exact, see the docstrings):
  * GiantStep runs on phi(G) = Sym(q) directly, lifting Young subgroups of
    Sym(q), instead of normalizing to Alt(q) with two cosets;
  * automorphism pruning of the individualization branches and of quotient
    enumeration, as in nauty;
  * a memo of Aut_G(x): once it is known, the remaining branches only search
    for one isomorphism ("one-mode"), pruned by Aut_G(x);
  * certificates only for x, only on uniform labels, cached.

Aggregation over the whole instance (Solver.young_step): on intransitive
groups, the orbits on which the group acts as a product of symmetric groups
serve as labels; all positions with one- or two-label supports refine them
jointly (1-WL or 2-WL), then LiftAndContinue or individualize, before the
orbit chain would split the instance into orbits.

What is simplified (see README.md for details):
  * aggregation: pulled-back colors (and certificate signatures, as a
    k-uniform colored hypergraph) are refined on the labels by WL-style
    refinement, then one label is individualized at a time. The paper uses
    ordered lockstep comparisons, Babai's Design Lemma and its "first
    rectangle" step instead;
  * no row/column step (Algorithm 4), no phases, hierarchy caps or budget
    bookkeeping: those only matter for the running-time proof;
  * primitive quotients that are neither giants, Johnson nor product
    actions are enumerated, or raise Unsupported when too large.
Every simplification keeps the answer exact; only the running time changes.
"""
import itertools
import math
from collections import Counter, OrderedDict, namedtuple
from operator import add

from .perm import identity, mul, inv, act, maps, parity, cycle, alt_gens, sym_gens
from .group import (PermGroup, ActionHom, RestrictionHom, reduce_gens, top_block_system,
                    johnson_structure, product_action, giant_labels, label_support,
                    johnson_embedding, hamming_embedding, clear_chain_cache)

Coset = namedtuple("Coset", "gens rep")


class Unsupported(Exception):
    """A case the minimal implementation does not handle within its limits."""


def combine(n, answers):
    """CombineExact: the union of an exhaustive family of exact branch answers,
    which is a coset. Representative: the first answer's. Generators: all
    stabilizer generators plus the ratios of the representatives."""
    answers = [a for a in answers if a is not None]
    if not answers:
        return None
    r0 = answers[0].rep
    r0i = inv(r0)
    gens = []
    for a in answers:
        gens.extend(a.gens)
        gens.append(mul(a.rep, r0i))
    return Coset(reduce_gens(n, gens), r0)


def color_classes(c):
    classes = {}
    for i, col in enumerate(c):
        classes.setdefault(col, []).append(i)
    return classes


def refine_labels(q, hx, hy, cx, cy, px=None, py=None):
    """Jointly refine label colorings of the two instances using
      * the colored k-uniform hypergraphs hx, hy: dict T -> (signature, roles),
        where roles[i] is an invariant of T[i] inside the certificate of T;
      * optional pair colorings px, py (q x q matrices of ints).
    Colors are renamed by one shared, content-based rule, so the result is
    isomorphism-invariant (any isomorphism maps the x-coloring to the y-coloring)."""
    cx, cy = list(cx), list(cy)
    while True:
        new = []
        for h, c, p in ((hx, cx, px), (hy, cy, py)):
            ms = [[] for _ in range(q)]
            for T, (sig, roles) in h.items():
                cols = [c[t] for t in T]
                for i, t in enumerate(T):
                    ms[t].append((sig, roles[i], tuple(sorted(cols[:i] + cols[i + 1:]))))
            if p is None:
                nb = [()] * q
            else:
                nb = [tuple(sorted((p[a][b], p[b][a], c[b]) for b in range(q) if b != a))
                      for a in range(q)]
            new.append([(c[g], nb[g], tuple(sorted(ms[g]))) for g in range(q)])
        rank = {k: i for i, k in enumerate(sorted(set(new[0]) | set(new[1])))}
        nx = [rank[k] for k in new[0]]
        ny = [rank[k] for k in new[1]]
        if len(set(nx)) == len(set(cx)) and len(set(ny)) == len(set(cy)):
            return nx, ny
        cx, cy = nx, ny


def _rank2(sx, sy):
    """Shared content-based names for two lists of signatures."""
    rank = {s: i for i, s in enumerate(sorted(set(sx) | set(sy)))}
    return [rank[s] for s in sx], [rank[s] for s in sy]


def wl2_joint(PX, PY, ranked=False):
    """Joint 2-dimensional WL (the coherent closure) of two m x m colorings,
    given as flat lists of sortable values (entry a*m+b is the pair (a, b)).
    The new color of (a, b) is (old color, multiset of (C(a, c), C(c, b))),
    named by rank in the union of both instances' signatures. (The same rule
    as refine.wl2, copied so that the front end can change independently.)
    A pair whose color class is a single pair (in both instances: the
    histograms agree) cannot split, so its multiset is not computed; the
    partitions are the same. Stops early once the diagonal is discrete (the
    label partition cannot change any more). ranked=True: PX, PY are already
    jointly named ints. Returns the flat int colorings, or None if the
    histograms differ."""
    fx, fy = (PX, PY) if ranked else _rank2(PX, PY)
    cnt = Counter(fx)
    if cnt != Counter(fy):
        return None
    m = math.isqrt(len(fx))
    k = len(cnt)
    kd = len(set(fx[::m + 1]))
    while True:
        if kd == m:
            return fx, fy
        single = {c for c, v in cnt.items() if v == 1}
        sigs = []
        for P in (fx, fy):
            K = 1 + max(P)
            rows = [P[a * m:(a + 1) * m] for a in range(m)]
            cols = [P[b::m] for b in range(m)]
            s = []
            for a in range(m):
                Pa = rows[a]
                ra = [c * K for c in Pa]
                for b in range(m):
                    c = Pa[b]
                    if c in single:
                        s.append((c, ()))
                    else:
                        s.append((c, tuple(sorted(map(add, ra, cols[b])))))
            sigs.append(s)
        fx, fy = _rank2(sigs[0], sigs[1])
        cnt = Counter(fx)
        if cnt != Counter(fy):
            return None
        k2 = len(cnt)
        if k2 == k:
            return fx, fy
        k = k2
        kd = len(set(fx[::m + 1]))


class YoungRoot:
    """A label structure for an intransitive group G0 (see Solver.young_root):
    labels = the positions of `gamma` (label i is gamma[i]), on which G0 acts
    as the full product of Sym(C) over `classes`; psi = the restriction to
    gamma; unary[a] / pair[(a, b)] = the positions w whose support is (a,) or
    (a, b), each with its G0-orbit index."""
    __slots__ = ("G", "psi", "m", "gamma", "classes", "unary", "pair")


_FALLBACK = object()


class Solver:
    def __init__(self, kappa=3, enum_limit=500, certificates=True, max_enum=100000,
                 cert_refine=True, seed=True, young=True, young_min=5, young_wl=1,
                 giant_wl=2, young_pick="small", recognize=True, product_hint=True,
                 scheme=True):
        self.kappa = kappa                  # size of the local test sets
        self.enum_limit = enum_limit        # enumerate groups/quotients up to this order
        self.certificates = certificates    # use local certificates in GiantStep
        self.cert_refine = cert_refine      # also refine labels by certificate signatures
        self.seed = seed                    # seed the memo for off-base one-mode branches
        self.max_enum = max_enum            # refuse to enumerate anything larger
        self.young = young                  # Young-label step on intransitive groups
        self.young_min = young_min          # individualize Young classes of this size
        self.young_wl = young_wl            # label refinement there: 2 = 2-WL, 1 = 1-WL
        self.giant_wl = giant_wl            # GiantStep pair colors: 2 = also 2-WL, 1 = 1-WL
        self.young_pick = young_pick        # class to individualize: "small" or "large"
        self.recognize = recognize          # Johnson k >= 3, product actions, other giants
        self.product_hint = product_hint    # after product refinement, use coordinate 0 next
        self._hints = {}                    # (n, gens) -> a block system to use for that group
        self._dispatch = OrderedDict()      # (n, gens) -> dispatch record (LRU)
        self.dispatch_cache = 256
        self.scheme = scheme                # Johnson/Hamming label structure before GiantStep
        self._schemes = {}                  # (G, phi, x) -> scheme of x's label coloring
        self.stats = Counter()
        clear_chain_cache()                 # (a cache only: results do not depend on it)
        self.memo = {}                      # (G.gens, x) -> generators of Aut_G(x)
        self._supp = {}                     # (G, phi) -> support map of label_projection
        self._certs = {}                    # (G, phi, x) -> local certificates of x
        self._yroots = {}                   # G.gens -> YoungRoot or None
        self._ynodes = {}                   # H.gens -> (YoungRoot, partition of the labels)
        self._ypull = {}                    # (root, coloring) -> pulled-back label colors
        self._ystate = {}                   # (H.gens, x, y) -> stable Young refinement

    # -- Solve: restrict to the positions that still need checking -----------
    def solve(self, G, D, x, y):
        """Iso_G(x|D, y|D) for a G-invariant set D of positions; the answer is a
        coset in G. Positions outside D are ignored."""
        self.stats["solve"] += 1
        n = G.n
        D = sorted(D)
        if not D:
            return Coset(list(G.gens), G.idn)
        xs = tuple(x[d] for d in D)
        ys = tuple(y[d] for d in D)
        if sorted(xs) != sorted(ys):
            return None
        if len(set(xs)) == 1:
            return Coset(list(G.gens), G.idn)
        if len(D) == n:
            return self.cont(G, tuple(x), tuple(y))
        rho = RestrictionHom(G, D)
        a = self.cont(rho.image_group(), xs, ys)
        if a is None:
            return None
        gens = [rho.lift(h) for h in a.gens] + rho.kernel().gens
        return Coset(reduce_gens(n, gens, G.short_base()), rho.lift(a.rep))


    # -- Continue -------------------------------------------------------------
    def cont(self, G, x, y):
        """Iso_G(x, y) for G acting faithfully on all positions range(n).

        Memo and one-mode. Every exact answer Aut_G(x) * rep is recorded as
        memo[(G.gens, x)] = generators of Aut_G(x). The key is exact, since a
        group is determined by its generator tuple. When the memo already holds
        Aut_G(x), the full answer only needs ONE isomorphism, and the recursion
        runs in one-mode (`known` = the generators of Aut_G(x)): the branch
        loops stop at the first nonempty branch and prune by the known
        automorphisms of x. The branches of a GiantStep or of a quotient
        enumeration share their x side and hence their group, so all branches
        after the first one hit the memo."""
        self.stats["cont"] += 1
        if sorted(x) != sorted(y):
            return None
        if len(set(x)) == 1:
            return Coset(list(G.gens), G.idn)
        key = (tuple(G.gens), tuple(x))
        known = self.memo.get(key)
        if known is None:
            a = self._cont(G, x, y, None)
            if a is not None:
                self.memo[key] = a.gens
            return a
        self.stats["memo_hit"] += 1
        if x == y:
            return Coset(known, G.idn)
        a = self._cont(G, x, y, known)
        return None if a is None else Coset(known, a.rep)

    def _cont(self, G, x, y, known):
        n = G.n
        if G.order() <= self.enum_limit:
            return self.enumerate(G, x, y, known)
        orbs = G.orbits()
        if len(orbs) > 1:
            if self.young:
                a = self.young_step(G, x, y, known)
                if a is not _FALLBACK:
                    return a
            # orbit-chain rule, largest orbit first
            orbs.sort(key=lambda o: (-len(o), o[0]))
            first = orbs[0]
            rest = [p for o in orbs[1:] for p in o]
            a1 = self.solve(G, first, x, y)
            if a1 is None:
                return None
            H = PermGroup(n, a1.gens, ambient_base=G.short_base())
            a2 = self.solve(H, rest, x, act(y, inv(a1.rep)))
            if a2 is None:
                return None
            return Coset(a2.gens, mul(a2.rep, a1.rep))
        return self.transitive(G, x, y, known)

    def enumerate(self, G, x, y, known=None):
        self.stats["enumerate"] += 1
        if known is not None:
            g = next((g for g in G.elements() if maps(g, x, y)), None)
            return None if g is None else Coset(known, g)
        isos = G.isomorphisms(x, y)      # = [g for g in G.elements() if maps(g, x, y)]
        if not isos:
            return None
        r0i = inv(isos[0])
        return Coset(reduce_gens(G.n, [mul(g, r0i) for g in isos]), isos[0])

    # -- the primitive-quotient dispatcher ------------------------------------
    def transitive(self, G, x, y, known=None):
        """Expose the primitive quotient P of degree d (the top of the stacked
        block hierarchy) and dispatch on it as in the paper (Sec. 6, with
        Maroti's form of Cameron's theorem):
          * natural giant (Sym(d) or Alt(d), d >= 5): GiantStep on the blocks;
          * small (order <= enum_limit, or d < 5): enumerate the quotient;
          * Johnson action of Sym(m) or Alt(m) on k-sets (k >= 2): GiantStep
            on the m recovered labels (r = 1);
          * product action on D^r points (r >= 2): product refinement, i.e.
            the union over the at most r! cosets of the coordinate-preserving
            subgroup, which acts imprimitively (finer hierarchy);
          * Sym(m) or Alt(m) in another action (e.g. on bisections, which are
            Cameron-small but have order m!): GiantStep on m labels found from
            the conjugation action on transpositions or 3-cycles;
          * anything else: enumerate the quotient, up to max_enum.
        The recognition is verified (see group.py): johnson_structure and
        giant_labels return homomorphisms onto Sym(m) or Alt(m), product_action
        a homomorphism onto the coordinate permutations. Every branch is an
        exact reduction."""
        if all(maps(g, x, x) for g in G.gens):
            # G preserves x, so x^g = x for every g in G: Iso_G(x, y) is G
            # when y = x and empty otherwise.
            self.stats["invariant"] += 1
            if x != y:
                return None
            return Coset(list(G.gens) if known is None else known, G.idn)
        kind, hom, d, order = self.dispatch(G)
        if kind in ("enum", "product", "other"):
            pass
        elif self.scheme:
            a = self.scheme_step(G, hom, x, y, known)
            if a is not NotImplemented:
                return a
        if kind == "giant":
            self.stats["giant_natural"] += 1
            return self.giant(G, hom, x, y, known)
        if kind == "enum":
            return self.enum_cosets(G, hom, x, y, known)
        if kind == "product":
            self.stats["product_refine"] += 1
            self.stats["product_cosets"] += hom.image_order()
            return self.coset_union(hom, range(G.n), x, y, known)
        if kind != "other":
            self.stats["giant_johnson" if kind.startswith("johnson") else "giant_abstract"] += 1
            if kind.startswith("johnson"):
                self.stats[kind] += 1
            return self.giant(G, hom, x, y, known)
        self.stats["unrecognized_primitive"] += 1
        if order > self.max_enum:
            raise Unsupported(f"large primitive quotient of degree {d} and order {order}")
        self.stats["enum_large_primitive"] += 1
        return self.enum_cosets(G, hom, x, y, known)

    def dispatch(self, G):
        """(kind, hom, d, order) for transitive G: the primitive quotient has
        degree d and the given order, and kind is
          "giant" (hom: G -> Sym(d), the block action or the identity),
          "enum" (hom: the block action, or None when G is primitive),
          "johnson_k<k>" or "abstract" (hom: G -> Sym(m) onto a giant),
          "product" (hom: G -> Sym(r), the coordinate permutations),
          "other" (hom: the block action, or None).
        It depends only on G, so it is cached by G's generators; reusing the
        homomorphism objects also keeps their kernels and the Young subgroups
        of young_group across calls (the results are identical)."""
        key = (G.n, tuple(G.gens))
        rec = self._dispatch.get(key)
        if rec is not None:
            self._dispatch.move_to_end(key)
            return rec
        rec = self._dispatch[key] = self._compute_dispatch(G)
        if len(self._dispatch) > self.dispatch_cache:
            self._dispatch.popitem(last=False)
        return rec

    def _compute_dispatch(self, G):
        n = G.n
        blocks = self._hints.get((n, tuple(G.gens))) if self._hints else None
        if blocks is None:
            blocks = top_block_system(G)
        else:
            self.stats["product_hint"] += 1
        if blocks is None:                          # G itself is primitive
            d, phi, order = n, None, G.order()
        else:
            d = len(blocks)
            block_of = [0] * n
            for i, B in enumerate(blocks):
                for p in B:
                    block_of[p] = i
            reps = [B[0] for B in blocks]
            phi = ActionHom(G, d, lambda g: tuple(block_of[g[r]] for r in reps))
            order = phi.image_order()
        if d >= 5 and order in (math.factorial(d), math.factorial(d) // 2):
            return "giant", phi if phi is not None else ActionHom(G, n, None), d, order
        if order <= self.enum_limit or d < 5:
            return "enum", phi, d, order
        P = phi.image_group() if phi else G

        def compose(m, f):
            if phi is None:
                return ActionHom(G, m, f)
            return ActionHom(G, m, lambda g: f(phi.image_of(g)))

        J = johnson_structure(P)
        if J is not None and (J[1] == 2 or self.recognize):
            m, k, f = J
            return f"johnson_k{k}", compose(m, f), d, order
        R = product_action(P) if self.recognize else None
        if R is not None:
            psi = compose(R.r, R.f)
            if self.product_hint:
                # Inherited hierarchy: the kernel K (coordinates fixed) acts on
                # the fibers of coordinate 0 as the group of that coordinate.
                # Their preimages are a block system of K; use it as K's next
                # primitive quotient (any block system gives exact reductions).
                fib = [0] * d
                for i, F in enumerate(R.fibers0):
                    for b in F:
                        fib[b] = i
                hint = [[] for _ in R.fibers0]
                for p in range(n):
                    hint[fib[p if phi is None else block_of[p]]].append(p)
                K = psi.kernel()
                self._hints[(n, tuple(K.gens))] = hint
            return "product", psi, d, order
        A = giant_labels(P) if self.recognize else None
        if A is not None:
            return "abstract", compose(*A), d, order
        return "other", phi, d, order

    def scheme_step(self, G, phi, x, y, known=None):
        """Johnson and Hamming structure on the labels (Babai's "Johnson"
        outcome of Split-or-Johnson, applied before GiantStep).

        phi: G -> Sym(q) is onto Sym(q) or Alt(q). If some color class of x's
        two-label projection (label_projection) is exactly a Johnson graph
        J(m, k) (m >= 2k >= 4) or a Hamming graph H(r, D) (D >= 2) on all q
        labels, its embedding E_x (labels -> k-subsets of range(m), or ->
        range(D)^r) is unique up to the automorphism group A of the graph
        (Sym(m), times complementation if m = 2k; Sym(D) wr Sym(r)). Every g in
        Iso_G(x, y) maps x's projection onto y's (that is what GiantStep uses
        too), so phi(g) maps the class graph of x onto that of y, hence E_x
        onto an embedding of y's graph. So y's class graph must have the same
        type (else Iso is empty), and phi(g) lies in J_x sigma0, where sigma0
        maps E_x to E_y and J_x = E_x^-1 A E_x <= Sym(q). Then
            Iso_G(x, y) = Iso_H(x, y^(tau^-1)) tau,
        with H = phi^-1(J_x & phi(G)) and tau a lift of sigma0 (multiplied by
        an odd element of J_x when phi(G) = Alt(q) and sigma0 is odd; if J_x
        has none, Iso is empty). Returns NotImplemented when x has no such
        class."""
        q = phi.m
        proj = self.label_projection(G, phi, x, y)
        if proj is None or proj[2] is None:
            return NotImplemented
        px, py = proj[2], proj[3]
        key = self._proj_key(G, phi) + (tuple(x),)
        sx = self._schemes.get(key, False)
        if sx is False:
            sx = self._schemes[key] = _find_scheme(q, px)
        if sx is None:
            return NotImplemented
        color, kind, ex = sx
        nbr = _class_graph(q, py, color)
        ey = None
        if nbr is not None:
            ey = johnson_embedding(nbr) if kind == "johnson" else hamming_embedding(nbr)
        self.stats["scheme_" + kind] += 1
        if ey is None or ey[:2] != ex[:2]:
            return None
        gens, order, sigma0 = _scheme_group(q, kind, ex, ey)
        if phi.image_order() != math.factorial(q):          # phi(G) = Alt(q)
            gens, odd = _even_part(gens)
            if odd is not None:
                order //= 2
            if parity(sigma0):
                if odd is None:
                    return None
                sigma0 = mul(odd, sigma0)
        H = phi.preimage(gens, order=order)
        tau = phi.lift(sigma0)
        a = self.solve(H, range(G.n), x, act(y, inv(tau)))
        if a is None:
            return None
        return Coset(a.gens if known is None else known, mul(a.rep, tau))

    def enum_cosets(self, G, phi, x, y, known=None):
        """Enumerate the quotient: Iso_G(x,y) = U_p Iso_K(x, y^(tau_p^-1)) tau_p."""
        if phi is None:
            return self.enumerate(G, x, y, known)
        self.stats["enum_cosets"] += 1
        return self.coset_union(phi, range(G.n), x, y, known)

    def coset_union(self, phi, D, x, y, known=None):
        """Iso_G(x|D, y|D) for G = phi.G and a G-invariant D, as the union over
        p in phi(G) of B(p) = Iso_K(x|D, y^(tau_p^-1)|D) tau_p, where
        K = ker(phi) and tau_p = lift(p).

        Every nonempty B(p) is a right coset Aut_K(x|D) sigma_p, and for
        automorphisms a of x and b of y in G, a B(p) b = B(phi(a) p phi(b)).

        Full mode. Aut_K(x|D) is computed once, as the x-vs-x branch; then
        each p only needs one isomorphism (its recursive call hits the memo).
        Once some sigma in Iso is known, each found generator a of Aut_G(x|D)
        gives b = sigma^-1 a sigma in Aut_G(y|D). If e^-1 p lies in
        P = <phi(b)> for an explored e, then B(p) = B(e) b is empty when B(e)
        is, and otherwise lies in <out> sigma^-1 a sigma ... = <out> sigma,
        where out = Aut_K(x|D) gens + the ratios sigma_p sigma^-1 found. So the
        pruned p add nothing: <out> sigma is all of Iso, i.e. <out> is the
        full automorphism group Aut_G(x|D).

        One-mode (Aut_G(x|D) = <known> given, one isomorphism wanted): B(p) is
        nonempty iff B(phi(a) p) is, so one p per orbit phi(<known>) p suffices."""
        n, m = phi.G.n, phi.m
        K = phi.kernel()
        elems = list(phi.image_group().elements())
        if known is not None:
            L = PermGroup(m, [phi.image_of(a) for a in known])
            explored = []
            for p in elems:
                if any(L.contains(mul(p, inv(e))) for e in explored):
                    self.stats["pruned"] += 1
                    continue
                explored.append(p)
                tau = phi.lift(p)
                a = self.solve(K, D, x, act(y, inv(tau)))
                if a is not None:
                    return Coset(known, mul(a.rep, tau))
            return None
        base = None                     # Aut_K(x|D): the x-vs-x branch
        sigma = s_inv = P = None
        ratios, explored = [], []
        for p in elems:
            if P is not None and any(P.contains(mul(inv(e), p)) for e in explored):
                self.stats["pruned"] += 1
                continue
            explored.append(p)
            tau = phi.lift(p)
            if base is None:
                base = self.solve(K, D, x, x)
            a = self.solve(K, D, x, act(y, inv(tau)))
            if a is None:
                continue
            rep = mul(a.rep, tau)       # phi(rep) = p, since a.rep is in K
            if sigma is None:
                sigma, s_inv = rep, inv(p)
                continue                # phi(Aut_K(x|D)) is trivial: P stays trivial
            ratios.append(mul(rep, inv(sigma)))
            # phi(sigma^-1 (rep sigma^-1) sigma) = phi(sigma)^-1 p
            P = PermGroup(m, (P.gens if P is not None else []) + [mul(s_inv, p)])
        if sigma is None:
            return None
        return Coset(reduce_gens(n, list(base.gens) + ratios), sigma)

    # -- giants ---------------------------------------------------------------
    def giant(self, G, phi, x, y, known=None):
        """phi: G -> Sym(q) with image Sym(q) or Alt(q), and G transitive.

        The paper normalizes Sym(q) to Alt(q) first, which costs two cosets with
        a full GiantStep each. GiantStep runs on G directly instead: the label
        refinement is invariant under all of G, LiftAndContinue lifts Young
        subgroups of Sym(q) when phi(G) = Sym(q) (no parity condition), and
        the large-symmetry branch adds the odd coset of ker(phi) when the
        certificates only map onto Alt(q). The parity-restricted path is kept
        for phi(G) = Alt(q)."""
        return self.giant_step(G, phi, x, y, known)

    def _proj_key(self, G, phi):
        return (tuple(G.gens), tuple(phi.image_of(g) for g in G.gens))

    def label_projection(self, G, phi, x, y):
        """The one-label or two-label map of the positions (the paper's
        support classification): the support of a position is the set of labels
        fixed by its stabilizer. Pull the colors back to the labels: unary label
        colors for one-label supports, a pair coloring for two-label supports.
        Returns (cx, cy, px, py), or None when supports are not 1 or 2 labels.
        G must be transitive. The support map depends only on (G, phi) and is
        cached."""
        n, q = G.n, phi.m
        key = self._proj_key(G, phi)
        supp = self._supp.get(key)
        if supp is None:
            F0, supp = label_support(G, phi)
            if len(F0) not in (1, 2):
                supp = ()
            self._supp[key] = supp
        if not supp:
            return None
        out = []
        for z in (x, y):
            fib = {}
            for w in range(n):
                fib.setdefault(supp[w], []).append(z[w])
            out.append({s: tuple(sorted(v)) for s, v in fib.items()})
        rank = {v: i for i, v in enumerate(sorted(set(out[0].values()) | set(out[1].values())))}
        if len(supp[0]) == 1:
            cx = [rank[out[0][(a,)]] for a in range(q)]
            cy = [rank[out[1][(a,)]] for a in range(q)]
            return cx, cy, None, None
        none = len(rank)
        px = [[rank[out[0][(a, b)]] if (a, b) in out[0] else none for b in range(q)] for a in range(q)]
        py = [[rank[out[1][(a, b)]] if (a, b) in out[1] else none for b in range(q)] for a in range(q)]
        return [0] * q, [0] * q, px, py

    def giant_step(self, G, phi, x, y, known=None):
        """GiantStep for phi(G) = Sym(q) or Alt(q).

        The labels are refined by the support projection first. Certificates
        are computed only when that leaves the labels uniform (just before
        individualization), and only for x, where they are cached: a full
        certificate is a group of automorphisms of x, which is all the
        large-symmetry branch and the pruning need. With cert_refine the
        certificate signatures of x and y also refine the labels (the paper's
        "structure" outcome); that needs the certificates of y as well."""
        self.stats["giant_step"] += 1
        n, q = G.n, phi.m
        sym = phi.image_order() == math.factorial(q)
        proj = self.label_projection(G, phi, x, y)
        cx, cy, px, py = proj if proj else ([0] * q, [0] * q, None, None)
        hx = hy = {}
        r = self.label_refine(q, hx, hy, cx, cy, px, py)
        if r is None:
            return None
        cx, cy = r
        seeds = []
        if len(set(cx)) == 1 and self.certificates and q > self.kappa:
            certs_x = self.certificates_of(G, phi, x)
            F = self.large_symmetry(phi, certs_x)
            if F is not None:
                return self.large_symmetry_step(G, phi, sym, F, x, y, known)
            seeds = [k for (_, _, K) in certs_x.values() if K for k in K]
            if self.cert_refine:
                certs_y = certs_x if x == y else self.certificates_of(G, phi, y)
                hx = {T: (s, r) for T, (s, r, _) in certs_x.items()}
                hy = {T: (s, r) for T, (s, r, _) in certs_y.items()}
                r = self.label_refine(q, hx, hy, cx, cy, px, py)
                if r is None:
                    return None
                cx, cy = r
        if len(set(cx)) > 1:
            return self.lift_and_continue(G, phi, sym, cx, cy, x, y)
        return self.individualize(G, phi, sym, cx, cy, hx, hy, px, py, x, y, known, seeds)

    def label_refine(self, q, hx, hy, cx, cy, px=None, py=None):
        """refine_labels (1-WL with the hypergraphs and pair colors), and with
        giant_wl=2 and a pair coloring, alternated with joint 2-WL (the
        coherent closure) of the pair coloring with the label colors on its
        diagonal, until stable. Both steps are joint and content-named, so
        every isomorphism maps the x-coloring onto the y-coloring. Returns
        (cx, cy), or None if the color histograms differ."""
        cx, cy = refine_labels(q, hx, hy, cx, cy, px, py)
        if Counter(cx) != Counter(cy):
            return None
        if px is None or self.giant_wl != 2:
            return cx, cy
        fx = [(0, px[a][b]) if a != b else None for a in range(q) for b in range(q)]
        fy = [(0, py[a][b]) if a != b else None for a in range(q) for b in range(q)]
        while True:
            k = len(set(cx))
            for a in range(q):
                fx[a * q + a] = (-1, cx[a])
                fy[a * q + a] = (-1, cy[a])
            r = wl2_joint(fx, fy)
            if r is None:
                return None
            fx, fy = r
            cx, cy = fx[::q + 1], fy[::q + 1]
            if not hx or len(set(cx)) == k:
                return cx, cy
            k = len(set(cx))
            qx = [fx[a * q:(a + 1) * q] for a in range(q)]
            qy = [fy[a * q:(a + 1) * q] for a in range(q)]
            cx, cy = refine_labels(q, hx, hy, cx, cy, qx, qy)
            if Counter(cx) != Counter(cy):
                return None
            if len(set(cx)) == k:
                return cx, cy
            fx = [(0, c) for c in fx]
            fy = [(0, c) for c in fy]

    def large_symmetry_step(self, G, phi, sym, F, x, y, known=None):
        """F <= Aut_G(x) with phi(F) >= Alt(q). For g in Iso_G(x, y) there is
        f in F with phi(f^-1 g) in {1, t'} (t' = phi(t), t the lift of a
        transposition; t' is needed only when phi(G) = Sym(q) > phi(F)). Then
        f^-1 g is in Iso_ker(x, y) or in Iso_ker(x, y^(t^-1)) t. Only x's
        certificates are used: if y lacks the symmetry, Iso is empty and so
        are these kernel cosets."""
        self.stats["large_symmetry"] += 1
        n, q = G.n, phi.m
        K = phi.kernel()
        cosets = [G.idn]
        if sym and PermGroup(q, [phi.image_of(f) for f in F]).order() < math.factorial(q):
            cosets.append(phi.lift(cycle(q, [0, 1])))
        answers = []
        for c in cosets:
            a = self.solve(K, range(n), x, act(y, inv(c)))
            if a is not None:
                answers.append(Coset(a.gens, mul(a.rep, c)))
                if known is not None:
                    break
        out = combine(n, answers)
        if out is None:
            return None
        if known is not None:
            return Coset(known, out.rep)
        return Coset(reduce_gens(n, list(F) + out.gens), out.rep)

    def individualize(self, G, phi, sym, cx, cy, hx, hy, px, py, x, y, known, seeds):
        """The labels are uniform: individualize one label on each side.

        B(l, g) = { g' in Iso_G(x, y) : phi(g') maps label l to label g } is
        computed exactly by refining with l individualized in x and g in y and
        calling LiftAndContinue (the refinement is isomorphism-invariant). For
        a in Aut_G(x) and b in Aut_G(y),
            a B(l, g) b = B(l^(phi(a)^-1), g^phi(b)).                    (*)

        Full mode: Iso = U_g B(0, g). Each nonempty B(0, g) is a right coset
        A0 sigma_g of A0 = Stab_{Aut_G(x)}(label 0), which is computed once as
        the x-vs-x branch B(0, 0) of (x, x). Afterwards every branch only needs
        one isomorphism (its LiftAndContinue group is the same, so the memo in
        cont applies). Pruning: once some sigma in Iso is known, every found
        a in Aut_G(x) (generators of A0, ratios sigma_g sigma^-1, automorphisms
        from full certificates) gives b = sigma^-1 a sigma in Aut_G(y). If g is
        in the orbit of an explored e under the group of these phi(b), then by
        (*) B(0, g) = B(0, e) b: empty if B(0, e) is, else contained in
        <out> sigma^-1 a sigma ... = <out> a sigma = <out> sigma. Hence the
        returned <out> sigma, with out = A0 gens + ratios + certificate
        automorphisms, contains all of Iso, and <out> = Aut_G(x) exactly.

        One-mode (Aut_G(x) = <known>, one isomorphism wanted): fix g = 0 on the
        y side. By (*) B(l, 0) is empty for all l of one phi(<known>)-orbit or
        for none, so one representative l per orbit suffices. l = 0 comes
        first: its branch group is the one used in full mode, so its recursion
        hits the memo."""
        q = phi.m

        def refined(l, g, z):
            cz, hz, pz = (cx, hx, px) if z is x else (cy, hy, py)
            ix = [2 * c for c in cx]
            iz = [2 * c for c in cz]
            ix[l] += 1
            iz[g] += 1
            return self.label_refine(q, hx, hz, ix, iz, px, pz)

        return self.branch_labels(G, phi, sym, list(range(q)), list(range(q)), refined,
                                  x, y, known, seeds)

    def branch_labels(self, G, phi, sym, Cx, Cy, refined, x, y, known, seeds=()):
        """Iso_G(x, y) = U_{g in Cy} B(l0, g), l0 = Cx[0], where Cx and Cy are
        the label classes of one color in x and y (every isomorphism maps l0
        into Cy). refined(l, g, z) is the joint invariant refinement with l
        individualized in x and g in z (None if it rules the branch out); each
        branch is finished by LiftAndContinue. The pruning, the memo and
        one-mode are those described in `individualize` (with label 0 read as
        l0, and the one-mode target 0 as Cy[0]); the arguments there only use
        (*), which holds for every invariant refinement."""
        n, q = G.n, phi.m
        l0, g0 = Cx[0], Cy[0]
        seeds = list(seeds)
        if known is not None:
            orbit = _label_orbits(q, [phi.image_of(a) for a in known])
            reps = []
            seen = set()
            for l in Cx:
                if orbit[l] not in seen:
                    seen.add(orbit[l])
                    reps.append(l)
            self.stats["pruned"] += len(Cx) - len(reps)
            for l in reps:
                r = refined(l, g0, y)
                if r is None:
                    continue
                self.stats["branch"] += 1
                if l != l0:
                    self.stats["one_offbase"] += 1
                    if self.seed:
                        self.seed_label_stabilizer(phi, sym, r[0], known, l, x)
                a = self.lift_and_continue(G, phi, sym, r[0], r[1], x, y, _stash(r, False))
                if a is not None:
                    return Coset(known, a.rep)
            return None

        parent = list(range(q))

        def find(v):
            while parent[v] != v:
                parent[v] = parent[parent[v]]
                v = parent[v]
            return v

        def absorb(perms):
            for p in perms:
                for i in range(q):
                    ri, rj = find(i), find(p[i])
                    if ri != rj:
                        parent[max(ri, rj)] = min(ri, rj)

        base = sigma = s = s_inv = None
        out = list(seeds)
        explored = []
        for g in Cy:
            if explored and find(g) in {find(e) for e in explored}:
                self.stats["pruned"] += 1
                continue
            explored.append(g)
            r = refined(l0, g, y)
            if r is None:
                continue
            ax, ay = r[0], r[1]
            self.stats["branch"] += 1
            if base is None:
                base = self.lift_and_continue(G, phi, sym, ax, ax, x, x, _stash(r, True))
            if x == y and ax == ay:
                a = base
            else:
                a = self.lift_and_continue(G, phi, sym, ax, ay, x, y, _stash(r, False))
            if a is None:
                continue
            if sigma is None:
                sigma = a.rep
                s = phi.image_of(sigma)
                s_inv = inv(s)
                absorb(mul(mul(s_inv, phi.image_of(h)), s) for h in list(base.gens) + seeds)
            else:
                out.append(mul(a.rep, inv(sigma)))
                absorb([mul(s_inv, phi.image_of(a.rep))])
        if sigma is None:
            return None
        return Coset(self.reduce_through(G, phi, list(base.gens) + out), sigma)

    def reduce_through(self, G, phi, gens):
        """An irredundant generating list of <gens> (gens in G). When phi is
        faithful on G, redundancy is decided on the images in Sym(m), which is
        much cheaper than in degree n; otherwise reduce_gens."""
        f = phi.__dict__.get("_faithful")
        if f is None:
            f = phi._faithful = phi.kernel().order() == 1
        if not f:
            return reduce_gens(G.n, gens)
        idn = G.idn
        gens = [g for g in dict.fromkeys(gens) if g != idn]
        if len(gens) <= 4:
            return gens
        back = {}
        for g in gens:
            back.setdefault(phi.image_of(g), g)
        return [back[h] for h in PermGroup(phi.m, list(back)).gens]

    def young_group(self, phi, sym, cx):
        """H = phi^-1(Young subgroup of the partition of cx) when phi(G) = Sym(q),
        and phi^-1(Young subgroup ∩ Alt(q)) when phi(G) = Alt(q). H depends
        only on the partition; it is built once per phi, so all branches of a
        GiantStep get the same group object (and the memo in cont applies)."""
        q = phi.m
        X = color_classes(cx)
        cache = phi.__dict__.setdefault("_young", {})
        key = tuple(tuple(C) for C in X.values())
        H = cache.get(key)
        if H is None:
            big = [C for C in X.values() if len(C) >= 2]
            if sym:
                ygens = [g for C in big for g in sym_gens(q, C)]
            else:
                ygens = [g for C in big for g in alt_gens(q, C)]
                transp = [cycle(q, C[:2]) for C in big]
                ygens += [mul(transp[0], t) for t in transp[1:]]
            root = getattr(phi, "_yroot", None)
            if root is None:
                H = cache[key] = phi.preimage(ygens)
            else:                           # a Young node: psi0^-1(Young(partition))
                # The label positions of the classes (all but one point each)
                # make a short base prefix with small orbits; the result is the
                # same group as phi.preimage(ygens).
                K = phi.kernel()
                order = math.prod(math.factorial(len(C)) for C in big) * K.order()
                base = [root.gamma[a] for C in big for a in C[:-1]]
                H = cache[key] = PermGroup(phi.G.n, [phi.lift(h) for h in ygens] + K.gens,
                                           base=base, order=order,
                                           ambient_base=phi.G.short_base())
                self._ynodes.setdefault(tuple(H.gens), (root, key))
        return H

    def lift_and_continue(self, G, phi, sym, cx, cy, x, y, stash=None):
        """The overcoset E of label maps taking color classes of cx to those of
        cy, intersected with phi(G), lifted to H tau in G (H = young_group);
        then Continue under H on (x, y^(tau^-1)). stash(pi), if given, is the
        stable Young refinement state of the continuation (pi = phi(tau));
        it is recorded for (H, x, y^(tau^-1)) so that young_step need not
        recompute it."""
        n, q = G.n, phi.m
        X, Y = color_classes(cx), color_classes(cy)
        pi = [0] * q
        for c, cls in X.items():
            for a, b in zip(cls, Y[c]):
                pi[a] = b
        pi = tuple(pi)
        H = self.young_group(phi, sym, cx)
        if not sym and parity(pi):
            big = [C for C in X.values() if len(C) >= 2]
            if not big:
                return None
            pi = mul(cycle(q, big[0][:2]), pi)
        tau = phi.lift(pi)
        yt = act(y, inv(tau))
        if stash is not None:
            if len(self._ystate) > 64:
                self._ystate.clear()
            self._ystate[(tuple(H.gens), tuple(x), yt)] = stash(pi)
        a = self.solve(H, range(n), x, yt)
        if a is None:
            return None
        return Coset(a.gens, mul(a.rep, tau))

    def seed_label_stabilizer(self, phi, sym, ax, known, l, x):
        """For the branch of x-label l (ax = the refined coloring of x with l
        individualized), Aut_H(x) = Stab_<known>(l) for H = young_group(ax):
        an element of Aut_G(x) = <known> preserves ax iff it fixes l, because
        the refinement is invariant and {l} is a class of ax. Record it in the
        memo, so that the branch runs in one-mode too."""
        n, q = phi.G.n, phi.m
        H = self.young_group(phi, sym, ax)
        key = (tuple(H.gens), tuple(x))
        if key in self.memo:
            return
        C = PermGroup(n + q, [a + tuple(n + v for v in phi.image_of(a)) for a in known],
                      base=[n + l])
        self.memo[key] = reduce_gens(n, [s[:n] for s in C._tail(1).gens])

    # -- the Young-label step: aggregation over the whole instance ------------
    def young_root(self, G):
        """A label structure for the intransitive group G, or None (cached).

        Labels: the union gamma of the G-orbits O with |O| >= 3 on which G acts
        as the full product of Sym(O) (the restriction psi to gamma has image
        exactly prod Sym(O); orbits are taken greedily, smallest first). On a
        graph stage these are the diagonal positions, i.e. the vertex classes.
        The support of a position w is the set of labels fixed by G_w (as in
        label_projection); positions with one or two labels in their support
        are recorded with their G-orbit index. Everything depends on G alone,
        and the support map is G-equivariant, hence H-equivariant for every
        subgroup H: supp(w^h) = supp(w)^psi(h)."""
        key = tuple(G.gens)
        if key in self._yroots:
            return self._yroots[key]
        r = self._yroots[key] = self._young_detect(G)
        return r

    def _young_detect(self, G):
        n = G.n
        order = G.order()
        orbs = G.orbits()
        cand = sorted((O for O in orbs if 3 <= len(O) < n
                       and order % math.factorial(len(O)) == 0), key=lambda O: (len(O), O[0]))
        if not any(len(O) >= self.young_min for O in cand):
            return None

        homs = {}

        def product(Os):
            t = math.prod(math.factorial(len(O)) for O in Os)
            if order % t:
                return False
            D = tuple(sorted(p for O in Os for p in O))
            h = homs[D] = RestrictionHom(G, D)
            return h.image_order() == t

        if not product(cand):
            acc = []
            for O in cand:
                if product(acc + [O]):
                    acc.append(O)
            cand = acc
        if not any(len(O) >= self.young_min for O in cand):
            return None
        self.stats["young_root"] += 1
        gamma = sorted(p for O in cand for p in O)
        m = len(gamma)
        lab = {p: i for i, p in enumerate(gamma)}
        psi = homs[tuple(gamma)]
        ig = [psi.image_of(g) for g in G.gens]
        gens = G.gens
        idm = tuple(range(m))
        unary = [[] for _ in range(m)]
        pair = {}
        for k, O in enumerate(orbs):
            # t[w] = psi(u_w) for a transversal element u_w with O[0]^u_w = w;
            # F = the labels fixed by psi(G_O[0]), checked on the Schreier
            # generators u_w g u_(w^g)^-1, which generate G_O[0].
            p = O[0]
            t = {p: idm}
            F = list(range(m))
            queue = [p]
            for w in queue:
                tw = t[w]
                for g, im in zip(gens, ig):
                    w2 = g[w]
                    t2 = t.get(w2)
                    if t2 is None:
                        t[w2] = mul(tw, im)
                        queue.append(w2)
                    elif F:
                        F = [a for a in F if im[tw[a]] == t2[a]]
            if len(F) == 1:
                a = F[0]
                for w in O:
                    unary[t[w][a]].append((w, k))
            elif len(F) == 2:
                a, b = F
                for w in O:
                    tw = t[w]
                    pair.setdefault((tw[a], tw[b]), []).append((w, k))
        R = YoungRoot()
        R.G, R.psi, R.m, R.gamma = G, psi, m, gamma
        R.classes = tuple(tuple(sorted(lab[p] for p in O)) for O in
                          sorted(cand, key=lambda O: O[0]))
        R.unary, R.pair = unary, pair
        psi._yroot = R
        return R

    def young_refine(self, R, cls, x, y):
        """Jointly refine the labels of R: the initial color of a label is its
        class index cls[a] and the colors (orbit, x[w]) of the positions with
        support (a,); a pair (a, b) gets those with support (a, b). 2-WL
        (young_wl=2) or 1-WL with pair colors (young_wl=1) follows. For g in
        Iso_H(x, y), H <= R.G preserving the classes, psi(g) maps the
        x-coloring onto the y-coloring (the support map is equivariant, orbits
        are invariant), so it maps the refined colors onto each other too.
        Returns (dx, dy, state) or None; `state` restarts the refinement with
        one label individualized on each side (young_marked)."""
        m = R.m
        init = []
        for z in (x, y):
            un, off = self.young_pullback(R, z)
            init.append(([(0, cls[a], un[a]) for a in range(m)], off))
        if self.young_wl == 2:
            none = (2,)
            flat = []
            for diag, off in init:
                f = [none] * (m * m)
                for a in range(m):
                    f[a * m + a] = diag[a]
                for (a, b), v in off.items():
                    f[a * m + b] = v
                flat.append(f)
            r = wl2_joint(flat[0], flat[1])
            if r is None:
                return None
            fx, fy = r
            return fx[::m + 1], fy[::m + 1], (fx, fy)
        (dgx, ofx), (dgy, ofy) = init
        cx, cy = _rank2(dgx, dgy)
        vals = {v: i for i, v in enumerate(sorted(set(ofx.values()) | set(ofy.values())))}
        nn = len(vals)
        px = [[nn] * m for _ in range(m)]
        py = [[nn] * m for _ in range(m)]
        for P, off in ((px, ofx), (py, ofy)):
            for (a, b), v in off.items():
                P[a][b] = vals[v]
        if Counter(cx) != Counter(cy):
            return None
        dx, dy = refine_labels(m, {}, {}, cx, cy, px, py)
        if Counter(dx) != Counter(dy):
            return None
        return dx, dy, (dx, dy, px, py)

    def young_marked(self, m, state, l, g):
        """The refinement of young_refine with label l individualized in x and
        g in y, restarted from its stable coloring `state` (jointly named).
        Starting from (stable coloring + mark) instead of (initial coloring +
        mark) gives the same stable partition, because the stable refinement
        is monotone and idempotent; either way it is joint and invariant."""
        if self.young_wl == 2:
            # 1-WL first (cheap): if it already makes the labels discrete, 2-WL
            # cannot refine the partition. Otherwise its label colors go on the
            # diagonal and 2-WL runs; the stable partition is the same as
            # 2-WL's from the marked coloring (1-WL steps are implied by 2-WL).
            fx, fy = state
            cx, cy = [2 * c for c in fx[::m + 1]], [2 * c for c in fy[::m + 1]]
            cx[l] += 1
            cy[g] += 1
            px = [fx[a * m:(a + 1) * m] for a in range(m)]
            py = [fy[a * m:(a + 1) * m] for a in range(m)]
            ax, ay = refine_labels(m, {}, {}, cx, cy, px, py)
            if Counter(ax) != Counter(ay):
                return None
            top = 2 * max(max(fx), max(fy)) + 2
            fx = [2 * c for c in fx]
            fy = [2 * c for c in fy]
            for a in range(m):
                fx[a * (m + 1)] = top + 2 * ax[a] + 1
                fy[a * (m + 1)] = top + 2 * ay[a] + 1
            if len(set(ax)) == m:
                return ax, ay, (fx, fy)
            r = wl2_joint(fx, fy, ranked=True)
            if r is None:
                return None
            return r[0][::m + 1], r[1][::m + 1], r
        dx, dy, px, py = state
        ix = [2 * c for c in dx]
        iy = [2 * c for c in dy]
        ix[l] += 1
        iy[g] += 1
        ax, ay = refine_labels(m, {}, {}, ix, iy, px, py)
        if Counter(ax) != Counter(ay):
            return None
        return ax, ay, (ax, ay, px, py)

    def young_child_state(self, m, info, pi, both_x):
        """The stable state (dx, dy, state) of young_refine for the
        continuation of a branch: labels of y are renamed by pi (y^(tau^-1) at
        label a is y at pi(a)); both_x: the x-vs-x branch. The child's initial
        coloring lies between the branch's marked coloring and its stable
        refinement, so its stable partition is this one."""
        if self.young_wl == 2:
            fx, fy = info
            if both_x:
                fy = fx
            fy = [fy[pi[a] * m + pi[b]] for a in range(m) for b in range(m)]
            return fx[::m + 1], fy[::m + 1], (fx, fy)
        ax, ay, px, py = info
        if both_x:
            ay, py = ax, px
        ay = [ay[pi[a]] for a in range(m)]
        py = [[py[pi[a]][pi[b]] for b in range(m)] for a in range(m)]
        return ax, ay, (ax, ay, px, py)

    def young_pullback(self, R, z):
        """The colors of z pulled back to the labels of R: per label, the sorted
        (orbit, z[w]) over the positions w with support (a,); per pair, those
        with support (a, b). Cached (the branches of one step share x and y)."""
        key = (id(R), z)
        c = self._ypull.get(key)
        if c is None:
            un = [tuple(sorted((k, z[w]) for w, k in ws)) for ws in R.unary]
            off = {s: (1, tuple(sorted((k, z[w]) for w, k in ws))) for s, ws in R.pair.items()}
            if len(self._ypull) > 256:
                self._ypull.clear()
            c = self._ypull[key] = (un, off)
        return c

    def young_step(self, G, x, y, known=None):
        """Iso_G(x, y) for intransitive G with a Young label structure: G is
        psi0^-1(Young(partition)) for a root R (G = R.G at the root). Returns
        _FALLBACK when there is none, or when no large class can be
        individualized usefully (then the orbit chain runs).

        1. Refine the labels jointly (young_refine). If the partition splits,
           LiftAndContinue under psi0^-1(Young(refined)), exact as in GiantStep:
           every g in Iso_G(x, y) maps the refined classes of x onto those of
           y, and the class-matching map lies in Young(partition) = psi0(G).
        2. If x is G-invariant, Iso_G(x, y) is G (x == y) or empty.
        3. Otherwise individualize a label of a class of size >= young_min
           (branch_labels), the smallest class that meets the support of a
           position in a G-orbit where x is not constant."""
        node = self._ynodes.get(tuple(G.gens))
        if node is None:
            R = self.young_root(G)
            if R is None:
                return _FALLBACK
            node = (R, R.classes)
        R, part = node
        m = R.m
        cls = [0] * m
        for i, C in enumerate(part):
            for a in C:
                cls[a] = i
        r = self._ystate.pop((tuple(G.gens), x, y), None)
        if r is None:
            self.stats["young_refine"] += 1
            r = self.young_refine(R, cls, x, y)
            if r is None:
                return None
        dx, dy, state = r
        if len(set(dx)) > len(part):
            self.stats["young_split"] += 1
            return self.lift_and_continue(R.G, R.psi, True, dx, dy, x, y)
        if all(maps(h, x, x) for h in G.gens):
            return Coset(list(G.gens), G.idn) if x == y else None
        touched = set()
        for O in G.orbits():
            x0 = x[O[0]]
            if any(x[w] != x0 for w in O):
                touched.update(O)
        involved = set()
        for a in range(m):
            if any(w in touched for w, _ in R.unary[a]):
                involved.add(cls[a])
        for (a, b), ws in R.pair.items():
            if cls[a] not in involved or cls[b] not in involved:
                if any(w in touched for w, _ in ws):
                    involved.update((cls[a], cls[b]))
        big = [C for i, C in enumerate(part) if len(C) >= self.young_min and i in involved]
        if not big:
            return _FALLBACK
        if self.young_pick == "large":
            C = list(min(big, key=lambda C: (-len(C), C[0])))
        else:
            C = list(min(big, key=lambda C: (len(C), C[0])))
        self.stats["young_ind"] += 1

        def refined(l, g, z):
            st = state
            if z is not y:              # (branch_labels only refines against y)
                rz = self.young_refine(R, cls, x, z)
                if rz is None:
                    return None
                st = rz[2]
            r = self.young_marked(m, st, l, g)
            if r is None:
                return None
            ax, ay, info = r
            return ax, ay, (lambda pi, both_x: self.young_child_state(m, info, pi, both_x))

        return self.branch_labels(R.G, R.psi, True, C, C, refined, x, y, known)

    # -- local certificates (Algorithm 3) -------------------------------------
    def certificates_of(self, G, phi, x):
        """All local certificates of x, cached by (G, phi, x)."""
        key = self._proj_key(G, phi) + (tuple(x),)
        c = self._certs.get(key)
        if c is None:
            c = self._certs[key] = self.all_certificates(G, phi, x)
        return c

    def all_certificates(self, G, phi, x):
        return {T: self.local_certificate(G, phi, x, T)
                for T in itertools.combinations(range(phi.m), self.kappa)}

    def large_symmetry(self, phi, certs):
        """Generators of the full certificates if they map onto Alt(q), else None."""
        F = [k for (_, _, K) in certs.values() if K for k in K]
        if not F:
            return None
        q = phi.m
        if PermGroup(q, [phi.image_of(g) for g in F]).order() * 2 >= math.factorial(q):
            return F
        return None

    def local_certificate(self, G, phi, x, T):
        """Returns (signature, roles, K): K is a list of generators of a group of
        automorphisms of x mapping onto Alt(T) (full), or None (nonfull). The
        signature and roles are isomorphism invariants of (x, T). This works for
        phi(G) = Sym(q) as well as Alt(q): A = phi^-1(Alt(T) x Alt(rest)) lies
        in G either way, and conjugation by g in G maps A_T to A_(T^phi(g))."""
        self.stats["certificate"] += 1
        n, q, k = G.n, phi.m, len(T)
        Tset = set(T)
        rest = [g for g in range(q) if g not in Tset]
        tidx = {t: i for i, t in enumerate(T)}

        def phiT(g):
            img = phi.image_of(g)
            return tuple(tidx[img[t]] for t in T)

        def onto(H):
            return PermGroup(k, [phiT(g) for g in H.gens]).order() == alt_order

        alt_order = math.factorial(k) // 2
        A = phi.preimage(alt_gens(q, T) + alt_gens(q, rest))
        W, sig = set(), []
        while True:
            img = PermGroup(k, [phiT(g) for g in A.gens])
            if img.order() != alt_order:
                size = {}
                for o in img.orbits():
                    for i in o:
                        size[i] = len(o)
                roles = tuple(size[i] for i in range(k))
                return (("N", tuple(sig), img.order()), roles, None)
            U = [v for v in range(n) if v not in W]
            orbs = A.orbits(U)
            V = [v for o in orbs if not onto(A.stabilizer(o[0])) for v in o]   # affected
            if not V:
                K = A.pointwise_stabilizer(U)
                if onto(K):
                    return (("F", tuple(sig)), (k,) * k, list(K.gens))
                # orbits on which the test action is visible
                V = [v for o in orbs
                     if all(phiT(g) == identity(k) for g in A.pointwise_stabilizer(o).gens)
                     for v in o]
                if not V:
                    V = U
            A = self.check_new_window(A, V, x, phiT, k)
            W.update(V)
            sig.append((len(V), tuple(sorted(x[v] for v in V)), A.order()))

    def check_new_window(self, A, V, x, phiT, k):
        """Aut_A(x on V), by enumerating the cosets of M = ker(phi_T on A),
        with the automorphism pruning of coset_union."""
        psi = ActionHom(A, k, phiT)
        return PermGroup(A.n, self.coset_union(psi, V, x, x).gens, ambient_base=A.short_base())


def _stash(r, both_x):
    """The state builder of a refined branch (see young_step), if any."""
    if len(r) < 3:
        return None
    f = r[2]
    return lambda pi: f(pi, both_x)


def _label_orbits(q, perms):
    """Orbit representatives (least element) of <perms> on range(q), per point."""
    parent = list(range(q))

    def find(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    for p in perms:
        for i in range(q):
            ri, rj = find(i), find(p[i])
            if ri != rj:
                parent[max(ri, rj)] = min(ri, rj)
    return [find(v) for v in range(q)]


def _class_graph(q, p, color):
    """Neighbour sets of the color class `color` of the pair coloring p, or
    None if the class is not symmetric."""
    nbr = [set() for _ in range(q)]
    for a in range(q):
        row = p[a]
        for b in range(q):
            if b != a and row[b] == color:
                if p[b][a] != color:
                    return None
                nbr[a].add(b)
    return nbr


def _find_scheme(q, p):
    """The first color class (by color) of the pair coloring p that is a
    Johnson or Hamming graph on all q labels: (color, kind, embedding)."""
    colors = sorted({p[a][b] for a in range(q) for b in range(q) if a != b})
    for color in colors:
        nbr = _class_graph(q, p, color)
        if nbr is None or not nbr[0]:
            continue
        e = johnson_embedding(nbr)
        if e is not None:
            return color, "johnson", e
        e = hamming_embedding(nbr)
        if e is not None:
            return color, "hamming", e
    return None


def _scheme_group(q, kind, ex, ey):
    """Generators of J_x <= Sym(q) (the automorphisms of x's embedding), its
    order, and sigma0 mapping x's embedding onto y's."""
    if kind == "johnson":
        m, k, sx = ex
        sy = ey[2]
        ix = {v: l for l, v in enumerate(sx)}
        iy = {v: l for l, v in enumerate(sy)}

        def lab(s):
            return tuple(ix[frozenset(s[i] for i in sx[l])] for l in range(q))

        gens = [lab(s) for s in sym_gens(m, range(m))]
        order = math.factorial(m)
        if m == 2 * k:                  # complementation
            full = frozenset(range(m))
            gens.append(tuple(ix[full - sx[l]] for l in range(q)))
            order *= 2
        sigma0 = tuple(iy[sx[l]] for l in range(q))
        return gens, order, sigma0
    r, D, cx = ex
    cy = ey[2]
    ix = {v: l for l, v in enumerate(cx)}
    iy = {v: l for l, v in enumerate(cy)}
    gens = [tuple(ix[(s[v[0]],) + v[1:]] for v in cx) for s in sym_gens(D, range(D))]
    gens += [tuple(ix[tuple(v[t[c]] for c in range(r))] for v in cx) for t in sym_gens(r, range(r))]
    order = math.factorial(D) ** r * math.factorial(r)
    sigma0 = tuple(iy[v] for v in cx)
    return gens, order, sigma0


def _even_part(gens):
    """Generators of the even permutations in <gens> (Schreier generators for
    the transversal {1, o}), and an odd element o of <gens> (or None)."""
    odd = next((g for g in gens if parity(g)), None)
    if odd is None:
        return list(gens), None
    oi = inv(odd)
    out = []
    for g in gens:
        if parity(g):
            out.append(mul(g, oi))
            out.append(mul(odd, g))
        else:
            out.append(g)
            out.append(mul(mul(odd, g), oi))
    n = len(odd)
    idn = tuple(range(n))
    return [g for g in dict.fromkeys(out) if g != idn], odd
