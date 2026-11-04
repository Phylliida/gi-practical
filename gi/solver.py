"""String isomorphism under a permutation group, following the recursion of
Hajiaghayi & JafariRaviz (arXiv:2611.01399), Section 6, Algorithm 5.

    Iso_G(x, y) = { g in G : x^g = y }

is returned as Coset(gens, rep): every isomorphism is h * rep for some h in
<gens> = Aut_G(x), or None if there is no isomorphism.

What is implemented as in the paper:
  * Solve / Continue with the orbit-chain rule (largest orbit first),
  * the primitive-quotient dispatcher: enumerate small quotients, treat
    natural giants and the Johnson action on 2-sets as giants,
  * normalization of Sym(q) to Alt(q) with two cosets,
  * constant-size local certificates (Algorithm 3), with CheckNewWindow done by
    enumerating cosets of ker(phi_T) and solving on the window,
  * the "large known symmetry" branch (full certificates generate Alt(q)),
  * LiftAndContinue and CombineExact.

What is simplified (see README.md for details):
  * aggregation: certificate signatures are refined on the labels as a
    k-uniform colored hypergraph, then one label is individualized at a time.
    The paper uses ordered lockstep comparisons, Babai's Design Lemma,
    coherent configurations and its "first rectangle" step instead;
  * no row/column step (Algorithm 4), no phases, hierarchy caps or budget
    bookkeeping: those only matter for the running-time proof;
  * product actions (Maroti case r >= 2) and Johnson actions on k-sets with
    k >= 3 are enumerated, or raise Unsupported when too large.
Every simplification keeps the answer exact; only the running time changes.
"""
import itertools
import math
from collections import Counter, namedtuple

from .perm import identity, mul, inv, act, maps, parity, cycle, alt_gens
from .group import (PermGroup, ActionHom, RestrictionHom, reduce_gens, top_block_system,
                    johnson_labels, label_support, clear_chain_cache)

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


class Solver:
    def __init__(self, kappa=3, enum_limit=500, certificates=True, max_enum=100000):
        self.kappa = kappa                  # size of the local test sets
        self.enum_limit = enum_limit        # enumerate groups/quotients up to this order
        self.certificates = certificates    # use local certificates in GiantStep
        self.max_enum = max_enum            # refuse to enumerate anything larger
        self.stats = Counter()
        clear_chain_cache()                 # (a cache only: results do not depend on it)

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
        return Coset(reduce_gens(n, gens), rho.lift(a.rep))

    # -- Continue -------------------------------------------------------------
    def cont(self, G, x, y):
        """Iso_G(x, y) for G acting faithfully on all positions range(n)."""
        self.stats["cont"] += 1
        n = G.n
        if sorted(x) != sorted(y):
            return None
        if len(set(x)) == 1:
            return Coset(list(G.gens), G.idn)
        if G.order() <= self.enum_limit:
            return self.enumerate(G, x, y)
        orbs = G.orbits()
        if len(orbs) > 1:
            # orbit-chain rule, largest orbit first
            orbs.sort(key=lambda o: (-len(o), o[0]))
            first = orbs[0]
            rest = [p for o in orbs[1:] for p in o]
            a1 = self.solve(G, first, x, y)
            if a1 is None:
                return None
            H = PermGroup(n, a1.gens)
            a2 = self.solve(H, rest, x, act(y, inv(a1.rep)))
            if a2 is None:
                return None
            return Coset(a2.gens, mul(a2.rep, a1.rep))
        return self.transitive(G, x, y)

    def enumerate(self, G, x, y):
        self.stats["enumerate"] += 1
        isos = [g for g in G.elements() if maps(g, x, y)]
        if not isos:
            return None
        r0i = inv(isos[0])
        return Coset(reduce_gens(G.n, [mul(g, r0i) for g in isos]), isos[0])

    # -- the primitive-quotient dispatcher ------------------------------------
    def transitive(self, G, x, y):
        n = G.n
        blocks = top_block_system(G)
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
            self.stats["giant_natural"] += 1
            if phi is None:
                phi = ActionHom(G, n, None)      # identity
            return self.giant(G, phi, x, y)
        if order <= self.enum_limit or d < 5:
            return self.enum_cosets(G, phi, x, y)
        J = johnson_labels(phi.image_group() if phi else G)
        if J is not None:
            self.stats["giant_johnson"] += 1
            m, f = J
            if phi is None:
                psi = ActionHom(G, m, f)
            else:
                psi = ActionHom(G, m, lambda g, phi=phi, f=f: f(phi.image_of(g)))
            return self.giant(G, psi, x, y)
        if order > self.max_enum:
            raise Unsupported(f"large primitive quotient of degree {d} and order {order}")
        self.stats["enum_large_primitive"] += 1
        return self.enum_cosets(G, phi, x, y)

    def enum_cosets(self, G, phi, x, y):
        """Enumerate the quotient: Iso_G(x,y) = U_p Iso_K(x, y^(tau_p^-1)) tau_p."""
        if phi is None:
            return self.enumerate(G, x, y)
        self.stats["enum_cosets"] += 1
        n = G.n
        K = phi.kernel()
        answers = []
        for p in phi.image_group().elements():
            tau = phi.lift(p)
            a = self.solve(K, range(n), x, act(y, inv(tau)))
            if a is not None:
                answers.append(Coset(a.gens, mul(a.rep, tau)))
        return combine(n, answers)

    # -- giants ---------------------------------------------------------------
    def giant(self, G, phi, x, y):
        """phi: G -> Sym(q) with image containing Alt(q). Normalize to Alt(q)
        (at most two cosets) and run GiantStep in each coset."""
        n, q = G.n, phi.m
        if phi.image_order() == math.factorial(q):
            alt = phi.preimage(alt_gens(q, range(q)), math.factorial(q) // 2)
            transitive = len(alt.orbits()) == 1
            psi = ActionHom(alt, q, phi.image_of) if transitive else None
            answers = []
            for c in (G.idn, phi.lift(cycle(q, [0, 1]))):
                yc = act(y, inv(c))
                # an intransitive normalized group goes to the orbit chain
                a = self.giant_step(alt, psi, x, yc) if transitive else self.cont(alt, x, yc)
                if a is not None:
                    answers.append(Coset(a.gens, mul(a.rep, c)))
            return combine(n, answers)
        return self.giant_step(G, phi, x, y)

    def label_projection(self, G, phi, x, y):
        """The one-label or two-label map of the positions (the paper's
        support classification): the support of a position is the set of labels
        fixed by its stabilizer. Pull the colors back to the labels: unary label
        colors for one-label supports, a pair coloring for two-label supports.
        Returns (cx, cy, px, py), or None when supports are not 1 or 2 labels.
        G must be transitive."""
        n, q = G.n, phi.m
        F0, supp = label_support(G, phi)
        if len(F0) not in (1, 2):
            return None
        out = []
        for z in (x, y):
            fib = {}
            for w in range(n):
                fib.setdefault(supp[w], []).append(z[w])
            out.append({s: tuple(sorted(v)) for s, v in fib.items()})
        rank = {v: i for i, v in enumerate(sorted(set(out[0].values()) | set(out[1].values())))}
        if len(F0) == 1:
            cx = [rank[out[0][(a,)]] for a in range(q)]
            cy = [rank[out[1][(a,)]] for a in range(q)]
            return cx, cy, None, None
        none = len(rank)
        px = [[rank[out[0][(a, b)]] if (a, b) in out[0] else none for b in range(q)] for a in range(q)]
        py = [[rank[out[1][(a, b)]] if (a, b) in out[1] else none for b in range(q)] for a in range(q)]
        return [0] * q, [0] * q, px, py

    def giant_step(self, G, phi, x, y):
        """GiantStep for phi(G) = Alt(q)."""
        self.stats["giant_step"] += 1
        n, q = G.n, phi.m
        hx = hy = {}
        if self.certificates and q > self.kappa:
            cx_full = self.all_certificates(G, phi, x)
            cy_full = cx_full if x == y else self.all_certificates(G, phi, y)
            big_x = self.large_symmetry(phi, cx_full)
            big_y = big_x if x == y else self.large_symmetry(phi, cy_full)
            if (big_x is None) != (big_y is None):
                return None
            if big_x is not None:
                # G = F * ker(phi) with F <= Aut(x), so Iso_G = F * Iso_ker
                self.stats["large_symmetry"] += 1
                a = self.solve(phi.kernel(), range(n), x, y)
                if a is None:
                    return None
                return Coset(reduce_gens(n, big_x + a.gens), a.rep)
            hx = {T: (s, r) for T, (s, r, _) in cx_full.items()}
            hy = {T: (s, r) for T, (s, r, _) in cy_full.items()}
        proj = self.label_projection(G, phi, x, y)
        cx, cy, px, py = proj if proj else ([0] * q, [0] * q, None, None)
        cx, cy = refine_labels(q, hx, hy, cx, cy, px, py)
        if Counter(cx) != Counter(cy):
            return None
        if len(set(cx)) > 1:
            return self.lift_and_continue(G, phi, cx, cy, x, y)
        # individualize one label of x and try every image in y
        answers = []
        for g1 in range(q):
            ix = [2 * c for c in cx]
            iy = [2 * c for c in cy]
            ix[0] += 1
            iy[g1] += 1
            ax, ay = refine_labels(q, hx, hy, ix, iy, px, py)
            if Counter(ax) != Counter(ay):
                continue
            self.stats["branch"] += 1
            answers.append(self.lift_and_continue(G, phi, ax, ay, x, y))
        return combine(n, answers)

    def lift_and_continue(self, G, phi, cx, cy, x, y):
        """The overcoset E of label maps taking color classes of cx to those of
        cy, intersected with phi(G) = Alt(q), lifted to H tau in G; then
        Continue under H on (x, y^(tau^-1))."""
        n, q = G.n, phi.m
        X, Y = color_classes(cx), color_classes(cy)
        pi = [0] * q
        for c, cls in X.items():
            for a, b in zip(cls, Y[c]):
                pi[a] = b
        pi = tuple(pi)
        big = [C for C in X.values() if len(C) >= 2]
        ygens = [g for C in big for g in alt_gens(q, C)]
        transp = [cycle(q, C[:2]) for C in big]
        ygens += [mul(transp[0], t) for t in transp[1:]]
        if parity(pi):
            if not transp:
                return None
            pi = mul(transp[0], pi)
        H = phi.preimage(ygens)
        tau = phi.lift(pi)
        a = self.solve(H, range(n), x, act(y, inv(tau)))
        if a is None:
            return None
        return Coset(a.gens, mul(a.rep, tau))

    # -- local certificates (Algorithm 3) -------------------------------------
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
        signature and roles are isomorphism invariants of (x, T)."""
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
        """Aut_A(x on V), by enumerating the cosets of M = ker(phi_T on A)."""
        n = A.n
        psi = ActionHom(A, k, phiT)
        M = psi.kernel()
        answers = []
        for p in psi.image_group().elements():
            c = psi.lift(p)
            a = self.solve(M, V, x, act(x, inv(c)))
            if a is not None:
                answers.append(Coset(a.gens, mul(a.rep, c)))
        return PermGroup(n, combine(n, answers).gens)
