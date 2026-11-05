"""Graph isomorphism through string isomorphism (the paper's Algorithm 1):
positions are ordered vertex pairs, and the allowed relabelings are vertex
permutations acting on both coordinates.

Front end (see refine.py). The two graphs are first refined jointly by
canonical color refinement (2-WL by default). Positions are colored by the
refined pair colors, and the group is the vertex-color-preserving subgroup, a
direct product of symmetric groups on the vertex color classes. This is exact:
every isomorphism maps refined colors onto refined colors, and the original
adjacency is a function of the refined pair color (one function for both
graphs), so every permutation mapping refined colors onto refined colors is an
isomorphism.

Staged orbit chain (staged=True, the default). Instead of handing the whole
product group to the recursion at once, the wrapper keeps the invariant

    Iso(X, Y) = Iso_G(x, y) * rho,   G = F_1 x ... x F_k,

where x, y are pair colorings, rho is a vertex permutation, and the factors
F_i act on disjoint vertex sets P_i: either the full Sym(P_i), or a group
found by an earlier stage. The remaining vertices are fixed by G. It repeats:

  1. refine x and y jointly, with the G-orbit of each vertex added to its
     color (an element of G maps x to y only if it maps refined x to refined
     y, since G fixes its orbits). Skipped when the orbit labels are already
     a function of the colors;
  2. shrink each Sym(P) factor to the product of Sym over the refined classes
     inside P, moving y by a class-wise bijection tau in Sym(P) (exact, as in
     LiftAndContinue);
  3. solve one stage with the recursion (Solver.solve) on a set D of
     positions under the factors acting there: a solved factor whose block
     P x P the refinement made dirty, the induced structure P x P of a Sym
     factor, or the cross block between two factors (merging them). The answer
     Aut(x|D) * r replaces those factors and moves y by r (the orbit-chain
     rule). A result that is a product of symmetric groups on its orbits
     becomes Sym factors again; a direct product of two parts is split.

When every block is clean (x == y there and G preserves x there), Iso_G(x, y)
is G itself. Every step is exact, so the answer is exact, and refinement
between stages carries what one stage learned to the whole graph.

Individualization (ir > 0). A stage on a Sym factor of size >= ir_min may be
replaced by branching on one vertex v of P (graph-level
individualization-refinement): Iso_G(x, y) = U_w Iso_{G_v}(x, y^(t_w^-1)) t_w
over w in P, with t_w the transposition (v w). Automorphisms use orbit
pruning: Aut_{G_v}(x) plus one element taking v to each point of its orbit.
Searches for a single isomorphism branch on the preimage of v instead, one
branch per orbit of the automorphisms already known (see individualize).
Policy decides when: always for the first ir levels, then up to
ir_max = O(log n) levels only when the recursion does not finish the stage
within a budget of a few refinement times. Depth O(log n) costs at most a
factor n^O(log n), so the n^O(log n) bound of the recursion is kept.
"""
import time
from math import factorial, prod, ceil, log2
from operator import itemgetter

from .perm import sym_gens, identity, mul, cycle
from .group import PermGroup, reduce_gens
from .solver import Solver, Coset
from .refine import refine_graphs, refine_pairs


def pair_coloring(adj, vcolors=None):
    n = len(adj)
    vc = vcolors or [0] * n
    return tuple(2 + vc[i] if i == j else int(bool(adj[i][j]))
                 for i in range(n) for j in range(n))


def on_pairs(n, g):
    """The action of the vertex permutation g on the ordered pairs."""
    return tuple(g[i] * n + g[j] for i in range(n) for j in range(n))


def vertex_perm(n, g):
    """The vertex permutation of a permutation of the pairs induced by one."""
    return tuple(g[i * n + i] // n for i in range(n))


def sym_on_pairs(n):
    # (only the identity fixes every diagonal position)
    return PermGroup(n * n, [on_pairs(n, g) for g in sym_gens(n, range(n))],
                     order=factorial(n), ambient_base=[i * (n + 1) for i in range(n)])


def product_sym_on_pairs(n, classes):
    """The direct product of Sym(C) over the vertex classes C, acting on pairs.
    The base is the diagonal pairs of all but the last point of each class."""
    gens = [on_pairs(n, g) for C in classes for g in sym_gens(n, C)]
    base = [v * n + v for C in classes for v in sorted(C)[:-1]]
    return PermGroup(n * n, gens, base=base, order=prod(factorial(len(C)) for C in classes),
                     ambient_base=[v * (n + 1) for v in range(n)])


def classes_of(c, among=None):
    out = {}
    for v in (range(len(c)) if among is None else among):
        out.setdefault(c[v], []).append(v)
    return out


def pull_back(P, pi):
    """The pair coloring P^(pi^-1): entry (i, j) is P[pi i][pi j]."""
    if len(P) < 2:
        return [list(row) for row in P]
    g = itemgetter(*pi)
    return [list(g(P[p])) for p in pi]


def solve_on(solver, n, vgens, D, x, y, vbase=None, order=None):
    """Iso_K(x|D, y|D) for K = <vgens> (vertex permutations) acting on pairs.
    D: a K-invariant list of pairs (i, j); every vertex moved by K must occur as
    a first coordinate in D (then K acts faithfully on D). The group is built
    directly on D. Optional: vbase, a base of K on the vertices (each (b, b)
    must be in D), and the exact order of K; they only speed up the
    construction (Schreier-Sims then sifts through the diagonal base points and
    stops at the known order). Returns a Coset of vertex permutations, or None."""
    idx = {p: k for k, p in enumerate(D)}
    m = len(D)
    pgens = [tuple(idx[(g[i], g[j])] for i, j in D) for g in vgens]
    if vbase is not None:
        base = [idx[(b, b)] for b in vbase]
        K = PermGroup(m, pgens, base=base, order=order, ambient_base=base)
    else:
        K = PermGroup(m, pgens)
    a = solver.solve(K, range(m), tuple(x[i][j] for i, j in D), tuple(y[i][j] for i, j in D))
    if a is None:
        return None
    first = {}
    for k, (i, j) in enumerate(D):
        first.setdefault(i, k)

    def back(h):
        p = list(range(n))
        for i, k in first.items():
            p[i] = D[h[k]][0]
        return tuple(p)

    return Coset([back(h) for h in a.gens], back(a.rep))


# Stages with more positions than this are solved in chunks of whole orbits.
CHUNK = 2000


def solve_stage(solver, n, parts, D, x, y):
    """Iso_K(x|D, y|D) for K = the product of the parts, as solve_on, but a large
    D is cut into chunks of K-orbits that are solved one after the other (the
    orbit-chain rule, as in Solver.cont):

        Iso_K(x|D1+D2, y|D1+D2) = Iso_K1(x|D2, y^(r1^-1)|D2) r1,
        where Iso_K(x|D1, y|D1) = K1 r1,

    for K-invariant D1, D2 (D2 is then K1-invariant). Every chunk also holds the
    diagonal positions of all vertices of the parts, so the current group acts
    faithfully on it. An orbit on which x is constant and y has the same
    constant value is skipped: every element of K maps x to y there, and that
    stays true after y moves by elements of K. The recursion then works with
    permutations of a chunk instead of all of D, which is much cheaper when D
    is large (e.g. the cross block of two big solved factors)."""
    vgens = factor_gens(n, parts)
    if len(D) <= CHUNK:
        return solve_on(solver, n, vgens, D, x, y, *factor_base_order(n, parts))
    verts = sorted({i for i, _ in D})
    diag = [(v, v) for v in verts]
    dset = set(diag)
    seen, orbits = set(dset), []
    for p in D:
        if p in seen:
            continue
        seen.add(p)
        orb = [p]
        for i, j in orb:
            for g in vgens:
                q = (g[i], g[j])
                if q not in seen:
                    seen.add(q)
                    orb.append(q)
        c = x[p[0]][p[1]]
        if all(x[i][j] == c and y[i][j] == c for i, j in orb):
            continue
        orbits.append(orb)
    if len(orbits) <= 1 and sum(map(len, orbits)) + len(diag) >= len(D):
        return solve_on(solver, n, vgens, D, x, y, *factor_base_order(n, parts))
    orbits.sort(key=lambda o: (len(o), o[0]))
    chunks, cur = [], []
    for o in orbits:
        if cur and len(cur) + len(o) > CHUNK:
            chunks.append(cur)
            cur = []
        cur += o
    chunks.append(cur)
    solver.stats["stage_chunks"] += len(chunks)
    gens, vbase, order = vgens, *factor_base_order(n, parts)
    rep = identity(n)
    for chunk in chunks:
        a = solve_on(solver, n, gens, sorted(diag + chunk), x, y, vbase, order)
        if a is None:
            return None
        y = pull_back(y, a.rep)
        rep = mul(a.rep, rep)
        gens = list(a.gens)
        H = PermGroup(n, gens)
        vbase, order = H.short_base(), H.order()
    return Coset(gens, rep)


def graph_iso(X, Y, solver=None, vcolors_x=None, vcolors_y=None, refine="2wl", staged=True,
              ir=3, ir_min=6, ir_max="auto", ir_budget=2.0):
    """X, Y: adjacency matrices (lists of rows; directed graphs, loops and edge
    colors allowed). vcolors_x/vcolors_y: optional vertex colors.
    refine: "2wl" (default), "1wl" or "none" (the front end's refinement).
    staged: use the staged orbit chain with refinement between stages.
    ir, ir_min, ir_max, ir_budget: the individualization policy (see Policy
    and the module docstring); ir=0 hands every stage to the recursion.
    Returns None if not isomorphic, else (sigma, aut_gens): sigma[i] is the
    image of vertex i (an isomorphism X -> Y) and aut_gens generate Aut(X)."""
    n = len(X)
    if len(Y) != n:
        return None
    if n == 0:
        return (), []
    solver = solver or Solver()
    pol = Policy(n, ir, ir_min, ir_max, ir_budget)
    r = pol.refine(lambda: refine_graphs(X, Y, vcolors_x, vcolors_y, refine))
    if r is None:
        solver.stats["refine_reject"] += 1
        return None
    PX, PY = r
    if staged and refine not in (None, "none"):
        ans = staged_iso(solver, n, PX, PY, refine, pol=pol)
    else:
        ans = direct_iso(solver, n, PX, PY)
    if ans is None:
        return None
    gens = [g for g in dict.fromkeys(ans.gens) if g != identity(n)]
    return ans.rep, gens


class OverBudget(Exception):
    """A budgeted call of the recursion ran out of time (its work is discarded)."""


class Policy:
    """When a stage on a Sym factor P (|P| >= ir_min, induced coloring not
    uniform) is replaced by graph-level individualization.

      * depth < ir: always (bounded depth, as before);
      * ir <= depth < ir_max: the recursion gets the stage first, with a time
        budget of ir_budget times the mean duration of a refinement of this
        graph (one individualization branch costs at least one refinement).
        If it finishes, its exact answer is used; if not, its work is
        discarded and the stage is individualized;
      * depth >= ir_max: never.

    A budgeted call can only be stopped between two recursive calls, so it may
    overrun its budget by one step of the group engine, and building the
    stage's group on the |P|^2 positions (before the recursion starts) cannot
    be stopped at all; Schreier-Sims for Sym(P) costs about |P|^3 sifts, while
    a refinement costs about n^3 steps. So a trial is only made when
    100 (|P|/n)^3 <= ir_budget (|P| <= 0.27 n for the default); larger
    factors are individualized at once. Stages at the same depth on factors
    of the same size tend to behave alike (they are often siblings in the
    individualization tree), so once a call for (depth, |P|) has run out of
    time, later stages with the same (depth, |P|) are individualized without
    a trial.

    Exactness never depends on the policy: both choices compute
    Iso_G(x, y) exactly, an aborted call leaves only exact results behind
    (the solver memoizes a group only when its computation finished), and the
    choice only affects which generators are returned. ir_max="auto" is
    max(ir, ceil(log2 n)): individualization depth O(log n) multiplies the
    running time by at most n^O(log n), so the n^O(log n) bound is kept.
    ir_budget=None disables the budgeted levels (ir_max = ir); ir_budget=0
    always individualizes up to ir_max (the recursion is stopped at once)."""

    def __init__(self, n, ir=3, ir_min=6, ir_max="auto", ir_budget=2.0):
        self.ir, self.ir_min, self.budget = ir, ir_min, ir_budget
        if ir <= 0 or ir_budget is None:
            ir_max = max(ir, 0)
        elif ir_max == "auto":
            ir_max = max(ir, ceil(log2(max(n, 2))))
        self.ir_max = ir_max
        self.n = n
        self.t_ref, self.n_ref = 0.0, 0
        self.aborted = set()            # (depth, |P|) whose budgeted call ran out of time

    def refine(self, f):
        """f() (a refinement), timed for the budget."""
        t0 = time.perf_counter()
        r = f()
        self.t_ref += time.perf_counter() - t0
        self.n_ref += 1
        return r

    def individualize_now(self, depth, P):
        """True: individualize; False: recursion; None: recursion on a budget."""
        if depth >= self.ir_max or len(P) < self.ir_min:
            return False
        if depth < self.ir or (depth, len(P)) in self.aborted:
            return True
        return None if 100 * (len(P) / self.n) ** 3 <= self.budget else True

    def trial(self, solver, f):
        """f() with every call of solver.solve / solver.cont checking a deadline;
        raises OverBudget when it passes. (The hooks are instance attributes,
        removed afterwards; solver.py is unchanged.)"""
        seconds = self.budget * self.t_ref / max(1, self.n_ref)
        deadline = time.perf_counter() + seconds
        d = solver.__dict__
        saved = {k: d[k] for k in ("solve", "cont") if k in d}

        def hook(inner):
            def h(*a):
                if time.perf_counter() > deadline:
                    raise OverBudget
                return inner(*a)
            return h

        for k in ("solve", "cont"):
            d[k] = hook(getattr(solver, k))
        try:
            return f()
        finally:
            for k in ("solve", "cont"):
                if k in saved:
                    d[k] = saved[k]
                else:
                    d.pop(k, None)


def align(n, x, y, classes):
    """Split each class by the diagonal colors; return (new classes, tau)
    where tau maps each X-class onto the Y-class of the same color, or None
    if the sizes differ."""
    tau = list(range(n))
    out = []
    for C in classes:
        cx, cy = classes_of([x[v][v] for v in range(n)], C), classes_of([y[v][v] for v in range(n)], C)
        if sorted((k, len(v)) for k, v in cx.items()) != sorted((k, len(v)) for k, v in cy.items()):
            return None
        for col, W in cx.items():
            for a, b in zip(W, cy[col]):
                tau[a] = b
            if len(W) > 1:
                out.append(W)
    return out, tuple(tau)


def direct_iso(solver, n, PX, PY):
    """The plain front end: one call of the recursion under the product of
    Sym(class) acting on all pairs."""
    r = align(n, PX, PY, [list(range(n))])
    if r is None:
        return None
    classes, tau = r
    y = pull_back(PY, tau)
    x = tuple(c for row in PX for c in row)
    yt = tuple(c for row in y for c in row)
    solver.stats["refine_classes"] = n - sum(len(C) - 1 for C in classes)
    if not classes:
        return Coset([], tau) if x == yt else None
    ans = solver.solve(product_sym_on_pairs(n, classes), range(n * n), x, yt)
    if ans is None:
        return None
    return Coset([vertex_perm(n, g) for g in ans.gens], mul(vertex_perm(n, ans.rep), tau))


def orbit_labels(n, gens, classes):
    """For each vertex, the least vertex of its orbit under <gens> x prod Sym(C)."""
    parent = list(range(n))

    def find(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[max(ra, rb)] = min(ra, rb)

    for g in gens:
        for i in range(n):
            union(i, g[i])
    for C in classes:
        for v in C[1:]:
            union(C[0], v)
    return [find(v) for v in range(n)]


def labels_add_information(x, y, lab):
    """Whether refining with the vertex labels lab can change anything: it
    cannot when one function of the diagonal color gives the label, in both x
    and y (x and y are already jointly refined, so refining again would only
    rename colors, consistently for both)."""
    f = {}
    for P in (x, y):
        for v in range(len(lab)):
            if f.setdefault(P[v][v], lab[v]) != lab[v]:
                return True
    return False


def factor_gens(n, factors):
    """Generators of G = prod of the factors."""
    return [g for P, gens in factors for g in (sym_gens(n, P) if gens is None else gens)]


def factor_base_order(n, factors):
    """A base (on the vertices) and the order of G = prod of the factors."""
    base, order = [], 1
    for P, gens in factors:
        if gens is None:
            base += sorted(P)[:-1]
            order *= factorial(len(P))
        elif gens:
            H = PermGroup(n, gens)
            base += H.short_base()
            order *= H.order()
    return base, order


def clean(x, y, A, B, gens):
    """Whether x == y on A x B and every generator (vertex permutations
    fixing A and B setwise) preserves x there. (Rows are compared as tuples.)"""
    if not A or not B:
        return True
    gB = itemgetter(*B)
    for i in A:
        if gB(x[i]) != gB(y[i]):
            return False
    for g in gens:
        gBg = itemgetter(*[g[j] for j in B])
        for i in A:
            if gBg(x[g[i]]) != gB(x[i]):
                return False
    return True


def sym_clean(x, y, A, B):
    """clean() for a group containing Sym(A) x Sym(B) (A, B disjoint or equal):
    x == y on A x B off the diagonal, and x uniform on its off-diagonal part."""
    if not A or not B:
        return True
    gB = itemgetter(*B)
    if A is not B and set(A).isdisjoint(B):
        cols = set()
        for i in A:
            t = gB(x[i])
            if t != gB(y[i]):
                return False
            cols.update(t if len(B) > 1 else (t,))
            if len(cols) > 1:
                return False
        return True
    if A is B or A == B:
        # fast path: whole rows (the diagonal entry occurring once in its row)
        cols = set()
        for i in A:
            t = gB(x[i])
            d = x[i][i]
            if t != gB(y[i]) or t.count(d) != 1:
                break
            off = set(t)                # the off-diagonal values of row i
            off.discard(d)
            cols |= off
            if len(cols) > 1:
                return False
        else:
            return True
    cols = {x[i][j] for i in A for j in B if i != j}
    return len(cols) <= 1 and all(x[i][j] == y[i][j] for i in A for j in B if i != j)


def factor_orbit_labels(n, factors):
    """orbit_labels for G = prod of the factors: each vertex labeled by the
    least vertex of its G-orbit (orbits of a factor lie inside its set P)."""
    lab = list(range(n))
    for P, gens in factors:
        if gens is None:
            m = min(P)
            for v in P:
                lab[v] = m
        elif gens:
            seen = set()
            for v in sorted(P):
                if v in seen:
                    continue
                seen.add(v)
                orb = [v]               # v is the least point of its orbit
                for a in orb:
                    for g in gens:
                        b = g[a]
                        if b not in seen:
                            seen.add(b)
                            orb.append(b)
                for b in orb:
                    lab[b] = v
    return lab


def new_factors(n, gens, P):
    """Split the group <gens> on the vertex set P into factors: its fixed points,
    then either the full symmetric groups on its orbits, or a direct product of
    two projections when it is one, or the group itself."""
    lab = orbit_labels(n, gens, [])
    orbs = {}
    for v in P:
        orbs.setdefault(lab[v], []).append(v)
    fixed = [O[0] for O in orbs.values() if len(O) == 1]
    orbs = [O for O in orbs.values() if len(O) > 1]
    if not orbs:
        return [], fixed
    order = PermGroup(n, gens).order()
    if order == prod(factorial(len(O)) for O in orbs):
        return [(O, None) for O in orbs], fixed
    moved = sorted(v for O in orbs for v in O)
    if len(orbs) > 1:
        # try a split of the orbits into two halves acting independently
        half = set(v for O in orbs[:len(orbs) // 2] for v in O)

        def proj(g, keep):
            return tuple(g[v] if v in keep else v for v in range(n))

        rest = set(moved) - half
        g1 = [proj(g, half) for g in gens]
        g2 = [proj(g, rest) for g in gens]
        o1, o2 = PermGroup(n, g1).order(), PermGroup(n, g2).order()
        if o1 * o2 == order:
            f1, x1 = new_factors(n, g1, sorted(half))
            f2, x2 = new_factors(n, g2, sorted(rest))
            return f1 + f2, fixed + x1 + x2
    return [(moved, list(gens))], fixed


def staged_iso(solver, n, x, y, method, factors=None, fixed=(),
               pol=None, depth=0, need_all=True, fresh=True, known=None):
    """Iso_G(x, y) as a Coset of vertex permutations, for G the direct product
    of the factors (P, gens): gens=None stands for Sym(P), otherwise <gens> is
    supported on P. The factors' vertex sets are disjoint; the other vertices
    (fixed) are fixed by G. factors=None: G = Sym(n).

    pol (a Policy; None: no individualization) decides when a stage on a Sym
    factor is replaced by branching on one of its vertices (with orbit pruning
    for the automorphisms); depth is the number of vertices individualized
    so far.
    need_all=False asks only for one isomorphism (the generators may then be
    incomplete); `known` may then list automorphisms of x in G, which prune
    the individualization branches. They stay automorphisms in every later
    group of the loop, since each stage replaces G by a subgroup containing
    Aut_G(x), and refinement keeps them (x is refined, never relabeled)."""
    rho = identity(n)
    pol = pol or Policy(n, ir=0)
    factors = [(list(range(n)), None)] if factors is None else list(factors)
    fixed = list(fixed)
    while True:
        # 1. refine with the G-orbits as extra vertex labels
        if not fresh:
            lab = factor_orbit_labels(n, factors)
            if labels_add_information(x, y, lab):
                solver.stats["refine"] += 1
                r = pol.refine(lambda: refine_pairs(x, y, lab, lab, method))
                if r is None:
                    solver.stats["refine_reject"] += 1
                    return None
                x, y = r
        fresh = False
        # 2. shrink the symmetric factors
        syms = [P for P, gens in factors if gens is None]
        r = align(n, x, y, syms)
        if r is None:
            return None
        sub, tau = r
        if any(tau[v] != v for v in range(n)):
            y = pull_back(y, tau)
            rho = mul(tau, rho)
        covered = set(v for W in sub for v in W)
        fixed += [v for P in syms for v in P if v not in covered]
        factors = [f for f in factors if f[1] is not None] + [(W, None) for W in sub]
        # 3. the next stage
        stage = pick_stage(n, x, y, factors, fixed)
        if stage is None:
            break
        if stage == "fail":
            return None
        kind, parts, D = stage
        now = kind == "self" and parts[0][1] is None and pol.individualize_now(depth, parts[0][0])
        a = OverBudget
        if now is None:
            solver.stats["stage"] += 1
            try:
                a = pol.trial(solver, lambda: solve_stage(solver, n, parts, D, x, y))
                solver.stats["trial_done"] += 1
            except OverBudget:
                solver.stats["trial_abort"] += 1
                pol.aborted.add((depth, len(parts[0][0])))
        if now or (now is None and a is OverBudget):
            a = individualize(solver, n, x, y, method, factors, fixed, parts[0][0],
                              pol, depth + 1, need_all, known)
            return None if a is None else Coset(a.gens, mul(a.rep, rho))
        if a is OverBudget:
            solver.stats["stage"] += 1
            a = solve_stage(solver, n, parts, D, x, y)
        if a is None:
            return None
        y = pull_back(y, a.rep)
        rho = mul(a.rep, rho)
        factors = [f for f in factors if not any(f is p for p in parts)]
        P = sorted(v for p in parts for v in p[0])
        nf, nfix = new_factors(n, a.gens, P)
        factors += nf
        fixed += nfix
    return Coset(factor_gens(n, factors), rho)


def individualize(solver, n, x, y, method, factors, fixed, C, pol, depth, need_all, known=None):
    """Iso_G(x, y) by branching on the vertex v = C[0], where Sym(C) is a
    factor of G. With t_u the transposition (v u) and G_v the stabilizer of v,
    there are two exhaustive ways to split Iso_G(x, y):

      by the image w of v:     Iso_G(x, y) = U_w Iso_{G_v}(x, y^(t_w^-1)) t_w,
      by the preimage u of v:  Iso_G(x, y) = U_u t_u Iso_{G_v}(x^(t_u), y).

    Full mode (need_all). Aut_G(x) is generated by A_v = Aut_{G_v}(x) (the
    branch w = v of x against x) and one element taking v to each point of its
    orbit; points already in the orbit of the generators found so far are
    skipped, and each remaining point u is tested by a search for ONE element
    of Iso_{G_v}(x, x^(t_u^-1)), knowing its automorphism group A_v. Then ONE
    isomorphism x -> y is searched with Aut_G(x) known.

    One-mode (need_all=False; `known` generates a group K of automorphisms of
    x in G). The pieces of the second split satisfy a P(u) = P(u^(a^-1)) ...
    precisely, for a in K, a P(u) is contained in P(a^-1(u)), where P(u) =
    {g in Iso : g(u) = v}. So P(u) is empty for all u in one K-orbit or for
    none, and one u per K-orbit on C suffices. The branch of u searches
    Iso_{G_v}(x^(t_u), y), whose known automorphisms are t_u Stab_K(u) t_u
    (they fix v and preserve x^(t_u)). With K = Aut_G(x) this costs one branch
    per orbit of Aut_G(x) on C instead of one per point; for non-isomorphic
    pairs, where every branch fails, that is the whole cost of the search."""
    v = C[0]
    sub = [f for f in factors if f[0] is not C] + ([(C[1:], None)] if len(C) > 2 else [])
    subfix = fixed + [v] + ([C[1]] if len(C) == 2 else [])
    idn = identity(n)

    def t(u):
        return cycle(n, [v, u]) if u != v else idn

    def search(xx, yy, all_, kn):
        solver.stats["ir_branch"] += 1
        return staged_iso(solver, n, xx, yy, method, sub, subfix, pol, depth, all_,
                          fresh=False, known=kn)

    def one(yy, kn):
        """One element of Iso_G(x, yy), given generators kn of automorphisms of x in G."""
        if kn is None:
            for w in C:
                a = search(x, pull_back(yy, t(w)), False, None)
                if a is not None:
                    return mul(a.rep, t(w))
            return None
        orbit = orbit_labels(n, kn, [])
        seen, reps = set(), []
        for u in C:                     # one u per orbit, v = C[0] first
            if orbit[u] not in seen:
                seen.add(orbit[u])
                reps.append(u)
        solver.stats["ir_pruned"] += len(C) - len(reps)
        K = PermGroup(n, kn) if kn else None
        for u in reps:
            tu = t(u)
            ku = K.stabilizer(u).gens if K is not None else []
            a = search(x if u == v else pull_back(x, tu), yy, False,
                       [mul(mul(tu, k), tu) for k in ku])
            if a is not None:
                return mul(tu, a.rep)
        return None

    if not need_all:
        r = one(y, known)
        return None if r is None else Coset([], r)
    a = search(x, x, True, None)
    av = list(a.gens) + ([a.rep] if a.rep != idn else [])
    gens = list(av)
    for u in C[1:]:
        orbit = orbit_labels(n, gens, [])
        if orbit[u] == orbit[v]:
            solver.stats["ir_pruned"] += 1
            continue
        tu = t(u)
        b = search(x, pull_back(x, tu), False, av)
        if b is not None:
            gens.append(mul(b.rep, tu))
    if x == y:
        sigma = idn
    else:
        sigma = one(y, gens)
        if sigma is None:
            return None
    return Coset(reduce_gens(n, gens), sigma)


def pick_stage(n, x, y, factors, fixed):
    """The next stage as (kind, parts, D): solve D under the product of the parts.
    Returns None when every block is clean (then Iso_G(x, y) = G), or "fail"
    when the fixed vertices already disagree. Order: a solved factor whose
    block refinement made dirty; a Sym factor with a non-uniform induced
    coloring (smallest first); the smallest pair of factors (the fixed vertices
    count as a factor without generators) whose cross block is not clean."""
    if not clean(x, y, fixed, fixed, []):
        return "fail"
    order = sorted(factors, key=lambda f: (len(f[0]), f[0][0]))
    for f in order:
        P, gens = f
        if gens is not None and not clean(x, y, P, P, gens):
            return "self", [f], [(i, j) for i in P for j in P]
    for f in order:
        P, gens = f
        if gens is None and not sym_clean(x, y, P, P):
            return "self", [f], [(i, j) for i in P for j in P]
    FIX = (fixed, [])
    parts = ([FIX] if fixed else []) + order
    best = None
    for a in range(len(parts)):
        for b in range(a + 1, len(parts)):
            (A, ga), (B, gb) = parts[a], parts[b]
            size = (1 if ga == [] else len(A)) + len(B)
            if best is not None and size >= best[0]:
                continue
            if ga is None and gb is None:
                ok = sym_clean(x, y, A, B) and sym_clean(x, y, B, A)
            else:
                gg = (sym_gens(n, A) if ga is None else ga) + (sym_gens(n, B) if gb is None else gb)
                ok = clean(x, y, A, B, gg) and clean(x, y, B, A, gg)
            if not ok:
                best = (size, parts[a], parts[b])
    if best is None:
        return None
    _, pa, pb = best
    A, B = pa[0], pb[0]
    D = sorted([(i, j) for i in A for j in B] + [(j, i) for i in A for j in B]
               + [(i, i) for i in A + B])
    return "merge", ([pa, pb] if pa is not FIX else [pb]), D
