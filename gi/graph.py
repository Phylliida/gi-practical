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
replaced by branching on the image of one vertex v of P (graph-level
individualization-refinement), up to ir levels deep:
Iso_G(x, y) = U_w Iso_{G_v}(x, y^(t_w^-1)) t_w over w in P, with t_w the
transposition (v w). Automorphisms use orbit pruning: Aut_{G_v}(x) plus one
element taking v to each point of its orbit. Bounded depth costs at most a
factor n^ir, so with constant (or O(log n)) depth the n^O(log n) bound of the
recursion is kept.
"""
from math import factorial, prod

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
    return PermGroup(n * n, [on_pairs(n, g) for g in sym_gens(n, range(n))])


def product_sym_on_pairs(n, classes):
    """The direct product of Sym(C) over the vertex classes C, acting on pairs.
    The base is the diagonal pairs of all but the last point of each class."""
    gens = [on_pairs(n, g) for C in classes for g in sym_gens(n, C)]
    base = [v * n + v for C in classes for v in sorted(C)[:-1]]
    return PermGroup(n * n, gens, base=base)


def classes_of(c, among=None):
    out = {}
    for v in (range(len(c)) if among is None else among):
        out.setdefault(c[v], []).append(v)
    return out


def pull_back(P, pi):
    """The pair coloring P^(pi^-1): entry (i, j) is P[pi i][pi j]."""
    n = len(P)
    return [[P[pi[i]][pi[j]] for j in range(n)] for i in range(n)]


def solve_on(solver, n, vgens, D, x, y):
    """Iso_K(x|D, y|D) for K = <vgens> (vertex permutations) acting on pairs.
    D: a K-invariant list of pairs (i, j); every vertex moved by K must occur as
    a first coordinate in D (then K acts faithfully on D). The group is built
    directly on D. Returns a Coset of vertex permutations, or None."""
    idx = {p: k for k, p in enumerate(D)}
    m = len(D)
    K = PermGroup(m, [tuple(idx[(g[i], g[j])] for i, j in D) for g in vgens])
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


def graph_iso(X, Y, solver=None, vcolors_x=None, vcolors_y=None, refine="2wl", staged=True,
              ir=3, ir_min=6):
    """X, Y: adjacency matrices (lists of rows; directed graphs, loops and edge
    colors allowed). vcolors_x/vcolors_y: optional vertex colors.
    refine: "2wl" (default), "1wl" or "none" (the front end's refinement).
    staged: use the staged orbit chain with refinement between stages.
    ir, ir_min: graph-level individualization depth and minimum class size
    (see the module docstring); ir=0 hands every stage to the recursion.
    Returns None if not isomorphic, else (sigma, aut_gens): sigma[i] is the
    image of vertex i (an isomorphism X -> Y) and aut_gens generate Aut(X)."""
    n = len(X)
    if len(Y) != n:
        return None
    if n == 0:
        return (), []
    solver = solver or Solver()
    r = refine_graphs(X, Y, vcolors_x, vcolors_y, refine)
    if r is None:
        solver.stats["refine_reject"] += 1
        return None
    PX, PY = r
    if staged and refine not in (None, "none"):
        ans = staged_iso(solver, n, PX, PY, refine, ir=ir, ir_min=ir_min)
    else:
        ans = direct_iso(solver, n, PX, PY)
    if ans is None:
        return None
    gens = [g for g in dict.fromkeys(ans.gens) if g != identity(n)]
    return ans.rep, gens


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


def clean(x, y, A, B, gens):
    """Whether x == y on A x B and every generator (vertex permutations
    fixing A and B setwise) preserves x there."""
    for i in A:
        xi, yi = x[i], y[i]
        for j in B:
            if xi[j] != yi[j] or any(x[g[i]][g[j]] != xi[j] for g in gens):
                return False
    return True


def sym_clean(x, y, A, B):
    """clean() for a group containing Sym(A) x Sym(B) (A, B disjoint or equal):
    x == y on A x B and x uniform on its off-diagonal part."""
    cols = {x[i][j] for i in A for j in B if i != j}
    return len(cols) <= 1 and all(x[i][j] == y[i][j] for i in A for j in B if i != j)


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
               ir=0, ir_min=6, need_all=True, fresh=True):
    """Iso_G(x, y) as a Coset of vertex permutations, for G the direct product
    of the factors (P, gens): gens=None stands for Sym(P), otherwise <gens> is
    supported on P. The factors' vertex sets are disjoint; the other vertices
    (fixed) are fixed by G. factors=None: G = Sym(n).

    ir > 0 enables graph-level individualization for up to ir levels: a stage
    on a Sym factor of size >= ir_min is replaced by branching on the image of
    one of its vertices (with orbit pruning for the automorphisms).
    need_all=False asks only for one isomorphism (the generators may then be
    incomplete)."""
    rho = identity(n)
    factors = [(list(range(n)), None)] if factors is None else list(factors)
    fixed = list(fixed)
    while True:
        # 1. refine with the G-orbits as extra vertex labels
        if not fresh:
            lab = orbit_labels(n, [g for P, gens in factors if gens for g in gens],
                               [P for P, gens in factors if gens is None])
            if labels_add_information(x, y, lab):
                solver.stats["refine"] += 1
                r = refine_pairs(x, y, lab, lab, method)
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
        if ir > 0 and kind == "self" and parts[0][1] is None and len(parts[0][0]) >= ir_min:
            a = individualize(solver, n, x, y, method, factors, fixed, parts[0][0],
                              ir - 1, ir_min, need_all)
            return None if a is None else Coset(a.gens, mul(a.rep, rho))
        solver.stats["stage"] += 1
        a = solve_on(solver, n, factor_gens(n, parts), D, x, y)
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


def individualize(solver, n, x, y, method, factors, fixed, C, ir, ir_min, need_all):
    """Iso_G(x, y) by branching on the image w of v = C[0], where Sym(C) is a
    factor of G: Iso_G(x, y) = U_w Iso_{G_v}(x, y^(t_w^-1)) t_w with t_w the
    transposition (v w). For the automorphisms, Aut_G(x) is generated by
    Aut_{G_v}(x) and one element taking v to each point of its orbit; points
    already in the orbit of the generators found so far are skipped."""
    v = C[0]
    sub = [f for f in factors if f[0] is not C] + ([(C[1:], None)] if len(C) > 2 else [])
    subfix = fixed + [v] + ([C[1]] if len(C) == 2 else [])

    def branch(yy, w, all_):
        t = cycle(n, [v, w]) if w != v else identity(n)
        solver.stats["ir_branch"] += 1
        a = staged_iso(solver, n, x, pull_back(yy, t), method, sub, subfix,
                       ir, ir_min, all_, fresh=False)
        return None if a is None else Coset(a.gens, mul(a.rep, t))

    if not need_all:
        for w in C:
            a = branch(y, w, False)
            if a is not None:
                return a
        return None
    a = branch(x, v, True)
    gens = list(a.gens) + [a.rep]
    for u in C[1:]:
        orbit = orbit_labels(n, gens, [])
        if orbit[u] == orbit[v]:
            continue
        b = branch(x, u, False)
        if b is not None:
            gens.append(b.rep)
    if x == y:
        sigma = identity(n)
    else:
        for w in C:
            b = branch(y, w, False)
            if b is not None:
                sigma = b.rep
                break
        else:
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
