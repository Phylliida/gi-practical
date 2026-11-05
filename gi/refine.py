"""Canonical color refinement of two graphs at once (the graph front end).

Every function here refines the two instances *jointly*: in each round, the
new color of a vertex or pair is a signature tuple that contains its old color,
and the signatures of both instances are named by one shared, content-based
rule (their rank in the sorted union). Two consequences:

  * invariance: if s is an isomorphism X -> Y (of the input colorings), then s
    maps the refined coloring of X onto the refined coloring of Y;
  * the input colors are a function of the refined colors, one function for
    both instances, because each name determines its signature, which contains
    the old color.

So a vertex permutation maps X onto Y iff it maps the refined coloring of X
onto the refined coloring of Y. If the color histograms of the two instances
differ in some round, the graphs are not isomorphic and None is returned.

Pair colorings are n x n lists of ints (row i, column j is the pair (i, j)).
"""
from collections import Counter
from operator import add


def _rank(sx, sy):
    """Shared content-based names for two lists of signatures."""
    rank = {s: i for i, s in enumerate(sorted(set(sx) | set(sy)))}
    return [rank[s] for s in sx], [rank[s] for s in sy]


def atomic_pairs(A, vcolors=None):
    """The atomic type of each ordered pair: for i != j the entries A[i][j] and
    A[j][i] (directed graphs and edge colors are allowed), for i == j the
    vertex color and the loop entry A[i][i]. Values must be sortable."""
    n = len(A)
    vc = vcolors if vcolors is not None else [0] * n
    return [[(0, vc[i], A[i][i]) if i == j else (1, A[i][j], A[j][i]) for j in range(n)]
            for i in range(n)]


def initial_pair_colors(X, Y, vx=None, vy=None):
    """Joint integer names for the atomic pair types of X and Y."""
    n = len(X)
    ax, ay = atomic_pairs(X, vx), atomic_pairs(Y, vy)
    fx, fy = _rank([t for row in ax for t in row], [t for row in ay for t in row])
    return [fx[i * n:(i + 1) * n] for i in range(n)], [fy[i * n:(i + 1) * n] for i in range(n)]


def wl1(PX, PY):
    """1-dimensional WL (color refinement) on vertices, starting from the
    diagonal of the pair colorings PX, PY and using the off-diagonal pair colors
    as (directed, colored) edges. Returns the stable vertex colorings (cx, cy),
    or None if the two graphs are distinguished."""
    n = len(PX)
    # neighbor lists, ignoring the most common off-diagonal pair color: its
    # count per color class is determined by the others and the class sizes
    off = Counter(PX[i][j] for i in range(n) for j in range(n) if i != j)
    off.update(PY[i][j] for i in range(n) for j in range(n) if i != j)
    blank = max(off, key=lambda c: (off[c], -c)) if off else None
    nbrs = []
    for P in (PX, PY):
        nbrs.append([[(P[i][j], j) for j in range(n) if j != i and P[i][j] != blank]
                     for i in range(n)])
    cx, cy = _rank([PX[i][i] for i in range(n)], [PY[i][i] for i in range(n)])
    if Counter(cx) != Counter(cy):
        return None
    k = len(set(cx))
    while True:
        sx = [(cx[i], tuple(sorted((e, cx[j]) for e, j in nbrs[0][i]))) for i in range(n)]
        sy = [(cy[i], tuple(sorted((e, cy[j]) for e, j in nbrs[1][i]))) for i in range(n)]
        cx, cy = _rank(sx, sy)
        if Counter(cx) != Counter(cy):
            return None
        k2 = len(set(cx))
        if k2 == k:
            return cx, cy
        k = k2


def wl1_pairs(PX, PY):
    """1-WL vertex colors, folded into the pair colors: the new color of (i, j)
    is (c(i), c(j), old color of (i, j)). Returns (PX', PY') or None."""
    r = wl1(PX, PY)
    if r is None:
        return None
    cx, cy = r
    n = len(PX)
    fx, fy = _rank([(cx[i], cx[j], PX[i][j]) for i in range(n) for j in range(n)],
                   [(cy[i], cy[j], PY[i][j]) for i in range(n) for j in range(n)])
    return [fx[i * n:(i + 1) * n] for i in range(n)], [fy[i * n:(i + 1) * n] for i in range(n)]


def wl2(PX, PY, max_rounds=None):
    """2-dimensional WL (the coherent closure) on the pair colorings: the new
    color of (i, j) is (C(i, j), multiset of (C(i, k), C(k, j)) over k).
    Returns the stable pair colorings (PX', PY') or None. O(n^3) per round."""
    n = len(PX)
    PX, PY = _rank([c for row in PX for c in row], [c for row in PY for c in row])
    if Counter(PX) != Counter(PY):
        return None
    PX = [PX[i * n:(i + 1) * n] for i in range(n)]
    PY = [PY[i * n:(i + 1) * n] for i in range(n)]
    k = len({c for row in PX for c in row})
    rounds = 0
    while max_rounds is None or rounds < max_rounds:
        rounds += 1
        sigs = []
        for P in (PX, PY):
            K = 1 + max(c for row in P for c in row)
            cols = [[P[i][j] for i in range(n)] for j in range(n)]
            s = []
            for i in range(n):
                ri = [c * K for c in P[i]]
                Pi = P[i]
                for j in range(n):
                    s.append((Pi[j], tuple(sorted(map(add, ri, cols[j])))))
            sigs.append(s)
        fx, fy = _rank(sigs[0], sigs[1])
        if Counter(fx) != Counter(fy):
            return None
        PX = [fx[i * n:(i + 1) * n] for i in range(n)]
        PY = [fy[i * n:(i + 1) * n] for i in range(n)]
        k2 = len(set(fx))
        if k2 == k:
            break
        k = k2
    return PX, PY


def refine_graphs(X, Y, vx=None, vy=None, method="2wl"):
    """Jointly refined pair colorings (n x n int lists) of X and Y, or None if
    refinement shows they are not isomorphic. method: "none", "1wl" or "2wl"."""
    PX, PY = initial_pair_colors(X, Y, vx, vy)
    return refine_pairs(PX, PY, method=method)


def refine_pairs(PX, PY, lx=None, ly=None, method="2wl"):
    """Jointly refine two int pair colorings. lx, ly: optional extra vertex
    labels (sortable), folded into the diagonal before refining. Returns the
    refined pair colorings or None."""
    n = len(PX)
    if lx is not None:
        fx, fy = _rank([(1, PX[i][j], lx[i]) if i == j else (0, PX[i][j])
                        for i in range(n) for j in range(n)],
                       [(1, PY[i][j], ly[i]) if i == j else (0, PY[i][j])
                        for i in range(n) for j in range(n)])
        PX = [fx[i * n:(i + 1) * n] for i in range(n)]
        PY = [fy[i * n:(i + 1) * n] for i in range(n)]
    if method in (None, "none"):
        fx = [c for row in PX for c in row]
        fy = [c for row in PY for c in row]
        return (PX, PY) if Counter(fx) == Counter(fy) else None
    if method == "1wl":
        return wl1_pairs(PX, PY)
    if method == "2wl":
        return wl2(PX, PY)
    raise ValueError(f"unknown refinement method {method!r}")
