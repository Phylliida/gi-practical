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

2-WL (wl2) refines each instance on its own instead, with names taken from
that instance alone (so one side can be cached and reused), and then checks
the second property directly; see wl2.

Pair colorings are n x n lists of ints (row i, column j is the pair (i, j)).
"""
import random as _random
import sys
from math import sumprod
from array import array
from collections import Counter, OrderedDict
from itertools import chain
from operator import add, itemgetter

_BIG = sys.byteorder == "big"


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


# -- 2-WL with packed bilinear signatures ---------------------------------------
#
# The multiset M(i, j) = {(C(i, k), C(k, j)) : k} is summarized by the integer
#
#     s(i, j) = sum_k U[C(i, k)] * V[C(k, j)],
#
# for two fixed tables U, V of pseudo-random integers (indexed by color names).
# s is a function of M(i, j), the same function for both graphs, so the new
# color (C(i, j), s(i, j)) is a canonical refinement in the sense of the module
# docstring: isomorphisms map it onto itself, it contains the old color, and
# different histograms still prove non-isomorphism. Exactness never depends on
# U and V. Two different multisets give the same s only on the zero set of a
# nonzero degree-2 polynomial in the table entries (probability <= 2^-58 for
# each pair of multisets, by Schwartz-Zippel), and such a coincidence would
# only make that round coarser than 2-WL, never wrong.
#
# All n sums of row i come from one big-integer expression: row k of V[C] is
# packed into an integer PV_k with one 128-bit field per column j, and
# sum_k U[C(i, k)] * PV_k holds s(i, j) in field j (the bit sizes are chosen
# so that no field overflows into the next). This moves the O(n^3) inner work
# into CPython's big-integer arithmetic.

_FIELD = 16                                     # bytes per packed field (128 bits)
_TABLE_BITS = 62
_TABLES = {}                                    # bits -> (U, V, generator)
assert array("Q").itemsize == 8


def _tables(size, n, field_bits=8 * _FIELD):
    """U, V with at least `size` entries, scaled so that a sum of n products
    U[a] V[b] stays below 2^field_bits."""
    bits = min(_TABLE_BITS, (field_bits - max(1, n).bit_length()) // 2)
    t = _TABLES.get(bits)
    if t is None:
        t = _TABLES[bits] = ([], [], _random.Random(bits))
    U, V, rng = t
    while len(U) < size:                # entry i is the same in every call
        U.append(rng.getrandbits(bits))
        V.append(rng.getrandbits(bits))
    return U, V


def _wl2_keys(P, n, U, V):
    """For each pair (i, j), row-major: the integer (C(i, j) << 128) + s(i, j).

    Row i: s(i, .) = sum_a U[a] S_a with S_a = sum of PV_k over C(i, k) = a.
    With b the most frequent color of the row and T the sum of all PV_k, this
    is U[b] T + sum_{a != b} (U[a] - U[b]) S_a, which needs one product per
    color and only the additions outside the largest class."""
    zeros = array("Q", [0]) * (2 * n)
    PV = []
    for row in P:
        a = array("Q", zeros)
        a[0::2] = array("Q", [V[c] for c in row])     # field j = V[C(k, j)]
        if _BIG:
            a.byteswap()
        PV.append(int.from_bytes(a.tobytes(), "little"))
    T = sum(PV)
    out = []
    nb = _FIELD * n
    for row in P:
        cls = {}
        for k, c in enumerate(row):
            if c in cls:
                cls[c].append(k)
            else:
                cls[c] = [k]
        b = max(cls, key=lambda c: len(cls[c]))
        ub = U[b]
        r = ub * T
        for c, ks in cls.items():
            if c != b:
                r += (U[c] - ub) * (sum(itemgetter(*ks)(PV)) if len(ks) > 1 else PV[ks[0]])
        q = array("Q", r.to_bytes(nb, "little"))
        if _BIG:
            q.byteswap()
        out.extend([(c << 128) | (h << 64) | lo for c, lo, h in zip(row, q[0::2], q[1::2])])
    return out


def _wl1_vertex_colors(P, k):
    """Colour refinement (1-WL) of the vertices of ONE pair coloring P with
    int names < k: the vertex color starts as the diagonal color, and the new
    color of i is (c(i), sum_j W[P(i, j)] Z[c(j)]) for fixed tables W, Z (a
    function of the multiset of (P(i, j), c(j)), as in 2-WL), named by rank
    in this graph's own key set. Returns the stable vertex colors and the
    number of classes after each round."""
    n = len(P)
    W, Z = _tables(max(k, n), n, 63)    # the sums fit in a C long (sumprod's fast path)
    names = {v: i for i, v in enumerate(sorted({P[i][i] for i in range(n)}))}
    c = [names[P[i][i]] for i in range(n)]
    m = len(names)
    trace = [m]
    getw = W.__getitem__
    while m < n:
        cz = [Z[x] for x in c]
        keys = [(ci << 64) | sumprod(map(getw, row), cz) for ci, row in zip(c, P)]
        uniq = sorted(set(keys))
        if len(uniq) == m:
            break
        rank = {v: i for i, v in enumerate(uniq)}
        c = list(map(rank.__getitem__, keys))
        m = len(uniq)
        trace.append(m)
    return c, trace


def wl2_single(P):
    """The stable 2-WL coloring of ONE pair coloring P (n x n, sortable
    values), named canonically from P alone: in every round a color is the rank
    of its key in this graph's own sorted set of keys. Returns (coloring,
    trace), trace = the number of colors after each round.

    1-WL runs first (its rounds cost O(n^2) instead of O(n^3)). If it splits
    the vertex classes, its colors are folded into the pair colors; if it
    makes them discrete, every pair has its own color and 2-WL cannot refine
    any further, so no 2-WL round is needed.

    Isomorphic inputs give the same trace and corresponding colorings (each
    round depends only on the multiset of keys), which is what wl2 needs."""
    n = len(P)
    names = {v: i for i, v in enumerate(sorted(set(chain.from_iterable(P))))}
    get = names.__getitem__
    P = [list(map(get, row)) for row in P]
    k = len(names)
    c, t1 = _wl1_vertex_colors(P, k)
    trace = [k, tuple(t1)]
    if len(t1) > 1:                     # 1-WL split the vertex classes: fold them in
        keys = [(ci * n + cj) * k + v for ci, row in zip(c, P) for cj, v in zip(c, row)]
        uniq = sorted(set(keys))
        rank = {v: i for i, v in enumerate(uniq)}
        f = list(map(rank.__getitem__, keys))
        P = [f[i * n:(i + 1) * n] for i in range(n)]
        k = len(uniq)
        trace.append(k)
        if t1[-1] == n:                 # discrete vertex colors: stable for 2-WL
            return P, tuple(trace)
    while True:
        U, V = _tables(k, n)
        keys = _wl2_keys(P, n, U, V)
        uniq = sorted(set(keys))
        if len(uniq) == k:              # the keys refine the old colors: stable
            return P, tuple(trace)
        rank = {v: i for i, v in enumerate(uniq)}
        f = list(map(rank.__getitem__, keys))
        P = [f[i * n:(i + 1) * n] for i in range(n)]
        k = len(uniq)
        trace.append(k)


# Refinements of single colorings, keyed by the input coloring. The front end
# refines the same side again and again (the x side against every candidate
# image in an individualization loop, x against x for the automorphisms).
_WL2_CACHE = OrderedDict()
_WL2_CACHE_LIMIT = 48


def _wl2_single_cached(P):
    key = tuple(chain.from_iterable(P))
    r = _WL2_CACHE.get(key)
    if r is None:
        r = _WL2_CACHE[key] = wl2_single(P)
        if len(_WL2_CACHE) > _WL2_CACHE_LIMIT:
            _WL2_CACHE.popitem(last=False)
    else:
        _WL2_CACHE.move_to_end(key)
    return r


def wl2(PX, PY):
    """2-dimensional WL (the coherent closure) of two pair colorings: the new
    color of (i, j) is (C(i, j), s(i, j)), where s summarizes the multiset of
    (C(i, k), C(k, j)) over k (see above). Returns the stable pair colorings
    (PX', PY') or None. O(n^3) word operations per round.

    Each side is refined separately by wl2_single (and cached), so the names
    are not shared by construction. They are checked instead:
      * invariance holds as for joint refinement: an isomorphism of the inputs
        maps PX' onto PY', since both sides run the same canonical procedure;
      * the input color must be one function of the refined color on both
        sides (checked directly below), so a permutation mapping PX' onto PY'
        maps PX onto PY.
    If the check, the traces or the histograms disagree, the inputs are not
    isomorphic (by invariance) and None is returned."""
    n = len(PX)
    RX, tx = _wl2_single_cached(PX)
    RY, ty = (RX, tx) if PY == PX else _wl2_single_cached(PY)
    if tx != ty:
        return None
    pairs = set(zip(chain.from_iterable(RX), chain.from_iterable(PX)))
    if RY is not RX:
        pairs.update(zip(chain.from_iterable(RY), chain.from_iterable(PY)))
    if len({r for r, _ in pairs}) != len(pairs):    # not one function on both sides
        return None
    if RY is not RX and Counter(chain.from_iterable(RX)) != Counter(chain.from_iterable(RY)):
        return None
    return RX, RY


def wl2_reference(PX, PY, max_rounds=None):
    """2-WL with the literal multisets as signatures (the definition; slow).
    Used by the tests to check that wl2 computes the same partitions."""
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
    if lx is not None and method == "2wl":
        # only the diagonal changes: (color, label) named jointly by negative
        # ints (off-diagonal colors are >= 0); wl2 renames everything anyway
        dx = [(PX[i][i], lx[i]) for i in range(n)]
        dy = [(PY[i][i], ly[i]) for i in range(n)]
        fx, fy = _rank(dx, dy)
        PX, PY = [list(row) for row in PX], [list(row) for row in PY]
        for i in range(n):
            PX[i][i] = -1 - fx[i]
            PY[i][i] = -1 - fy[i]
    elif lx is not None:
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
