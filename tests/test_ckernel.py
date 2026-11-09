"""The compiled kernel (gi/_ckernel.c) against its Python references.

Run in both modes; with GI_NO_CKERNEL=1 the C-versus-Python comparisons are
skipped and the whole-pipeline comparisons still run, against a subprocess in
the other mode (if the kernel is built). GI_REQUIRE_CKERNEL=1 turns a missing
kernel into a failure, so that a broken build cannot pass as a skip.
"""
import hashlib
import json
import os
import random
import subprocess
import sys

import pytest

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

import gi.group as group
import gi.kernel as kernel
import gi.perm as perm
import gi.refine as refine
from gi.group import LazyTransversal, PermGroup

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
ck = kernel.ck
if os.environ.get("GI_REQUIRE_CKERNEL") == "1" and ck is None:
    raise RuntimeError("GI_REQUIRE_CKERNEL=1 but the compiled kernel is not loaded")
needs_ck = pytest.mark.skipif(ck is None, reason="compiled kernel not loaded")


def outcome(f, *args):
    """The result of f(*args), or the type and message of the exception."""
    try:
        return ("ok", f(*args))
    except Exception as e:                  # noqa: BLE001 (comparing both sides)
        return ("raised", type(e).__name__, str(e))


def rperm(rng, n):
    p = list(range(n))
    rng.shuffle(p)
    return tuple(p)


DEGREES = [0, 1, 2, 3, 4, 5, 6, 7, 16, 100, 513, 2000]


# -- permutation primitives ----------------------------------------------------
@needs_ck
@pytest.mark.parametrize("n", DEGREES)
def test_mul_inv_act_maps_random(n):
    rng = random.Random(n + 1)
    for _ in range(40 if n < 1000 else 5):
        p, q = rperm(rng, n), rperm(rng, n)
        assert ck.mul(p, q) == perm.py_mul(p, q)
        assert type(ck.mul(p, q)) is tuple
        assert ck.inv(p) == perm.py_inv(p)
        x = tuple(rng.randrange(3) for _ in range(n))
        assert ck.act(x, p) == perm.py_act(x, p)
        assert ck.act(list(x), p) == perm.py_act(list(x), p)
        y = perm.py_act(x, p)
        assert ck.maps(p, x, y) is True and perm.py_maps(p, x, y) is True
        z = tuple(rng.randrange(3) for _ in range(n))
        assert ck.maps(p, x, z) == perm.py_maps(p, x, z)


@needs_ck
def test_large_degree():
    rng = random.Random(5)
    n = 200000
    p, q = rperm(rng, n), rperm(rng, n)
    assert ck.mul(p, q) == perm.py_mul(p, q)
    assert ck.inv(p) == perm.py_inv(p)
    x = tuple(i % 7 for i in range(n))
    assert ck.act(x, p) == perm.py_act(x, p)
    assert ck.maps(p, x, perm.py_act(x, p)) is True
    assert ck.orbits(n, [p, q]) == _py_orbits(n, [p, q])


BAD_INPUTS = [
    ((0, 2), (5, 6)),                       # out of range
    ((0, -1), (5, 6)),                      # negative: Python indexes from the end
    ((1.0, 0), (5, 6)),                     # not ints
    ((True, False), (5, 6)),                # bools are ints in Python
    ((1, 0), [5, 6]),                       # a list
    ([1, 0], (5, 6)),
    ((1, 0, 2**40), (5, 6, 7)),             # beyond the fast int range
    ((0, 0, 1), (5, 6, 7)),                 # not a permutation
    ((), ()),
    ((0,), (9,)),
    (None, (1, 2)),
    ((1, 0), None),
    ((0, 1), ("a", "b")),                   # q need not hold ints
]


@needs_ck
@pytest.mark.parametrize("a,b", BAD_INPUTS)
def test_invalid_input_matches_reference(a, b):
    assert outcome(ck.mul, a, b) == outcome(perm.py_mul, a, b)
    assert outcome(ck.inv, a) == outcome(perm.py_inv, a)
    assert outcome(ck.act, b, a) == outcome(perm.py_act, b, a)
    assert outcome(ck.act, a, b) == outcome(perm.py_act, a, b)
    for c in (b, a, (1, 2, 3), (0, 1), ("x", "y")):
        assert outcome(ck.maps, a, b, c) == outcome(perm.py_maps, a, b, c)
        assert outcome(ck.maps, b, a, c) == outcome(perm.py_maps, b, a, c)


@needs_ck
def test_maps_early_exit_order():
    # a mismatch before a bad entry of g: the reference's first 4 points are
    # checked one by one, so it returns False there, later it reads all of g
    for g, x, y in [((1, 0, 9, 9, 9), (7, 7, 7, 7, 7), (1, 2, 3)),
                    ((0, 1, 2, 3, 0, 9), (1, 2, 3, 4, 5, 6), (1, 2, 3, 4)),
                    ((0, 1, 2, 3, 4, 9), (1, 2, 3, 4, 8, 6), (1, 2, 3, 4, 5, 6)),
                    ((0, 1, 2, 3, 4, -1), (1, 2, 3, 4, 8, 6), (1, 2, 3, 4, 5, 6)),
                    ((0, 1), (1, 2, 3), (1, 2, 3)),
                    ((0, 1, 2), (1, 2), (1, 2, 3))]:
        assert outcome(ck.maps, g, x, y) == outcome(perm.py_maps, g, x, y)
    # colors that are not small ints go to the reference
    big = 2 ** 70
    assert ck.maps((1, 0), (big, 1), (1, big)) is True
    assert ck.maps((1, 0), ((1,), 2), (2, (1,))) is True
    assert ck.maps((1, 0), ("a", 2), (2, "b")) is False


@needs_ck
def test_wrong_argument_counts():
    for f, r in ((ck.mul, perm.py_mul), (ck.inv, perm.py_inv), (ck.act, perm.py_act),
                 (ck.maps, perm.py_maps)):
        assert outcome(f)[:2] == outcome(r)[:2]
        assert outcome(f, (0,), (0,), (0,), (0,))[:2] == outcome(r, (0,), (0,), (0,), (0,))[:2]
    assert ck.orbits(3) is None and ck.sift((0,), [], []) is None
    assert ck.sifts_to_id((0,)) is None and ck.make_fast_plan([], [], 0) is None
    assert ck.wl2_single([[0]]) is None


@needs_ck
def test_refcounts():
    """Results own references to shared items; inputs end as they started."""
    n = 2000
    rng = random.Random(9)
    p, q = rperm(rng, n), rperm(rng, n)
    marker = object()
    x = tuple([marker] * n)
    before = sys.getrefcount(marker)
    r = ck.act(x, p)
    assert sys.getrefcount(marker) == before + n
    del r
    assert sys.getrefcount(marker) == before
    q2 = tuple([marker] * n)
    before = sys.getrefcount(marker)
    r = ck.mul(p, q2)
    assert sys.getrefcount(marker) == before + n
    del r
    assert sys.getrefcount(marker) == before
    # a failure part-way must release what the partial result held
    bad = p[:-1] + (10 ** 9,)
    before = sys.getrefcount(marker)
    with pytest.raises(IndexError):
        ck.mul(bad, q2)
    assert sys.getrefcount(marker) == before
    for f, args in ((ck.mul, (p, q)), (ck.inv, (p,))):
        counts = [sys.getrefcount(a) for a in args]
        for _ in range(500):
            f(*args)
        assert [sys.getrefcount(a) for a in args] == counts


# -- orbits ----------------------------------------------------------------------
def _py_orbits(n, gens):
    saved, group._ck = group._ck, None
    try:
        G = PermGroup.__new__(PermGroup)
        G.n, G.gens, G._orbs, G._snap = n, gens, None, None
        return G.orbits()
    finally:
        group._ck = saved


@needs_ck
@pytest.mark.parametrize("n", [0, 1, 2, 3, 8, 50, 700])
def test_orbits_random(n):
    rng = random.Random(n + 3)
    for _ in range(30):
        gens = []
        for _ in range(rng.randrange(4)):
            pts = list(range(n))
            rng.shuffle(pts)
            pts = pts[:rng.randrange(n + 1)]
            gens.append(perm.cycle(n, pts) if pts else tuple(range(n)))
        assert ck.orbits(n, gens) == _py_orbits(n, gens)


@needs_ck
def test_orbits_rejects_unusual_input():
    assert ck.orbits(3, [(0, 1)]) is None
    assert ck.orbits(3, [(0, 1, 5)]) is None
    assert ck.orbits(3, [[0, 1, 2]]) is None
    assert ck.orbits(3, ((0, 1, 2),)) is None
    assert ck.orbits(-1, []) is None
    assert ck.orbits(3, [(0, 1, 2.0)]) is None
    assert ck.orbits(2 ** 40, []) is None


# -- sift, the fast plan -----------------------------------------------------------
def _random_groups(rng, count, degrees=(2, 3, 5, 8, 11, 20, 40)):
    out = []
    for _ in range(count):
        n = rng.choice(degrees)
        gens = [rperm(rng, n) if rng.random() < 0.4
                else perm.cycle(n, rng.sample(range(n), rng.randint(2, min(n, 4))))
                for _ in range(rng.randint(1, 4))]
        amb = None
        G = PermGroup(n, gens)
        if rng.random() < 0.7:
            G2 = PermGroup(n, gens, ambient_base=G.short_base())
            out.append((n, gens, G2))
        else:
            out.append((n, gens, G))
    return out


def _python_sift(G, g, start):
    saved, group._ck = group._ck, None
    try:
        return G.sift(g, start)
    finally:
        group._ck = saved


def _python_fast(G, factors, start):
    saved, group._ck = group._ck, None
    try:
        return G._sifts_to_id(factors, start)
    finally:
        group._ck = saved


@needs_ck
def test_sift_random():
    rng = random.Random(77)
    calls = 0
    for n, gens, G in _random_groups(rng, 60):
        for _ in range(40):
            if rng.random() < 0.6:
                # products of generators: they sift through
                g = tuple(range(n))
                for _ in range(rng.randrange(6)):
                    g = perm.py_mul(g, rng.choice(gens))
            else:
                g = rperm(rng, n)
            for start in {0, rng.randrange(len(G.base) + 1)}:
                plan = G._plans
                r1 = G.sift(g, start)
                r2 = _python_sift(G, g, start)
                assert r1 == r2, (n, g, start)
                if r1[1] == len(G.base) and r1[0] == g and not G._nontrivial():
                    assert r1[0] is g
                calls += 1
    assert calls > 1000


@needs_ck
def test_fast_sift_random():
    rng = random.Random(78)
    count = 0
    for n, gens, G in _random_groups(rng, 60):
        if G._amb is None:
            continue
        for _ in range(40):
            f1 = tuple(range(n))
            for _ in range(rng.randrange(5)):
                f1 = perm.py_mul(f1, rng.choice(gens))
            factors = rng.choice([(f1,), (f1, rng.choice(gens), rperm(rng, n)),
                                  (rperm(rng, n),)])
            for start in {0, rng.randrange(len(G.base) + 1)}:
                assert G._sifts_to_id(factors, start) == _python_fast(G, factors, start)
                count += 1
    assert count > 300


@needs_ck
def test_make_fast_plan_random():
    rng = random.Random(79)
    for n, gens, G in _random_groups(rng, 80):
        G._amb = [rng.randrange(n) for _ in range(rng.randint(1, 8))]
        for start in range(len(G.base) + 2):
            nt = G._nontrivial()
            c = ck.make_fast_plan(G.base, nt, start, G._amb, n)
            saved, group._ck = group._ck, None
            try:
                try:
                    p = G._make_fast_plan(start)
                except IndexError:
                    p = None
            finally:
                group._ck = saved
            assert c == p, (n, start, G.base, nt, G._amb)


@needs_ck
def test_sift_lazy_transversal():
    """Explicit chains (LazyTransversal) go through the method-call path."""
    n = 6
    t = perm.cycle(n, [0, 1])
    lt = LazyTransversal([0, 1], lambda p: t, tuple(range(n)))
    G = PermGroup.from_bsgs(n, [t], [0], [[t]], [lt])
    g = perm.cycle(n, [0, 1, 2])
    assert G.sift(g) == _python_sift(G, g, 0)
    assert G.sift(t) == _python_sift(G, t, 0)
    G._amb = [0, 2]
    for f in (g, t, tuple(range(n))):
        assert G._sifts_to_id((f,), 0) == _python_fast(G, (f,), 0)


@needs_ck
def test_sift_rejects_unusual_input():
    idn = tuple(range(3))
    plan = [(0, 0, None, None)]
    assert ck.sift([0, 1, 2], plan, [{}], [0]) is None
    assert ck.sift((0, 1, 7), plan, [{}], [0]) is None
    assert ck.sift((1, 0, 2), plan, [{1: (0, 1)}], [0]) is None     # a wrong-degree element
    assert ck.sift((1, 0, 2), plan, [{1: (2**40, 1, 2)}], [0]) is None
    assert ck.sift(idn, [("bad",)], [{}], [0]) is None
    assert ck.sifts_to_id((), (idn,), [], []) is None
    assert ck.sifts_to_id((0, 9), (idn,), [], []) is None
    assert ck.sifts_to_id((0, 1), (idn, (0, 1)), [], []) is None
    assert ck.make_fast_plan([0], [0], 0, [], 0) is None


@needs_ck
def test_transversal_get_error_propagates():
    class Bad:
        def get(self, p, default=None):
            raise KeyError("from get")
    plan = [(0, 0, None, None)]
    with pytest.raises(KeyError):
        ck.sift((1, 0, 2), plan, [Bad()], [0])
    with pytest.raises(KeyError):
        ck.sifts_to_id((0, 1), ((1, 0, 2),), [(0, 0)], [Bad()])


# -- 2-WL --------------------------------------------------------------------------
def _py_wl2_single(P):
    saved, refine._ck = refine._ck, None
    try:
        return refine.wl2_single(P)
    finally:
        refine._ck = saved


def _random_matrix(rng, n, colors):
    return [[rng.randrange(colors) for _ in range(n)] for _ in range(n)]


def _graph_pairs(rng, n, p=0.5):
    A = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i):
            A[i][j] = A[j][i] = int(rng.random() < p)
    return [[(0 if i == j else 1 + A[i][j]) for j in range(n)] for i in range(n)]


@needs_ck
@pytest.mark.parametrize("n", [1, 2, 3, 4, 5, 8, 16, 33, 64])
def test_wl2_single_random(n):
    rng = random.Random(n * 11)
    for _ in range(25):
        kind = rng.randrange(4)
        if kind == 0:
            P = _random_matrix(rng, n, rng.randint(1, 6))
        elif kind == 1:
            P = _graph_pairs(rng, n, rng.choice([0.1, 0.5, 0.8]))
        elif kind == 2:
            P = [[(0 if i == j else 1) for j in range(n)] for i in range(n)]    # complete
        else:
            P = _random_matrix(rng, n, n * n + 1)                               # near-discrete
        if rng.random() < 0.3:
            P = [[-v - 1 for v in row] for row in P]                            # negative names
        assert ck.wl2_single(P, refine._tables) == _py_wl2_single(P)


@needs_ck
def test_wl2_single_structured():
    import networkx as nx
    graphs = [nx.hypercube_graph(3), nx.petersen_graph(), nx.random_regular_graph(3, 30, seed=2),
              nx.circular_ladder_graph(9), nx.cycle_graph(20), nx.complete_graph(6)]
    for G in graphs:
        nodes = sorted(G.nodes(), key=repr)
        idx = {v: i for i, v in enumerate(nodes)}
        A = [[0] * len(nodes) for _ in nodes]
        for u, v in G.edges():
            A[idx[u]][idx[v]] = A[idx[v]][idx[u]] = 1
        P = [[(0 if i == j else 1 + A[i][j]) for j in range(len(A))] for i in range(len(A))]
        assert ck.wl2_single(P, refine._tables) == _py_wl2_single(P)


@needs_ck
def test_wl2_single_large_degree():
    rng = random.Random(3)
    P = _graph_pairs(rng, 128)
    assert ck.wl2_single(P, refine._tables) == _py_wl2_single(P)


@needs_ck
def test_wl2_single_rejects_unusual_input():
    assert ck.wl2_single([], refine._tables) is None
    assert ck.wl2_single([[0, 1]], refine._tables) is None             # not square
    assert ck.wl2_single([[0], [1, 2]], refine._tables) is None
    assert ck.wl2_single([[2 ** 40]], refine._tables) is None
    assert ck.wl2_single([["a"]], refine._tables) is None
    assert ck.wl2_single([[(0, 1)]], refine._tables) is None
    assert ck.wl2_single(((0,),), refine._tables) is None
    # values the fast path refuses still get the reference's answer
    assert refine.wl2_single([[2 ** 40]]) == _py_wl2_single([[2 ** 40]])
    P = [[("a", 1), ("b", 2)], [("b", 2), ("a", 1)]]
    assert refine.wl2_single(P) == _py_wl2_single(P)


@needs_ck
def test_wl2_single_uses_tables_of_the_reference():
    """Every table the reference asks for is asked for, with the same arguments."""
    rng = random.Random(4)
    P = _graph_pairs(rng, 24)
    log_c, log_p = [], []
    real = refine._tables

    def spy(log):
        def f(size, n, field_bits=128):
            log.append((size, n, field_bits))
            return real(size, n, field_bits)
        return f
    r = ck.wl2_single(P, spy(log_c))
    saved_ck, saved_t = refine._ck, refine._tables
    refine._ck, refine._tables = None, spy(log_p)
    try:
        assert r == refine.wl2_single(P)
    finally:
        refine._ck, refine._tables = saved_ck, saved_t
    assert log_c == log_p


def _ref_check(PX, PY, RX, RY):
    """The reference test in refine.wl2, written out."""
    from collections import Counter
    from itertools import chain as ch
    pairs = set(zip(ch.from_iterable(RX), ch.from_iterable(PX)))
    if RY is not RX:
        pairs.update(zip(ch.from_iterable(RY), ch.from_iterable(PY)))
    if len({r for r, _ in pairs}) != len(pairs):
        return False
    if RY is not RX and Counter(ch.from_iterable(RX)) != Counter(ch.from_iterable(RY)):
        return False
    return True


@needs_ck
@pytest.mark.parametrize("n", [1, 2, 3, 5, 9, 20])
def test_wl2_check_random(n):
    rng = random.Random(n * 13)
    outcomes = set()
    for _ in range(300):
        PX = _random_matrix(rng, n, rng.randint(1, 4))
        s = list(range(n))
        rng.shuffle(s)
        PY = [[PX[s[i]][s[j]] for j in range(n)] for i in range(n)]
        RX, _ = _py_wl2_single(PX)
        RY, _ = _py_wl2_single(PY)
        for _ in range(4):
            a = [list(r) for r in RX]
            b = [list(r) for r in RY]
            c = [list(r) for r in PY]
            kind = rng.randrange(5)
            i, j = rng.randrange(n), rng.randrange(n)
            if kind == 1:                       # break the function
                c[i][j] += 1
            elif kind == 2:                     # break the histogram
                b[i][j] = rng.randrange(n * n)
            elif kind == 3:
                a[i][j] = rng.randrange(n * n)
            r = ck.wl2_check(PX, c, a, b)
            assert r == _ref_check(PX, c, a, b)
            outcomes.add(r)
        same = ck.wl2_check(PX, PX, RX, RX)
        assert same == _ref_check(PX, PX, RX, RX) and same is True
    if n > 2:
        assert outcomes == {True, False}


@needs_ck
def test_wl2_check_rejects_unusual_input():
    P = [[0, 1], [1, 0]]
    assert ck.wl2_check([], [], [], []) is None
    assert ck.wl2_check(P, P, [[0, 4], [1, 0]], P) is None              # a color outside range(N)
    assert ck.wl2_check(P, P, [[0, -1], [1, 0]], P) is None
    assert ck.wl2_check(P, P, [[0, 1]], P) is None
    assert ck.wl2_check([[2 ** 40, 0], [0, 0]], P, P, P) is None
    assert ck.wl2_check(P, P, P, [[0.0, 1], [1, 0]]) is None
    assert ck.wl2_check(P, P) is None


@needs_ck
def test_wl2_both_paths():
    """refine.wl2, kernel on and off, on isomorphic and non-isomorphic pairs."""
    rng = random.Random(21)
    seen = set()
    for _ in range(40):
        n = rng.randint(2, 18)
        PX = _graph_pairs(rng, n, 0.4)
        s = list(range(n))
        rng.shuffle(s)
        PY = [[PX[s[i]][s[j]] for j in range(n)] for i in range(n)] if rng.random() < 0.6 \
            else _graph_pairs(rng, n, 0.4)
        a = refine.wl2(PX, PY)
        saved, refine._ck = refine._ck, None
        refine._WL2_CACHE.clear()
        try:
            b = refine.wl2(PX, PY)
        finally:
            refine._ck = saved
            refine._WL2_CACHE.clear()
        assert a == b
        seen.add(a is None)
    assert seen == {True, False}


# -- whole pipelines in both modes ---------------------------------------------------
_SCRIPT = r"""
import hashlib, json, random, sys
sys.path.insert(0, %(root)r)
sys.setrecursionlimit(100000)
import networkx as nx
from gi import graph_iso, Solver
from gi.bounded import bounded_iso_lists
from gi.canon import canonical_labeling_lists
from gi.group import PermGroup
from gi.kernel import active
from gi.refine import refine_graphs
from bench import irhard

def adj(G):
    nodes = sorted(G.nodes(), key=repr)
    idx = {v: i for i, v in enumerate(nodes)}
    A = [[0] * len(nodes) for _ in nodes]
    for u, v in G.edges():
        A[idx[u]][idx[v]] = A[idx[v]][idx[u]] = 1
    return A

def nbrs(A):
    return [[j for j, v in enumerate(r) if v] for r in A]

def shuffled(A, rng):
    n = len(A)
    p = list(range(n))
    rng.shuffle(p)
    return [[A[p[i]][p[j]] for j in range(n)] for i in range(n)]

rng = random.Random(11)
out = []
graphs = [nx.petersen_graph(), nx.hypercube_graph(4), nx.random_regular_graph(3, 24, seed=5),
          nx.paley_graph(13).to_undirected(), nx.circular_ladder_graph(8),
          nx.complete_bipartite_graph(4, 4), nx.dodecahedral_graph(), nx.grid_2d_graph(3, 4)]
for G in graphs:
    A = adj(G)
    B = shuffled(A, rng)
    for kw in ({}, {"ir": 0}):
        S = Solver(certificates=False)
        out.append(("graph_iso", repr(graph_iso(A, B, solver=S, **kw)), sorted(S.stats.items())))
    out.append(("refine", repr(refine_graphs(A, B))))
    if max(sum(r) for r in A) <= 4:
        out.append(("bounded", repr(bounded_iso_lists(nbrs(A), nbrs(B),
                                                      solver=Solver(cameron_no_enum=True, certificates=False)))))
        out.append(("canon", repr(canonical_labeling_lists(nbrs(A)))))
for k in (8, 12):
    for I in irhard.fam_ns(k, random.Random(k)):
        out.append(("ns", repr(bounded_iso_lists(I["X"], I["Y"], solver=Solver(cameron_no_enum=True, certificates=False)))))
        out.append(("ns-canon", repr(canonical_labeling_lists(I["X"]))))
for b in (8, 12):
    for I in irhard.fam_cfix(b, random.Random(b)):
        out.append(("cfi", repr(bounded_iso_lists(I["X"], I["Y"], solver=Solver(cameron_no_enum=True, certificates=False)))))

# Chains, compared entry by entry: base, strong generators, transversals with
# their insertion order, plans' results.
n = 30
rg = random.Random(1)
for t in range(50):
    gens = []
    for _ in range(rg.randint(1, 4)):
        p = list(range(n)); rg.shuffle(p)
        gens.append(tuple(p) if rg.random() < 0.3 else tuple(
            q for q in __import__("gi.perm", fromlist=["cycle"]).cycle(n, rg.sample(range(n), rg.randint(2, 6)))))
    G = PermGroup(n, gens)
    H = PermGroup(n, gens, ambient_base=G.short_base())
    for X in (G, H):
        out.append(("chain", X.base, X.S, [list(t.items()) for t in X.T],
                    [list(t.items()) for t in X.Ti], X._par, X.gens, X.order(), X.orbits()))
print(json.dumps(dict(active=active(), digest=hashlib.sha256(repr(out).encode()).hexdigest(),
                      items=len(out))))
"""


def _run_mode(no_ck):
    env = dict(os.environ)
    env.pop("GI_NO_CKERNEL", None)
    if no_ck:
        env["GI_NO_CKERNEL"] = "1"
    out = subprocess.run([sys.executable, "-c", _SCRIPT % {"root": ROOT}], env=env, check=True,
                         capture_output=True, text=True, timeout=180)
    return json.loads(out.stdout.strip().splitlines()[-1])


@pytest.mark.skipif(not os.path.exists(os.path.join(ROOT, "gi")) or
                    not any(f.startswith("_ckernel") and f.endswith(".so")
                            for f in os.listdir(os.path.join(ROOT, "gi"))),
                    reason="compiled kernel not built")
def test_pipelines_identical_in_both_modes():
    """The same sigma, generators, chains, orbits, partitions and stats."""
    a = _run_mode(False)
    b = _run_mode(True)
    assert a["active"] is True and b["active"] is False
    assert a["items"] == b["items"] and a["items"] > 100
    assert a["digest"] == b["digest"]


def test_no_ckernel_env_disables():
    env = dict(os.environ, GI_NO_CKERNEL="1")
    out = subprocess.run([sys.executable, "-c",
                          "import sys; sys.path.insert(0, %r); from gi.kernel import active;"
                          "print(active())" % ROOT],
                         env=env, check=True, capture_output=True, text=True)
    assert out.stdout.strip() == "False"
