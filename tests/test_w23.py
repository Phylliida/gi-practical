"""The w23-speed2 kernel primitives against their Python references, and the
algorithmic changes of the canonical path (docs/w23-speed2.md).

The C-versus-Python comparisons are skipped without the kernel; the others run
in both modes. GI_REQUIRE_CKERNEL=1 makes a missing kernel a failure (see
tests/test_ckernel.py).
"""
import math
import os
import random
import subprocess
import sys
from collections import Counter

import pytest

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

import networkx as nx

import gi.bounded as bounded
import gi.canon as canon
import gi.ea2 as ea2
import gi.kernel as kernel
import gi.wl as wl
from gi.bounded import _Graph, _truncated_profiles, class_plan, bounded_iso_lists
from gi.canon import _closure_dense, _closure_sparse, _table_to_pos, _rows_to_pos, canonical_labeling_lists, _form_of
from gi.ea2 import EAAction, SparseEA, compose, XorBasis
from gi.group import PermGroup
from bench import irhard

ck = kernel.ck
if os.environ.get("GI_REQUIRE_CKERNEL") == "1" and ck is None:
    raise RuntimeError("GI_REQUIRE_CKERNEL=1 but the compiled kernel is not loaded")
needs_ck = pytest.mark.skipif(ck is None, reason="compiled kernel not loaded")


@pytest.fixture
def no_ck(monkeypatch):
    """The Python references: every module's kernel handle off."""
    for mod in (wl, bounded, canon, ea2):
        monkeypatch.setattr(mod, "_ck", None)


# -- graphs ---------------------------------------------------------------------------
def rand_nbr(rng, n, p):
    nbr = [[] for _ in range(n)]
    for u in range(n):
        for v in range(u + 1, n):
            if rng.random() < p:
                nbr[u].append(v)
                nbr[v].append(u)
    return nbr


def regular(d, n, seed):
    G = nx.random_regular_graph(d, n, seed=seed)
    idx = {v: i for i, v in enumerate(sorted(G.nodes()))}
    nbr = [[] for _ in range(n)]
    for u, v in G.edges():
        nbr[idx[u]].append(idx[v])
        nbr[idx[v]].append(idx[u])
    return [sorted(r) for r in nbr]


def cube(d):
    return [sorted(v ^ (1 << i) for i in range(d)) for v in range(1 << d)]


def relabel(nbr, rng):
    n = len(nbr)
    s = list(range(n))
    rng.shuffle(s)
    out = [None] * n
    for v in range(n):
        out[s[v]] = sorted(s[w] for w in nbr[v])
    return out


GRAPHS = [lambda r: rand_nbr(r, 30, 0.15), lambda r: rand_nbr(r, 60, 0.05), lambda r: rand_nbr(r, 8, 0.5),
          lambda r: regular(3, 40, r.randrange(10**6)), lambda r: regular(4, 50, r.randrange(10**6)),
          lambda r: cube(4), lambda r: cube(5), lambda r: [[(v + 1) % 16, (v - 1) % 16] for v in range(16)]]


# -- wl_refine ------------------------------------------------------------------------
def py_refine(nbr, col, roots=(), stable=False):
    handle, wl._ck = wl._ck, None
    try:
        return wl.refine(nbr, col, roots, stable)
    finally:
        wl._ck = handle


@needs_ck
def test_wl_refine_random():
    rng = random.Random(1)
    for t in range(300):
        nbr = GRAPHS[t % len(GRAPHS)](rng)
        n = len(nbr)
        ncol = rng.choice([1, 2, 3, n])
        col = [rng.randrange(ncol) for _ in range(n)]
        roots = tuple(rng.sample(range(n), rng.randint(0, 3)))
        got = ck.wl_refine(nbr, col, roots, False)
        assert got == py_refine(nbr, col, roots, False)
        assert type(got) is list
        # stable start: an equitable coloring, roots individualized
        st = py_refine(nbr, col, (), False)
        got = ck.wl_refine(nbr, st, roots, True)
        assert got == py_refine(nbr, st, roots, True)


@needs_ck
def test_wl_refine_shapes():
    assert ck.wl_refine([], [], (), False) == []
    assert ck.wl_refine([[]], [0], (), False) == [0]
    assert ck.wl_refine([[], []], [5, -3], (), False) == py_refine([[], []], [5, -3], (), False)
    assert ck.wl_refine([[1], [0]], [0, 0], (0,), True) == py_refine([[1], [0]], [0, 0], (0,), True)
    # unusual input: declined (None), so the Python body decides
    assert ck.wl_refine([[1], [0]], ["a", "b"], (), False) is None
    assert ck.wl_refine([[1], [0]], [0, 0], (5,), False) is None
    assert ck.wl_refine([[1], [0]], [0, 0], (), 1) is None
    assert ck.wl_refine([[1.5], [0]], [0, 0], (), False) is None
    assert wl.refine([[1], [0]], ["a", "b"]) == py_refine([[1], [0]], ["a", "b"])


# -- class_plan ------------------------------------------------------------------------
def py_plan(g, col, u0, u1):
    handle, bounded._ck = bounded._ck, None
    try:
        return bounded.class_plan(g, col, u0, u1)
    finally:
        bounded._ck = handle


@needs_ck
def test_class_plan_random():
    rng = random.Random(2)
    for t in range(200):
        nbr = [sorted(r) for r in GRAPHS[t % len(GRAPHS)](rng)]
        n = len(nbr)
        col0 = [rng.randrange(max(1, n // 5)) for _ in range(n)] if t % 3 == 0 else [0] * n
        edges = [(u, v) for u in range(n) for v in nbr[u]]
        if not edges:
            continue
        u0, u1 = rng.choice(edges)
        g = _Graph(nbr, py_refine(nbr, col0, (), False))
        col = py_refine(nbr, g.col, (u0, u1), True)
        assert ck.class_plan(nbr, col, u0, u1) == py_plan(g, col, u0, u1)


@needs_ck
def test_class_plan_rejects_unusual():
    assert ck.class_plan([[1], [0]], [0, 7], 0, 1) is NotImplemented       # color out of range
    assert ck.class_plan([[1, 1], [0]], [0, 0], 0, 1) is NotImplemented    # not strictly sorted
    assert ck.class_plan([[1], [0]], [0, 0], 0, 5) is NotImplemented


# -- bit-parallel balls ----------------------------------------------------------------
def py_profiles(g, edges, C, use_col):
    handle, bounded._ck = bounded._ck, None
    try:
        return _truncated_profiles(g, edges, C, use_col)
    finally:
        bounded._ck = handle


@needs_ck
@pytest.mark.parametrize("seed", range(60))
def test_truncated_profiles_both_paths(seed):
    rng = random.Random(seed)
    nbr = [sorted(r) for r in GRAPHS[seed % len(GRAPHS)](rng)]
    n = len(nbr)
    ncol = rng.choice([1, 2, 4, 5])
    col = [rng.randrange(ncol) for _ in range(n)]
    g = _Graph(nbr, col)
    edges = [(u, v) for u in range(n) for v in nbr[u]]
    if not edges:
        return
    C = sorted(rng.sample(range(len(edges)), max(1, len(edges) // 2)))
    use_col = 1 < len(set(col)) <= 4
    assert _truncated_profiles(g, edges, C, use_col) == py_profiles(g, edges, C, use_col)


def test_truncated_profiles_keys_stay_invariant():
    """Stage-1 keys under relabelling (the k1 recomputed only when the partition
    changes must still be the keys of the final vertex names)."""
    rng = random.Random(7)
    for d in (3, 4, 5):
        G = cube(d)
        s = list(range(1 << d))
        rng.shuffle(s)
        H = [sorted(s[w] for w in G[s.index(v)]) for v in range(1 << d)]
        for X in (G, H):
            g = _Graph(X, [0] * (1 << d))
            edges = [(u, v) for u in range(1 << d) for v in X[u]]
            k = _truncated_profiles(g, edges, list(range(len(edges))), False)
            assert len(set(k)) == 1             # edge-transitive: one class


# -- edge orbits -----------------------------------------------------------------------
@needs_ck
def test_orbit_absorb_matches_python_partition():
    rng = random.Random(3)
    for t in range(60):
        d = rng.randint(2, 5)
        nbr = cube(d)
        n = len(nbr)
        edges = [(u, v) for u in range(n) for v in nbr[u]]
        eidx = {e: i for i, e in enumerate(edges)}
        K = sorted(rng.sample(range(len(edges)), len(edges)))
        tbl = ck.orbit_table(nbr, K)
        assert tbl is not None
        pos = {f: i for i, f in enumerate(K)}
        parent_c, parent_p = list(range(len(K))), list(range(len(K)))

        def find(p, v):
            while p[v] != v:
                p[v] = p[p[v]]
                v = p[v]
            return v

        comps_c = comps_p = len(K)
        for _ in range(rng.randint(1, 6)):
            p = list(range(d))
            rng.shuffle(p)
            flip = rng.randrange(n)
            a = tuple(sum(((v >> i) & 1) << p[i] for i in range(d)) ^ flip for v in range(n))
            comps_c -= ck.orbit_absorb(tbl, parent_c, comps_c, a)
            for i, f in enumerate(K):
                u, v = edges[f]
                x, y = find(parent_p, i), find(parent_p, pos[eidx[(a[u], a[v])]])
                if x != y:
                    parent_p[max(x, y)] = min(x, y)
                    comps_p -= 1
            assert comps_c == comps_p
            assert [find(parent_c, i) for i in range(len(K))] == [find(parent_p, i) for i in range(len(K))]


@needs_ck
def test_orbit_absorb_rejects_non_automorphism():
    nbr = cube(3)
    edges = [(u, v) for u in range(8) for v in nbr[u]]
    tbl = ck.orbit_table(nbr, list(range(len(edges))))
    parent = list(range(len(edges)))
    a = tuple([1, 0] + list(range(2, 8)))       # not an automorphism
    before = list(parent)
    assert ck.orbit_absorb(tbl, parent, len(edges), a) is None
    assert parent == before


# -- check_lists, BFS, automorphism test --------------------------------------------------
def py_check(nbr):
    handle, bounded._ck = bounded._ck, None
    try:
        return bounded._check_lists(nbr)
    finally:
        bounded._ck = handle


@needs_ck
def test_check_lists():
    rng = random.Random(6)
    for t in range(100):
        nbr = [sorted(r) for r in GRAPHS[t % len(GRAPHS)](rng)]
        r = ck.check_lists(nbr)
        assert r == py_check(nbr) and r is not nbr and all(a is not b for a, b in zip(r, nbr))
    assert ck.check_lists([]) == []
    for bad in ([[0]], [[1], []], [[1, 1], [0]], [[2, 1], [0], [0]], [[5], [0]], [[1.0], [0]], [(1,), (0,), 3]):
        assert ck.check_lists(bad) is None      # (the Python body raises or sorts)
    assert ck.check_lists([(1,), (0,)]) == [[1], [0]] == py_check([(1,), (0,)])
    with pytest.raises(bounded.NotSimple):
        bounded._check_lists([[0]])
    assert bounded._check_lists([[2, 1], [0], [0]]) == [[1, 2], [0], [0]]


@needs_ck
def test_bfs_dist():
    rng = random.Random(7)
    for t in range(100):
        nbr = GRAPHS[t % len(GRAPHS)](rng)
        g = _Graph(nbr, [0] * len(nbr))
        s = rng.randrange(len(nbr))
        handle, bounded._ck = bounded._ck, None
        try:
            ref = bounded._bfs_dist(g, s)
        finally:
            bounded._ck = handle
        assert ck.bfs_dist(nbr, s) == ref
    assert ck.bfs_dist([[1], [0]], 2) is None


@needs_ck
def test_is_automorphism():
    rng = random.Random(8)
    for t in range(200):
        nbr = [sorted(r) for r in GRAPHS[t % len(GRAPHS)](rng)]
        n = len(nbr)
        p = list(range(n))
        rng.shuffle(p)
        phi = tuple(p)
        ref = all(sorted(phi[w] for w in nbr[v]) == nbr[phi[v]] for v in range(n))
        assert ck.is_automorphism(nbr, phi) is ref
        assert ck.is_automorphism(nbr, tuple(range(n))) is True
    d = 4
    nbr = cube(d)
    assert ck.is_automorphism(nbr, tuple(v ^ 5 for v in range(16))) is True
    assert ck.is_automorphism(nbr, (0, 0) + tuple(range(2, 16))) is None   # not a permutation
    assert ck.is_automorphism(nbr, tuple(range(15))) is None


# -- closures -------------------------------------------------------------------------
def rand_perm(rng, n):
    p = list(range(n))
    rng.shuffle(p)
    return tuple(p)


def involution(rng, n):
    pts = rng.sample(range(n), 2 * rng.randint(0, n // 2))
    g = list(range(n))
    for i in range(0, len(pts), 2):
        g[pts[i]], g[pts[i + 1]] = pts[i + 1], pts[i]
    return tuple(g)


@needs_ck
@pytest.mark.parametrize("seed", range(120))
def test_closure_dense(seed):
    rng = random.Random(seed)
    n = rng.randint(3, 25)
    kind = seed % 2
    gens = [rand_perm(rng, n) for _ in range(rng.randint(1, 4))]
    if kind == 0:
        seeds = list({frozenset(rng.sample(range(n), rng.randint(1, min(n, 5)))) for _ in range(rng.randint(1, 6))})
        image = canon._set_image
    else:
        seeds = []
        for _ in range(rng.randint(1, 6)):
            a, b = rng.sample(range(n), 2)
            seeds.append((min(a, b), max(a, b)))
        seeds = list(dict.fromkeys(seeds))
        image = canon._pair_image
    py_list, rows = _closure_dense(seeds, gens, image)
    key = (lambda S: tuple(sorted(S))) if kind == 0 else None
    py_pos = sorted(py_list, key=key)
    pidx = {S: i for i, S in enumerate(py_pos)}
    py_acts = _rows_to_pos(rows, py_list, pidx)
    res = ck.closure_dense(seeds, gens, kind)
    assert res is not None
    assert res[0] == py_pos
    assert res[1] == py_acts


@needs_ck
def test_closure_dense_rejects_unusual():
    g = [(1, 0, 2)]
    assert ck.closure_dense([{0}], g, 0) is None            # a set, not a frozenset
    assert ck.closure_dense([(0, 1)], g, 2) is None         # bad kind
    assert ck.closure_dense([(1, 0)], g, 1) is None         # unsorted pair
    assert ck.closure_dense([frozenset([7])], g, 0) is None  # point out of range


def rand_sparse_group(rng, n, k):
    """A SparseEA with k independent commuting involutions on range(n): disjoint
    products of transpositions over blocks."""
    gens = []
    pts = list(range(n))
    rng.shuffle(pts)
    pairs = [(pts[i], pts[i + 1]) for i in range(0, n - 1, 2)]
    for _ in range(k):
        g = {}
        for a, b in rng.sample(pairs, rng.randint(1, len(pairs))):
            g[a], g[b] = b, a
        gens.append(g)
    return SparseEA(gens)


@needs_ck
@pytest.mark.parametrize("seed", range(120))
def test_closure_sparse(seed):
    rng = random.Random(seed)
    n = rng.randint(4, 30)
    kind = seed % 2
    G = rand_sparse_group(rng, n, rng.randint(1, 5))
    if kind == 0:
        seeds = list({frozenset(rng.sample(range(n), rng.randint(1, min(n, 5)))) for _ in range(rng.randint(1, 6))})
        image = canon._set_image_sparse
    else:
        seeds = []
        for _ in range(rng.randint(1, 6)):
            a, b = rng.sample(range(n), 2)
            seeds.append((min(a, b), max(a, b)))
        seeds = list(dict.fromkeys(seeds))
        image = canon._pair_image_sparse
    py_list, table = _closure_sparse(seeds, G, image)
    key = (lambda S: tuple(sorted(S))) if kind == 0 else None
    py_pos = sorted(py_list, key=key)
    pidx = {S: i for i, S in enumerate(py_pos)}
    py_table = _table_to_pos(table, py_list, pidx)
    res = ck.closure_sparse(seeds, G.gens, G.who, kind)
    assert res is not None
    assert res[0] == py_pos
    assert res[1] == py_table


@needs_ck
def test_closure_sparse_rejects_unusual():
    G = SparseEA([{0: 1, 1: 0}])
    assert ck.closure_sparse([{0}], G.gens, G.who, 0) is None       # a set
    assert ck.closure_sparse([frozenset([0])], [], G.who, 0) is None
    assert ck.closure_sparse([frozenset([0])], G.gens, G.who, 3) is None


# -- SparseEA ----------------------------------------------------------------------------
@needs_ck
def test_ea_compose_and_order():
    rng = random.Random(4)
    for _ in range(200):
        n = rng.randint(2, 40)
        dicts = []
        for _ in range(rng.randint(0, 5)):
            pts = rng.sample(range(n), 2 * rng.randint(0, n // 2))
            g = {}
            for i in range(0, len(pts), 2):
                g[pts[i]], g[pts[i + 1]] = pts[i + 1], pts[i]
            dicts.append(g)
        a = ck.ea_compose(dicts)
        handle, ea2._ck = ea2._ck, None
        try:
            b = compose(dicts)
        finally:
            ea2._ck = handle
        assert a == b and list(a.items()) == list(b.items())


@needs_ck
def test_ea_who_maintenance():
    """The compiled add/extend/remove keep the same index as the reference."""
    rng = random.Random(5)
    for _ in range(60):
        n = rng.randint(4, 30)
        a, b = SparseEA(), SparseEA()
        ids = []
        for step in range(rng.randint(5, 25)):
            act = rng.random()
            if act < 0.6 or not ids:
                pts = rng.sample(range(n), 2 * rng.randint(1, n // 2))
                g = {}
                for i in range(0, len(pts), 2):
                    g[pts[i]], g[pts[i + 1]] = pts[i + 1], pts[i]
                ia = a.add(dict(g))
                handle, ea2._ck = ea2._ck, None
                try:
                    ib = b.add(dict(g))
                finally:
                    ea2._ck = handle
                assert ia == ib
                ids.append(ia)
            elif act < 0.8:
                gid = rng.choice(ids)
                base = n + rng.randint(0, 5)
                e = {base: base + 1, base + 1: base}
                a.extend(gid, dict(e))
                handle, ea2._ck = ea2._ck, None
                try:
                    b.extend(gid, dict(e))
                finally:
                    ea2._ck = handle
            else:
                gid = ids.pop(rng.randrange(len(ids)))
                a.remove(gid)
                handle, ea2._ck = ea2._ck, None
                try:
                    b.remove(gid)
                finally:
                    ea2._ck = handle
            assert a.gens == b.gens and a.who == b.who


# -- ea_canon ----------------------------------------------------------------------------
def py_canon(k, act, m, x):
    handle, ea2._ck = ea2._ck, None
    try:
        return EAAction(k, act, m).canon(x)
    finally:
        ea2._ck = handle


def rand_ea_action(rng, m, k):
    """k commuting involutions on m positions (products of transpositions on a
    fixed pairing, or identity)."""
    pts = list(range(m))
    rng.shuffle(pts)
    pairs = [(pts[i], pts[i + 1]) for i in range(0, m - 1, 2)]
    act = []
    for _ in range(k):
        g = list(range(m))
        for a, b in pairs:
            if rng.random() < 0.5:
                g[a], g[b] = b, a
        act.append(tuple(g))
    return act


@needs_ck
@pytest.mark.parametrize("seed", range(300))
def test_ea_canon(seed):
    rng = random.Random(seed)
    m = rng.choice([2, 4, 8, 16, 32, 100, 256])
    k = rng.choice([0, 1, 2, 3, 8, 63, 64, 65, 130])
    ncol = rng.choice([1, 2, 3, 9])
    act = rand_ea_action(rng, m, k)
    x = tuple(rng.randrange(ncol) for _ in range(m))
    assert ck.ea_canon(k, act, m, x) == py_canon(k, act, m, x)
    assert ck.ea_canon(k, act, m, list(x)) == py_canon(k, act, m, x)


@needs_ck
def test_ea_canon_rejects_unusual():
    act = [(1, 0)]
    assert ck.ea_canon(1, (act[0],), 2, (0, 1)) is None     # act not a list
    assert ck.ea_canon(1, act, 2, ("a", "b")) is None
    assert ck.ea_canon(2, act, 2, (0, 1)) is None           # wrong number of generators


# -- whole pipelines in both modes --------------------------------------------------------
FAMS = [lambda rng: rand_nbr(rng, 30, 0.1), lambda rng: regular(3, 30, rng.randrange(10**5)),
        lambda rng: regular(4, 40, rng.randrange(10**5)), lambda rng: cube(5), lambda rng: cube(6)]


@pytest.mark.parametrize("seed", range(40))
def test_canonical_form_under_relabelling(seed):
    rng = random.Random(seed)
    nbr = FAMS[seed % len(FAMS)](rng)
    Y = relabel(nbr, rng)
    lx, gx = canonical_labeling_lists(nbr)
    ly, gy = canonical_labeling_lists(Y)
    fx, fy = _form_of(nbr, lx, None), _form_of(Y, ly, None)
    assert fx == fy
    n = len(nbr)
    for g in gx:
        for v in range(n):
            assert sorted(g[w] for w in nbr[v]) == nbr[g[v]]
    ox = PermGroup(n, gx).order() if gx else 1
    oy = PermGroup(n, gy).order() if gy else 1
    assert ox == oy


@pytest.mark.parametrize("d", [2, 3, 4, 5, 6, 7])
def test_hypercube_order(d):
    nbr = cube(d)
    lab, gens = canonical_labeling_lists(nbr)
    assert PermGroup(1 << d, gens).order() == 2 ** d * math.factorial(d)


@pytest.mark.parametrize("seed", range(15))
def test_non_isomorphic_forms_differ(seed):
    rng = random.Random(seed)
    X, Y = regular(3, 30, 2 * seed + 1), regular(3, 30, 2 * seed + 2)
    bo = bounded_iso_lists(X, Y)
    fx = _form_of(X, canonical_labeling_lists(X)[0], None)
    fy = _form_of(Y, canonical_labeling_lists(Y)[0], None)
    assert (fx == fy) == (bo is not None)


def test_probe_automorphism_soundness():
    """Whatever the probe returns is an automorphism mapping the first edge
    onto the second; on a vertex-transitive graph it can succeed."""
    rng = random.Random(9)
    G = _Graph(cube(5), [0] * 32)
    edges = [(u, v) for u in range(32) for v in G.nbr[u]]
    found = 0
    st = Counter()
    for _ in range(30):
        f0, f1 = rng.choice(edges), rng.choice(edges)
        phi = canon._probe_automorphism(G, f0, f1, st)
        if phi is not None:
            found += 1
            assert phi[f0[0]] == f1[0] and phi[f0[1]] == f1[1]
            assert sorted(phi) == list(range(32))
            for v in range(32):
                assert sorted(phi[w] for w in G.nbr[v]) == G.nbr[phi[v]]
    assert found == st["canon_probe_ok"] and found > 0
    # a rooted-inequivalent pair in a graph with few automorphisms
    H = _Graph(regular(3, 30, 3), [0] * 30)
    e0 = (0, H.nbr[0][0])
    e1 = (1, H.nbr[1][0])
    phi = canon._probe_automorphism(H, e0, e1, Counter())
    if phi is not None:
        assert phi[e0[0]] == e1[0] and phi[e0[1]] == e1[1]
        for v in range(30):
            assert sorted(phi[w] for w in H.nbr[v]) == H.nbr[phi[v]]


def _both_modes_digest(script):
    outs = []
    for no_ck_mode in (False, True):
        env = dict(os.environ)
        if no_ck_mode:
            env["GI_NO_CKERNEL"] = "1"
        else:
            env.pop("GI_NO_CKERNEL", None)
        r = subprocess.run([sys.executable, "-c", script], env=env, check=True, capture_output=True,
                           text=True, timeout=300, cwd=os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
        outs.append(r.stdout.strip())
    return outs


@pytest.mark.skipif(ck is None, reason="compiled kernel not loaded")
def test_w23_pipeline_identical_in_both_modes():
    """Whole canonical labelings (labelling, form, generators) with the kernel
    on and off, on the families the compiled paths serve."""
    script = r"""
import random, hashlib, sys
sys.setrecursionlimit(100000)
from gi.canon import canonical_labeling_lists
from gi.bounded import bounded_iso_lists
from bench import irhard
out = []
for k in (8, 16, 24):
    for I in irhard.fam_ns(k, random.Random(k)):
        out.append(("ns", repr(canonical_labeling_lists(I["X"])), repr(bounded_iso_lists(I["X"], I["Y"]))))
for b in (8, 16, 24):
    for I in irhard.fam_cfix(b, random.Random(b)):
        out.append(("cfix", repr(canonical_labeling_lists(I["X"]))))
for b in (10, 20):
    for I in irhard.fam_mzgen(b, random.Random(b)):
        out.append(("mz", repr(canonical_labeling_lists(I["X"]))))
for d in (4, 6, 7):
    nb = [sorted(v ^ (1 << i) for i in range(d)) for v in range(1 << d)]
    out.append(("cube", repr(canonical_labeling_lists(nb))))
print(hashlib.sha256(repr(out).encode()).hexdigest(), len(out))
"""
    a, b = _both_modes_digest(script)
    assert a == b and int(a.split()[1]) > 10


def test_lazy_group_gens_equal_permgroup(monkeypatch):
    """_perm_H's generators are those PermGroup keeps (the Sym generators of all
    but the first block of an orbit are redundant)."""
    real = canon._LazyGroup
    checked = [0]

    class Checked(real):
        def __init__(self, n, gens, order):
            super().__init__(n, gens, order)
            P = PermGroup(n, gens, order=order)
            assert P.gens == gens, "wrapper generators differ from the chain's"
            assert P.order() == order
            checked[0] += 1

    monkeypatch.setattr(canon, "_LazyGroup", Checked)
    rng = random.Random(0)
    graphs = [(cube(3), None), (cube(4), None), (cube(5), None), (relabel(cube(5), rng), None),
              (nx_to(nx.complete_bipartite_graph(3, 4)), None), (nx_to(nx.ladder_graph(7)), None),
              (nx_to(nx.cycle_graph(12)), None), (nx_to(nx.johnson_graph(6, 2)) if hasattr(nx, "johnson_graph")
                                                  else cube(2), None)]
    # twin classes in several colors and sizes: trees of stars and blown-up cycles, colored
    for t in range(30):
        m = rng.randint(3, 7)
        k = rng.randint(2, 5)
        nb = [[] for _ in range(m + m * k)]
        for i in range(m):                      # a cycle of hubs, each with k leaves
            j = (i + 1) % m
            nb[i].append(j)
            nb[j].append(i)
            for l in range(k):
                v = m + i * k + l
                nb[i].append(v)
                nb[v].append(i)
        nb = [sorted(set(r)) for r in nb]
        cols = None
        if t % 2:
            cols = [0] * m + [rng.randrange(2) for _ in range(m * k)]
        graphs.append((nb, cols))
    for G, cols in graphs:
        canonical_labeling_lists(G, cols)
    assert checked[0] > 0


def nx_to(G):
    nodes = sorted(G.nodes(), key=repr)
    idx = {v: i for i, v in enumerate(nodes)}
    nb = [[] for _ in nodes]
    for u, v in G.edges():
        nb[idx[u]].append(idx[v])
        nb[idx[v]].append(idx[u])
    return [sorted(r) for r in nb]
