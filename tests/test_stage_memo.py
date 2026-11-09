"""The incremental stage loop and the caches added with it (docs/w22-speed.md).

Three kinds of test:
  * the tracked scan against the full rescan (random states, and whole runs with
    the debug audit on), and that the audit does detect stale verdicts;
  * fault injection: a wrong verdict must not be able to change the answer;
  * the C fast paths against their Python references, and the chain cache's
    id-keyed front under id reuse and eviction.
"""
import itertools
import os
import random
import subprocess
import sys

import pytest

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

import gi.graph as graph
import gi.group as group
import gi.kernel as kernel
import gi.solver as solver
from bench.families import instances
from gi import graph_iso, Solver
from gi.graph import StageMemo, clean, pick_stage, pick_stage_tracked, pull_back, sym_clean
from gi.group import PermGroup, clear_chain_cache
from gi.perm import sym_gens

ck = kernel.ck
needs_ck = pytest.mark.skipif(ck is None, reason="compiled kernel not loaded")
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")


def rperm(rng, n):
    p = list(range(n))
    rng.shuffle(p)
    return tuple(p)


def rand_state(rng):
    """Random x, y, factors and fixed vertices, biased so that blocks are often clean."""
    n = rng.randint(2, 14)
    colors = rng.choice([1, 2, 3])
    x = [[rng.randrange(colors) for _ in range(n)] for _ in range(n)]
    if rng.random() < 0.5:
        x = [[0] * n for _ in range(n)]
    y = [list(r) for r in x]
    if rng.random() < 0.5:
        for _ in range(rng.randint(1, 3)):
            y[rng.randrange(n)][rng.randrange(n)] = rng.randrange(colors + 1)
    pts = list(range(n))
    rng.shuffle(pts)
    fixed, factors = [], []
    i = 0
    while i < n:
        k = rng.randint(1, min(4, n - i))
        P = sorted(pts[i:i + k])
        i += k
        if k == 1 or rng.random() < 0.15:
            fixed += P
        elif rng.random() < 0.5:
            factors.append((P, None))
        else:
            g = list(range(n))
            q = P[1:] + P[:1]
            for a, b in zip(P, q):
                g[a] = b
            factors.append((P, [tuple(g)]))
    return n, x, y, factors, fixed


@pytest.mark.parametrize("seed", range(400))
def test_tracked_equals_full_scan_random(seed):
    rng = random.Random(seed)
    n, x, y, factors, fixed = rand_state(rng)
    memo = StageMemo()
    for _ in range(6):
        got = pick_stage_tracked(n, x, y, factors, fixed, memo)
        assert got == pick_stage(n, x, y, factors, fixed)
        memo.audit(n, x, y, factors, fixed, got)
        # the loop's moves: y moved by an element of G (no moved fixed vertex),
        # or a refinement (colors replaced, memo cleared)
        r = rng.random()
        if r < 0.45 and factors:
            P, gens = rng.choice(factors)
            if gens is None:
                pi = list(range(n))
                a, b = rng.sample(P, 2)
                pi[a], pi[b] = b, a
                pi = tuple(pi)
            else:
                pi = gens[0]
            y = pull_back(y, pi)
            memo.moved(pi, factors, fixed)
        elif r < 0.65 and factors:
            P, gens = factors.pop(rng.randrange(len(factors)))
            fixed = fixed + [v for v in P]
            # (a vertex that stops moving: nothing moved, verdicts stay valid)
        elif r < 0.8:
            x = [list(row) for row in x]
            x[rng.randrange(n)][rng.randrange(n)] = 5
            y = [list(row) for row in y]
            memo.clear()


def test_audit_detects_stale_verdicts():
    """The debug audit is not vacuous: y changing without moved() is caught."""
    n = 6
    x = [[0] * n for _ in range(n)]
    y = [[0] * n for _ in range(n)]
    factors = [([0, 1], None), ([2, 3], None)]
    fixed = [4, 5]
    memo = StageMemo()
    stage = pick_stage_tracked(n, x, y, factors, fixed, memo)
    assert stage is None
    memo.audit(n, x, y, factors, fixed, stage)
    y2 = [list(r) for r in y]
    y2[0][2] = 7                        # a change in the block of the factors, unreported
    with pytest.raises(AssertionError):
        memo.audit(n, x, y2, factors, fixed, pick_stage_tracked(n, x, y2, factors, fixed, memo))


def test_moved_invalidates_exactly_the_touched_factors():
    n = 6
    x = [[0] * n for _ in range(n)]
    y = [[0] * n for _ in range(n)]
    fa, fb = ([0, 1], None), ([2, 3], None)
    memo = StageMemo()
    assert pick_stage_tracked(n, x, y, [fa, fb], [4, 5], memo) is None
    s0, s1 = memo.sid(fa), memo.sid(fb)
    memo.moved((1, 0, 2, 3, 4, 5), [fa, fb], [4, 5])    # only fa moved
    assert memo.sid(fa) != s0 and memo.sid(fb) == s1


def test_moved_fixed_vertex_clears_everything():
    n = 4
    memo = StageMemo()
    memo.verdict[(0, 0)] = True
    memo.fix_ok = 2
    memo.moved((0, 1, 3, 2), [], [2, 3])
    assert memo.verdict == {} and memo.fix_ok == 0


WORKLOAD = [("tiny", {}), ("small", {}), ("medium", {}), ("hard", {}),
            ("tiny", {"ir": 0}), ("small", {"ir": 0}), ("medium", {"ir": 0})]


@pytest.mark.parametrize("tier,kw", WORKLOAD, ids=[f"{t}:{k}" for t, k in WORKLOAD])
def test_audit_passes_on_benchmark(monkeypatch, tier, kw):
    """The full rescan alongside the tracked scan, over a whole tier."""
    monkeypatch.setattr(graph, "STAGE_CHECK", True)
    audits = [0]
    orig = StageMemo.audit

    def counted(self, *a):
        audits[0] += 1
        return orig(self, *a)

    monkeypatch.setattr(StageMemo, "audit", counted)
    for name, t, X, Y, _, _ in instances(tiers={tier}):
        if t == tier:
            S = Solver(certificates=False)
            graph_iso(X, Y, solver=S, **kw)
            assert S.stats["stage_memo_mismatch"] == 0, name
    assert audits[0] > 0


def run_tier(tier, **kw):
    out = {}
    for name, t, X, Y, _, _ in instances(tiers={tier}):
        if t == tier:
            S = Solver(certificates=False)
            out[name] = graph_iso(X, Y, solver=S, **kw)
    return out


def test_refinement_clears_the_verdicts(monkeypatch):
    """The loop itself must forget its verdicts at a refinement. A block that
    was clean turns dirty when the (patched) refinement recolors it; with the
    audit on, a stale verdict raises instead of waiting for the final rescan."""
    monkeypatch.setattr(graph, "STAGE_CHECK", True)
    n = 8
    F1, F2, F3, F4 = [0, 1], [2, 3], [4, 5], [6, 7]
    x = [[0] * n for _ in range(n)]
    for v in range(n):
        x[v][v] = 1
    # Only the cross block of F2 and F3 is dirty, so the first scan stores
    # (F1, F2), (F1, F3) and (F1, F4) as clean and picks (F2, F3). F1 and F4
    # survive that stage, and so does the verdict of their block.
    x[2][4] = x[4][2] = 2
    y = [list(r) for r in x]
    calls, stored = [0], [False]
    orig = graph.pick_stage_tracked

    def spy(n, x, y, factors, fixed, memo):
        r = orig(n, x, y, factors, fixed, memo)
        live = {memo.sid(f): f for f in factors}
        stored[0] = stored[0] or any(v and sa in live and sb in live
                                     and {live[sa][0][0], live[sb][0][0]} == {0, 6}
                                     for (sa, sb), v in memo.verdict.items())
        return r

    def recolor(px, py, lx, ly, method):
        """A refinement that makes the surviving clean block differ."""
        calls[0] += 1
        px2, py2 = [list(r) for r in px], [list(r) for r in py]
        py2[0][6] = 9
        return px2, py2

    monkeypatch.setattr(graph, "pick_stage_tracked", spy)
    monkeypatch.setattr(graph, "refine_pairs", recolor)
    S = Solver(certificates=False)
    r = graph.staged_iso(S, n, x, y, "2wl", [(F1, None), (F2, None), (F3, None), (F4, None)], [],
                         fresh=True)
    assert stored[0], "the scenario must store a clean verdict for (F1, F4)"
    assert calls[0] >= 1, "the scenario must reach a refinement"
    assert r is None                    # the recolored block has no isomorphism
    assert S.stats["stage_memo_mismatch"] == 0


def test_wrong_clean_verdicts_cannot_change_the_answer(monkeypatch):
    """pick_stage_tracked claiming "all clean" is overruled by the full rescan
    at the end of the loop, so the outputs are unchanged."""
    want = run_tier("hard")

    def always_clean(n, x, y, factors, fixed, memo):
        return None

    monkeypatch.setattr(graph, "pick_stage_tracked", always_clean)
    S_seen = []
    for name, t, X, Y, _, _ in instances(tiers={"hard"}):
        if t == "hard":
            S = Solver(certificates=False)
            assert graph_iso(X, Y, solver=S) == want[name], name
            S_seen.append(S.stats["stage_memo_mismatch"])
    assert any(S_seen)                  # the fallback was really exercised


def test_wrong_dirty_verdicts_stay_exact(monkeypatch):
    """A spurious stage (a verdict wrongly dirty) costs time, not exactness."""
    orig = graph.pick_stage_tracked

    def spurious(n, x, y, factors, fixed, memo):
        s = orig(n, x, y, factors, fixed, memo)
        if s is None and factors:           # claim the smallest factor's own block is dirty
            f = sorted(factors, key=lambda f: (len(f[0]), f[0][0]))[0]
            P = f[0]
            calls[0] += 1
            if calls[0] < 40:
                return "self", [f], [(i, j) for i in P for j in P]
        return s

    calls = [0]
    monkeypatch.setattr(graph, "pick_stage_tracked", spurious)
    for name, t, X, Y, want_iso, want_aut in instances(tiers={"tiny", "small", "medium"}):
        r = graph_iso(X, Y, solver=Solver(certificates=False))
        assert (r is not None) == want_iso, name
        if r is not None:
            sigma, gens = r
            n = len(X)
            assert all(Y[sigma[i]][sigma[j]] == X[i][j] for i in range(n) for j in range(n)), name
            for g in gens:
                assert all(X[g[i]][g[j]] == X[i][j] for i in range(n) for j in range(n)), name
    assert calls[0] > 0


# -- C fast paths ---------------------------------------------------------------


def rmatrix(rng, n, colors):
    return [[rng.randrange(colors) for _ in range(n)] for _ in range(n)]


def py_clean(x, y, A, B, gens, monkeypatch):
    monkeypatch.setattr(graph, "_ck", None)
    try:
        return graph.clean(x, y, A, B, gens)
    finally:
        monkeypatch.undo()


@needs_ck
@pytest.mark.parametrize("n", [1, 2, 3, 5, 8, 13, 40])
def test_clean_random_agrees(n, monkeypatch):
    rng = random.Random(n)
    for _ in range(100):
        x = rmatrix(rng, n, rng.choice([1, 2, 300, 2 ** 40]))
        y = [list(r) for r in x]
        if rng.random() < 0.3:
            y[rng.randrange(n)][rng.randrange(n)] = rng.randrange(5)
        pts = list(range(n))
        rng.shuffle(pts)
        A, B = pts[:rng.randint(0, n)], pts[:rng.randint(0, n)]
        gens = []
        for _ in range(rng.randint(0, 3)):
            g = list(range(n))
            if n > 1 and A and rng.random() < 0.6:
                a, b = rng.choice(A), rng.choice(A)
                g[a], g[b] = g[b], g[a]
            gens.append(tuple(g))
        want = py_clean(x, y, A, B, gens, monkeypatch)
        got = ck.clean(x, y, A, B, gens)
        assert got is want or got is None


@needs_ck
def test_clean_falls_back_on_other_shapes():
    x, y = [[0, 1], [1, 0]], [[0, 1], [1, 0]]
    assert ck.clean([tuple(r) for r in x], y, [0], [1], []) is None
    assert ck.clean(x, y, (0,), [1], []) is None
    assert ck.clean(x, y, [5], [1], []) is None          # out of range: the reference raises
    assert ck.clean(x, y, [-1], [1], []) is None         # negative index: reference semantics
    assert ck.clean(x, y, [0], [1], [[0, 1]]) is None    # a generator that is a list
    assert ck.clean(x, y, [], [1], []) is True
    assert ck.clean(x, y, [0], [], []) is True


@pytest.mark.parametrize("seed", range(120))
def test_action_on_pairs_agrees(seed):
    rng = random.Random(seed)
    n = rng.randint(1, 12)
    P = list(range(n))
    D = [(i, j) for i in P for j in P]
    if rng.random() < 0.5:
        rng.shuffle(D)
    if rng.random() < 0.3:
        D = D + D[:3]                    # duplicates: the last occurrence names the position
    gens = [rperm(rng, n) for _ in range(rng.randint(0, 4))]
    want = _py_pairs(D, gens)
    assert graph.action_on_pairs(n, D, gens) == want
    if ck is not None and D:
        pi, pj = map(list, zip(*D))
        assert ck.action_on_pairs(n, pi, pj, gens) == want


def _py_pairs(D, gens):
    idx = {p: k for k, p in enumerate(D)}
    return [tuple(idx[(g[i], g[j])] for i, j in D) for g in gens]


def test_action_on_pairs_leaving_d_raises():
    with pytest.raises(KeyError):
        graph.action_on_pairs(3, [(0, 0), (0, 1)], [(1, 2, 0)])


@needs_ck
def test_action_on_pairs_other_shapes():
    assert ck.action_on_pairs(2, [0, 1], [1], [(0, 1)]) is None      # different lengths
    assert ck.action_on_pairs(2, [0, 5], [1, 1], [(0, 1)]) is None   # out of range
    assert ck.action_on_pairs(2, [0, 1], [1, 1], [(0,)]) is None     # a short generator
    assert ck.action_on_pairs(2, [0, 1], [1, 1], [[0, 1]]) is None   # a list generator


def refine_ref(q, cx, cy, px, py, monkeypatch):
    monkeypatch.setattr(solver, "_ck", None)
    try:
        return solver.refine_labels(q, {}, {}, cx, cy, px, py)
    finally:
        monkeypatch.undo()


@pytest.mark.parametrize("seed", range(150))
def test_refine_labels_agrees(seed, monkeypatch):
    """Same ranks as the Python reference (the code table's order of first
    appearance decides the names)."""
    rng = random.Random(seed)
    q = rng.randint(1, 14)
    kinds = rng.choice([2, 3, 7])
    cx = [rng.randrange(kinds) for _ in range(q)]
    cy = list(cx) if rng.random() < 0.6 else [rng.randrange(kinds) for _ in range(q)]
    p = rng.choice([2, 3, 9, 2000])
    px = [[rng.randrange(p) for _ in range(q)] for _ in range(q)]
    py = [list(r) for r in px]
    if rng.random() < 0.5:
        py[rng.randrange(q)][rng.randrange(q)] = rng.randrange(p)
    want = refine_ref(q, cx, cy, px, py, monkeypatch)
    assert solver.refine_labels(q, {}, {}, cx, cy, px, py) == want
    if ck is not None:
        assert ck.refine_labels_pairs(q, cx, cy, px, py) == want


@needs_ck
def test_refine_labels_other_shapes_fall_back(monkeypatch):
    q, cx, cy = 2, [0, 1], [0, 1]
    px = [[1, 2], [3, 4]]
    assert ck.refine_labels_pairs(0, [], [], [], []) is None         # (no labels: Python)
    assert ck.refine_labels_pairs(q, [-1, 1], cy, px, px) is None    # a negative color
    assert ck.refine_labels_pairs(q, [0], cy, px, px) is None        # wrong length
    assert ck.refine_labels_pairs(q, cx, cy, [[1, 2]], px) is None   # not q x q
    assert ck.refine_labels_pairs(q, cx, cy, [[1, 2], [3, 2 ** 40]], px) is None   # huge entry
    # the hypergraph path stays in Python
    hx = {(0, 1): (("s",), (0, 0))}
    want = refine_ref(q, cx, cy, px, px, monkeypatch)
    assert solver.refine_labels(q, {}, {}, cx, cy, px, px) == want
    solver.refine_labels(q, hx, hx, cx, cy, px, px)   # (no error in the fallback path)


# -- chain cache ---------------------------------------------------------------


def chain_of(G):
    return (G.n, list(G.gens), list(G.base), [list(s) for s in G.S],
            [dict(t) for t in G.T], [dict(t) for t in G.Ti], G.order())


def fresh_chain(n, gens, base):
    saved = dict(group._CHAINS), dict(group._CHAIN_IDS), group._chains_size
    clear_chain_cache()
    try:
        return chain_of(PermGroup(n, gens, base=base))
    finally:
        group._CHAINS.clear()
        group._CHAIN_IDS.clear()
        group._CHAINS.update(saved[0])
        group._CHAIN_IDS.update(saved[1])
        group._chains_size = saved[2]


def check_cache_consistent():
    assert group._chains_size == sum(c.size for c in group._CHAINS.values())
    for k, c in group._CHAIN_IDS.items():
        assert any(c is v for v in group._CHAINS.values())
        assert any(k == ik for ik, _ in c.idkeys)
    for c in group._CHAINS.values():
        for ik, gens in c.idkeys:
            assert group._CHAIN_IDS[ik] is c
            # the id-key's generators are the live objects
            assert ik[1] == tuple(map(id, gens))


@pytest.mark.parametrize("limit", [1 << 8, 1 << 12, 1 << 24])
def test_chain_cache_id_front_stress(monkeypatch, limit):
    """Generators of equal value in fresh objects (id reuse), under eviction:
    every construction must equal a fresh, uncached one. The two bugs this
    guards against: an id-key whose generator objects were freed (a false hit
    on a recycled id), and a chain evicting itself while being hit."""
    rng = random.Random(limit)
    monkeypatch.setattr(group, "CHAIN_CACHE_LIMIT", limit)
    clear_chain_cache()
    n = 8
    pool = [[rperm(rng, n) for _ in range(rng.randint(1, 3))] for _ in range(15)]
    held = {}
    for step in range(1500):
        i = rng.randrange(len(pool))
        r = rng.random()
        gens = pool[i] if r < 0.5 else [tuple(g) for g in pool[i]]
        if r > 0.75:                     # value-equal new objects each time
            gens = [tuple(list(g)) for g in pool[i]]
        base = () if rng.random() < 0.5 else tuple(rng.sample(range(n), rng.randint(1, 3)))
        held[step % 7] = gens            # some of them stay alive for a while
        G = PermGroup(n, gens, base=base)
        if step % 25 == 0:
            assert chain_of(G) == fresh_chain(n, gens, base)
            check_cache_consistent()
        assert G.order() == PermGroup(n, [tuple(g) for g in gens]).order()
        junk = [tuple((v + step) % n for v in range(n)) for _ in range(3)]  # churn the allocator
        del junk
    check_cache_consistent()
    clear_chain_cache()
    assert not group._CHAIN_IDS and not group._CHAINS


def test_alias_of_the_oldest_chain_survives_its_own_trim(monkeypatch):
    """Registering an alias can overflow the cache and trim it. The chain being
    hit must be moved to the young end first, or it evicts itself."""
    clear_chain_cache()
    n = 8
    a = [(1, 0, 3, 2, 5, 4, 7, 6)]
    b = [(1, 2, 3, 4, 5, 6, 7, 0)]
    want = PermGroup(n, a).order()
    PermGroup(n, b)
    assert next(iter(group._CHAINS.values())).gens == tuple(a)    # a is the oldest
    monkeypatch.setattr(group, "CHAIN_CACHE_LIMIT", group._chains_size)     # exactly full
    H = PermGroup(n, [tuple(list(g)) for g in a])   # equal value, new objects: an alias
    assert H.order() == want
    check_cache_consistent()
    clear_chain_cache()


def test_shared_levels_are_not_mutated():
    """_NO_PAR and the shared {b: idn} transversals are safe only if nothing
    writes to them; run a workload and check they are intact."""
    run_tier("small")
    run_tier("small", ir=0)
    assert group._NO_PAR == {}
    for n, levels in group._TRIVIAL_LEVELS.items():
        idn = group._identity(n)
        for b, d in enumerate(levels):
            assert d == {b: idn}


@pytest.mark.parametrize("seed", range(40))
def test_chain_with_prescribed_base_matches_reference(seed):
    """A chain with a long prescribed base (shared trivial levels) equals the
    chain built by adding the generators to an empty group with that base."""
    rng = random.Random(seed)
    n = rng.randint(3, 12)
    gens = [rperm(rng, n) for _ in range(rng.randint(1, 3))]
    base = rng.sample(range(n), rng.randint(1, n))
    clear_chain_cache()
    G = PermGroup(n, gens, base=base)
    assert G.base[:len(base)] == base
    H = PermGroup(n)
    H.base = list(base)
    H.S = [[] for _ in base]
    H.T = [{b: H.idn} for b in base]
    H.Ti = [{b: H.idn} for b in base]
    H._par = [{} for _ in base]
    H._ok = [{} for _ in base]
    H._ord_T = H.T
    H._nt, H._nt_T = [], H.T
    H._done = False
    for g in gens:
        H.add(g)
    assert chain_of(G)[1:] == chain_of(H)[1:]


def test_cont_leaves_the_shared_orbits_alone():
    """_cont sorts its copy of the orbit list; the cached list keeps its order."""
    n = 6
    G = PermGroup(n, [(1, 0, 3, 2, 5, 4)])
    before = [list(o) for o in G.orbits_shared()]
    x = tuple(range(n))
    Solver(certificates=False)._cont(G, x, x, None)
    assert [list(o) for o in G.orbits_shared()] == before
    assert G.orbits() == sorted(G.orbits())


@pytest.mark.parametrize("seed", range(160))
def test_schreier_scan_skip_matches_the_reference(seed):
    """Levels skipped by _scanned must not change the chain: base, orbit sizes
    and order against the unoptimized reference (tests/_ref_group.py)."""
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import _ref_group as ref
    rng = random.Random(seed)
    kind = seed % 4
    if kind == 0:                        # imprimitive: long chains, many restarts
        a, b = rng.choice([(2, 5), (3, 4), (2, 6), (4, 3)])
        n = a * b
        gens = []
        for _ in range(rng.randint(2, 4)):
            top = list(range(b))
            rng.shuffle(top)
            p = [0] * n
            for i in range(b):
                inner = list(range(a))
                rng.shuffle(inner)
                for j in range(a):
                    p[i * a + j] = top[i] * a + inner[j]
            gens.append(tuple(p))
    elif kind == 1:                      # intransitive products
        n = rng.randint(6, 16)
        cut = rng.randint(2, n - 2)
        gens = []
        for _ in range(rng.randint(2, 4)):
            left, right = list(range(cut)), list(range(cut, n))
            rng.shuffle(left)
            rng.shuffle(right)
            gens.append(tuple(left + right))
    elif kind == 2:                      # generic
        n = rng.randint(5, 12)
        gens = [rperm(rng, n) for _ in range(rng.randint(2, 3))]
    else:                                # sparse, with an element order hint
        n = rng.randint(5, 12)
        gens = []
        for _ in range(rng.randint(3, 6)):
            k = rng.randint(2, min(4, n))
            pts = rng.sample(range(n), k)
            img = pts[:]
            rng.shuffle(img)
            p = list(range(n))
            for u, v in zip(pts, img):
                p[u] = v
            gens.append(tuple(p))
    clear_chain_cache()
    G, R = PermGroup(n, gens), ref.PermGroup(n, gens)
    assert G.order() == R.order()
    assert list(G.base) == list(R.base)
    assert [len(t) for t in G.T] == [len(t) for t in R.T]
    assert [list(t) for t in G.T] == [list(t) for t in R.T]     # (element order)
