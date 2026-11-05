"""Tests of the canonical refinement front end (gi/refine.py and graph.graph_iso):
invariance of the joint refinement, rejection of non-isomorphic pairs, and
exactness of graph_iso with each refinement method on undirected, directed,
vertex-colored, edge-colored and looped graphs. Run: python3 -m pytest -q tests"""
import itertools
import os
import random
import sys

import pytest

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.setrecursionlimit(100000)

from gi import graph_iso, Solver
from gi.group import PermGroup
from gi.refine import refine_graphs, initial_pair_colors, wl1, wl2, wl2_reference

METHODS = ["none", "1wl", "2wl"]
# front-end modes: refinement method plus graph_iso keyword arguments
MODES = {
    "none": dict(refine="none"),
    "1wl-direct": dict(refine="1wl", staged=False),
    "2wl-direct": dict(refine="2wl", staged=False),
    "1wl-staged": dict(refine="1wl"),
    "2wl-staged": dict(refine="2wl", ir=0),
    "2wl-default": dict(),
    "2wl-ir": dict(refine="2wl", ir=3, ir_min=2),
}


def relabel(A, s):
    n = len(A)
    B = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            B[s[i]][s[j]] = A[i][j]
    return B


def recolor(c, s):
    out = [None] * len(c)
    for i, v in enumerate(c):
        out[s[i]] = v
    return out


def rand_matrix(n, rng, p=0.4, values=(1,), directed=False, loops=False):
    A = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i == j and not loops:
                continue
            if directed or i <= j:
                if rng.random() < p:
                    A[i][j] = rng.choice(values)
                if not directed:
                    A[j][i] = A[i][j]
    return A


def cycle(n):
    A = [[0] * n for _ in range(n)]
    for i in range(n):
        A[i][(i + 1) % n] = A[(i + 1) % n][i] = 1
    return A


def disjoint(A, B):
    n, m = len(A), len(B)
    C = [[0] * (n + m) for _ in range(n + m)]
    for i in range(n):
        for j in range(n):
            C[i][j] = A[i][j]
    for i in range(m):
        for j in range(m):
            C[n + i][n + j] = B[i][j]
    return C


def brute(A, B, ca=None, cb=None):
    n = len(A)
    ca = ca or [0] * n
    cb = cb or [0] * n
    return [s for s in itertools.permutations(range(n))
            if all(cb[s[i]] == ca[i] for i in range(n))
            and all(B[s[i]][s[j]] == A[i][j] for i in range(n) for j in range(n))]


def check_answer(A, B, res, ca=None, cb=None):
    n = len(A)
    isos = brute(A, B, ca, cb)
    assert (res is None) == (not isos)
    if res is None:
        return
    sigma, gens = res
    ca = ca or [0] * n
    cb = cb or [0] * n
    assert sorted(sigma) == list(range(n))
    assert all(cb[sigma[i]] == ca[i] for i in range(n))
    assert all(B[sigma[i]][sigma[j]] == A[i][j] for i in range(n) for j in range(n))
    for g in gens:
        assert all(ca[g[i]] == ca[i] for i in range(n))
        assert all(A[g[i]][g[j]] == A[i][j] for i in range(n) for j in range(n))
    assert PermGroup(n, gens).order() == len(brute(A, A, ca, ca))


# -- the refinement itself ------------------------------------------------------
@pytest.mark.parametrize("method", ["1wl", "2wl"])
def test_refinement_is_invariant(method):
    """For Y = X^s, the joint refinement satisfies PY = PX^s exactly, and the
    original adjacency is a function of the refined pair color."""
    rng = random.Random(3)
    for _ in range(40):
        n = rng.randint(1, 9)
        directed = rng.random() < 0.5
        A = rand_matrix(n, rng, rng.choice([0.2, 0.5]), values=(1, 2), directed=directed,
                        loops=rng.random() < 0.3)
        s = list(range(n))
        rng.shuffle(s)
        B = relabel(A, s)
        PX, PY = refine_graphs(A, B, method=method)
        for i in range(n):
            for j in range(n):
                assert PY[s[i]][s[j]] == PX[i][j]
        f = {}
        for P, M in ((PX, A), (PY, B)):
            for i in range(n):
                for j in range(n):
                    key = (P[i][j], i == j)
                    assert f.setdefault(key, M[i][j]) == M[i][j]


def partition(P):
    n = len(P)
    cls = {}
    for i in range(n):
        for j in range(n):
            cls.setdefault(P[i][j], []).append((i, j))
    return sorted(cls.values())


def test_packed_wl2_matches_definition():
    """wl2 (packed bilinear signatures) computes the same partitions and the
    same rejections as 2-WL with literal multiset signatures, on undirected,
    directed, edge-colored and looped graphs, isomorphic or not."""
    rng = random.Random(21)
    for _ in range(80):
        n = rng.randint(1, 13)
        directed = rng.random() < 0.4
        values = (1,) if rng.random() < 0.5 else (1, 2, 3)
        A = rand_matrix(n, rng, rng.choice([0.2, 0.4, 0.6]), values, directed, rng.random() < 0.2)
        if rng.random() < 0.5:
            s = list(range(n))
            rng.shuffle(s)
            B = relabel(A, s)
        else:
            B = rand_matrix(n, rng, 0.4, values, directed, rng.random() < 0.2)
        PX, PY = initial_pair_colors(A, B)
        fast, ref = wl2(PX, PY), wl2_reference(PX, PY)
        assert (fast is None) == (ref is None)
        if fast is not None:
            assert partition(fast[0]) == partition(ref[0])
            assert partition(fast[1]) == partition(ref[1])
    # strongly regular and CFI graphs, where many rounds are needed
    for X, Z in ((rook4(), shrikhande()), (cfi(K4, 4), cfi(K4, 4, twist=True)),
                 (cfi(K3, 3), cfi(K3, 3, twist=True))):
        PX, PY = initial_pair_colors(X, Z)
        fast, ref = wl2(PX, PY), wl2_reference(PX, PY)
        assert (fast is None) == (ref is None)
        if fast is not None:
            assert partition(fast[0]) == partition(ref[0])


def test_wl_separates_and_rejects():
    # C6 vs 2C3: 1-WL equivalent, 2-WL distinguishes
    X, Y = cycle(6), disjoint(cycle(3), cycle(3))
    PX, PY = initial_pair_colors(X, Y)
    assert wl1(PX, PY) is not None
    assert wl2(PX, PY) is None
    assert refine_graphs(X, Y, method="2wl") is None
    for kw in MODES.values():
        assert graph_iso(X, Y, solver=Solver(certificates=False), **kw) is None
    # different degree sequences: rejected by 1-WL already
    assert refine_graphs(cycle(5), [[int(i != j) for j in range(5)] for i in range(5)],
                         method="1wl") is None


def test_directed_cycle_vs_reverse_tournament():
    # a directed 3-cycle is isomorphic to its reverse; the transitive tournament is not
    C = [[0, 1, 0], [0, 0, 1], [1, 0, 0]]
    R = [[0, 0, 1], [1, 0, 0], [0, 1, 0]]
    T = [[0, 1, 1], [0, 0, 1], [0, 0, 0]]
    for kw in MODES.values():
        res = graph_iso(C, R, solver=Solver(certificates=False), **kw)
        check_answer(C, R, res)
        assert graph_iso(C, T, solver=Solver(certificates=False), **kw) is None


# -- graph_iso with each front end, against brute force ----------------------------
CFGS = [dict(certificates=False, enum_limit=1), dict(certificates=True, enum_limit=1, kappa=3)]


@pytest.mark.parametrize("mode", list(MODES))
@pytest.mark.parametrize("cfg", CFGS, ids=["nocert", "cert3"])
def test_random_against_brute(mode, cfg):
    rng = random.Random(11)
    for _ in range(30):
        n = rng.randint(1, 6)
        directed = rng.random() < 0.4
        values = (1,) if rng.random() < 0.6 else (1, 2)
        A = rand_matrix(n, rng, rng.choice([0.3, 0.5, 0.7]), values, directed,
                        loops=rng.random() < 0.2)
        ca = [rng.randint(0, 1) for _ in range(n)] if rng.random() < 0.3 else None
        if rng.random() < 0.6:
            s = list(range(n))
            rng.shuffle(s)
            B = relabel(A, s)
            cb = recolor(ca, s) if ca else None
        else:
            B = rand_matrix(n, rng, 0.5, values, directed, loops=rng.random() < 0.2)
            cb = [rng.randint(0, 1) for _ in range(n)] if ca else None
        res = graph_iso(A, B, solver=Solver(**cfg), vcolors_x=ca, vcolors_y=cb, **MODES[mode])
        check_answer(A, B, res, ca, cb)


@pytest.mark.parametrize("mode", list(MODES))
def test_symmetric_and_regular(mode):
    """Vertex-transitive and regular graphs, where refinement leaves large classes."""
    rng = random.Random(5)
    graphs = [cycle(6), disjoint(cycle(3), cycle(3)), cycle(7),
              [[int(i != j) for j in range(5)] for i in range(5)],
              [[int((i ^ j) in (1, 2, 4)) for j in range(8)] for i in range(8)]]   # Q3
    for A in graphs:
        n = len(A)
        s = list(range(n))
        rng.shuffle(s)
        B = relabel(A, s)
        res = graph_iso(A, B, solver=Solver(certificates=False, enum_limit=1), **MODES[mode])
        sigma, gens = res
        assert all(B[sigma[i]][sigma[j]] == A[i][j] for i in range(n) for j in range(n))
        assert all(A[g[i]][g[j]] == A[i][j] for g in gens for i in range(n) for j in range(n))
        if n <= 7:
            assert PermGroup(n, gens).order() == len(brute(A, A))
    q3 = graphs[-1]
    res = graph_iso(q3, q3, solver=Solver(certificates=False), **MODES[mode])
    assert PermGroup(8, res[1]).order() == 48


@pytest.mark.parametrize("mode", list(MODES))
def test_vertex_colors_break_symmetry(mode):
    A = cycle(6)
    ca = [1, 0, 0, 0, 0, 0]
    cb = [0, 0, 0, 1, 0, 0]
    res = graph_iso(A, A, solver=Solver(certificates=False), vcolors_x=ca, vcolors_y=cb,
                    **MODES[mode])
    check_answer(A, A, res, ca, cb)
    assert graph_iso(A, A, vcolors_x=ca, vcolors_y=[0, 0, 0, 0, 0, 0], **MODES[mode]) is None


def petersen():
    A = [[0] * 10 for _ in range(10)]
    for i in range(5):
        for a, b in ((i, (i + 1) % 5), (i, i + 5), (i + 5, (i + 2) % 5 + 5)):
            A[a][b] = A[b][a] = 1
    return A


@pytest.mark.parametrize("mode", list(MODES))
def test_larger_known_groups(mode):
    """Known automorphism group orders where brute force is too slow: the
    Petersen graph (120), a disjoint union C4 + C4 + K1 (2 * 8 * 8 = 128) and
    a directed 9-cycle with chords i -> i+3 (9)."""
    rng = random.Random(9)
    c4 = cycle(4)
    dc = [[int((j - i) % 9 in (1, 3)) for j in range(9)] for i in range(9)]
    for A, order in ((petersen(), 120), (disjoint(disjoint(c4, c4), [[0]]), 128), (dc, 9)):
        n = len(A)
        s = list(range(n))
        rng.shuffle(s)
        B = relabel(A, s)
        sigma, gens = graph_iso(A, B, solver=Solver(certificates=False), **MODES[mode])
        assert all(B[sigma[i]][sigma[j]] == A[i][j] for i in range(n) for j in range(n))
        assert all(A[g[i]][g[j]] == A[i][j] for g in gens for i in range(n) for j in range(n))
        assert PermGroup(n, gens).order() == order


def rook4():
    V = [(a, b) for a in range(4) for b in range(4)]
    return [[int(u != v and (u[0] == v[0] or u[1] == v[1])) for v in V] for u in V]


def shrikhande():
    V = [(a, b) for a in range(4) for b in range(4)]
    S = {(0, 1), (0, 3), (1, 0), (3, 0), (1, 1), (3, 3)}
    return [[int(((v[0] - u[0]) % 4, (v[1] - u[1]) % 4) in S) for v in V] for u in V]


def cfi(base_edges, nv, twist=False):
    """Cai-Furer-Immerman graph over a base graph (edges on range(nv)); with
    twist=True one edge is twisted (the two graphs are not isomorphic)."""
    names, E = {}, set()

    def node(t):
        return names.setdefault(t, len(names))

    edges = sorted(tuple(sorted(e)) for e in base_edges)
    for v in range(nv):
        inc = [e for e in edges if v in e]
        for e in inc:
            node(("a", v, e, 0)), node(("a", v, e, 1))
        for bits in itertools.product((0, 1), repeat=len(inc)):
            if sum(bits) % 2 == 0:
                m = node(("m", v, bits))
                for e, bit in zip(inc, bits):
                    E.add((m, node(("a", v, e, bit))))
    for k, (u, v) in enumerate(edges):
        t = 1 if (twist and k == 0) else 0
        for b in (0, 1):
            E.add((node(("a", u, (u, v), b)), node(("a", v, (u, v), b ^ t))))
    n = len(names)
    A = [[0] * n for _ in range(n)]
    for a, b in E:
        A[a][b] = A[b][a] = 1
    return A


K3 = [(0, 1), (1, 2), (0, 2)]
K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]


def check_pair(X, Z, kws, rng):
    """Z is not isomorphic to X; a relabeled X is. Every front-end mode must
    agree, and all must give the same automorphism group order."""
    n = len(X)
    s = list(range(n))
    rng.shuffle(s)
    Y = relabel(X, s)
    orders = set()
    for kw in kws:
        assert graph_iso(X, relabel(Z, s), solver=Solver(certificates=False), **kw) is None
        sigma, gens = graph_iso(X, Y, solver=Solver(certificates=False), **kw)
        assert all(Y[sigma[i]][sigma[j]] == X[i][j] for i in range(n) for j in range(n))
        assert all(X[g[i]][g[j]] == X[i][j] for g in gens for i in range(n) for j in range(n))
        orders.add(PermGroup(n, gens).order())
    assert len(orders) == 1
    return orders.pop()


def test_wl_equivalent_non_isomorphic():
    """Pairs that 2-WL cannot separate: rook4 vs Shrikhande (strongly regular
    with the same parameters) and CFI(K4) vs its twist. The answers must still
    be exact."""
    rng = random.Random(4)
    X, Z = rook4(), shrikhande()
    assert refine_graphs(X, Z, method="2wl") is not None
    assert check_pair(X, Z, [dict(), dict(ir=1), dict(ir=3, ir_min=2)], rng) == 1152
    assert PermGroup(16, graph_iso(Z, Z)[1]).order() == 192
    X, Z = cfi(K4, 4), cfi(K4, 4, twist=True)
    assert refine_graphs(X, Z, method="2wl") is not None
    assert check_pair(X, Z, [dict()], rng) == 192


def test_1wl_equivalent_cfi_k3():
    """CFI(K3) and its twist are 2-regular (1-WL equivalent); 2-WL separates
    them. The 1-WL front end must reach the same answer by individualization and
    the recursion. (Without individualization the bare recursion is too slow on
    Sym(18) acting on pairs.)"""
    rng = random.Random(6)
    X, Z = cfi(K3, 3), cfi(K3, 3, twist=True)
    PX, PY = initial_pair_colors(X, Z)
    assert wl1(PX, PY) is not None
    assert refine_graphs(X, Z, method="2wl") is None
    check_pair(X, Z, [dict(refine="1wl"), dict(refine="1wl", ir=2, ir_min=4), dict()], rng)


def test_individualization_pruning():
    """Graph-level individualization with orbit pruning (one-mode: the y-side
    vertex is fixed, the x-side vertex runs over orbits of the known Aut(x)).
    Symmetric graphs against slightly perturbed or relabeled copies, checked
    against brute force; the pruning must actually skip branches."""
    rng = random.Random(17)
    c4 = cycle(4)
    q3 = [[int((i ^ j) in (1, 2, 4)) for j in range(8)] for i in range(8)]
    bases = [disjoint(c4, c4), q3, cycle(8), disjoint(cycle(3), cycle(5)),
             disjoint(disjoint(cycle(3), cycle(3)), [[0, 1], [1, 0]])]
    pruned = 0
    for A in bases:
        n = len(A)
        aut = len(brute(A, A))
        for trial in range(4):
            s = list(range(n))
            rng.shuffle(s)
            B = relabel(A, s)
            if trial % 2:               # move one edge: usually not isomorphic
                i, j = rng.sample(range(n), 2)
                k, l = rng.sample(range(n), 2)
                if B[i][j] != B[k][l]:
                    B[i][j], B[j][i], B[k][l], B[l][k] = B[k][l], B[l][k], B[i][j], B[j][i]
            iso = bool(brute(A, B)) if trial % 2 else True
            for kw in (dict(ir=3, ir_min=2), dict(ir=1, ir_min=2), dict(ir=3, ir_min=3)):
                S = Solver(certificates=False)
                res = graph_iso(A, B, solver=S, **kw)
                pruned += S.stats["ir_pruned"]
                assert (res is not None) == iso
                if res is not None:
                    sigma, gens = res
                    assert all(B[sigma[i]][sigma[j]] == A[i][j] for i in range(n) for j in range(n))
                    assert all(A[g[i]][g[j]] == A[i][j] for g in gens
                               for i in range(n) for j in range(n))
                    assert PermGroup(n, gens).order() == aut
    assert pruned > 0
    # CFI(K4) and its twist (2-WL equivalent): all individualization depths agree
    X, Z = cfi(K4, 4), cfi(K4, 4, twist=True)
    S = Solver(certificates=False)
    assert graph_iso(X, relabel(Z, list(range(len(Z)))[::-1]), solver=S, ir=3, ir_min=2) is None
    assert S.stats["ir_pruned"] > 0
    assert check_pair(X, Z, [dict(ir=1, ir_min=2), dict(ir=2, ir_min=4), dict(ir=0)], rng) == 192


def test_policy_budgeted_levels(monkeypatch):
    """The individualization policy: levels below ir always individualize;
    levels in [ir, ir_max) give the recursion a time budget first. ir_budget=0
    individualizes up to ir_max without trials, ir_budget=None turns the
    budgeted levels off, a huge budget lets every trial finish, and trials
    that always time out (simulated) fall back to individualization. Every
    setting is exact, and an aborted call leaves the solver unpatched."""
    import gi.graph
    from gi.graph import Policy, OverBudget
    rng = random.Random(23)
    q3 = [[int((i ^ j) in (1, 2, 4)) for j in range(8)] for i in range(8)]
    settings = [dict(ir=1, ir_min=2, ir_budget=0), dict(ir=1, ir_min=2, ir_budget=None),
                dict(ir=1, ir_min=2, ir_max=4, ir_budget=0), dict(ir=1, ir_min=2, ir_budget=1e9),
                "timeout"]
    real_trial = Policy.trial

    def always_late(self, solver, f):
        return real_trial(self, solver, lambda: (_ for _ in ()).throw(OverBudget()))

    aborted = done = 0
    for A, order in ((petersen(), 120), (q3, 48), (rook4(), 1152)):
        n = len(A)
        s = list(range(n))
        rng.shuffle(s)
        B = relabel(A, s)
        for kw in settings:
            if kw == "timeout":
                monkeypatch.setattr(Policy, "trial", always_late)
                kw = dict(ir=1, ir_min=2, ir_budget=1e9)
            else:
                monkeypatch.setattr(Policy, "trial", real_trial)
            S = Solver(certificates=False)
            sigma, gens = graph_iso(A, B, solver=S, **kw)
            assert all(B[sigma[i]][sigma[j]] == A[i][j] for i in range(n) for j in range(n))
            assert all(A[g[i]][g[j]] == A[i][j] for g in gens for i in range(n) for j in range(n))
            assert PermGroup(n, gens).order() == order
            assert "cont" not in S.__dict__ and "solve" not in S.__dict__
            aborted += S.stats["trial_abort"]
            done += S.stats["trial_done"]
    assert aborted > 0 and done > 0
    monkeypatch.setattr(Policy, "trial", real_trial)
    # non-isomorphic pairs under every setting
    X, Z = rook4(), shrikhande()
    for kw in settings[:-1]:
        assert graph_iso(X, relabel(Z, list(range(16))[::-1]), solver=Solver(certificates=False),
                         **kw) is None
    # a budget of 0 stops the recursion at its first call
    pol = Policy(16, ir=1, ir_budget=0)
    pol.refine(lambda: None)
    S = Solver(certificates=False)
    G = PermGroup(4, [(1, 0, 2, 3), (1, 2, 3, 0)])
    with pytest.raises(OverBudget):
        pol.trial(S, lambda: S.solve(G, range(4), (0, 0, 1, 1), (1, 1, 0, 0)))
    assert "cont" not in S.__dict__ and "solve" not in S.__dict__
    assert Policy(100, ir=3).ir_max == 7 and Policy(100, ir=0).ir_max == 0
    assert Policy(100, ir=3, ir_budget=None).ir_max == 3


def test_policy_deterministic(monkeypatch):
    """The budget counts work, not time: the same input gives the same sigma
    and generators even when the clock jumps (a loaded machine), and a
    trial's budget is ir_budget * WORK_PER_REFINEMENT * n^2 units, one per
    position of each recursive call."""
    import time
    from gi.graph import Policy, OverBudget, WORK_PER_REFINEMENT
    rng = random.Random(31)
    pairs = list(itertools.combinations(range(8), 2))       # T(8), 28 vertices
    A = [[int(len(set(p) & set(q)) == 1) for q in pairs] for p in pairs]
    s = list(range(28))
    rng.shuffle(s)
    B = relabel(A, s)
    kw = {}
    runs = []
    for jumpy in (False, True, False):
        if jumpy:
            real = time.perf_counter
            ticks = itertools.count()
            monkeypatch.setattr(time, "perf_counter", lambda: real() + 0.05 * next(ticks))
        S = Solver(certificates=False)
        runs.append((graph_iso(A, B, solver=S, **kw), S.stats["trial_done"], S.stats["trial_abort"]))
        monkeypatch.undo()
    assert runs[0] == runs[1] == runs[2]
    assert runs[0][1] > 0
    # the budget in units
    pol = Policy(16, ir=1, ir_budget=2.0)
    assert pol.work_budget() == 2.0 * WORK_PER_REFINEMENT * 256
    S = Solver(certificates=False)
    G = PermGroup(4, [(1, 0, 2, 3), (1, 2, 3, 0)])
    calls = []
    pol.budget = 5 / (WORK_PER_REFINEMENT * 256)      # 5 units: one call of degree 4 only
    with pytest.raises(OverBudget):
        pol.trial(S, lambda: [calls.append(1), S.cont(G, (0, 1, 2, 3), (0, 1, 2, 3)),
                              calls.append(2), S.cont(G, (0, 1, 2, 3), (0, 1, 2, 3))])
    assert calls == [1, 2] and "cont" not in S.__dict__


def test_chunked_stages(monkeypatch):
    """Stages solved in chunks of orbits (forced by a tiny CHUNK) give the same
    exact answers: random graphs against brute force, CFI(K4) and its twist,
    rook4 vs Shrikhande."""
    import gi.graph
    monkeypatch.setattr(gi.graph, "CHUNK", 6)
    rng = random.Random(29)
    for _ in range(25):
        n = rng.randint(2, 7)
        A = rand_matrix(n, rng, rng.choice([0.3, 0.5]), (1, 2), rng.random() < 0.3)
        s = list(range(n))
        rng.shuffle(s)
        B = relabel(A, s) if rng.random() < 0.6 else rand_matrix(n, rng, 0.4, (1, 2))
        for kw in (dict(ir=0), dict()):
            S = Solver(certificates=False)
            check_answer(A, B, graph_iso(A, B, solver=S, **kw))
    S = Solver(certificates=False)
    graph_iso(cfi(K4, 4), cfi(K4, 4), solver=S, ir=0)
    assert S.stats["stage_chunks"] > 0
    assert check_pair(cfi(K4, 4), cfi(K4, 4, twist=True), [dict(ir=0), dict()], rng) == 192
    assert check_pair(rook4(), shrikhande(), [dict(ir=0), dict()], rng) == 1152
