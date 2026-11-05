"""Luks's bounded-degree reduction (gi/bounded.py) and the dispatcher
modification (M) (Solver(cameron_no_enum=True)), checked against brute force.
Run: python3 -m pytest -q tests"""
import itertools
import math
import os
import random
import sys

import pytest

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.setrecursionlimit(100000)

import networkx as nx

from gi import Solver, graph_iso
from gi.bounded import bounded_iso, NotSimple
from gi.group import PermGroup
from gi.perm import act, maps, parity


# -- helpers ----------------------------------------------------------------------
def adj(G):
    nodes = sorted(G.nodes(), key=repr)
    idx = {v: i for i, v in enumerate(nodes)}
    n = len(nodes)
    A = [[0] * n for _ in range(n)]
    for u, v in G.edges():
        if u != v:
            A[idx[u]][idx[v]] = A[idx[v]][idx[u]] = 1
    return A


def relabel(A, s, colors=None):
    n = len(A)
    B = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            B[s[i]][s[j]] = A[i][j]
    if colors is None:
        return B
    cB = [None] * n
    for i in range(n):
        cB[s[i]] = colors[i]
    return B, cB


def shuffled(A, rng, colors=None):
    s = list(range(len(A)))
    rng.shuffle(s)
    return relabel(A, s, colors)


def brute_isos(A, B, ca=None, cb=None, cap=200000):
    """All isomorphisms A -> B (color-preserving) by backtracking over a BFS
    order of A, checking adjacency to every assigned vertex. Independent of
    gi."""
    n = len(A)
    ca = ca or [0] * n
    cb = cb or [0] * n
    da = [sum(r) for r in A]
    db = [sum(r) for r in B]
    order, seen = [], set()
    for s in range(n):
        if s in seen:
            continue
        seen.add(s)
        q = [s]
        for v in q:
            order.append(v)
            for w in range(n):
                if A[v][w] and w not in seen:
                    seen.add(w)
                    q.append(w)
    assign = [-1] * n
    used = [False] * n
    out = []

    def rec(t):
        if len(out) > cap:
            raise RuntimeError("too many isomorphisms for brute force")
        if t == n:
            out.append(tuple(assign))
            return
        v = order[t]
        for w in range(n):
            if used[w] or da[v] != db[w] or ca[v] != cb[w]:
                continue
            if all(A[v][u] == B[w][assign[u]] for u in order[:t]):
                assign[v], used[w] = w, True
                rec(t + 1)
                assign[v], used[w] = -1, False

    rec(0)
    return out


def check(A, B, res, ca=None, cb=None, isos=None, auts=None):
    n = len(A)
    ca = ca or [0] * n
    cb = cb or [0] * n
    if isos is None:
        isos = brute_isos(A, B, ca, cb)
    if auts is None:
        auts = brute_isos(A, A, ca, ca)
    assert (res is None) == (not isos)
    if res is None:
        return
    sigma, gens = res
    assert sorted(sigma) == list(range(n))
    assert all(B[sigma[i]][sigma[j]] == A[i][j] for i in range(n) for j in range(n))
    assert all(cb[sigma[i]] == ca[i] for i in range(n))
    for g in gens:
        assert all(A[g[i]][g[j]] == A[i][j] for i in range(n) for j in range(n))
        assert all(ca[g[i]] == ca[i] for i in range(n))
    assert (PermGroup(n, gens).order() if gens else 1) == len(auts)


def random_regular(d, n, rng):
    return adj(nx.random_regular_graph(d, n, seed=rng.randrange(10 ** 9)))


def random_tree(n, rng):
    G = nx.Graph()
    G.add_nodes_from(range(n))
    G.add_edges_from((i, rng.randrange(i)) for i in range(1, n))
    return adj(G)


def solvers():
    return [Solver(cameron_no_enum=True), Solver(cameron_no_enum=True, certificates=False),
            Solver(enum_limit=1, certificates=False)]


# -- exactness on bounded-degree graphs -------------------------------------------------
@pytest.mark.parametrize("d,sizes", [(3, (4, 6, 8, 10, 12)), (4, (5, 6, 7, 8, 9, 10, 11))])
def test_random_regular(d, sizes):
    rng = random.Random(10 * d)
    for n in sizes:
        for _ in range(3):
            A = random_regular(d, n, rng)
            B = shuffled(A, rng)
            C = random_regular(d, n, rng)
            for S in solvers():
                # BFS layers (Luks's order): twin classes have <= d - 1 members
                check(A, B, bounded_iso(A, B, solver=S, layers="bfs"))
                check(A, C, bounded_iso(A, C, solver=S, layers="bfs"))
                assert 1 <= S.stats["luks_twin_max"] <= d - 1
            for kw in (dict(), dict(rooted_wl=False, ea=False), dict(ea=False)):
                S = Solver(cameron_no_enum=True, certificates=False)
                check(A, B, bounded_iso(A, B, solver=S, **kw))
                check(A, C, bounded_iso(A, C, solver=S, **kw))


def test_trees():
    rng = random.Random(3)
    for n in range(2, 11):
        for _ in range(4):
            A = random_tree(n, rng)
            B = shuffled(A, rng)
            T = random_tree(n, rng)
            S = Solver(cameron_no_enum=True)
            check(A, B, bounded_iso(A, B, solver=S))
            check(A, T, bounded_iso(A, T, solver=S))
    # stars and spiders: large Sym factors (d - 1 = 7 leaves at the root edge)
    for G in (nx.star_graph(7), nx.balanced_tree(2, 3), nx.balanced_tree(3, 2)):
        A = adj(G)
        B = shuffled(A, rng)
        check(A, B, bounded_iso(A, B))


def test_cycles_and_unions():
    rng = random.Random(4)
    C = nx.cycle_graph
    U = nx.disjoint_union_all
    pairs = [
        (C(7), C(7)),
        (U([C(3), C(3)]), C(6)),                     # 2-regular, not isomorphic
        (U([C(4), C(4)]), C(8)),
        (U([C(3), C(5)]), U([C(4), C(4)])),
        (U([C(3), C(4), C(3)]), U([C(4), C(3), C(3)])),
        (nx.path_graph(6), nx.path_graph(6)),
        (U([nx.path_graph(3), nx.empty_graph(2)]), U([nx.empty_graph(1), nx.path_graph(3), nx.empty_graph(1)])),
        (U([nx.complete_graph(4), nx.complete_graph(4)]), nx.hypercube_graph(3)),
        (U([nx.complete_graph(4), nx.complete_graph(4)]), U([nx.complete_graph(4), nx.complete_graph(4)])),
        (nx.empty_graph(4), nx.empty_graph(4)),
        (U([nx.petersen_graph(), C(5)]), U([C(5), nx.petersen_graph()])),
        (U([nx.complete_bipartite_graph(3, 3), nx.complete_graph(4), nx.complete_graph(4)]),
         U([nx.complete_graph(4), nx.complete_bipartite_graph(3, 3), nx.complete_graph(4)])),
        (nx.complete_bipartite_graph(3, 3), nx.circular_ladder_graph(3)),    # K33 vs prism
    ]
    for G, H in pairs:
        A, B = adj(G), shuffled(adj(H), rng)
        check(A, B, bounded_iso(A, B))
        check(A, B, bounded_iso(A, B, refine=False))


def test_colored():
    rng = random.Random(5)
    for n in (6, 8, 10):
        for _ in range(4):
            A = random_regular(3, n, rng)
            ca = [rng.randrange(2) for _ in range(n)]
            B, cb = shuffled(A, rng, ca)
            check(A, B, bounded_iso(A, B, vcolors_x=ca, vcolors_y=cb), ca, cb)
            cc = list(cb)
            rng.shuffle(cc)
            check(A, B, bounded_iso(A, B, vcolors_x=ca, vcolors_y=cc), ca, cc)
            check(A, B, bounded_iso(A, B, vcolors_x=ca, vcolors_y=cc, refine=False), ca, cc)


def test_against_graph_iso():
    """Medium bounded-degree graphs (CFI pairs, hypercubes, random 3-regular):
    decision, isomorphism, generators and |Aut| against the default pipeline,
    whose exactness is tested elsewhere."""
    rng = random.Random(6)
    sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "bench"))
    from families import cfi
    cases = []
    for base in (nx.complete_graph(4), nx.complete_bipartite_graph(3, 3), nx.random_regular_graph(3, 8, seed=1)):
        A = adj(cfi(base))
        cases.append((A, shuffled(A, rng)))
        cases.append((A, shuffled(adj(cfi(base, True)), rng)))
    for d in (3, 4):
        A = adj(nx.hypercube_graph(d))
        cases.append((A, shuffled(A, rng)))
    A = random_regular(3, 30, rng)
    cases.append((A, shuffled(A, rng)))
    cases.append((A, random_regular(3, 30, rng)))
    for A, B in cases:
        n = len(A)
        ref = graph_iso(A, B, solver=Solver(certificates=False))
        res = bounded_iso(A, B)
        assert (res is None) == (ref is None)
        if res is None:
            continue
        sigma, gens = res
        assert all(B[sigma[i]][sigma[j]] == A[i][j] for i in range(n) for j in range(n))
        assert all(A[g[i]][g[j]] == A[i][j] for g in gens for i in range(n) for j in range(n))
        assert PermGroup(n, gens).order() == PermGroup(n, ref[1]).order()


def test_root_degree():
    """root="degree" (another root edge per component) is exact too."""
    rng = random.Random(7)
    for _ in range(12):
        n = rng.randint(4, 11)
        A = random_tree(n, rng) if rng.random() < 0.5 else random_regular(3, 2 * (n // 2), rng)
        n = len(A)
        B = shuffled(A, rng)
        C = random_tree(n, rng) if rng.random() < 0.5 else random_regular(3, n - n % 2, rng)
        for flag in (False, True):
            S = Solver(cameron_no_enum=flag)
            check(A, B, bounded_iso(A, B, solver=S, root="degree"))
            if len(C) == n:
                check(A, C, bounded_iso(A, C, solver=S, root="degree"))


def test_rejects_non_simple():
    with pytest.raises(NotSimple):
        bounded_iso([[1, 0], [0, 0]], [[1, 0], [0, 0]])
    with pytest.raises(NotSimple):
        bounded_iso([[0, 1], [0, 0]], [[0, 1], [0, 0]])


# -- the dispatcher modification (M) --------------------------------------------------
def kset_group(m, k, alt, rng):
    """Sym(m) / Alt(m) on the k-subsets of range(m): (generators, all elements)."""
    S = list(itertools.combinations(range(m), k))
    idx = {s: i for i, s in enumerate(S)}

    def lift(s):
        return tuple(idx[tuple(sorted(s[a] for a in T))] for T in S)

    top = [tuple(range(1, m)) + (0,), (1, 0) + tuple(range(2, m))]
    if alt:
        top = [(1, 2, 0) + tuple(range(3, m)),
               tuple(range(1, m)) + (0,) if m % 2 else (0,) + tuple(range(2, m)) + (1,)]
    els = [lift(s) for s in itertools.permutations(range(m)) if not alt or not parity(s)]
    return len(S), [lift(s) for s in top], els


@pytest.mark.parametrize("m,k,alt", [(5, 2, False), (6, 2, True), (5, 2, True)])
def test_cameron_no_enum(m, k, alt):
    """J(5,2) (order 120) and Alt(6) on 2-sets (order 360) pass the small
    test (enum_limit = 500): the default dispatcher enumerates them, (M)
    takes the Johnson path. Both are exact."""
    rng = random.Random(m + 10 * alt)
    d, gens, els = kset_group(m, k, alt, rng)
    G = PermGroup(d, gens)
    assert G.order() == math.factorial(m) // (2 if alt else 1)
    for _ in range(6):
        x = tuple(rng.randrange(3) for _ in range(d))
        y = act(x, rng.choice(els)) if rng.random() < 0.6 else tuple(rng.sample(x, d))
        isos = [g for g in els if maps(g, x, y)]
        auts = [g for g in els if maps(g, x, x)]
        for flag in (False, True):
            S = Solver(cameron_no_enum=flag)
            a = S.solve(G, range(d), x, y)
            assert (a is None) == (not isos)
            if a is not None:
                assert maps(a.rep, x, y)
                assert all(maps(g, x, x) for g in a.gens)
                assert PermGroup(d, a.gens).order() == len(auts)
            if len(set(x)) > 1 and sorted(x) == sorted(y):
                if flag:
                    assert S.stats["cameron_skip_enum"] > 0
                    assert S.stats["cameron_small_johnson"] > 0
                    assert S.stats["alt_section_max"] >= m
                else:
                    assert S.stats["enumerate"] > 0


def test_cameron_in_pipeline():
    """Johnson gadgets (bench/bounded.py, jgad) with the root on a hub edge:
    the up-sets of the grandchildren are the 2-sets of a twin class of 5, so
    the solver meets Sym(5) on 10 points (order 120 <= enum_limit). Without
    (M) it is enumerated, with (M) it takes the Johnson path; both exact."""
    from bench.bounded import jgad
    rng = random.Random(11)
    for twist in (False, True):
        A = jgad(4, random.Random(5))
        B = shuffled(jgad(4, random.Random(5), twist=twist), rng)
        n = len(A)
        ref = graph_iso(A, B, solver=Solver(certificates=False))
        for flag in (False, True):
            S = Solver(cameron_no_enum=flag, certificates=False)
            # Luks's original layering (BFS, no rooted refinement, no EA path),
            # where the Sym(5) twin classes reach the dispatcher
            res = bounded_iso(A, B, solver=S, root="degree", rooted_wl=False, ea=False)
            assert (res is None) == (ref is None)
            if res is not None:
                sigma, gens = res
                assert all(B[sigma[i]][sigma[j]] == A[i][j] for i in range(n) for j in range(n))
                assert all(A[g[i]][g[j]] == A[i][j] for g in gens for i in range(n) for j in range(n))
                assert PermGroup(n, gens).order() == PermGroup(n, ref[1]).order()
            if flag:
                assert S.stats["cameron_small_johnson"] > 0
                assert S.stats["enum_quotient_max_order"] < 60
            else:
                assert S.stats["enum_quotient_max_order"] == 120


def test_cameron_flag_keeps_small_solvable():
    """Groups whose order is not divisible by |Alt(5)| are still enumerated
    under (M) (they have no Alt(m) section with m >= 5)."""
    rng = random.Random(9)
    d, gens, els = kset_group(4, 2, False, rng)        # Sym(4) on 6 points
    G = PermGroup(d, gens)
    x = (0, 1, 0, 1, 2, 2)
    S = Solver(cameron_no_enum=True)
    a = S.solve(G, range(d), x, x)
    assert S.stats["enumerate"] > 0 and S.stats["cameron_skip_enum"] == 0
    assert PermGroup(d, a.gens).order() == sum(maps(g, x, x) for g in els)
