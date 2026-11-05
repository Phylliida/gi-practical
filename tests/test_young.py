"""Exactness tests for the Young-label step (aggregation over the whole
instance) and the label refinements of the giant step: string isomorphism
under groups with giant quotients, checked against brute-force enumeration of
the group. Run: python3 -m pytest -q tests"""
import itertools
import math
import os
import random
import sys

import pytest

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.setrecursionlimit(100000)

from gi import graph_iso, Solver
from gi.group import PermGroup
from gi.perm import act, maps, sym_gens, mul, inv
from gi.solver import wl2_joint

CONFIGS = [dict(certificates=False, enum_limit=1, young_min=3, young_wl=2),
           dict(certificates=False, enum_limit=1, young_min=3, young_wl=1),
           dict(certificates=True, enum_limit=1, kappa=3, young_min=3, young_wl=2),
           dict(certificates=False, enum_limit=1, young_min=5, young_pick="large"),
           dict(certificates=False, enum_limit=1, young=False, giant_wl=1),
           dict(certificates=False)]
IDS = ["wl2-min3", "wl1-min3", "cert3-wl2-min3", "min5-large", "noyoung-gwl1", "default"]


def check_string(G, x, y, ans):
    """Compare ans with brute force over all elements of G."""
    isos = [g for g in G.elements() if maps(g, x, y)]
    assert (ans is not None) == bool(isos)
    if ans is None:
        return
    assert G.contains(ans.rep) and maps(ans.rep, x, y)
    for h in ans.gens:
        assert G.contains(h) and maps(h, x, x)
    auts = sum(1 for g in G.elements() if maps(g, x, x))
    assert PermGroup(G.n, ans.gens).order() == auts


def on_pairs_group(classes, V):
    """prod Sym(C) over the classes, acting on the ordered pairs of V
    (positions (i, j) -> i * |V| + j), with the vertices outside the classes
    fixed."""
    v = len(V)

    def lift(g):
        return tuple(g[i] * v + g[j] for i in range(v) for j in range(v))

    gens = [lift(g) for C in classes for g in sym_gens(v, C)]
    return PermGroup(v * v, gens)


def random_pair_coloring(v, rng, k=2):
    return tuple((3 + rng.randrange(2)) if i == j else rng.randrange(k)
                 for i in range(v) for j in range(v))


@pytest.mark.parametrize("cfg", CONFIGS, ids=IDS)
def test_young_pairs_brute(cfg):
    """Young groups on pairs (the shape of the graph stages), with random
    colorings: y a relabeling of x by a group element (or by a random
    permutation outside the group), or a random coloring."""
    rng = random.Random(11)
    shapes = [[[0, 1, 2]], [[0, 1, 2, 3]], [[0, 1, 2], [3, 4, 5]], [[0, 1, 2, 3], [4, 5]],
              [[0, 1, 2, 3, 4]], [[0, 1, 2], [4, 5, 6]], [[0, 1, 2, 3], [4, 5, 6]]]
    for trial in range(28):
        classes = shapes[trial % len(shapes)]
        v = 1 + max(max(C) for C in classes)
        G = on_pairs_group(classes, range(v))
        x = random_pair_coloring(v, rng, k=rng.choice([2, 3]))
        mode = trial % 3
        if mode == 0:
            g = rng.choice(list(G.elements()))
            y = act(x, g)
        elif mode == 1:
            s = list(range(v))
            rng.shuffle(s)
            y = act(x, tuple(s[i] * v + s[j] for i in range(v) for j in range(v)))
        else:
            y = random_pair_coloring(v, rng)
        S = Solver(**cfg)
        ans = S.solve(G, range(G.n), x, y)
        check_string(G, x, y, ans)


@pytest.mark.parametrize("cfg", CONFIGS, ids=IDS)
def test_young_cross_block_brute(cfg):
    """Sym(A) x Sym(B) on A x B, B x A and the diagonal (a merge stage),
    with a structured cross block (a 0/1 matrix) so that refinement and
    individualization both happen."""
    rng = random.Random(5)
    for trial in range(12):
        a, b = rng.choice([(3, 3), (4, 3), (3, 5), (4, 4)])
        V = list(range(a + b))
        A, B = V[:a], V[a:]
        D = sorted([(i, j) for i in A for j in B] + [(j, i) for i in A for j in B]
                   + [(i, i) for i in V])
        idx = {p: k for k, p in enumerate(D)}
        gens = [tuple(idx[(g[i], g[j])] for i, j in D)
                for C in (A, B) for g in sym_gens(a + b, C)]
        G = PermGroup(len(D), gens)
        M = {(i, j): rng.randrange(2) for i in A for j in B}
        x = tuple(M[(i, j)] if (i, j) in M else (M[(j, i)] + 2 if (j, i) in M else 9)
                  for i, j in D)
        if trial % 2:
            g = rng.choice(list(G.elements()))
            y = act(x, g)
        else:
            M2 = dict(M)
            k = rng.choice(list(M2))
            M2[k] ^= 1
            k2 = rng.choice([q for q in M2 if M2[q] != M[k] ^ 1] or [k])
            M2[k2] ^= 1
            y = tuple(M2[(i, j)] if (i, j) in M2 else (M2[(j, i)] + 2 if (j, i) in M2 else 9)
                      for i, j in D)
        ans = Solver(**cfg).solve(G, range(G.n), x, y)
        check_string(G, x, y, ans)


@pytest.mark.parametrize("cfg", CONFIGS, ids=IDS)
def test_giant_quotient_brute(cfg):
    """Sym(q) on ordered pairs without the diagonal (transitive, giant
    quotient on rows) and Sym(q) on 2-sets (Johnson), checked by brute
    force."""
    rng = random.Random(7)
    for q in (5, 6):
        pairs = [(i, j) for i in range(q) for j in range(q) if i != j]
        idx = {p: k for k, p in enumerate(pairs)}
        G = PermGroup(len(pairs), [tuple(idx[(g[i], g[j])] for i, j in pairs)
                                   for g in sym_gens(q, range(q))])
        sets = list(itertools.combinations(range(q), 2))
        sidx = {s: k for k, s in enumerate(sets)}
        J = PermGroup(len(sets), [tuple(sidx[tuple(sorted((g[i], g[j])))] for i, j in sets)
                                  for g in sym_gens(q, range(q))])
        for H in (G, J):
            for trial in range(4):
                x = tuple(rng.randrange(2) for _ in range(H.n))
                if trial % 2:
                    y = act(x, rng.choice(list(H.elements())))
                else:
                    y = tuple(rng.randrange(2) for _ in range(H.n))
                check_string(H, x, y, Solver(**cfg).solve(H, range(H.n), x, y))


def test_young_coupled_orbits():
    """Two orbits on which the group acts by the same Sym(4) (not a direct
    product): the structure must keep only one of them, and stay exact."""
    rng = random.Random(3)
    # Sym(4) acting on two copies of {0..3} and on the pairs between them
    pts = [(c, i) for c in range(2) for i in range(4)]
    pos = pts + [(p, q) for p in pts for q in pts if p[0] == 0 and q[0] == 1]
    idx = {p: k for k, p in enumerate(pos)}

    def img(g, p):
        if isinstance(p[0], int):
            return (p[0], g[p[1]])
        return (img(g, p[0]), img(g, p[1]))

    G = PermGroup(len(pos), [tuple(idx[img(g, p)] for p in pos) for g in sym_gens(4, range(4))])
    assert G.order() == 24
    for trial in range(10):
        x = tuple(rng.randrange(2) for _ in range(G.n))
        y = act(x, rng.choice(list(G.elements()))) if trial % 2 else \
            tuple(rng.randrange(2) for _ in range(G.n))
        for cfg in CONFIGS[:2]:
            check_string(G, x, y, Solver(**cfg).solve(G, range(G.n), x, y))


def test_wl2_joint_basic():
    # C6 vs 2 C3 as pair colorings: 2-WL distinguishes them
    def cyc(ls):
        n = sum(ls)
        P = [[0] * n for _ in range(n)]
        off = 0
        for L in ls:
            for i in range(L):
                a, b = off + i, off + (i + 1) % L
                P[a][b] = P[b][a] = 1
            off += L
        for i in range(n):
            P[i][i] = 2
        return [c for row in P for c in row]

    assert wl2_joint(cyc([6]), cyc([3, 3])) is None
    r = wl2_joint(cyc([6]), cyc([6]))
    assert r is not None and r[0] == r[1]


def relabel(A, s):
    n = len(A)
    B = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            B[s[i]][s[j]] = A[i][j]
    return B


def brute(A, B):
    n = len(A)
    return [s for s in itertools.permutations(range(n))
            if all(B[s[i]][s[j]] == A[i][j] for i in range(n) for j in range(n))]


@pytest.mark.parametrize("cfg", CONFIGS[:4], ids=IDS[:4])
def test_graphs_recursion_only(cfg):
    """Whole graphs with the front end's individualization off (ir=0), so the
    Young step and the giant step do the work; brute force on n <= 7."""
    rng = random.Random(9)
    for _ in range(40):
        n = rng.randint(3, 7)
        p = rng.choice([0.3, 0.5])
        A = [[0] * n for _ in range(n)]
        for i in range(n):
            for j in range(i + 1, n):
                if rng.random() < p:
                    A[i][j] = A[j][i] = 1
        if rng.random() < 0.6:
            s = list(range(n))
            rng.shuffle(s)
            B = relabel(A, s)
        else:
            B = [row[:] for row in A]
            i, j = rng.sample(range(n), 2)
            B[i][j] = B[j][i] = 1 - B[i][j]
        res = graph_iso(A, B, solver=Solver(**cfg), ir=0)
        isos, auts = brute(A, B), brute(A, A)
        assert (res is None) == (not isos)
        if res is not None:
            sigma, gens = res
            assert all(B[sigma[i]][sigma[j]] == A[i][j] for i in range(n) for j in range(n))
            assert all(A[g[i]][g[j]] == A[i][j] for g in gens for i in range(n) for j in range(n))
            assert PermGroup(n, gens).order() == len(auts)


def _srg_cases():
    sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "bench"))
    import networkx as nx
    from bench.families import adj, paley, rook, shrikhande, triangular, kneser, shuffled
    rng = random.Random(4)
    cases = []
    for name, G, aut in [("Petersen", nx.petersen_graph(), 120), ("Paley13", paley(13), 78),
                         ("rook4", rook(4), 1152), ("Shrikhande", shrikhande(), 192),
                         ("T6", triangular(6), 720), ("Kneser(6,2)", kneser(6, 2), 720),
                         ("K44", nx.complete_bipartite_graph(4, 4), 1152),
                         ("Q4", nx.hypercube_graph(4), 384)]:
        A = adj(G)
        cases.append((name, A, shuffled(A, rng), True, aut))
    cases.append(("rook4-vs-Shrikhande", adj(rook(4)), shuffled(adj(shrikhande()), rng),
                  False, None))
    return cases


@pytest.mark.parametrize("cfg", CONFIGS[:4], ids=IDS[:4])
def test_srg_recursion_only(cfg):
    """Strongly regular and other symmetric graphs with ir=0 (Young step
    with individualization, one-mode and pruning), against known |Aut|."""
    for name, A, B, iso, aut in _srg_cases():
        S = Solver(**cfg)
        res = graph_iso(A, B, solver=S, ir=0)
        n = len(A)
        assert (res is not None) == iso, name
        if res is None:
            continue
        sigma, gens = res
        assert all(B[sigma[i]][sigma[j]] == A[i][j] for i in range(n) for j in range(n)), name
        assert all(A[g[i]][g[j]] == A[i][j] for g in gens for i in range(n) for j in range(n))
        assert PermGroup(n, gens).order() == aut, name
        if cfg.get("young", True):
            assert S.stats["young_ind"] > 0 or S.stats["young_split"] > 0, name


def _pairs_from_edges(v, edges, diag=None):
    E = set()
    for a, b in edges:
        E.add((a, b))
        E.add((b, a))
    diag = diag or {}
    return tuple(3 + diag.get(i, 0) if i == j else int((i, j) in E)
                 for i in range(v) for j in range(v))


@pytest.mark.parametrize("cfg", CONFIGS, ids=IDS)
def test_young_symmetric_brute(cfg):
    """Symmetric colorings (uniform under refinement, so labels must be
    individualized: pruning, the memo and one-mode run), against brute force:
    C6 vs C6 / 2C3 under Sym(6); a 3x4 biregular cross block under
    Sym(3) x Sym(4); K33 vs prism under Sym(6); Petersen-like C5 + pendant
    structure under Sym(5) x Sym(2)."""
    rng = random.Random(2)
    c6 = [(i, (i + 1) % 6) for i in range(6)]
    c33 = [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3)]
    k33 = [(i, j) for i in range(3) for j in range(3, 6)]
    prism = c33 + [(0, 3), (1, 4), (2, 5)]
    cross = [(a, 3 + b) for a in range(3) for b in range(4) if (a + b) % 3 != 0]
    c5p = [(i, (i + 1) % 5) for i in range(5)] + [(0, 5), (2, 6)]
    cases = [([list(range(6))], 6, c6, c6), ([list(range(6))], 6, c6, c33),
             ([list(range(6))], 6, k33, k33), ([list(range(6))], 6, k33, prism),
             ([[0, 1, 2], [3, 4, 5, 6]], 7, cross, cross),
             ([[0, 1, 2, 3, 4], [5, 6]], 7, c5p, c5p)]
    for classes, v, ex, ey in cases:
        G = on_pairs_group(classes, range(v))
        x = _pairs_from_edges(v, ex)
        y0 = _pairs_from_edges(v, ey)
        for _ in range(2):
            g = rng.choice(list(G.elements()))
            y = act(y0, g)
            check_string(G, x, y, Solver(**cfg).solve(G, range(G.n), x, y))
        check_string(G, x, x, Solver(**cfg).solve(G, range(G.n), x, x))
