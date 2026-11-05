"""Exactness tests for branching economy: automorphism pruning, the memo and
one-mode, GiantStep on Sym(q) without normalization, the Alt(q) path and the
large-symmetry branch. Run: python3 -m pytest -q tests"""
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
from gi.perm import act, alt_gens, sym_gens, maps, parity

CONFIGS = [dict(certificates=False, enum_limit=1),
           dict(certificates=True, enum_limit=1, kappa=3),
           dict(certificates=True, enum_limit=1, kappa=3, cert_refine=False),
           dict(certificates=False)]
IDS = ["nocert", "cert3", "cert3-norefine", "default-enum"]


def relabel(A, s):
    n = len(A)
    B = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            B[s[i]][s[j]] = A[i][j]
    return B


def shuffled(A, seed):
    s = list(range(len(A)))
    random.Random(seed).shuffle(s)
    return relabel(A, s)


def from_edges(n, edges):
    A = [[0] * n for _ in range(n)]
    for u, v in edges:
        A[u][v] = A[v][u] = 1
    return A


def complete(n):
    return from_edges(n, itertools.combinations(range(n), 2))


def complete_bipartite(a, b):
    return from_edges(a + b, [(i, a + j) for i in range(a) for j in range(b)])


def cycles(*lengths):
    edges, off = [], 0
    for L in lengths:
        edges += [(off + i, off + (i + 1) % L) for i in range(L)]
        off += L
    return from_edges(off, edges)


def petersen():
    outer = [(i, (i + 1) % 5) for i in range(5)]
    spokes = [(i, i + 5) for i in range(5)]
    inner = [(5 + i, 5 + (i + 2) % 5) for i in range(5)]
    return from_edges(10, outer + spokes + inner)


def check_answer(A, B, res, aut_order, iso):
    n = len(A)
    assert (res is not None) == iso
    if res is None:
        return
    sigma, gens = res
    assert sorted(sigma) == list(range(n))
    assert all(B[sigma[i]][sigma[j]] == A[i][j] for i in range(n) for j in range(n))
    assert all(A[g[i]][g[j]] == A[i][j] for g in gens for i in range(n) for j in range(n))
    assert PermGroup(n, gens).order() == aut_order


def cycle_aut(lengths):
    """|Aut| of a disjoint union of cycles (lengths >= 3)."""
    from collections import Counter
    out = 1
    for L, k in Counter(lengths).items():
        out *= math.factorial(k) * (2 * L) ** k
    return out


ISO_CASES = [
    ("K5", complete(5), 120),
    ("K6", complete(6), 720),
    ("K7", complete(7), 5040),
    ("empty6", [[0] * 6 for _ in range(6)], 720),
    ("K33", complete_bipartite(3, 3), 72),
    ("K44", complete_bipartite(4, 4), 1152),
    ("K55", complete_bipartite(5, 5), 2 * 120 * 120),
    ("K25", complete_bipartite(2, 5), 2 * 120),
    ("2C3", cycles(3, 3), cycle_aut([3, 3])),
    ("2C4", cycles(4, 4), cycle_aut([4, 4])),
    ("3C3", cycles(3, 3, 3), cycle_aut([3, 3, 3])),
    ("C3+C4", cycles(3, 4), cycle_aut([3, 4])),
    ("2C3+C4", cycles(3, 3, 4), cycle_aut([3, 3, 4])),
    ("2C5", cycles(5, 5), cycle_aut([5, 5])),
    ("C9", cycles(9), 18),
    ("Petersen", petersen(), 120),
]


@pytest.mark.parametrize("cfg", CONFIGS, ids=IDS)
@pytest.mark.parametrize("name,A,aut", ISO_CASES, ids=[c[0] for c in ISO_CASES])
def test_symmetric_iso(cfg, name, A, aut):
    if cfg.get("certificates") and len(A) > 8:
        pytest.skip("certificates are slow on larger graphs")
    for B in (A, shuffled(A, len(A))):
        S = Solver(**cfg)
        check_answer(A, B, graph_iso(A, B, solver=S), aut, True)


NONISO_CASES = [
    ("C8-2C4", cycles(8), cycles(4, 4)),
    ("C6-2C3", cycles(6), cycles(3, 3)),
    ("C7-C3+C4", cycles(7), cycles(3, 4)),
    ("C9-3C3", cycles(9), cycles(3, 3, 3)),
    ("2C5-C10", cycles(5, 5), cycles(10)),
    ("K33-prism", complete_bipartite(3, 3),
     from_edges(6, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (0, 3), (1, 4), (2, 5)])),
    ("Petersen-C10+chords", petersen(),
     from_edges(10, [(i, (i + 1) % 10) for i in range(10)] + [(i, i + 5) for i in range(5)])),
]


@pytest.mark.parametrize("cfg", CONFIGS, ids=IDS)
@pytest.mark.parametrize("name,A,B", NONISO_CASES, ids=[c[0] for c in NONISO_CASES])
def test_noniso(cfg, name, A, B):
    if cfg.get("certificates") and len(A) > 8:
        pytest.skip("certificates are slow on larger graphs")
    assert graph_iso(A, shuffled(B, 3), solver=Solver(**cfg)) is None


def brute_group(n, gens):
    return list(PermGroup(n, gens).elements())


def on_pairs(n, g):
    return tuple(g[i] * n + g[j] for i in range(n) for j in range(n))


@pytest.mark.parametrize("alt", [False, True], ids=["sym", "alt"])
@pytest.mark.parametrize("cfg", CONFIGS[:3], ids=IDS[:3])
def test_string_iso_pairs(alt, cfg):
    """Iso_G(x, y) for G = Sym(5) or Alt(5) acting on ordered pairs, against brute
    force. With G = Alt(q) the giant step takes the parity-restricted path."""
    n = 5
    rng = random.Random(7 if alt else 8)
    vg = (alt_gens if alt else sym_gens)(n, range(n))
    G = PermGroup(n * n, [on_pairs(n, g) for g in vg])
    elems = list(G.elements())
    for trial in range(12):
        k = rng.choice([2, 3])
        x = tuple(rng.randrange(k) if i % (n + 1) else 5 for i in range(n * n))
        if trial % 3 == 2:
            y = tuple(rng.randrange(k) if i % (n + 1) else 5 for i in range(n * n))
        else:
            y = act(x, rng.choice(elems))
        S = Solver(**cfg)
        res = S.solve(G, range(n * n), x, y)
        isos = [g for g in elems if maps(g, x, y)]
        auts = [g for g in elems if maps(g, x, x)]
        assert (res is None) == (not isos)
        if res is not None:
            assert G.contains(res.rep) and maps(res.rep, x, y)
            assert all(G.contains(g) and maps(g, x, x) for g in res.gens)
            assert PermGroup(n * n, res.gens).order() == len(auts)


def test_pruning_happens():
    """Petersen (|Aut| = 120): the baseline explored 260 branches. The front end
    is bypassed (Sym(n) on raw pairs) so that the recursion does the work.
    (scheme=False: the non-edges of Petersen form T(5) = J(5, 2), so the
    scheme step would reduce Sym(10) to Sym(5) without any branching.)"""
    S = Solver(certificates=False, enum_limit=1, scheme=False)
    A = petersen()
    B = shuffled(A, 1)
    check_answer(A, B, graph_iso(A, B, solver=S, refine="none", staged=False, ir=0), 120, True)
    assert S.stats["pruned"] > 0
    assert S.stats["branch"] <= 20


@pytest.mark.parametrize("refine", [True, False])
def test_large_symmetry_sym(refine):
    """G = Sym(5) x C2 on two copies of the labels, x = the copy index. The full
    certificates generate Alt(5) on the labels while phi(G) = Sym(5), so the
    large-symmetry branch must add the odd coset of ker(phi)."""
    q = 5
    n = 2 * q
    gens = [g + tuple(q + v for v in g) for g in sym_gens(q, range(q))]
    gens.append(tuple(range(q, n)) + tuple(range(q)))
    G = PermGroup(n, gens)
    elems = list(G.elements())
    x = (0,) * q + (1,) * q
    rng = random.Random(3)
    ys = [act(x, rng.choice(elems)) for _ in range(6)] + [x]
    ys += [(0, 1, 0, 1, 0, 1, 0, 1, 0, 1), (0, 0, 0, 0, 1, 1, 1, 1, 1, 0)]
    for y in ys:
        S = Solver(certificates=True, enum_limit=1, kappa=3, cert_refine=refine)
        res = S.solve(G, range(n), x, y)
        isos = [g for g in elems if maps(g, x, y)]
        assert (res is None) == (not isos)
        if res is not None:
            assert S.stats["large_symmetry"] > 0
            assert G.contains(res.rep) and maps(res.rep, x, y)
            assert all(G.contains(g) and maps(g, x, x) for g in res.gens)
            assert PermGroup(n, res.gens).order() == len([g for g in elems if maps(g, x, x)])


def wreath(a, b):
    """Sym(a) wr Sym(b) acting imprimitively on a*b points (blocks of size a)."""
    n = a * b
    gens = []
    for g in sym_gens(a, range(a)):           # Sym(a) on the first block
        gens.append(tuple(g[i] if i < a else i for i in range(n)))
    for h in sym_gens(b, range(b)):           # permute the blocks
        gens.append(tuple(h[i // a] * a + i % a for i in range(n)))
    return PermGroup(n, gens)


@pytest.mark.parametrize("a,b", [(2, 3), (3, 3), (2, 4)])
def test_quotient_enumeration(a, b):
    """Imprimitive groups with a small nonabelian quotient (enum_cosets), with the
    first nonempty coset often not the identity one, against brute force."""
    G = wreath(a, b)
    n = G.n
    elems = list(G.elements())
    rng = random.Random(a * 10 + b)
    for trial in range(15):
        x = tuple(rng.randrange(3) for _ in range(n))
        y = act(x, rng.choice(elems)) if trial % 4 else tuple(rng.randrange(3) for _ in range(n))
        S = Solver(certificates=False, enum_limit=1)
        res = S.solve(G, range(n), x, y)
        isos = [g for g in elems if maps(g, x, y)]
        assert (res is None) == (not isos)
        if res is not None:
            assert G.contains(res.rep) and maps(res.rep, x, y)
            assert all(maps(g, x, x) for g in res.gens)
            assert PermGroup(n, res.gens).order() == len([g for g in elems if maps(g, x, x)])


@pytest.mark.parametrize("alt", [False, True], ids=["sym", "alt"])
def test_one_mode_strings(alt):
    """One solver, memo primed with Aut_G(x): later Iso_G(x, y) calls run in
    one-mode at the top and must still be exact."""
    n = 6
    rng = random.Random(11 if alt else 12)
    vg = (alt_gens if alt else sym_gens)(n, range(n))
    G = PermGroup(n * n, [on_pairs(n, g) for g in vg])
    for trial in range(4):
        k = rng.choice([2, 3])
        x = tuple(rng.randrange(k) if i % (n + 1) else 5 for i in range(n * n))
        S = Solver(certificates=False, enum_limit=1)
        aut = S.solve(G, range(n * n), x, x)
        order = PermGroup(n * n, aut.gens).order()
        for _ in range(5):
            g = tuple(rng.sample(range(n), n))
            if alt and parity(g):
                g = (g[1], g[0]) + g[2:]
            y = act(x, on_pairs(n, g))
            res = S.solve(G, range(n * n), x, y)
            assert res is not None and maps(res.rep, x, y) and G.contains(res.rep)
            assert PermGroup(n * n, res.gens).order() == order
        z = tuple(rng.randrange(k) if i % (n + 1) else 5 for i in range(n * n))
        res = S.solve(G, range(n * n), x, z)
        if res is not None:
            assert maps(res.rep, x, z) and G.contains(res.rep)


@pytest.mark.parametrize("lengths", [(3, 4), (3, 3, 4), (3, 5), (4, 4)])
def test_one_mode_graphs(lengths):
    """Cycle unions defeat 1-WL, so uniform label classes contain several
    automorphism orbits. Reuse one solver so that the memo is hot."""
    A = cycles(*lengths)
    aut = cycle_aut(list(lengths))
    S = Solver(certificates=False, enum_limit=1)
    check_answer(A, A, graph_iso(A, A, solver=S), aut, True)
    for seed in range(4):
        B = shuffled(A, seed)
        check_answer(A, B, graph_iso(A, B, solver=S), aut, True)
    n = len(A)
    C = cycles(n)
    assert graph_iso(A, shuffled(C, 9), solver=S) is None
