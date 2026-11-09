"""Tests of the w14-solver additions: the worklist 1-WL (gi/wl.py), the staged
root classes, sparse elementary abelian groups, and pipeline dispatch."""
import os
import random
import sys
from collections import Counter

import pytest

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.setrecursionlimit(100000)

from gi.wl import refine as wl_refine


def naive_1wl(nbr, col, roots=()):
    """Round-based 1-WL (coarsest equitable partition refining the initial
    one, with the roots individualized): the classes as a set of frozensets."""
    n = len(nbr)
    c = list(col)
    for i, r in enumerate(roots):
        c[r] = ("root", i)
    while True:
        sig = [(c[v], tuple(sorted(map(repr, (c[w] for w in nbr[v]))))) for v in range(n)]
        rank = {s: i for i, s in enumerate(sorted(set(sig), key=repr))}
        new = [rank[s] for s in sig]
        if len(set(new)) == len(set(map(repr, c))):
            return partition(new)
        c = new


def partition(col):
    classes = {}
    for v, c in enumerate(col):
        classes.setdefault(c, set()).add(v)
    return {frozenset(s) for s in classes.values()}


def random_graph(n, rng, p=None):
    p = rng.choice((0.1, 0.2, 0.3, 0.5)) if p is None else p
    nbr = [[] for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < p:
                nbr[i].append(j)
                nbr[j].append(i)
    return nbr


def random_regular_multigraph_free(n, d, rng):
    """A connected-or-not simple d-regular graph by rejection (small n)."""
    while True:
        pts = [i for i in range(n) for _ in range(d)]
        rng.shuffle(pts)
        E = set()
        ok = True
        for a, b in zip(pts[0::2], pts[1::2]):
            if a == b or (min(a, b), max(a, b)) in E:
                ok = False
                break
            E.add((min(a, b), max(a, b)))
        if ok:
            nbr = [[] for _ in range(n)]
            for a, b in E:
                nbr[a].append(b)
                nbr[b].append(a)
            return nbr


def shuffled_copy(nbr, col, rng):
    n = len(nbr)
    p = list(range(n))
    rng.shuffle(p)
    out = [None] * n
    outcol = [None] * n
    for v in range(n):
        out[p[v]] = sorted(p[w] for w in nbr[v])
        outcol[p[v]] = col[v]
    return out, outcol, p


@pytest.mark.parametrize("seed", range(150))
def test_refine_equals_naive_and_is_canonical(seed):
    rng = random.Random(seed)
    n = rng.randint(2, 40)
    if seed % 3 == 0:
        nbr = random_regular_multigraph_free(n + (n % 2) + 2, 3, rng)
        n = len(nbr)
    else:
        nbr = random_graph(n, rng)
    col = [rng.randrange(1, 4) for _ in range(n)] if seed % 2 else [0] * n
    roots = tuple(rng.sample(range(n), rng.choice((0, 1, 2)))) if n >= 2 else ()
    c = wl_refine(nbr, col, roots)
    assert partition(c) == naive_1wl(nbr, col, roots)
    # stable start: refining a stable coloring further with roots gives the same
    # partition as running everything together
    c0 = wl_refine(nbr, col)
    c1 = wl_refine(nbr, c0, roots, True)
    assert partition(c1) == partition(c)
    # names are canonical: relabelling the graph relabels the names
    nbr2, col2, p = shuffled_copy(nbr, col, rng)
    roots2 = tuple(p[r] for r in roots)
    c2 = wl_refine(nbr2, col2, roots2)
    assert all(c2[p[v]] == c[v] for v in range(n))
    c3 = wl_refine(nbr2, wl_refine(nbr2, col2), roots2, True)
    assert all(c3[p[v]] == c1[v] for v in range(n))


# -- sparse elementary abelian groups -------------------------------------------------
from gi.ea2 import SparseEA, compose
from gi.perm import mul


def random_ea_dense(rng, n, k):
    """k independent commuting involutions on range(n): a random partition of
    points into small blocks, each generator swaps a random subset of block
    pairs (independent by construction: each generator has a private pair)."""
    pts = list(range(n))
    rng.shuffle(pts)
    pairs = [(pts[2 * i], pts[2 * i + 1]) for i in range(n // 2)]
    gens = []
    for i in range(k):
        chosen = set(rng.sample(range(len(pairs)), rng.randint(1, len(pairs))))
        chosen |= {i % len(pairs)}
        g = list(range(n))
        for j in chosen:
            a, b = pairs[j]
            g[a], g[b] = b, a
        gens.append(tuple(g))
    return gens


@pytest.mark.parametrize("seed", range(40))
def test_sparse_ea_products_and_restrict(seed):
    rng = random.Random(seed)
    n = rng.randint(4, 30)
    k = rng.randint(1, min(8, n // 2))
    dense = random_ea_dense(rng, n, k)
    G = SparseEA.from_tuples(dense)
    assert G.order() == 1 << len(G.gens) and len(G.gens) == k
    # who index: exactly the generators moving p
    for p in range(n):
        assert sorted(G.who.get(p, ())) == [i for i in G.gens if p in G.gens[i]]
    ids = sorted(G.gens)
    for gid, g in zip(ids, dense):
        assert G.dense(gid, n) == g
    # products of random subsets, against dense multiplication
    for _ in range(10):
        bits = [i for i in range(k) if rng.random() < 0.5]
        expect = tuple(range(n))
        for i in bits:
            expect = mul(expect, dense[i])
        c = compose([G.gens[ids[i]] for i in bits])
        got = list(range(n))
        for p, q in c.items():
            got[p] = q
        assert tuple(got) == expect
    # restrict to random combinations: same span as the dense span
    N = []
    for _ in range(rng.randint(1, k)):
        v = rng.getrandbits(k) | (1 << rng.randrange(k))
        N.append(v)
    # (use an independent basis of the chosen combinations)
    from gi.ea2 import XorBasis
    B = XorBasis()
    indep = []
    for v in N:
        if B.reduce(v):
            B.add(v)
            indep.append(v)
    ids0 = sorted(G.gens)
    new = G.restrict(ids0, indep)
    assert len(new) == len(indep) and len(G.gens) == len(indep)
    def elems(gens):
        out = {tuple(range(n))}
        for g in gens:
            out |= {mul(e, g) for e in out}
        return out
    combos = []
    for v in indep:
        e = tuple(range(n))
        for i in range(k):
            if v >> i & 1:
                e = mul(e, dense[i])
        combos.append(e)
    assert elems([G.dense(g, n) for g in new]) == elems(combos)
    for p in range(n):
        assert sorted(G.who.get(p, ())) == sorted(i for i in G.gens if p in G.gens[i])


# -- individualization-refinement canonizer ---------------------------------------------
import itertools
from gi.canon import ir_canon


def _colored_graph(n, rng):
    p = rng.choice((0.2, 0.35, 0.5))
    adj = [[] for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < p:
                adj[i].append(j)
                adj[j].append(i)
    ncol = rng.randint(1, 3)
    col = [rng.randrange(ncol) for _ in range(n)]
    return adj, col


def _relabeled(adj, col, p):
    n = len(adj)
    a2 = [None] * n
    c2 = [None] * n
    for v in range(n):
        a2[p[v]] = sorted(p[w] for w in adj[v])
        c2[p[v]] = col[v]
    return a2, c2


def _form(adj, col, lab):
    n = len(adj)
    cl = [None] * n
    for v in range(n):
        cl[lab[v]] = col[v]
    return (tuple(cl), tuple(sorted((min(lab[u], lab[v]), max(lab[u], lab[v])) for u in range(n)
                                    for v in adj[u] if u < v)))


def _brute_aut(adj, col):
    n = len(adj)
    E = {(u, v) for u in range(n) for v in adj[u]}
    out = []
    for p in itertools.permutations(range(n)):
        if all(col[p[i]] == col[i] for i in range(n)) and all((p[u], p[v]) in E for u, v in E):
            out.append(p)
    return out


def _gen_group(gens, n):
    idn = tuple(range(n))
    seen = {idn}
    frontier = [idn]
    while frontier:
        new = []
        for e in frontier:
            for g in gens:
                h = tuple(g[e[i]] for i in range(n))
                if h not in seen:
                    seen.add(h)
                    new.append(h)
        frontier = new
    return seen


@pytest.mark.parametrize("seed", range(120))
def test_ir_canon_against_brute_force(seed):
    rng = random.Random(1000 + seed)
    n = rng.randint(1, 7)
    adj, col = _colored_graph(n, rng)
    lab, auts = ir_canon(adj, col)
    assert sorted(lab) == list(range(n))
    # labelling stays inside each color class
    cls = {}
    for v in range(n):
        cls.setdefault(col[v], []).append(v)
    for c, vs in cls.items():
        assert sorted(lab[v] for v in vs) == sorted(vs)
    form = _form(adj, col, lab)
    # every automorphism found is one; they generate the whole group
    E = {(u, v) for u in range(n) for v in adj[u]}
    for a in auts:
        assert sorted(a) == list(range(n))
        assert all(col[a[i]] == col[i] for i in range(n))
        assert all((a[u], a[v]) in E for u, v in E)
    assert len(_gen_group(auts, n)) == len(_brute_aut(adj, col))
    # the form is invariant under color-preserving relabellings (the case that
    # matters: the classes are the blocks, fixed label sets)
    for _ in range(6):
        p = list(range(n))
        for vs in cls.values():         # a random permutation of each class
            img = vs[:]
            rng.shuffle(img)
            for a, b in zip(vs, img):
                p[a] = b
        a2, c2 = _relabeled(adj, col, p)
        assert c2 == col
        l2, _ = ir_canon(a2, c2)
        assert _form(a2, c2, l2) == form
    # another graph with the same color classes: forms equal iff isomorphic
    b, cb = _colored_graph(n, rng)
    cb = col                             # (same color classes)
    lb, _ = ir_canon(b, cb)
    Eb = {(u, v) for u in range(n) for v in b[u]}
    iso = any(all(cb[p[i]] == col[i] for i in range(n)) and
              {(p[u], p[v]) for u, v in E} == Eb
              for p in itertools.permutations(range(n)))
    assert (_form(b, cb, lb) == form) == iso


# -- staged root classes, certificates, pipeline dispatch -------------------------------
import networkx as nx

from gi.bounded import _Graph, root_class, bounded_iso_lists, NotSimple
from gi.group import PermGroup
from gi.solver import Solver
import gi.graph as gg
from gi import graph_iso


def lists_matrix(A):
    return [[j for j, x in enumerate(r) if x] for r in A]


def matrix_of(nbr):
    n = len(nbr)
    A = [[0] * n for _ in range(n)]
    for u in range(n):
        for v in nbr[u]:
            A[u][v] = 1
    return A


def relabeled_nbr(nbr, p):
    n = len(nbr)
    out = [None] * n
    for v in range(n):
        out[p[v]] = sorted(p[w] for w in nbr[v])
    return out


def connected_random(n, rng):
    while True:
        nbr = random_graph(n, rng)
        if all(nbr) and nx.is_connected(_nxg(nbr)):
            return [sorted(r) for r in nbr]


def _nxg(nbr):
    G = nx.Graph()
    G.add_nodes_from(range(len(nbr)))
    G.add_edges_from((u, v) for u, r in enumerate(nbr) for v in r if u < v)
    return G


@pytest.mark.parametrize("seed", range(60))
def test_root_class_respects_isomorphisms(seed):
    rng = random.Random(2000 + seed)
    n = rng.randint(3, 40)
    if n < 10:
        nbr = connected_random(max(n, 4), rng)
    else:
        nbr = random_regular_multigraph_free(n + (n % 2), rng.choice((3, 4, 5)), rng)
        comps = list(nx.connected_components(_nxg(nbr)))
        if len(comps) > 1:
            return
    n = len(nbr)
    col = wl_refine(nbr, [0] * n)
    edges = [(u, v) for u in range(n) for v in nbr[u]]
    C, keys = root_class(_Graph(nbr, col), edges)
    p = list(range(n))
    rng.shuffle(p)
    nbr2 = relabeled_nbr(nbr, p)
    col2 = wl_refine(nbr2, [0] * n)
    assert all(col2[p[v]] == col[v] for v in range(n))
    edges2 = [(u, v) for u in range(n) for v in nbr2[u]]
    C2, keys2 = root_class(_Graph(nbr2, col2), edges2)
    assert keys2 == keys
    img = {(p[u], p[v]) for u, v in (edges[f] for f in C)}
    assert {edges2[f] for f in C2} == img
    res = root_class(_Graph(nbr2, col2), edges2, keys)
    assert res is not None and {edges2[f] for f in res[0]} == img


def _check_iso_answer(X, Y, res, name=""):
    """res is None or (sigma, gens): checks against networkx (decision)
    and the validity of sigma and of each generator."""
    n = len(X)
    A, B = _nxg(lists_matrix(X)), _nxg(lists_matrix(Y))
    expect = nx.is_isomorphic(A, B)
    assert (res is not None) == expect, name
    if res is None:
        return None
    sigma, gens = res
    assert sorted(sigma) == list(range(n)), name
    for i in range(n):
        for j in range(n):
            assert X[i][j] == Y[sigma[i]][sigma[j]], name
    for g in gens:
        for i in range(n):
            for j in range(n):
                assert X[i][j] == X[g[i]][g[j]], name
    return gens


def _aut_order_vf2(nbr):
    G = _nxg(nbr)
    return sum(1 for _ in nx.algorithms.isomorphism.GraphMatcher(G, G).isomorphisms_iter())


@pytest.mark.parametrize("seed", range(30))
def test_dispatch_agrees_with_vf2(seed):
    rng = random.Random(3000 + seed)
    n = rng.randint(4, 12)
    nbr = random_regular_multigraph_free(n + (n % 2), 3, rng) if seed % 3 == 0 else random_graph(n, rng)
    n = len(nbr)
    A = matrix_of([sorted(r) for r in nbr])
    p = list(range(n))
    rng.shuffle(p)
    B = matrix_of(relabeled_nbr(lists_matrix(A), p))
    C = matrix_of(random_graph(n, rng))
    for method in ("auto", "bounded", "hybrid"):
        for X, Y in ((A, B), (A, C)):
            S = Solver(certificates=False)
            res = graph_iso(X, Y, solver=S, method=method)
            gens = _check_iso_answer(X, Y, res)
            if gens is not None and n <= 12:
                order = PermGroup(n, gens).order() if gens else 1
                assert order == _aut_order_vf2(lists_matrix(A)) if X is A and Y is B else True
            assert S.stats["pipeline_bounded"] + S.stats["pipeline_hybrid"] >= 1


def test_dispatch_budget_fallback_is_exact(monkeypatch):
    rng = random.Random(5)
    # a highly symmetric graph that the bounded pipeline solves through its solver
    # (rook graph K4 box K4), with the work budget set to zero: it must fall back
    k = 4
    nbr = [[] for _ in range(k * k)]
    for a, b in itertools.product(range(k), repeat=2):
        for c, d in itertools.product(range(k), repeat=2):
            if (a, b) != (c, d) and (a == c or b == d):
                nbr[a * k + b].append(c * k + d)
    A = matrix_of(nbr)
    p = list(range(k * k))
    rng.shuffle(p)
    B = matrix_of(relabeled_nbr(nbr, p))
    C = matrix_of(relabeled_nbr(nbr, p))
    C[0][1] = C[1][0] = 1 - C[0][1]
    C[2][7] = C[7][2] = 1 - C[2][7]
    monkeypatch.setattr(gg, "BOUNDED_WORK_PER_N2", 0)
    S = Solver(certificates=False)
    res = graph_iso(A, B, solver=S)
    gens = _check_iso_answer(A, B, res)
    order = PermGroup(16, gens).order()
    assert order == _aut_order_vf2(nbr)
    S2 = Solver(certificates=False)
    assert graph_iso(A, C, solver=S2) is None or _check_iso_answer(A, C, graph_iso(A, C, solver=Solver())) is not None
    assert S.stats["pipeline_fallback"] == 1 and S.stats["pipeline_hybrid"] == 1


def test_dispatch_non_simple_graphs_use_hybrid():
    A = [[0, 2, 0], [2, 0, 1], [0, 1, 0]]    # an edge colored 2
    B = [[0, 1, 0], [1, 0, 2], [0, 2, 0]]
    S = Solver(certificates=False)
    assert graph_iso(A, B, solver=S) is not None and S.stats["pipeline_hybrid"] == 1
    D = [[0, 1, 0], [0, 0, 1], [0, 0, 0]]    # directed
    with pytest.raises(NotSimple):
        graph_iso(D, D, solver=Solver(), method="bounded")
    S = Solver(certificates=False)
    assert graph_iso(D, D, solver=S) is not None and S.stats["pipeline_hybrid"] == 1


@pytest.mark.parametrize("seed", range(25))
def test_discrete_certificates_rigid_graphs(seed):
    """Random sparse graphs: rooted refinement usually becomes discrete. The
    bounded pipeline's answer and |Aut| against networkx."""
    rng = random.Random(4000 + seed)
    n = rng.randint(8, 18)
    p0 = rng.choice((0.25, 0.35))
    nbr = [[] for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < p0:
                nbr[i].append(j)
                nbr[j].append(i)
    A = matrix_of(nbr)
    p = list(range(n))
    rng.shuffle(p)
    nbr2 = relabeled_nbr(nbr, p)
    res = bounded_iso_lists(nbr, nbr2, Solver(certificates=False))
    gens = _check_iso_answer(A, matrix_of(nbr2), res)
    order = PermGroup(n, gens).order() if gens else 1
    assert order == _aut_order_vf2(nbr)
    # a one-edge perturbation: the decision against VF2
    nbr3 = [list(r) for r in nbr2]
    u, v = rng.sample(range(n), 2)
    if v in nbr3[u]:
        nbr3[u].remove(v)
        nbr3[v].remove(u)
    else:
        nbr3[u].append(v)
        nbr3[v].append(u)
    res = bounded_iso_lists(nbr, nbr3, Solver(certificates=False))
    _check_iso_answer(A, matrix_of(nbr3), res)
