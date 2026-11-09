"""Canonical labeling (gi/canon.py) checked against brute force and known
answers: invariance under relabeling, separation of non-isomorphic pairs
(CFI, multipedes, random graphs), agreement with brute-force canonical forms
on all tiny graphs, Aut generators, and the two string canonizers (EA2 least
images by linear algebra, perm_canon by search) against enumeration.
Run: python3 -m pytest -q tests"""
import itertools
import os
import random
import sys
from collections import Counter

import pytest

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.setrecursionlimit(100000)

import networkx as nx

from gi.canon import (canonical_form, canonical_form_lists, canonical_labeling,
                      canonical_labeling_lists, canon_iso, canon_iso_lists, perm_canon,
                      relabel_lists)
from gi.ea2 import EA2, EAAction
from gi.group import PermGroup
from gi.perm import act, mul, identity
from gi.bounded import bounded_iso_lists
from bench.families import cfi
from bench import irhard


# -- helpers --------------------------------------------------------------------------------
def lists_of(G):
    nodes = sorted(G.nodes(), key=repr)
    idx = {v: i for i, v in enumerate(nodes)}
    nb = [[] for _ in nodes]
    for u, v in G.edges():
        if u != v:
            nb[idx[u]].append(idx[v])
            nb[idx[v]].append(idx[u])
    return nb


def relabeled(nbr, rng, colors=None):
    n = len(nbr)
    s = list(range(n))
    rng.shuffle(s)
    out = [None] * n
    for i in range(n):
        out[s[i]] = sorted(s[j] for j in nbr[i])
    if colors is None:
        return out
    c2 = [None] * n
    for i in range(n):
        c2[s[i]] = colors[i]
    return out, c2


def edge_set(nbr):
    return {(u, v) for u in range(len(nbr)) for v in nbr[u]}


def check_labeling(nbr, colors=None):
    """canonical_labeling_lists: lab is a bijection, every generator is an
    automorphism; returns (form, |<gens>|)."""
    lab, gens = canonical_labeling_lists(nbr, colors)
    n = len(nbr)
    assert sorted(lab) == list(range(n))
    E = edge_set(nbr)
    for g in gens:
        assert sorted(g) == list(range(n))
        assert all((g[u], g[v]) in E for u, v in E)
        if colors is not None:
            assert all(colors[g[v]] == colors[v] for v in range(n))
    form = canonical_form_lists(nbr, colors)
    can = relabel_lists(nbr, lab)
    assert form[2] == tuple(sorted(i * n + j for i in range(n) for j in can[i] if i < j))
    order = PermGroup(n, gens).order() if gens else 1
    return form, order


def brute_aut_count(nbr, colors=None):
    G = nx.Graph()
    G.add_nodes_from(range(len(nbr)))
    G.add_edges_from((u, v) for u in range(len(nbr)) for v in nbr[u])
    if colors is not None:
        for v in range(len(nbr)):
            G.nodes[v]["c"] = colors[v]
        nm = nx.algorithms.isomorphism.categorical_node_match("c", None)
        return sum(1 for _ in nx.algorithms.isomorphism.GraphMatcher(G, G, node_match=nm)
                   .isomorphisms_iter())
    return sum(1 for _ in nx.algorithms.isomorphism.GraphMatcher(G, G).isomorphisms_iter())


def nx_of(nbr):
    G = nx.Graph()
    G.add_nodes_from(range(len(nbr)))
    G.add_edges_from((u, v) for u in range(len(nbr)) for v in nbr[u])
    return G


# -- the string canonizers -------------------------------------------------------------------
def random_ea_action(rng, d, k, nquot):
    """An elementary abelian 2-group with basis of k independent translations
    of F_2^d acting on the union of nquot quotients F_2^d / W (random W), one
    of them with W = 0 (so the action is faithful)."""
    vecs = []
    while len(vecs) < k:
        v = rng.randrange(1, 1 << d)
        span = {0}
        for w in vecs:
            span |= {s ^ w for s in span}
        if v not in span:
            vecs.append(v)
    blocks = []
    for i in range(nquot):
        W = [] if i == 0 else [rng.randrange(1 << d) for _ in range(rng.randrange(d))]
        span = {0}
        for w in W:
            span |= {s ^ w for s in span}
        reps, rep_of = [], {}
        for a in range(1 << d):
            if a in rep_of:
                continue
            for s in span:
                rep_of[a ^ s] = len(reps)
            reps.append(a)
        blocks.append((reps, rep_of))
    offs, m = [], 0
    for reps, _ in blocks:
        offs.append(m)
        m += len(reps)
    acts = []
    for v in vecs:
        p = [0] * m
        for (reps, rep_of), o in zip(blocks, offs):
            for i, a in enumerate(reps):
                p[o + i] = o + rep_of[a ^ v]
        acts.append(tuple(p))
    # shuffle the positions so that orbits interleave
    sh = list(range(m))
    rng.shuffle(sh)
    acts = [tuple(sh[p[sh.index(q)]] for q in range(m)) for p in acts]
    return acts, m


def orbit_major(acts, m):
    seen, order = [False] * m, []
    for p in range(m):
        if seen[p]:
            continue
        orb, stack = {p}, [p]
        while stack:
            q = stack.pop()
            for g in acts:
                if g[q] not in orb:
                    orb.add(g[q])
                    stack.append(g[q])
        for q in orb:
            seen[q] = True
        order.extend(sorted(orb))
    return order


@pytest.mark.parametrize("seed", range(40))
def test_ea_canon_bruteforce(seed):
    rng = random.Random(seed)
    d = rng.randrange(2, 6)
    k = rng.randrange(1, d + 1)
    acts, m = random_ea_action(rng, d, k, rng.randrange(1, 4))
    E = EA2(m, acts)
    order = orbit_major(acts, m)
    for _ in range(5):
        x = tuple(rng.randrange(rng.randrange(1, 4)) for _ in range(m))
        c, N = EAAction(k, acts, m).canon(x)
        imgs = {}
        for a in range(1 << k):
            y = act(x, E.elem(a))
            imgs[a] = tuple(y[q] for q in order)
        least = min(imgs.values())
        assert imgs[c] == least
        span = {0}
        for v in N:
            span |= {s ^ v for s in span}
        assert len(span) == 1 << len(N)
        assert {c ^ s for s in span} == {a for a, y in imgs.items() if y == least}


def random_group(rng, n):
    gens = []
    for _ in range(rng.randrange(1, 4)):
        p = list(range(n))
        if rng.random() < 0.5:
            rng.shuffle(p)
        else:                           # a product of a few random transpositions
            for _ in range(rng.randrange(1, 3)):
                i, j = rng.sample(range(n), 2)
                p[i], p[j] = p[j], p[i]
        gens.append(tuple(p))
    return PermGroup(n, gens)


@pytest.mark.parametrize("seed", range(60))
def test_perm_canon_bruteforce(seed):
    rng = random.Random(1000 + seed)
    n = rng.randrange(2, 8)
    G = random_group(rng, n)
    elems = list(G.elements())
    for _ in range(4):
        x = tuple(rng.randrange(rng.randrange(1, 4)) for _ in range(n))
        F, lam, gens = perm_canon(G, x)
        assert F == min(act(x, h) for h in elems)
        assert G.contains(lam) and act(x, lam) == F
        stab = [h for h in elems if act(F, h) == F]
        assert all(act(F, g) == F for g in gens)
        assert (PermGroup(n, gens).order() if gens else 1) == len(stab)


def test_perm_canon_young_on_pairs():
    """Sym(A) x Sym(B) on the pairs A x B with a perfect matching (the first
    layer of a hypercube): least image and stabilizer of order |A|!."""
    for q in (3, 4, 5):
        A, B = list(range(q)), list(range(q, 2 * q))
        pairs = [(a, b) for a in A for b in B]
        pidx = {e: i for i, e in enumerate(pairs)}
        gens = []
        for blk in (A, B):
            for g in ([blk[1], blk[0]] + blk[2:], blk[1:] + blk[:1]):
                p = list(range(2 * q))
                for u, v in zip(blk, g):
                    p[u] = v
                gens.append(tuple(pidx[(p[a], p[b])] for a, b in pairs))
        P = PermGroup(len(pairs), gens)
        rng = random.Random(q)
        perm = B[:]
        rng.shuffle(perm)
        x = tuple(1 if b == perm[a] else 0 for a, b in pairs)
        F, lam, auts = perm_canon(P, x)
        assert act(x, lam) == F
        assert sum(F) == q
        assert PermGroup(len(pairs), auts).order() == [1, 1, 2, 6, 24, 120][q]
        # the least image is the same from every start
        for _ in range(5):
            h = mul(gens[rng.randrange(len(gens))], gens[rng.randrange(len(gens))])
            assert perm_canon(P, act(x, h))[0] == F


# -- exhaustive tiny graphs --------------------------------------------------------------------
def all_graphs(n):
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    for mask in range(1 << len(pairs)):
        nbr = [[] for _ in range(n)]
        for b, (i, j) in enumerate(pairs):
            if mask >> b & 1:
                nbr[i].append(j)
                nbr[j].append(i)
        yield nbr


def brute_form(nbr, colors=None):
    """Brute-force canonical form: the least (colors, adjacency string) over
    all n! labellings, and the number of labellings attaining it (= |Aut|)."""
    n = len(nbr)
    E = edge_set(nbr)
    best, cnt = None, 0
    for p in itertools.permutations(range(n)):
        cl = None
        if colors is not None:
            cl = [None] * n
            for v in range(n):
                cl[p[v]] = colors[v]
            cl = tuple(cl)
        s = (cl, tuple(sorted(p[u] * n + p[v] for u, v in E if p[u] < p[v])))
        if best is None or s < best:
            best, cnt = s, 1
        elif s == best:
            cnt += 1
    return best, cnt


@pytest.mark.parametrize("n", [1, 2, 3, 4, 5])
def test_all_graphs_agree_with_brute_force(n):
    """For every labelled graph on n <= 5 vertices: our forms induce exactly the
    brute-force isomorphism classes, and |<aut gens>| = |Aut|."""
    ours, theirs = {}, {}
    for nbr in all_graphs(n):
        form, order = check_labeling(nbr)
        bf, cnt = brute_form(nbr)
        assert order == cnt
        assert ours.setdefault(form, bf) == bf
        assert theirs.setdefault(bf, form) == form


def test_colored_tiny_graphs_agree_with_brute_force():
    rng = random.Random(5)
    ours, theirs = {}, {}
    for _ in range(400):
        n = rng.randrange(2, 7)
        nbr = [[] for _ in range(n)]
        for i in range(n):
            for j in range(i + 1, n):
                if rng.random() < 0.4:
                    nbr[i].append(j)
                    nbr[j].append(i)
        colors = [rng.choice("ab") for _ in range(n)]
        form, order = check_labeling(nbr, colors)
        bf, cnt = brute_form(nbr, colors)
        assert order == cnt
        assert ours.setdefault(form, bf) == bf
        assert theirs.setdefault(bf, form) == form
        nb2, c2 = relabeled(nbr, rng, colors)
        assert canonical_form_lists(nb2, c2) == form


def test_random_small_graphs_against_networkx():
    """Random graphs on 6-9 vertices (dense and sparse): forms agree with VF2's
    isomorphism decision on random pairs, and |Aut| with VF2's count."""
    rng = random.Random(11)
    graphs = []
    for _ in range(120):
        n = rng.randrange(6, 10)
        p = rng.choice([0.2, 0.35, 0.5])
        G = nx.gnp_random_graph(n, p, seed=rng.randrange(10 ** 6))
        graphs.append(lists_of(G))
    forms = []
    for nbr in graphs:
        form, order = check_labeling(nbr)
        assert order == brute_aut_count(nbr)
        forms.append(form)
    for _ in range(600):
        i, j = rng.randrange(len(graphs)), rng.randrange(len(graphs))
        same = nx.is_isomorphic(nx_of(graphs[i]), nx_of(graphs[j]))
        assert (forms[i] == forms[j]) == same


# -- relabeling invariance on bounded-degree families -----------------------------------------
def family_graphs():
    rng = random.Random(3)
    out = []
    for d, n in [(3, 20), (3, 50), (4, 30), (5, 24), (3, 120)]:
        out.append((f"{d}reg{n}", lists_of(nx.random_regular_graph(d, n, seed=rng.randrange(10 ** 6))), None))
    for k in (3, 4, 5, 6):
        out.append((f"Q{k}", lists_of(nx.hypercube_graph(k)), 2 ** k * [1, 1, 2, 6, 24, 120, 720][k]))
    out.append(("petersen", lists_of(nx.petersen_graph()), 120))
    out.append(("dodecahedron", lists_of(nx.dodecahedral_graph()), 120))
    out.append(("grid5x6", lists_of(nx.grid_2d_graph(5, 6)), 4))
    out.append(("torus4x4", lists_of(nx.grid_2d_graph(4, 4, periodic=True)), 384))
    out.append(("tree", lists_of(nx.random_labeled_tree(40, seed=7)) if hasattr(nx, "random_labeled_tree")
                else lists_of(nx.random_tree(40, seed=7)), None))
    out.append(("K33", lists_of(nx.complete_bipartite_graph(3, 3)), 72))
    out.append(("K25", lists_of(nx.complete_bipartite_graph(2, 5)), 240))
    out.append(("star6", lists_of(nx.star_graph(6)), 720))
    out.append(("cycles", lists_of(nx.disjoint_union_all([nx.cycle_graph(5), nx.cycle_graph(5),
                                                           nx.cycle_graph(6), nx.path_graph(3),
                                                           nx.empty_graph(2)])), 10 * 10 * 2 * 12 * 2 * 2))
    base = nx.random_regular_graph(3, 8, seed=1)
    out.append(("CFI(3reg8)", lists_of(cfi(base)), None))
    out.append(("CFI(K4)", lists_of(cfi(nx.complete_graph(4))), None))
    return out


@pytest.mark.parametrize("name,nbr,aut", family_graphs(), ids=lambda v: v if isinstance(v, str) else "")
def test_relabel_invariance(name, nbr, aut):
    rng = random.Random(sum(map(ord, name)))
    form, order = check_labeling(nbr)
    if aut is not None:
        assert order == aut
    res = bounded_iso_lists(nbr, nbr)
    assert order == (PermGroup(len(nbr), res[1]).order() if res[1] else 1)
    for _ in range(8):
        assert canonical_form_lists(relabeled(nbr, rng)) == form
    for layers in ("bfs",):
        f2 = canonical_form_lists(nbr, layers=layers)
        assert all(canonical_form_lists(relabeled(nbr, rng), layers=layers) == f2 for _ in range(3))


def test_disconnected_and_colored():
    rng = random.Random(9)
    P = nx.petersen_graph()
    G = nx.disjoint_union_all([P, P, nx.cycle_graph(4), nx.cycle_graph(4), nx.empty_graph(3)])
    nbr = lists_of(G)
    n = len(nbr)
    form, order = check_labeling(nbr)
    assert order == 120 * 120 * 2 * 8 * 8 * 2 * 6
    colors = [rng.choice([0, 1, 2]) for _ in range(n)]
    cf, co = check_labeling(nbr, colors)
    assert co == brute_aut_count(nbr, colors)
    for _ in range(5):
        assert canonical_form_lists(relabeled(nbr, rng)) == form
        nb2, c2 = relabeled(nbr, rng, colors)
        assert canonical_form_lists(nb2, c2) == cf
    # colors are part of the form
    c3 = [c + 10 for c in colors]
    assert canonical_form_lists(nbr, c3) != cf
    assert canonical_form_lists(nbr, c3)[2] == cf[2]


def test_matrix_interface_and_canon_iso():
    rng = random.Random(4)
    G = nx.random_regular_graph(3, 30, seed=2)
    nbr = lists_of(G)
    n = len(nbr)
    A = [[0] * n for _ in range(n)]
    for u in range(n):
        for v in nbr[u]:
            A[u][v] = 1
    assert canonical_form(A) == canonical_form_lists(nbr)
    assert canonical_labeling(A)[0] == canonical_labeling_lists(nbr)[0]
    Y = relabeled(nbr, rng)
    B = [[0] * n for _ in range(n)]
    for u in range(n):
        for v in Y[u]:
            B[u][v] = 1
    sigma, gens = canon_iso(A, B)
    EY = edge_set(Y)
    assert all((sigma[u], sigma[v]) in EY for u, v in edge_set(nbr))
    other = lists_of(nx.random_regular_graph(3, 30, seed=3))
    assert (canon_iso_lists(nbr, other) is None) == (not nx.is_isomorphic(G, nx_of(other)))


# -- non-isomorphic pairs that defeat refinement ---------------------------------------------
@pytest.mark.parametrize("seed", range(3))
def test_cfi_twisted_pairs(seed):
    rng = random.Random(seed)
    for d, b in [(3, 8), (3, 12), (4, 6)]:
        base = nx.random_regular_graph(d, b, seed=100 * seed + b)
        if not nx.is_connected(base):
            continue
        X, Xt = lists_of(cfi(base)), lists_of(cfi(base, True))
        fx = canonical_form_lists(X)
        assert canonical_form_lists(relabeled(X, rng)) == fx
        assert canonical_form_lists(relabeled(Xt, rng)) != fx
        assert canonical_form_lists(relabeled(Xt, rng)) == canonical_form_lists(Xt)


@pytest.mark.parametrize("fam,size", [("ns", 4), ("ns", 8), ("ns", 16), ("cfix", 10), ("cfix", 20),
                                      ("nst", 8), ("nsr", 8)])
def test_irhard_pairs(fam, size):
    """Neuen-Schweitzer multipedes (answers known by their lemma), CFI over
    random cubic graphs, shrunken multipedes: forms equal exactly on the
    isomorphic pairs; |Aut| = 1 on ns/nsr."""
    insts = irhard.FAMILIES[fam](size, random.Random(7919 * size))
    fx = None
    for I in insts:
        if fx is None:
            fx, order = check_labeling(I["X"])
            if I["aut"] is not None:
                assert order == I["aut"]
            else:
                res = bounded_iso_lists(I["X"], I["X"])
                assert order == (PermGroup(len(I["X"]), res[1]).order() if res[1] else 1)
        fy = canonical_form_lists(I["Y"])
        claim = I["claim"]
        if claim is None:
            claim = bounded_iso_lists(I["X"], I["Y"]) is not None
        assert (fy == fx) == claim


def test_random_regular_other_graphs():
    """Random regular graphs: a relabeled copy has the same form, a second random
    graph (non-isomorphic w.h.p., checked by VF2) a different one."""
    rng = random.Random(21)
    for d, n in [(3, 40), (4, 40), (3, 200)]:
        X = lists_of(nx.random_regular_graph(d, n, seed=n + d))
        Z = lists_of(nx.random_regular_graph(d, n, seed=n + d + 1000))
        fx = canonical_form_lists(X)
        assert canonical_form_lists(relabeled(X, rng)) == fx
        assert (canonical_form_lists(Z) == fx) == nx.is_isomorphic(nx_of(X), nx_of(Z))


def structured_graphs():
    out = [("heawood", nx.heawood_graph()), ("tutte-coxeter", nx.LCF_graph(30, [-13, -9, 7, -7, 9, 13], 5)),
           ("mobius-kantor", nx.LCF_graph(16, [5, -5], 8)), ("desargues", nx.desargues_graph()),
           ("pappus", nx.pappus_graph()), ("K4xC5", nx.cartesian_product(nx.complete_graph(4), nx.cycle_graph(5))),
           ("C4xC4xC3", nx.cartesian_product(nx.cartesian_product(nx.cycle_graph(4), nx.cycle_graph(4)),
                                             nx.cycle_graph(3))),
           ("K33xK2", nx.cartesian_product(nx.complete_bipartite_graph(3, 3), nx.complete_graph(2))),
           ("circulant", nx.circulant_graph(30, [1, 4, 11])), ("line(petersen)", nx.line_graph(nx.petersen_graph())),
           ("hex", nx.hexagonal_lattice_graph(3, 4)), ("tri", nx.triangular_lattice_graph(3, 5))]
    G = nx.hypercube_graph(5)
    G.remove_edge(*sorted(G.edges())[0])
    out.append(("Q5-minus-edge", G))
    base = nx.random_regular_graph(4, 6, seed=3)
    out.append(("CFI(4reg6)", cfi(base)))
    out.append(("CFI(4reg6)-twist", cfi(base, True)))
    return [(name, lists_of(G)) for name, G in out]


def test_structured_graphs_exercise_all_paths():
    """Vertex-transitive and product graphs, CFI over a 4-regular base: these
    reach the permutation-group path in both phases (non-abelian layer groups
    with non-invariant strings) as well as the elementary abelian one."""
    rng = random.Random(17)
    total = Counter()
    forms = {}
    for name, nbr in structured_graphs():
        st = Counter()
        canonical_labeling_lists(nbr, stats=st)
        total.update(st)
        form, order = check_labeling(nbr)
        res = bounded_iso_lists(nbr, nbr)
        assert order == (PermGroup(len(nbr), res[1]).order() if res[1] else 1), name
        for _ in range(4):
            assert canonical_form_lists(relabeled(nbr, rng)) == form, name
        forms[name] = (form, nbr)
    fa, Xa = forms["CFI(4reg6)"]
    fb, Xb = forms["CFI(4reg6)-twist"]
    assert fa != fb and bounded_iso_lists(Xa, Xb) is None
    for key in ("canon_perm_p1", "canon_perm_p2", "canon_invariant"):
        assert total[key] > 0, key
    st = Counter()
    canonical_labeling_lists(irhard.FAMILIES["nst"](16, random.Random(1))[0]["X"], stats=st)
    assert st["canon_ea_p1"] > 0 and st["canon_ea_p2"] > 0


def _small_base(rng):
    while True:
        n = rng.randrange(3, 7)
        G = nx.gnm_random_graph(n, rng.randrange(n - 1, min(n * (n - 1) // 2, 2 * n) + 1),
                                seed=rng.randrange(10 ** 6))
        if nx.is_connected(G) and max(dict(G.degree()).values()) <= 4:
            return G


def _lift(B, k, rng):
    G = nx.Graph()
    G.add_nodes_from((v, i) for v in B.nodes() for i in range(k))
    for u, v in B.edges():
        p = list(range(k))
        rng.shuffle(p)
        G.add_edges_from(((u, i), (v, p[i])) for i in range(k))
    return G


def _cfi_random_twists(B, rng):
    G = nx.Graph()
    E = [tuple(sorted(e)) for e in B.edges()]
    tw = {e: rng.randrange(2) for e in E}
    for v in B.nodes():
        es = [tuple(sorted(e)) for e in B.edges(v)]
        G.add_nodes_from(("o", v, e, c) for e in es for c in (0, 1))
        for bits in itertools.product((0, 1), repeat=len(es)):
            if sum(bits) % 2 == 0:
                G.add_edges_from((("m", v, bits), ("o", v, e, c)) for e, c in zip(es, bits))
    for u, v in E:
        G.add_edges_from((("o", u, (u, v), c), ("o", v, (u, v), c ^ tw[(u, v)])) for c in (0, 1))
    return G


@pytest.mark.parametrize("seed", range(4))
def test_structured_random_graphs(seed):
    """Random covers (lifts) of small graphs, products of small graphs and CFI
    graphs with random twists: these have nontrivial non-abelian layer groups
    and WL-equivalent non-isomorphic pairs. Forms against gi.bounded's
    isomorphism test on pairs of equal size, |Aut| against its group, and
    relabeling invariance."""
    rng = random.Random(500 + seed)
    items = []
    for _ in range(40):
        t = rng.randrange(3)
        if t == 0:
            G = _lift(_small_base(rng), rng.randrange(2, 4), rng)
        elif t == 1:
            G = nx.cartesian_product(_small_base(rng), _small_base(rng))
        else:
            G = _cfi_random_twists(_small_base(rng), rng)
        nbr = lists_of(G)
        form, order = check_labeling(nbr)
        res = bounded_iso_lists(nbr, nbr)
        assert order == (PermGroup(len(nbr), res[1]).order() if res[1] else 1)
        assert canonical_form_lists(relabeled(nbr, rng)) == form
        items.append((form, nbr))
    by = {}
    for form, nbr in items:
        by.setdefault((len(nbr), sum(map(len, nbr))), []).append((form, nbr))
    for L in by.values():
        for (f1, n1), (f2, n2) in itertools.combinations(L, 2):
            assert (f1 == f2) == (bounded_iso_lists(n1, n2) is not None)
