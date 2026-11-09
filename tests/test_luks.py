"""The Luks canonizer of strings (gi/luks.py) and its use in gi/canon.py:
canonicity (the form depends only on the group as a set and the orbit of the
string), Aut against enumeration of the group, method selection, and the
adversarial families of bench/adversary.py (forms equal under relabelling,
different on non-isomorphic pairs, Aut checked, no exponential path used at
degree <= 5)."""
import math
import random
import sys
from collections import Counter

import networkx as nx
import pytest

from gi.group import PermGroup, ActionHom, RestrictionHom
from gi.luks import luks_canon, LimitExceeded, enum_limit_default
from gi.perm import act, mul, inv, sym_gens, alt_gens, cycle
from gi.canon import canonical_form_lists, canonical_labeling_lists, relabel_lists, _form_of
from bench import adversary, irhard


def rand_elem(G, rng):
    e = G.idn
    for _ in range(30):
        s = rng.choice(G.gens) if G.gens else G.idn
        e = mul(e, s if rng.random() < .7 else inv(s))
    return e


def wreath(n, b, top):
    """Sym(b) wr (top on the n//b blocks), top a list of block permutations."""
    m = n // b
    gens = []
    for i in range(m):
        gens += sym_gens(n, [i * b + j for j in range(b)])
    for t in top:
        g = list(range(n))
        for i in range(m):
            for j in range(b):
                g[i * b + j] = t[i] * b + j
        gens.append(tuple(g))
    return gens


def tree_wreath(n):
    gens = []

    def rec(lo, hi):
        if hi - lo < 2:
            return
        mid = (lo + hi) // 2
        p = list(range(n))
        for j in range(mid - lo):
            p[lo + j], p[mid + j] = mid + j, lo + j
        gens.append(tuple(p))
        rec(lo, mid)
        rec(mid, hi)
    rec(0, n)
    return gens


def random_group(n, rng):
    t = rng.randrange(7)
    if t == 0:
        return PermGroup(n, [tuple(rng.sample(range(n), n)) for _ in range(rng.randrange(1, 4))])
    if t == 1 and n >= 4:
        b = rng.choice([2, 3])
        m = n // b
        return PermGroup(n, wreath(m * b, b, [[(i + 1) % m for i in range(m)]]) if m > 1 else wreath(b, b, [])) \
            if n == m * b else PermGroup(n, [])
    if t == 2:
        pts = list(range(n))
        rng.shuffle(pts)
        gens, i = [], 0
        while i < n:
            sz = rng.choice([1, 2, 3, 4])
            gens += sym_gens(n, pts[i:i + sz])
            i += sz
        return PermGroup(n, gens)
    if t == 3:
        g = list(range(n))
        rng.shuffle(g)
        return PermGroup(n, [tuple(g)])
    if t == 4:
        pts = list(range(n))
        rng.shuffle(pts)
        gens, i = [], 0
        while i + 2 < n:
            gens.append(cycle(n, pts[i:i + 3]))
            i += 3
        return PermGroup(n, gens)
    if t == 5:
        k = n.bit_length() - 1
        return PermGroup(n, tree_wreath(1 << k) if n == 1 << k else [])
    # elementary abelian
    pts = list(range(n))
    rng.shuffle(pts)
    gens, i = [], 0
    while i + 1 < n:
        gens.append(cycle(n, pts[i:i + 2]))
        i += 2
    return PermGroup(n, gens)


def check_group(G, x, rng):
    n = G.n
    F, lam, gens = luks_canon(G, x)
    assert act(x, lam) == F
    assert G.contains(lam)
    for a in gens:
        assert G.contains(a) and act(F, a) == F
    for _ in range(3):                  # canonical on the orbit of x
        h = rand_elem(G, rng)
        y = act(x, h)
        Fy, ly, _ = luks_canon(G, y)
        assert Fy == F and act(y, ly) == Fy
    if G.gens:                          # a different generating set of the same group
        G2 = PermGroup(n, [rand_elem(G, rng) for _ in range(len(G.gens) + 3)])
        if G2.order() == G.order():
            assert luks_canon(G2, x)[0] == F
    if G.order() <= 3000:               # Aut against listing the group
        count = sum(1 for g in G.elements() if act(F, g) == F)
        U = PermGroup(n, gens) if gens else PermGroup(n)
        assert U.order() == count
    return F


@pytest.mark.parametrize("seed", range(4))
def test_random_groups(seed):
    rng = random.Random(1000 + seed)
    for _ in range(80):
        n = rng.randrange(2, 15)
        G = random_group(n, rng)
        x = tuple(rng.randrange(rng.choice([2, 3, 4])) for _ in range(n))
        check_group(G, x, rng)


def test_structured_groups_exercise_all_paths():
    """Natural giants, small groups (listed), elementary abelian groups,
    imprimitive groups (blocks and cosets), products, and the chain rule."""
    rng = random.Random(7)
    st = Counter()
    groups = [
        PermGroup(6, sym_gens(6, list(range(6)))),
        PermGroup(7, alt_gens(7, list(range(7)))),
        PermGroup(5, [cycle(5, [0, 1, 2, 3, 4])]),                          # Z_5 (primitive, listed)
        PermGroup(9, wreath(9, 3, [[1, 2, 0], [1, 0, 2]])),                  # S_3 wr S_3
        PermGroup(16, wreath(16, 2, [[1, 2, 3, 0, 5, 6, 7, 4], [4, 5, 6, 7, 0, 1, 2, 3]])),
        PermGroup(8, tree_wreath(8)),
        PermGroup(16, tree_wreath(16)),
        PermGroup(10, sym_gens(10, [0, 1, 2]) + sym_gens(10, [5, 6, 7, 8])),     # a direct product
        PermGroup(12, [(1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10), (2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9)]),
    ]
    for G in groups:
        for _ in range(6):
            x = tuple(rng.randrange(3) for _ in range(G.n))
            check_group(G, x, rng)
            luks_canon(G, x, st)
    for key in ("canon_luks_calls", "canon_luks_nodes", "canon_luks_giant", "canon_luks_listed", "canon_luks_cosets"):
        assert st[key] > 0, key


@pytest.mark.parametrize("n", [3, 4, 5, 6])
def test_alternating_points_is_least_image(n):
    """On a natural Alt(n) the form is the least even image (it is also the
    least image, by listing Alt(n))."""
    rng = random.Random(n)
    G = PermGroup(n, alt_gens(n, list(range(n))))
    for _ in range(10):
        x = tuple(rng.randrange(n) if rng.random() < .5 else i for i, _ in enumerate(range(n)))
        F, lam, _ = luks_canon(G, x)
        assert F == min(act(x, g) for g in G.elements())


def test_symmetric_points_sorted():
    n = 6
    G = PermGroup(n, sym_gens(n, list(range(n))))
    x = (3, 1, 2, 1, 0, 2)
    F, lam, gens = luks_canon(G, x)
    assert F == tuple(sorted(x)) and act(x, lam) == F
    assert PermGroup(n, gens).order() == 4      # value classes of sizes 1, 2, 2, 1: 2! 2!


def test_strict_limit():
    """Z_2 wr S_8 on 16 points has a primitive quotient S_8 on 8 blocks of
    order 40320 > enum_limit_default(8), so the strict mode refuses it and
    the default falls back to the exact search, canonically."""
    b, m = 2, 8
    G = PermGroup(16, wreath(16, b, [[1, 0, 2, 3, 4, 5, 6, 7], [1, 2, 3, 4, 5, 6, 7, 0]]))
    x = tuple(int(i % 3 == 0) for i in range(16))
    with pytest.raises(LimitExceeded):
        luks_canon(G, x, strict=True)
    st = Counter()
    F, _, _ = luks_canon(G, x, st)
    assert st["canon_luks_fallback"] >= 1
    rng = random.Random(3)
    for _ in range(4):
        y = act(x, rand_elem(G, rng))
        assert luks_canon(G, y)[0] == F
    # a solvable group never exceeds the limit (Palfy-Wolf)
    G2 = PermGroup(16, wreath(16, 2, [[1, 0, 2, 3, 4, 5, 6, 7], [2, 3, 0, 1, 6, 7, 4, 5], [4, 5, 6, 7, 0, 1, 2, 3]]))
    luks_canon(G2, x, strict=True)


def test_enum_limit_covers_solvable_primitive():
    """The largest solvable primitive groups are within the limit: a sanity
    check of the arithmetic of the Palfy-Wolf bound (degrees p^a)."""
    for k in (2, 3, 4, 8, 9, 16, 25, 27, 81, 256, 625, 729, 6561):
        assert 24 ** (-1 / 3) * k ** 3.24399 < enum_limit_default(k)
    assert enum_limit_default(7) == 5040


# -- graph level: the adversarial families ------------------------------------------------------
def lists_order(gens, n):
    return PermGroup(n, gens).order() if gens else 1


def check_labeling(X, st=None, **kw):
    n = len(X)
    lab, gens = canonical_labeling_lists(X, stats=st, **kw)
    assert sorted(lab) == list(range(n))
    E = {(u, v) for u in range(n) for v in X[u]}
    for g in gens:
        assert all((g[u], g[v]) in E for u, v in E)
    return _form_of(X, lab, None), lists_order(gens, n)


def family_instances():
    rng = random.Random(40)
    out = []
    out += adversary.FAMILIES["cfi3"](6, rng)
    out += adversary.FAMILIES["cfi3"](10, rng)
    out += adversary.FAMILIES["tm"](3, rng)
    out += adversary.FAMILIES["tm"](4, rng)
    out += adversary.FAMILIES["tb3"](3, rng)
    out += adversary.FAMILIES["tb4"](2, rng)
    out += adversary.FAMILIES["cfit"](6, rng)
    out += adversary.FAMILIES["nst3"](4, rng)
    return out


@pytest.mark.parametrize("I", family_instances(), ids=lambda I: I["name"])
def test_adversarial_families(I):
    X, Y = I["X"], I["Y"]
    fx, ox = check_labeling(X)
    fy, oy = check_labeling(Y)
    claim = I["claim"]
    if claim is None:                   # (a random other matching: answer from VF2)
        claim = nx.is_isomorphic(nx.Graph([(u, v) for u, r in enumerate(X) for v in r]),
                                 nx.Graph([(u, v) for u, r in enumerate(Y) for v in r]))
    assert (fx == fy) == claim
    if fx == fy:
        assert ox == oy
    rng = random.Random(9)
    assert canonical_form_lists(relabel_lists(X, rng.sample(range(len(X)), len(X)))) == fx
    # guarantee mode: another canonizer, with the same decisions
    g1 = canonical_form_lists(X, guarantee=True)
    g2 = canonical_form_lists(Y, guarantee=True)
    assert (g1 == g2) == (fx == fy)
    assert canonical_form_lists(relabel_lists(X, rng.sample(range(len(X)), len(X))), guarantee=True) == g1


def test_degree_at_most_5_uses_no_exponential_path():
    """At maximum degree <= 5 the default never reaches ir_canon or the
    least-image search, on the adversarial families and on random graphs."""
    rng = random.Random(5)
    fams = [("cfi3", 8), ("tm", 4), ("tb3", 3), ("tb4", 2), ("cfit", 8)]
    for fam, size in fams:
        for I in adversary.FAMILIES[fam](size, rng):
            assert max(map(len, I["X"])) <= 5
            st = Counter()
            canonical_labeling_lists(I["X"], stats=st)
            assert st["canon_ir"] == 0 and st["canon_luks_fallback"] == 0 and st["canon_perm_nodes"] == 0, fam
    from bench.adversary import add_triple
    for s in range(30):
        n = rng.randrange(10, 40)
        G = nx.random_regular_graph(rng.choice([3, 4]), n if n % 2 == 0 else n + 1, seed=s)
        X = [sorted(G.neighbors(v)) for v in sorted(G.nodes())]
        X = add_triple(X, 0)
        st = Counter()
        check_labeling(X, st)
        assert st["canon_ir"] == 0 and st["canon_luks_fallback"] == 0 and st["canon_perm_nodes"] == 0


def test_ir_path_kept_for_large_twin_blocks():
    """A twin block of >= 5 in a layer where the group fixes the blocks still
    uses ir_canon by default, and guarantee=True avoids it, with equal
    decisions."""
    # K_{1,5}-like: two adjacent centers with 5 leaves each, plus a matching between the leaf sets
    nb = 2 + 10
    X = [[] for _ in range(nb)]
    def edge(a, b):
        X[a].append(b)
        X[b].append(a)
    edge(0, 1)
    for i in range(5):
        edge(0, 2 + i)
        edge(1, 7 + i)
        edge(2 + i, 7 + i)
    st = Counter()
    f1, o1 = check_labeling(X, st)
    assert st["canon_ir"] >= 1
    st = Counter()
    f2, o2 = check_labeling(X, st, guarantee=True)
    assert st["canon_ir"] == 0
    assert o1 == o2
    rng = random.Random(1)
    Y = relabel_lists(X, rng.sample(range(nb), nb))
    assert canonical_form_lists(Y) == f1 and canonical_form_lists(Y, guarantee=True) == f2


# -- referee tests (docs/redteam-w40-solvable.md) ---------------------------------------------------
def test_palfy_wolf_constant_exact():
    """Wolf 1982, Theorem 3.1 and Corollary 3.3: a solvable primitive group of degree k has order at most
    k^(alpha + 1) / 24^(1/3), alpha = (3 log 48 + log 24) / (3 log 9) = 2.24399...; equality for AGL(2, 3)
    at k = 9, so the exponent cannot be rounded down."""
    alpha = (3 * math.log(48) + math.log(24)) / (3 * math.log(9))
    bound = lambda k: k ** (alpha + 1) / 24 ** (1 / 3)
    assert math.isclose(bound(9), 432)
    assert 24 ** (-1 / 3) * 9 ** 3.2439 < 432            # (3.2439 is too small at k = 9)
    for k in (2, 3, 4, 5, 7, 8, 9, 16, 25, 27, 81, 256, 625, 729, 6561, 3 ** 12):
        assert bound(k) < k ** 4 <= enum_limit_default(k) or k < 7


@pytest.mark.parametrize("seed", range(20))
def test_ea_kernels_have_a_basis_as_generators(seed):
    """The elementary abelian test of gi.luks reads the number of generators: a kernel must not have
    redundant ones, whatever generating set of G it came from."""
    rng = random.Random(seed)
    a = rng.randint(2, 5)
    m = 1 << a
    n = 2 * m
    gens = []
    for i in range(a):
        g = list(range(n))
        for x in range(m):
            g[x] = x ^ (1 << i)
            g[m + x] = m + (x ^ (1 << ((i + 1) % a)))
        gens.append(tuple(g))
    swap = tuple(list(range(m, n)) + list(range(m)))
    base = gens + [swap]

    def rnd():
        e = tuple(range(n))
        for _ in range(12):
            e = mul(e, rng.choice(base))
        return e
    G = PermGroup(n, [rnd() for _ in range(rng.randint(3, 8))] + base)
    side = lambda g: (0 if g[0] < m else 1, 0 if g[m] < m else 1)
    N = ActionHom(G, 2, side).kernel()
    assert N.order() == 1 << len(N.gens)
    F = PermGroup(n, gens + [tuple(rng.sample(gens, 1)[0])])    # (intransitive: O1, O2 orbits)
    N2 = RestrictionHom(F, list(range(m))).kernel()
    assert N2.order() == 1 or N2.order() == 1 << len(N2.gens)


def twin_gadget(k, t):
    """A binary tree with a tail on its root; k of its leaves (all at one depth) carry a twin t-set each;
    t further vertices each joined to the j-th twin of every such leaf. Twin blocks have size t, maximum degree is
    max(k, t + 1), and the up-set of a further vertex has t^k images under the group."""
    D = 0
    while (1 << D) < k:
        D += 1
    nbr, level = [[]], [0]
    for _ in range(D):
        nxt = []
        for p in level:
            for _ in range(2):
                v = len(nbr)
                nbr.append([p])
                nbr[p].append(v)
                nxt.append(v)
        level = nxt
    W = [[] for _ in range(t)]
    for s in level[:k]:
        for j in range(t):
            v = len(nbr)
            nbr.append([s])
            nbr[s].append(v)
            W[j].append(v)
    for j in range(t):
        w = len(nbr)
        nbr.append(list(W[j]))
        for a in W[j]:
            nbr[a].append(w)
    prev = 0
    for _ in range(4):
        u = len(nbr)
        nbr.append([prev])
        nbr[prev].append(u)
        prev = u
    return nbr


def test_product_action_section_at_degree_5():
    """Sym(3) wr D4 in product action on 81 up-sets (primitive, solvable): degree 5, one listed node, no
    exponential path, forms invariant."""
    X = twin_gadget(4, 3)
    assert max(map(len, X)) <= 5
    st = Counter()
    fx, _ = check_labeling(X, st)
    assert st["canon_phase1_max_degree"] == 81
    assert st["canon_ir"] == 0 and st["canon_luks_fallback"] == 0 and st["canon_perm_nodes"] == 0
    rng = random.Random(1)
    assert canonical_form_lists(relabel_lists(X, rng.sample(range(len(X)), len(X)))) == fx


def test_twin_blocks_alone_do_not_bound_the_position_domain():
    """Theorem A of docs/w40-solvable.md is polynomial only for bounded degree: with twin blocks of 3 and
    degree k the phase-1 domain has 3^k points (the bound m <= 2 n^d is attained in spirit)."""
    Y = twin_gadget(6, 3)                               # twin blocks of 3, degree 6
    st = Counter()
    canonical_labeling_lists(Y, stats=st)
    assert max(map(len, Y)) == 6
    assert st["canon_phase1_max_degree"] == 3 ** 6
    assert st["canon_ir"] == 0 and st["canon_luks_fallback"] == 0
