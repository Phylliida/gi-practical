"""The optimized group layer must give exactly the results of the baseline code
(tests/_ref_group.py): same chains, element order, lifts, kernels and block
systems. Run: python3 -m pytest -q tests"""
import math
import os
import random
import sys

import pytest

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import _ref_group as ref
from gi import group as gg
from gi.perm import mul


def rand_perm(n, rng, pts=None):
    pts = list(range(n)) if pts is None else list(pts)
    img = pts[:]
    rng.shuffle(img)
    p = list(range(n))
    for a, b in zip(pts, img):
        p[a] = b
    return tuple(p)


def imprimitive_gen(n, a, rng):
    """A permutation of range(n) (n = a*b) preserving the blocks {i*a..i*a+a-1}."""
    b = n // a
    top = rand_perm(b, rng)
    p = [0] * n
    for i in range(b):
        inner = rand_perm(a, rng)
        for j in range(a):
            p[i * a + j] = top[i] * a + inner[j]
    return tuple(p)


def random_groups(seed, count):
    rng = random.Random(seed)
    out = []
    for _ in range(count):
        kind = rng.randrange(5)
        if kind == 0:
            n = rng.randint(2, 9)
            gens = [rand_perm(n, rng) for _ in range(rng.randint(1, 3))]
        elif kind == 1:
            a, b = rng.choice([(2, 2), (2, 3), (3, 2), (2, 4), (4, 2), (3, 3)])
            n = a * b
            gens = [imprimitive_gen(n, a, rng) for _ in range(rng.randint(1, 3))]
        elif kind == 2:                     # intransitive
            n = rng.randint(4, 10)
            cut = rng.randint(1, n - 1)
            gens = [mul(rand_perm(n, rng, range(cut)), rand_perm(n, rng, range(cut, n)))
                    for _ in range(rng.randint(1, 3))]
        elif kind == 3:                     # small cyclic / dihedral-like
            n = rng.randint(3, 12)
            c = tuple((i + 1) % n for i in range(n))
            r = tuple((-i) % n for i in range(n))
            gens = [c] + ([r] if rng.random() < 0.5 else [])
        else:                               # sparse generators with fixed points
            n = rng.randint(3, 10)
            gens = []
            for _ in range(rng.randint(1, 4)):
                k = rng.randint(2, min(4, n))
                gens.append(rand_perm(n, rng, rng.sample(range(n), k)))
        out.append((n, gens))
    return out


GROUPS = random_groups(7, 150)


@pytest.fixture(autouse=True, params=["cache", "nocache"])
def chain_cache(request, monkeypatch):
    """Run every test with and without the chain cache."""
    gg.clear_chain_cache()
    if request.param == "nocache":
        monkeypatch.setattr(gg, "CHAIN_CACHE_LIMIT", 0)
    yield
    gg.clear_chain_cache()


def chain(G):
    return (list(G.base), [list(S) for S in G.S], [list(T.items()) for T in G.T],
            [list(T.items()) for T in G.Ti], list(G.gens))


def test_chain_identical():
    for n, gens in GROUPS:
        R = ref.PermGroup(n, gens)
        gg.clear_chain_cache()
        assert chain(gg.PermGroup(n, gens)) == chain(R)
        assert chain(gg.PermGroup(n, gens)) == chain(R)                 # cache hit
        gg.clear_chain_cache()
        assert chain(gg.PermGroup(n, gens, order=R.order())) == chain(R)
        assert chain(gg.PermGroup(n, gens)) == chain(R)                 # cached early-stop chain
        base = random.Random(n).sample(range(n), min(3, n))
        Rb = ref.PermGroup(n, gens, base=base)
        assert chain(gg.PermGroup(n, gens, base=base, order=R.order())) == chain(Rb)
        if R.order() <= 2000:
            assert list(gg.PermGroup(n, gens).elements()) == list(R.elements())
        G = gg.PermGroup(n, gens)
        pts = sorted(random.Random(len(gens)).sample(range(n), min(2, n)))
        assert chain(G.pointwise_stabilizer(pts)) == chain(R.pointwise_stabilizer(pts))
        assert chain(G.stabilizer(n - 1)) == chain(R.stabilizer(n - 1))


def test_wrong_order_detected():
    """A wrong `order` is caught when the orbit product passes it, or on a cache
    hit (a value the product happens to reach exactly is not caught)."""
    gens = [(1, 2, 3, 0), (1, 0, 2, 3)]
    gg.clear_chain_cache()
    with pytest.raises(ValueError):
        gg.PermGroup(4, gens, order=5)
    assert gg.PermGroup(4, gens).order() == 24
    if gg.CHAIN_CACHE_LIMIT > 0:
        with pytest.raises(ValueError):
            gg.PermGroup(4, gens, order=12)


def test_restriction_hom():
    for n, gens in GROUPS:
        R = ref.PermGroup(n, gens)
        G = gg.PermGroup(n, gens)
        for D in R.orbits():
            if len(D) == n:
                continue
            idx = {d: i for i, d in enumerate(D)}
            rho_r = ref.ActionHom(R, len(D), lambda g: tuple(idx[g[d]] for d in D))
            rho = gg.RestrictionHom(G, D)
            assert rho.image_order() == rho_r.image_order()
            assert chain(rho.image_group()) == chain(rho_r.image_group())
            assert chain(rho.kernel()) == chain(rho_r.kernel())
            for g in gens:
                assert rho.image_of(g) == rho_r.image_of(g)
            if rho_r.image_order() <= 500:
                for p in rho_r.image_group().elements():
                    assert rho.lift(p) == rho_r.lift(p)


def test_action_homs():
    for n, gens in GROUPS:
        R = ref.PermGroup(n, gens)
        G = gg.PermGroup(n, gens)
        # identity
        idr = ref.ActionHom(R, n, lambda g: g)
        idh = gg.ActionHom(G, n, None)
        assert idh.image_order() == idr.image_order()
        assert chain(idh.image_group()) == chain(idr.image_group())
        assert chain(idh.kernel()) == chain(idr.kernel())
        for g in gens:
            assert idh.lift(g) == idr.lift(g)
        # action on the orbit of 0 shifted, through the combined group
        orb = R.orbits([0])[0]
        idx = {d: i for i, d in enumerate(orb)}
        f = lambda g: tuple(idx[g[d]] for d in orb)
        hr = ref.ActionHom(R, len(orb), f)
        h = gg.ActionHom(G, len(orb), f)
        assert chain(h.C) == chain(hr.C)
        assert chain(h.kernel()) == chain(hr.kernel())
        assert chain(h.image_group()) == chain(hr.image_group())
        if hr.image_order() <= 500:
            for p in hr.image_group().elements():
                assert h.lift(p) == hr.lift(p)
            hs = list(hr.image_group().gens[:1])
            Hr = ref.PermGroup(n, [hr.lift(x) for x in hs] + hr.kernel().gens)
            assert chain(h.preimage(hs)) == chain(Hr)


def test_blocks_and_support():
    for n, gens in GROUPS:
        R = ref.PermGroup(n, gens)
        if len(R.orbits()) != 1:
            continue
        G = gg.PermGroup(n, gens)
        assert gg.minimal_block_labels(n, G.gens, gg.stabilizer_orbit_reps(G)) == \
            ref.minimal_block_labels(n, R.gens)
        assert gg.minimal_block_labels(n, G.gens) == ref.minimal_block_labels(n, R.gens)
        assert gg.top_block_system(G) == ref.top_block_system(R)
        for a in range(1, n):
            assert gg.minimal_block(n, G.gens, 0, a) == ref.minimal_block(n, R.gens, 0, a)
        # label support for the action on blocks (or the identity action)
        blocks = ref.top_block_system(R) or [[p] for p in range(n)]
        where = {p: i for i, B in enumerate(blocks) for p in B}
        f = lambda g: tuple(where[g[B[0]]] for B in blocks)
        phi = gg.ActionHom(G, len(blocks), f)
        R0 = ref.PermGroup(n, R.gens, base=[0])
        imgs = [f(h) for h in R0._tail(1).gens]
        F0 = [a for a in range(len(blocks)) if all(im[a] == a for im in imgs)]
        supp = [None] * n
        for w, u in R0.T[0].items():
            im = f(u)
            supp[w] = tuple(im[a] for a in F0)
        assert gg.label_support(G, phi) == (F0, supp)


def test_isomorphisms():
    rng = random.Random(3)
    for n, gens in GROUPS:
        G = gg.PermGroup(n, gens)
        if G.order() > 3000:
            continue
        for _ in range(4):
            x = tuple(rng.randrange(2) for _ in range(n))
            g = rng.choice(list(G.elements()))
            y = ref.act(x, g) if rng.random() < 0.7 else tuple(rng.randrange(2) for _ in range(n))
            assert G.isomorphisms(x, y) == [h for h in G.elements() if ref.maps(h, x, y)]
            K = G.stabilizer(n - 1)
            assert K.isomorphisms(x, y) == [h for h in K.elements() if ref.maps(h, x, y)]


def test_johnson_labels():
    import itertools
    rng = random.Random(5)
    for m in (5, 6, 7):
        pairs = list(itertools.combinations(range(m), 2))
        relabel = list(range(len(pairs)))
        rng.shuffle(relabel)
        idx = {pr: relabel[i] for i, pr in enumerate(pairs)}

        def on_pairs(s):
            p = [0] * len(pairs)
            for pr in pairs:
                a, b = sorted((s[pr[0]], s[pr[1]]))
                p[idx[pr]] = idx[(a, b)]
            return tuple(p)

        for alt in (False, True):
            gens = []
            for _ in range(3):
                s = rand_perm(m, rng)
                if alt and ref.parity(s):
                    s = mul(s, ref.cycle(m, [0, 1]))
                gens.append(on_pairs(s))
            R = ref.PermGroup(len(pairs), gens)
            G = gg.PermGroup(len(pairs), gens)
            jr, jg = ref.johnson_labels(R), gg.johnson_labels(G)
            assert (jr is None) == (jg is None)
            if jr is None:
                continue
            assert jr[0] == jg[0]
            els = list(R.elements())
            for g in rng.sample(els, min(200, len(els))):
                assert jr[1](g) == jg[1](g)


def test_ambient_base():
    rng = random.Random(11)
    for n, gens in GROUPS:
        R = ref.PermGroup(n, gens)
        G = gg.PermGroup(n, gens)
        els = list(R.elements()) if R.order() <= 2000 else None
        for _ in range(3):
            if els is not None:
                sub = [rng.choice(els) for _ in range(rng.randint(1, 3))]
            else:
                sub = [mul(rng.choice(gens), rng.choice(gens)) for _ in range(2)]
            base = rng.sample(range(n), min(n, rng.randint(0, 3)))
            assert chain(gg.PermGroup(n, sub, base=base, ambient_base=G.short_base())) == \
                chain(ref.PermGroup(n, sub, base=base))


# -- explicit chains (PermGroup.from_bsgs) ----------------------------------
def check_bsgs(G):
    """Every property from_bsgs relies on, checked against built chains:
    T[l][p] fixes base[:l], maps base[l] to p and Ti[l][p] is its inverse;
    S[l] fixes base[:l]; the orbit of base[l] under <S[l]> is the key set of
    T[l]; S[l+1] lies in <S[l]> and |<S[l]>| = |T[l]| |<S[l+1]>| (so <S[l+1]>
    is the whole stabilizer of base[l] in <S[l]>); <gens> = <S[0]>; and the
    _ok-skipping convention: s in S[l] fixing base[l] is in S[l+1]."""
    n, idn, base = G.n, G.idn, G.base
    built = [gg.PermGroup(n, list(S)) for S in G.S] + [gg.PermGroup(n, [])]
    for l, b in enumerate(base):
        for p, u in G.T[l].items():
            assert u[b] == p and all(u[c] == c for c in base[:l])
            assert mul(u, G.Ti[l][p]) == idn
            assert built[l].contains(u)
        for s in G.S[l]:
            assert all(s[c] == c for c in base[:l])
            if s[b] == b and l + 1 < len(base):
                assert s in G.S[l + 1]
        orb = {b}
        queue = [b]
        for p in queue:
            for s in G.S[l]:
                if s[p] not in orb:
                    orb.add(s[p])
                    queue.append(s[p])
        assert orb == set(G.T[l])
        nxt = G.S[l + 1] if l + 1 < len(base) else []
        assert all(built[l].contains(s) for s in nxt)
        assert built[l].order() == len(G.T[l]) * gg.PermGroup(n, list(nxt)).order()
    full = gg.PermGroup(n, list(G.gens))
    assert full.order() == G.order() == (built[0].order() if G.S else 1)
    assert all(full.contains(s) for s in G.strong_gens())


def pair_actions(n, classes, D, rng, count):
    """Random elements of prod Sym(C) as vertex permutations and on D."""
    idx = {p: k for k, p in enumerate(D)}
    out = []
    for _ in range(count):
        g = list(range(n))
        for C in classes:
            img = list(C)
            rng.shuffle(img)
            for a, b in zip(C, img):
                g[a] = b
        out.append(tuple(idx[(g[i], g[j])] for i, j in D))
    return out


SYM_CASES = [
    (5, [[0, 1, 2, 3, 4]], "all"),
    (6, [[0, 2, 4], [1, 3, 5]], "all"),
    (7, [[1, 3, 5], [0, 2], [4, 6]], "all"),
    (7, [[0, 1, 2, 3], [4, 5]], "all"),
    (7, [[2, 3, 4, 5]], "block"),                 # a self stage P x P
    (7, [[0, 1, 2], [4, 5, 6]], "merge"),         # cross block of two factors
    (8, [[1, 2, 3]], "fixed"),                    # a factor against fixed vertices
    (6, [[5, 4, 3], [2, 0, 1]], "all"),           # unsorted classes
]


def sym_case(n, classes, kind):
    verts = sorted(v for C in classes for v in C)
    if kind == "all":
        D = [(i, j) for i in range(n) for j in range(n)]
    elif kind == "block":
        D = [(i, j) for i in verts for j in verts]
    elif kind == "merge":
        A, B = classes
        D = sorted([(i, j) for i in A for j in B] + [(j, i) for i in A for j in B]
                   + [(i, i) for i in A + B])
    else:
        A, B = [0, 6, 7], classes[0]
        D = sorted([(i, j) for i in A for j in B] + [(j, i) for i in A for j in B]
                   + [(i, i) for i in A + B])
    return D


def test_sym_product_group():
    """graph.sym_product_group writes the chain of prod Sym(C) on pairs down;
    it must be a valid chain of the right group: same order and membership
    as the chain Schreier-Sims builds from its generators, and transposition
    transversals."""
    from gi.graph import sym_product_group
    from gi.perm import sym_gens
    rng = random.Random(17)
    for n, classes, kind in SYM_CASES:
        D = sym_case(n, classes, kind)
        K = sym_product_group(n, classes, D)
        check_bsgs(K)
        m = len(D)
        idx = {p: k for k, p in enumerate(D)}
        vg = [g for C in classes for g in sym_gens(n, C)]   # the old Schreier-Sims path
        B = gg.PermGroup(m, [tuple(idx[(g[i], g[j])] for i, j in D) for g in vg])
        want = math.prod(math.factorial(len(C)) for C in classes)
        assert K.order() == want == B.order() == gg.PermGroup(m, K.gens).order()
        for g in pair_actions(n, classes, D, rng, 20):
            assert K.contains(g) and B.contains(g)
        for g in K.gens:
            assert B.contains(g)
        for _ in range(20):                     # random permutations of D: same verdict
            g = rand_perm(m, rng)
            assert K.contains(g) == B.contains(g)
        # transposition transversals on the base points
        assert K._transp == len(K.base)
        for l, b in enumerate(K.base):
            for p, u in K.T[l].items():
                assert all(u[c] == (p if c == b else b if c == p else c) for c in K.base)
                assert mul(u, u) == K.idn
        # restriction to the diagonal of the classes with >= 3 points reuses the chain
        gamma = sorted(idx[(v, v)] for C in classes if len(C) >= 3 for v in C)
        if gamma:
            psi = gg.RestrictionHom(K, gamma)
            assert psi.C is K
            built = gg.PermGroup(m, list(K.gens), base=gamma, order=K.order())
            assert psi.image_order() == gg.PermGroup(len(gamma), [psi.image_of(g) for g in K.gens]).order()
            assert psi.kernel().order() * psi.image_order() == K.order()
            for g in pair_actions(n, classes, D, rng, 5):
                p = psi.image_of(g)
                h = psi.lift(p)
                assert psi.image_of(h) == p and built.contains(h)


def test_young_preimage():
    """group.young_preimage writes the chain of psi^-1(Young(partition)) down;
    it must equal (same order, mutual membership) the preimage built by
    Schreier-Sims from lifts and the kernel."""
    from gi.graph import sym_product_group
    from gi.perm import sym_gens
    rng = random.Random(29)
    for n, classes, kind in SYM_CASES:
        D = sym_case(n, classes, kind)
        K = sym_product_group(n, classes, D)
        idx = {p: k for k, p in enumerate(D)}
        gamma = sorted(idx[(v, v)] for C in classes if len(C) >= 3 for v in C)
        if not gamma:
            continue
        psi = gg.RestrictionHom(K, gamma)
        lab = {p: i for i, p in enumerate(gamma)}
        root = [[lab[idx[(v, v)]] for v in C] for C in classes if len(C) >= 3]
        for _ in range(6):
            part = []
            for C in root:                      # a random refinement of the classes
                C = list(C)
                rng.shuffle(C)
                cut = sorted(rng.sample(range(1, len(C)), rng.randint(0, len(C) - 1)))
                for a, b in zip([0] + cut, cut + [len(C)]):
                    part.append(C[a:b])
            big = [Y for Y in part if len(Y) >= 2]
            H = gg.young_preimage(psi, big)
            assert H is not None
            check_bsgs(H)
            hs = [g for Y in big for g in sym_gens(len(gamma), Y)]
            W = psi.preimage(hs) if hs else psi.kernel()
            assert H.order() == W.order()
            assert all(W.contains(g) for g in H.strong_gens())
            assert all(H.contains(g) for g in W.gens)
            for g in pair_actions(n, classes, D, rng, 10):
                img = psi.image_of(g)
                inside = all(img[a] in Y for Y in part for a in Y)
                assert H.contains(g) == inside == W.contains(g)
    # a chain without transposition transversals is refused
    G = gg.PermGroup(4, [(1, 2, 3, 0), (1, 0, 2, 3)])
    assert gg.young_preimage(gg.RestrictionHom(G, [0, 1, 2, 3]), [[0, 1]]) is None
