"""The optimized group layer must give exactly the results of the baseline code
(tests/_ref_group.py): same chains, element order, lifts, kernels and block
systems. Run: python3 -m pytest -q tests"""
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
