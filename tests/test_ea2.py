"""Elementary abelian 2-groups by linear algebra (gi/ea2.py) and the
elementary abelian path of the bounded-degree reduction, against brute force.
Run: python3 -m pytest -q tests"""
import itertools
import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.setrecursionlimit(100000)

import pytest

from gi import Solver
from gi.bounded import bounded_iso, bounded_iso_lists
from gi.ea2 import EA2, EAAction, XorBasis, is_ea2, nullspace
from gi.perm import act, mul


def random_ea_action(rng, k, norbits, maxdim):
    """F_2^k acting on norbits orbits; orbit j is F_2^k / K_j for a random
    subspace K_j of codimension <= maxdim, its points the cosets (labelled by
    reduced representatives). Returns (act, m)."""
    act_lists = [[] for _ in range(k)]
    m = 0
    for _ in range(norbits):
        d = rng.randint(0, min(maxdim, k))
        # a random surjection F_2^k -> F_2^d: images of the basis vectors
        while True:
            img = [rng.randrange(1 << d) for _ in range(k)]
            span = XorBasis()
            for v in img:
                span.add(v)
            if span.rank() == d:
                break
        for i in range(k):
            act_lists[i].extend(m + (p ^ img[i]) for p in range(1 << d))
        m += 1 << d
    return [tuple(a) for a in act_lists], m


def elem_on_positions(actions, a, m):
    g = tuple(range(m))
    i = 0
    while a:
        if a & 1:
            g = mul(g, actions[i])
        a >>= 1
        i += 1
    return g


def brute(actions, k, m, x, y):
    return {a for a in range(1 << k) if act(x, elem_on_positions(actions, a, m)) == tuple(y)}


def span_of(vectors):
    out = {0}
    for v in vectors:
        out |= {u ^ v for u in out}
    return out


def test_xor_basis_solution_and_kernel():
    rng = random.Random(3)
    for _ in range(200):
        k = rng.randint(1, 9)
        B = XorBasis()
        sol = rng.randrange(1 << k)
        for _ in range(rng.randint(0, 2 * k)):
            r = rng.randrange(1 << k)
            assert B.add(r, (r & sol).bit_count() & 1)
        a0 = B.solution(k)
        rows = list(B.rows.values())
        assert all(((r & a0).bit_count() & 1) == s for r, s in rows)
        ker = B.kernel(k)
        assert len(ker) == k - B.rank()
        brute_ker = {a for a in range(1 << k) if all((r & a).bit_count() % 2 == 0 for r, _ in rows)}
        assert span_of(ker) == brute_ker
        if rows:                         # a contradicting equation is refused
            r, s = rows[0]
            assert not B.add(r, s ^ 1)


def test_nullspace():
    rng = random.Random(4)
    for _ in range(100):
        k = rng.randint(1, 8)
        vs = [rng.randrange(1 << k) for _ in range(rng.randint(0, k))]
        ann = nullspace(vs, k)
        U = span_of(vs)
        assert span_of(ann) == {r for r in range(1 << k)
                                if all((r & u).bit_count() % 2 == 0 for u in U)}


@pytest.mark.parametrize("seed", range(40))
def test_ea_string_iso_brute_force(seed):
    rng = random.Random(seed)
    k = rng.randint(1, 7)
    actions, m = random_ea_action(rng, k, rng.randint(1, 6), 3)
    ncol = rng.randint(1, 3)
    x = tuple(rng.randrange(ncol) for _ in range(m))
    if rng.random() < 0.6:               # an image of x, then sometimes perturbed
        y = act(x, elem_on_positions(actions, rng.randrange(1 << k), m))
        if rng.random() < 0.3:
            y = list(y)
            y[rng.randrange(m)] = rng.randrange(ncol)
            y = tuple(y)
    else:
        y = tuple(rng.randrange(ncol) for _ in range(m))
    want = brute(actions, k, m, x, y)
    res = EAAction(k, actions, m).iso(x, y)
    if not want:
        assert res is None
        return
    a0, N = res
    got = {a0 ^ u for u in span_of(N)}
    assert got == want
    assert span_of(N) == brute(actions, k, m, x, x)      # N is Aut_G(x)


def test_ea_action_reuse_and_elements():
    rng = random.Random(11)
    k = 5
    actions, m = random_ea_action(rng, k, 5, 3)
    A = EAAction(k, actions, m)
    for _ in range(20):
        x = tuple(rng.randrange(2) for _ in range(m))
        y = act(x, elem_on_positions(actions, rng.randrange(1 << k), m))
        a0, N = A.iso(x, y)
        assert act(x, elem_on_positions(actions, a0, m)) == y
    G = EA2(m, actions)
    assert is_ea2(actions, m)
    assert G.elem(0b101) == mul(actions[0], actions[2]) and G.order() == 32


def test_is_ea2():
    assert is_ea2([(1, 0, 3, 2), (2, 3, 0, 1)], 4)
    assert not is_ea2([(1, 0, 2), (0, 2, 1)], 3)        # do not commute
    assert not is_ea2([(1, 2, 0)], 3)                    # not an involution


# -- the elementary abelian path of bounded_iso ------------------------------------
def cfi_lists(b, E, twists):
    inc = [[] for _ in range(b)]
    for ei, (u, v) in enumerate(E):
        inc[u].append(ei)
        inc[v].append(ei)
    nbr, outer = [], {}
    for v in range(b):
        for ei in inc[v]:
            for c in (0, 1):
                outer[(v, ei, c)] = len(nbr)
                nbr.append([])
    for v in range(b):
        for bits in itertools.product((0, 1), repeat=len(inc[v])):
            if sum(bits) % 2:
                continue
            m = len(nbr)
            nbr.append([outer[(v, ei, c)] for ei, c in zip(inc[v], bits)])
            for o in nbr[m]:
                nbr[o].append(m)
    for ei, (u, v) in enumerate(E):
        t = 1 if ei in twists else 0
        for c in (0, 1):
            p, q = outer[(u, ei, c)], outer[(v, ei, c ^ t)]
            nbr[p].append(q)
            nbr[q].append(p)
    return nbr


def relabel(nbr, rng):
    n = len(nbr)
    s = list(range(n))
    rng.shuffle(s)
    out = [None] * n
    for i in range(n):
        out[s[i]] = sorted(s[j] for j in nbr[i])
    return out


def check_answer(X, Y, res):
    n = len(X)
    sigma, gens = res
    EY = {(u, v) for u in range(n) for v in Y[u]}
    assert all((sigma[u], sigma[v]) in EY for u in range(n) for v in X[u])
    EX = {(u, v) for u in range(n) for v in X[u]}
    for g in gens:
        assert all((g[u], g[v]) in EX for u in range(n) for v in X[u])


def group_order(gens, n):
    from gi.group import PermGroup
    return PermGroup(n, gens).order()


BASES = {
    "K4": (4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]),
    "K33": (6, [(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5)]),
    "prism": (6, [(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5), (0, 3), (1, 4), (2, 5)]),
    "petersen": (10, [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4), (0, 5), (1, 6), (2, 7), (3, 8),
                      (4, 9), (5, 7), (7, 9), (6, 9), (6, 8), (5, 8)]),
}


@pytest.mark.parametrize("name", sorted(BASES))
def test_bounded_ea_matches_permutation_path_on_cfi(name):
    """CFI graphs: isomorphic (two twists) and non-isomorphic (one twist)
    pairs; the EA path and the permutation-group path give the same decision
    and the same |Aut| (checked by Schreier-Sims), and the answers verify."""
    b, E = BASES[name]
    rng = random.Random(len(E))
    X = cfi_lists(b, E, set())
    Y2 = relabel(cfi_lists(b, E, {0, 3}), rng)
    Y1 = relabel(cfi_lists(b, E, {2}), rng)
    n = len(X)
    for Y, iso in ((Y2, True), (Y1, False)):
        S1 = Solver(cameron_no_enum=True, certificates=False)
        r1 = bounded_iso_lists(X, Y, solver=S1)
        r0 = bounded_iso_lists(X, Y, solver=Solver(cameron_no_enum=True, certificates=False),
                               ea=False, rooted_wl=False)
        assert (r1 is not None) == iso == (r0 is not None)
        if iso:
            check_answer(X, Y, r1)
            assert group_order(r1[1], n) == group_order(r0[1], n)
        assert S1.stats["luks_ea_layers"] > 0


def test_bounded_ea_fallback_and_back():
    """A graph whose layers need the permutation path for a while (twin
    blocks of size 3 at the hub of a 3-regular-ish tree-like gadget); the
    result must still be exact."""
    # K_{1,3} with each leaf attached to a CFI-like square: twin classes of 3
    rng = random.Random(5)
    nbr = [[1, 2, 3]] + [[0] for _ in range(3)]
    for leaf in (1, 2, 3):
        a, bb = len(nbr), len(nbr) + 1
        nbr.extend([[leaf], [leaf]])
        nbr[leaf] += [a, bb]
    X = [sorted(r) for r in nbr]
    Y = relabel(X, rng)
    S = Solver(cameron_no_enum=True, certificates=False)
    res = bounded_iso_lists(X, Y, solver=S)
    check_answer(X, Y, res)
    # Aut: Sym(3) on the leaves times a swap per leaf pair: 3! * 2^3
    assert group_order(res[1], len(X)) == 48
    assert S.stats["luks_ea_fallback"] > 0
