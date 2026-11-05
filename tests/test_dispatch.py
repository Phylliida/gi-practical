"""The primitive-quotient dispatcher: recognition of Johnson actions on k-sets
and of product actions (Maroti's large case), and exact string isomorphism
under such groups, checked against brute force over group elements that are
generated independently of gi. Run: python3 -m pytest -q tests"""
import itertools
import math
import os
import random
import sys

import pytest

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.setrecursionlimit(100000)

from gi import Solver, graph_iso
from gi import group as gg
from gi.group import PermGroup, johnson_structure, johnson_labels, product_action
from gi.perm import mul, inv, act, maps, parity


def rand_perm(m, rng, even=False):
    p = list(range(m))
    rng.shuffle(p)
    p = tuple(p)
    if even and parity(p):
        p = (p[1], p[0]) + p[2:]
    return p


def scramble(d, rng):
    s = list(range(d))
    rng.shuffle(s)
    return s


# -- Sym(m) / Alt(m) on k-sets -------------------------------------------------
class KSets:
    """Sym(m) or Alt(m) acting on the k-subsets of range(m), with the points
    numbered at random. `elements()` lists the whole group from Sym(m)."""

    def __init__(self, m, k, alt, rng):
        self.m, self.k, self.alt = m, k, alt
        self.S = list(itertools.combinations(range(m), k))
        self.d = len(self.S)
        lab = scramble(self.d, rng)
        self.idx = {s: lab[i] for i, s in enumerate(self.S)}
        while True:
            self.top = [rand_perm(m, rng, alt) for _ in range(2)]
            want = math.factorial(m) // (2 if alt else 1)
            if PermGroup(m, self.top).order() == want:
                break
        self.gens = [self.lift(s) for s in self.top]

    def lift(self, s):
        p = [0] * self.d
        for T in self.S:
            p[self.idx[T]] = self.idx[tuple(sorted(s[a] for a in T))]
        return tuple(p)

    def elements(self):
        for s in itertools.permutations(range(self.m)):
            if not self.alt or not parity(s):
                yield self.lift(s)

    def true_stars(self):
        return {frozenset(self.idx[T] for T in self.S if a in T): a for a in range(self.m)}


JOHNSON = [(5, 2), (6, 2), (7, 2), (7, 3), (8, 3), (9, 3), (9, 4), (11, 4)]


@pytest.mark.parametrize("m,k", JOHNSON)
def test_johnson_structure(m, k):
    rng = random.Random(100 * m + k)
    for alt in (False, True):
        A = KSets(m, k, alt, rng)
        P = PermGroup(A.d, A.gens)
        J = johnson_structure(P)
        assert J is not None and J[:2] == (m, k)
        f = J[2]
        # the stars are exactly the true stars {k-sets containing a}
        true = A.true_stars()
        sigma = [true[s] for s in f.stars]          # recovered label i = true label sigma[i]
        assert sorted(sigma) == list(range(m))
        # f is the natural action up to this relabeling (hence a homomorphism)
        for _ in range(10):
            s = rand_perm(m, rng, alt)
            g = A.lift(s)
            assert all(sigma[f(g)[i]] == s[sigma[i]] for i in range(m))
        assert johnson_labels(P)[0] == m
        assert product_action(P) is None


def test_johnson_rejects_non_johnson():
    rng = random.Random(7)
    # Sym(m) on m points, Sym(6) on 10 points (3|3 bisections) and a product
    # action of degree 36 = C(9, 2) are not Johnson actions on k >= 2 sets
    for m in (6, 10, 15):
        P = PermGroup(m, [rand_perm(m, rng) for _ in range(2)])
        assert johnson_structure(P) is None
    bis = sorted({frozenset([A, tuple(sorted(set(range(6)) - set(A)))])
                  for A in itertools.combinations(range(6), 3)}, key=sorted)
    ix = {b: i for i, b in enumerate(bis)}

    def on_bis(s):
        return tuple(ix[frozenset(tuple(sorted(s[a] for a in A)) for A in b)] for b in bis)

    P = PermGroup(10, [on_bis(rand_perm(6, rng)) for _ in range(3)])
    assert P.order() == 720 and johnson_structure(P) is None
    W = Product(6, 1, 2, False, True, rng)
    assert johnson_structure(PermGroup(W.d, W.gens)) is None


def test_star_verification():
    """A wrong star system is rejected by the verification."""
    rng = random.Random(3)
    A = KSets(7, 3, False, rng)
    P = PermGroup(A.d, A.gens)
    stars = [set(s) for s in A.true_stars()]
    assert gg._star_action(P, [frozenset(s) for s in stars], 3) is not None
    # move one point between two stars: still 3 stars per point, not invariant
    p = next(iter(stars[0] - stars[1]))
    q = next(iter(stars[1] - stars[0]))
    stars[0].remove(p), stars[0].add(q), stars[1].remove(q), stars[1].add(p)
    assert gg._star_action(P, [frozenset(s) for s in stars], 3) is None


# -- product actions -------------------------------------------------------------
class Product:
    """A subgroup of Sym(m) wr Sym(r) acting on r-tuples of k-subsets of
    range(m) (D = C(m, k) points per coordinate), with the points numbered at
    random: (Sym(m) or Alt(m))^r, extended by the coordinate permutations
    `top` ('sym': all of Sym(r), 'cyc': the r-cycle, None: none)."""

    def __init__(self, m, k, r, alt, top, rng):
        self.m, self.k, self.r, self.alt = m, k, r, alt
        self.top = {True: "sym", False: None}.get(top, top)
        self.S = list(itertools.combinations(range(m), k))
        self.D = len(self.S)
        self.sidx = {s: i for i, s in enumerate(self.S)}
        self.pts = list(itertools.product(range(self.D), repeat=r))
        self.d = len(self.pts)
        lab = scramble(self.d, rng)
        self.idx = {t: lab[i] for i, t in enumerate(self.pts)}
        base = [rand_perm(m, rng, alt) for _ in range(2)]
        while PermGroup(m, base).order() != math.factorial(m) // (2 if alt else 1):
            base = [rand_perm(m, rng, alt) for _ in range(2)]
        ident = tuple(range(m))
        self.gens = [self.elem([s if c == i else ident for i in range(r)], tuple(range(r)))
                     for c in range(r) for s in base]
        for pi in self.coord_perms()[1:]:
            if self.top == "cyc" and pi != tuple((i + 1) % r for i in range(r)):
                continue
            self.gens.append(self.elem([ident] * r, pi))

    def coord_perms(self):
        if self.top is None:
            return [tuple(range(self.r))]
        if self.top == "cyc":
            return [tuple((i + j) % self.r for i in range(self.r)) for j in range(self.r)]
        return list(itertools.permutations(range(self.r)))

    def elem(self, ss, pi):
        """First apply ss[c] in coordinate c, then move coordinate c to pi[c]."""
        acts = [[self.sidx[tuple(sorted(s[a] for a in T))] for T in self.S] for s in ss]
        p = [0] * self.d
        for t in self.pts:
            u = [None] * self.r
            for c in range(self.r):
                u[pi[c]] = acts[c][t[c]]
            p[self.idx[t]] = self.idx[tuple(u)]
        return tuple(p)

    def elements(self):
        one = [s for s in itertools.permutations(range(self.m)) if not self.alt or not parity(s)]
        for pi in self.coord_perms():
            for ss in itertools.product(one, repeat=self.r):
                yield self.elem(ss, pi)

    def order(self):
        one = math.factorial(self.m) // (2 if self.alt else 1)
        return one ** self.r * len(self.coord_perms())


PRODUCTS = [(3, 1, 2, False, "sym"), (4, 1, 2, False, "sym"), (5, 1, 2, False, "sym"),
            (5, 1, 2, True, "sym"), (6, 1, 2, False, "sym"), (5, 2, 2, False, "sym"),
            (3, 1, 3, False, "sym"), (3, 1, 3, False, "cyc"), (4, 1, 3, False, "cyc")]


@pytest.mark.parametrize("m,k,r,alt,top", PRODUCTS)
def test_product_action(m, k, r, alt, top):
    rng = random.Random(m * 1000 + k * 100 + r * 10 + alt)
    W = Product(m, k, r, alt, top, rng)
    P = PermGroup(W.d, W.gens)
    assert P.order() == W.order()
    R = product_action(P)
    assert R is not None
    rr, f, lines0 = R
    assert rr == r
    # lines0 are the lines of one true coordinate
    true_lines = {c: {frozenset(W.idx[t] for t in W.pts if t[:c] + t[c + 1:] == rest)
                      for rest in itertools.product(range(W.D), repeat=r - 1)}
                  for c in range(r)}
    assert any({frozenset(L) for L in lines0} == true_lines[c] for c in range(r))
    # f is a homomorphism onto the coordinate permutations
    img = PermGroup(r, [f(g) for g in P.gens])
    assert img.order() == len(W.coord_perms())
    els = [W.elem([rand_perm(m, rng, alt) for _ in range(r)], rng.choice(W.coord_perms()))
           for _ in range(6)]
    for g in els:
        for h in els:
            assert f(mul(g, h)) == mul(f(g), f(h))


def test_product_rejects():
    rng = random.Random(5)
    # imprimitive (no coordinate swap): the lines are not one orbital structure
    W = Product(5, 1, 2, False, None, rng)
    assert product_action(PermGroup(W.d, W.gens)) is None
    # Sym(9) on the 36 2-sets: degree 6^2, but no product structure
    A = KSets(9, 2, False, rng)
    P = PermGroup(A.d, A.gens)
    assert product_action(P) is None
    b, T, orbs = gg._suborbits(P)
    for orb in orbs:
        nbr = gg._orbital_graph(A.d, T, b, orb)
        assert nbr is None or gg._product_lines(P, T, b, orb, nbr, 2, 6) is None


# -- string isomorphism under these groups -------------------------------------
def brute(elements, x, y):
    return [g for g in elements if maps(g, x, y)]


def check(G, x, y, ans, isos, auts):
    assert (ans is None) == (not isos)
    if ans is None:
        return
    assert maps(ans.rep, x, y)
    assert all(maps(g, x, x) for g in ans.gens)
    assert PermGroup(G.n, ans.gens).order() == len(auts)


CFGS = [dict(certificates=False, enum_limit=1), dict(certificates=True, enum_limit=1, kappa=3)]


def colorings(G_elements, d, rng, count):
    out = []
    for _ in range(count):
        ncol = rng.choice([2, 2, 3])
        x = tuple(rng.randrange(ncol) for _ in range(d))
        if rng.random() < 0.6:
            g = rng.choice(G_elements)
            y = act(x, g)
        else:
            y = list(x)
            rng.shuffle(y)
            y = tuple(y)
        out.append((x, y))
    return out


@pytest.mark.parametrize("cfg", CFGS, ids=["nocert", "cert3"])
@pytest.mark.parametrize("m,k,alt", [(5, 2, False), (6, 2, True), (7, 3, False), (7, 3, True),
                                     (6, 2, False)])
def test_string_iso_johnson(cfg, m, k, alt):
    """Positions are the k-sets (G primitive, Johnson) and, as an imprimitive
    variant, the flags (T, a) with a in T (top quotient Johnson)."""
    rng = random.Random(m * 10 + k + alt)
    A = KSets(m, k, alt, rng)
    els = list(A.elements())
    G = PermGroup(A.d, A.gens)
    for x, y in colorings(els, A.d, rng, 6):
        S = Solver(**cfg)
        ans = S.solve(G, range(A.d), x, y)
        check(G, x, y, ans, brute(els, x, y), brute(els, x, x))
        if len(set(x)) > 1 and sorted(x) == sorted(y):
            assert S.stats[f"johnson_k{k}"] > 0
    # flags
    F = [(T, a) for T in A.S for a in T]
    fidx = {fl: i for i, fl in enumerate(F)}

    def on_flags(s):
        return tuple(fidx[(tuple(sorted(s[b] for b in T)), s[a])] for T, a in F)

    perms = [s for s in itertools.permutations(range(m)) if not alt or not parity(s)]
    fels = [on_flags(s) for s in perms]
    H = PermGroup(len(F), [on_flags(s) for s in A.top])
    for x, y in colorings(fels, len(F), rng, 4):
        S = Solver(**cfg)
        ans = S.solve(H, range(len(F)), x, y)
        check(H, x, y, ans, brute(fels, x, y), brute(fels, x, x))


@pytest.mark.parametrize("cfg", CFGS, ids=["nocert", "cert3"])
@pytest.mark.parametrize("m,k,r,alt,top", [(4, 1, 2, False, "sym"), (5, 1, 2, False, "sym"),
                                           (5, 1, 2, True, "sym"), (3, 1, 3, False, "sym"),
                                           (5, 2, 2, False, "sym")])
def test_string_iso_product(cfg, m, k, r, alt, top):
    rng = random.Random(m * 100 + k * 10 + r + alt)
    W = Product(m, k, r, alt, top, rng)
    els = list(W.elements())
    assert len(els) == W.order()
    G = PermGroup(W.d, W.gens)
    for x, y in colorings(els, W.d, rng, 5):
        S = Solver(**cfg)
        ans = S.solve(G, range(W.d), x, y)
        check(G, x, y, ans, brute(els, x, y), brute(els, x, x))
        if len(set(x)) > 1 and sorted(x) == sorted(y):
            assert S.stats["product_refine"] > 0


@pytest.mark.parametrize("recognize", [True, False])
def test_rook_graphs(recognize):
    """K_m x K_m: Aut = Sym(m) wr Sym(2) in product action, with the recursion
    alone (no graph-level individualization)."""
    for m in (4, 5):
        A = [[int((i // m == j // m) != (i % m == j % m)) for j in range(m * m)]
             for i in range(m * m)]
        s = scramble(m * m, random.Random(m))
        B = [[A[s.index(i)][s.index(j)] for j in range(m * m)] for i in range(m * m)]
        S = Solver(certificates=False, recognize=recognize)
        res = graph_iso(A, B, solver=S, ir=0)
        assert res is not None
        sigma, gens = res
        n = m * m
        assert all(B[sigma[i]][sigma[j]] == A[i][j] for i in range(n) for j in range(n))
        assert all(A[g[i]][g[j]] == A[i][j] for g in gens for i in range(n) for j in range(n))
        assert PermGroup(n, gens).order() == 2 * math.factorial(m) ** 2
