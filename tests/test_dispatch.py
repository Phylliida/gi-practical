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
from gi.group import PermGroup, johnson_structure, johnson_labels, product_action, giant_labels
from gi.perm import mul, inv, act, maps, parity, alt_gens


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
    rr, f, lines0, fibers0 = R
    assert rr == r
    true_fibers = {c: {frozenset(W.idx[t] for t in W.pts if t[c] == v) for v in range(W.D)}
                   for c in range(r)}
    assert {frozenset(F) for F in fibers0} == true_fibers[
        next(c for c in range(r) if {frozenset(L) for L in lines0} == {
            frozenset(W.idx[t] for t in W.pts if t[:c] + t[c + 1:] == rest)
            for rest in itertools.product(range(W.D), repeat=r - 1)})]
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


# -- Sym(m) / Alt(m) in other actions --------------------------------------------
class Bisections:
    """Sym(m) or Alt(m) (m even) acting on the k|k bisections {A, complement}
    of range(m), k = m/2: primitive, Cameron-small, not a Johnson action."""

    def __init__(self, m, alt, rng):
        k = m // 2
        self.m, self.alt = m, alt
        self.B = sorted({frozenset([A, tuple(sorted(set(range(m)) - set(A)))])
                         for A in itertools.combinations(range(m), k)}, key=sorted)
        self.d = len(self.B)
        lab = scramble(self.d, rng)
        self.idx = {b: lab[i] for i, b in enumerate(self.B)}
        while True:
            self.top = [rand_perm(m, rng, alt) for _ in range(2)]
            if PermGroup(m, self.top).order() == math.factorial(m) // (2 if alt else 1):
                break
        self.gens = [self.lift(t) for t in self.top]

    def lift(self, s):
        p = [0] * self.d
        for b in self.B:
            p[self.idx[b]] = self.idx[frozenset(tuple(sorted(s[a] for a in A)) for A in b)]
        return tuple(p)

    def elements(self):
        for s in itertools.permutations(range(self.m)):
            if not self.alt or not parity(s):
                yield self.lift(s)


def pgl2(q, special):
    """PGL(2, q) (or PSL(2, q)) on the q + 1 points of the projective line, q prime."""
    pts = list(range(q)) + ["inf"]
    ix = {v: i for i, v in enumerate(pts)}

    def mobius(a, b, c, e):
        out = []
        for v in pts:
            if v == "inf":
                w = "inf" if c == 0 else a * pow(c, q - 2, q) % q
            else:
                num, den = (a * v + b) % q, (c * v + e) % q
                w = "inf" if den == 0 else num * pow(den, q - 2, q) % q
            out.append(ix[w])
        return tuple(out)

    squares = {(i * i) % q for i in range(1, q)}
    gens = [mobius(1, 1, 0, 1), mobius(0, q - 1, 1, 0)]
    gens.append(mobius(next(a for a in range(2, q) if a in squares) if special
                       else next(a for a in range(2, q) if a not in squares), 0, 0, 1))
    return PermGroup(q + 1, gens)


@pytest.mark.parametrize("m,alt", [(6, False), (8, False), (8, True), (10, False)])
def test_giant_labels_bisections(m, alt):
    rng = random.Random(m + alt)
    A = Bisections(m, alt, rng)
    P = PermGroup(A.d, A.gens)
    assert johnson_structure(P) is None and product_action(P) is None
    R = giant_labels(P)
    assert R is not None and R[0] == m
    f = R[1]
    els = [A.lift(rand_perm(m, rng, alt)) for _ in range(8)]
    for g in els:
        for h in els:
            assert f(mul(g, h)) == mul(f(g), f(h))
    img = PermGroup(m, [f(g) for g in P.gens])
    assert img.order() == P.order()


def test_giant_labels_small():
    """PGL(2,5) = Sym(5) and PSL(2,5) = Alt(5) on 6 points are giants; groups
    of factorial order that are not giants are rejected."""
    for special, order in ((False, 120), (True, 60)):
        P = pgl2(5, special)
        assert P.order() == order
        R = giant_labels(P)
        assert R is not None and R[0] == 5
        assert PermGroup(5, [R[1](g) for g in P.gens]).order() == order
    # PGL(2,7) has order 336, PSL(2,7) order 168: not factorial
    assert giant_labels(pgl2(7, False)) is None
    # Z_2 x Alt(5) and Z_2 x Alt(6) have orders 5! and 6!, but no class of transpositions
    for m in (5, 6):
        gens = [c + (m, m + 1) for c in alt_gens(m, range(m))]
        gens.append(tuple(range(m)) + (m + 1, m))
        P = PermGroup(m + 2, gens)
        assert P.order() == math.factorial(m)
        assert giant_labels(P) is None


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


@pytest.mark.parametrize("cfg", CFGS, ids=["nocert", "cert3"])
@pytest.mark.parametrize("m,alt", [(6, False), (8, True)])
def test_string_iso_bisections(cfg, m, alt):
    """Sym(6) on 10 and Alt(8) on 35 bisections: primitive groups of order
    m! or m!/2 that are not Johnson actions (the abstract giant path)."""
    if m == 8 and cfg["certificates"]:
        pytest.skip("slow; the nocert run covers the Alt(8) path")
    rng = random.Random(m * 7 + alt)
    A = Bisections(m, alt, rng)
    els = list(A.elements())
    G = PermGroup(A.d, A.gens)
    for x, y in colorings(els, A.d, rng, 5):
        S = Solver(**cfg)
        ans = S.solve(G, range(A.d), x, y)
        check(G, x, y, ans, brute(els, x, y), brute(els, x, x))
        if len(set(x)) > 1 and sorted(x) == sorted(y):
            assert S.stats["giant_abstract"] > 0


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


# -- Johnson and Hamming structure on the labels (scheme_step) ------------------
def johnson_graph(m, k, rng=None):
    V = list(itertools.combinations(range(m), k))
    perm = scramble(len(V), rng) if rng else list(range(len(V)))
    A = [[0] * len(V) for _ in V]
    for i, a in enumerate(V):
        for j, b in enumerate(V):
            if len(set(a) & set(b)) == k - 1:
                A[perm[i]][perm[j]] = 1
    return A, [frozenset(V[perm.index(l)]) for l in range(len(V))]


def hamming_graph(r, D, rng=None):
    V = list(itertools.product(range(D), repeat=r))
    perm = scramble(len(V), rng) if rng else list(range(len(V)))
    A = [[0] * len(V) for _ in V]
    for i, a in enumerate(V):
        for j, b in enumerate(V):
            if sum(u != v for u, v in zip(a, b)) == 1:
                A[perm[i]][perm[j]] = 1
    return A


def nbrs(A):
    return [{j for j in range(len(A)) if A[i][j]} for i in range(len(A))]


def kneser_graph(m, k):
    V = list(itertools.combinations(range(m), k))
    return [[int(not set(a) & set(b)) for b in V] for a in V]


def shrikhande():
    V = [(a, b) for a in range(4) for b in range(4)]
    D = {(0, 1), (0, 3), (1, 0), (3, 0), (1, 1), (3, 3)}
    return [[int(((c - a) % 4, (d - b) % 4) in D) for (c, d) in V] for (a, b) in V]


def chang1():
    A, sets = johnson_graph(8, 2)
    S = {frozenset(e) for e in [(0, 1), (2, 3), (4, 5), (6, 7)]}
    n = len(A)
    return [[A[i][j] ^ int(i != j and ((sets[i] in S) != (sets[j] in S))) for j in range(n)]
            for i in range(n)]


@pytest.mark.parametrize("m,k", [(6, 2), (7, 2), (10, 2), (7, 3), (8, 3), (6, 3), (8, 4), (9, 4)])
def test_johnson_embedding(m, k):
    rng = random.Random(m * 10 + k)
    A, true = johnson_graph(m, k, rng)
    e = gg.johnson_embedding(nbrs(A))
    assert e is not None and e[:2] == (m, k)
    sets = e[2]
    # the recovered stars are the true stars (or, for m = 2k, the co-stars)
    stars = {frozenset(l for l in range(len(A)) if i in sets[l]) for i in range(m)}
    tstars = {frozenset(l for l in range(len(A)) if a in true[l]) for a in range(m)}
    co = {frozenset(l for l in range(len(A)) if a not in true[l]) for a in range(m)}
    assert stars == tstars or (m == 2 * k and stars == co)
    assert gg.hamming_embedding(nbrs(A)) is None


def test_scheme_embeddings_reject():
    assert gg.johnson_embedding(nbrs(chang1())) is None             # SRG(28,12,6,4), not T(8)
    assert gg.johnson_embedding(nbrs(kneser_graph(7, 3))) is None
    assert gg.hamming_embedding(nbrs(shrikhande())) is None          # SRG(16,6,2,2), not H(2,4)
    assert gg.johnson_embedding(nbrs(hamming_graph(2, 5))) is None


@pytest.mark.parametrize("r,D", [(2, 3), (2, 4), (2, 6), (3, 3), (3, 4), (3, 2), (5, 2)])
def test_hamming_embedding(r, D):
    rng = random.Random(r * 10 + D)
    A = hamming_graph(r, D, rng)
    e = gg.hamming_embedding(nbrs(A))
    assert e is not None and e[:2] == (r, D)
    assert len(set(e[2])) == D ** r


def check_graph(A, B, iso, aut_order, **solver_kw):
    S = Solver(certificates=False, **solver_kw)
    res = graph_iso(A, B, solver=S, ir=0)
    n = len(A)
    assert (res is not None) == iso
    if res is not None:
        sigma, gens = res
        assert all(B[sigma[i]][sigma[j]] == A[i][j] for i in range(n) for j in range(n))
        assert all(A[g[i]][g[j]] == A[i][j] for g in gens for i in range(n) for j in range(n))
        assert PermGroup(n, gens).order() == aut_order
    return S


def relabeled(A, rng):
    s = scramble(len(A), rng)
    n = len(A)
    B = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            B[s[i]][s[j]] = A[i][j]
    return B


@pytest.mark.parametrize("scheme", [True, False])
def test_scheme_graphs(scheme):
    """Johnson, Kneser and Hamming graphs with the recursion alone (ir=0)."""
    rng = random.Random(11)
    cases = [(johnson_graph(7, 2)[0], 5040), (johnson_graph(6, 3)[0], 1440),
             (hamming_graph(2, 5), 28800), (hamming_graph(3, 3), 1296),
             (hamming_graph(4, 2), 384)]
    if scheme:
        cases += [(johnson_graph(7, 3)[0], 5040), (kneser_graph(7, 3), 5040)]
    for A, order in cases:
        S = check_graph(A, relabeled(A, rng), True, order, scheme=scheme)
        if scheme:
            assert S.stats["scheme_johnson"] + S.stats["scheme_hamming"] > 0
    check_graph(johnson_graph(8, 2)[0], relabeled(chang1(), rng), False, None, scheme=scheme)
    check_graph(hamming_graph(2, 4), relabeled(shrikhande(), rng), False, None, scheme=scheme)


@pytest.mark.parametrize("m,k", [(7, 2), (6, 2)])
def test_scheme_alt(m, k):
    """GiantStep under Alt(q) (q labels, positions the ordered pairs): the
    scheme step must respect parity. Aut(J(m, k)) <= Alt(q) iff a
    transposition of range(m) acts evenly on the k-sets."""
    rng = random.Random(m + k)
    A, _ = johnson_graph(m, k)
    q = len(A)
    P = [(a, b) for a in range(q) for b in range(q) if a != b]
    pix = {p: i for i, p in enumerate(P)}

    def on_pairs(s):
        return tuple(pix[(s[a], s[b])] for a, b in P)

    G = PermGroup(len(P), [on_pairs(g) for g in alt_gens(q, range(q))],
                  order=math.factorial(q) // 2)
    x = tuple(A[a][b] for a, b in P)
    trans_odd = math.comb(m - 2, k - 1) % 2 == 1
    aut_alt = math.factorial(m) // (2 if trans_odd else 1)
    for odd in (False, True):
        pi = rand_perm(q, rng, even=True)
        if odd:
            pi = (pi[1], pi[0]) + pi[2:]
        y = act(x, on_pairs(pi))
        S = Solver(certificates=False, enum_limit=1)
        ans = S.solve(G, range(len(P)), x, y)
        assert S.stats["scheme_johnson"] > 0
        if odd and not trans_odd:
            assert ans is None
            continue
        assert ans is not None and maps(ans.rep, x, y)
        assert all(maps(g, x, x) for g in ans.gens)
        assert PermGroup(len(P), ans.gens).order() == aut_alt
