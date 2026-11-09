#!/usr/bin/env python3
"""Exact-rational implementation of the replacement-form machinery of
"The Exponential Time Hypothesis is False" (OpenAI, Oct 2026), Secs. 2-4.

Purpose: test the *identities* (not the asymptotics) on small formulas.
Nothing here depends on the size bounds in Lemma 4.5/4.8; schedules are random
and h (label multiplicity) is whatever comes out. All arithmetic is exact (Fraction).
"""
from fractions import Fraction as Fr
from collections import defaultdict
from math import comb, floor
import itertools
import random

# ---------------------------------------------------------------- polynomials
def ptrim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p or [Fr(0)]

def padd(a, b):
    n = max(len(a), len(b))
    return ptrim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])

def pmul(a, b):
    out = [Fr(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return ptrim(out)

def pscale(c, p):
    return ptrim([c * x for x in p])

def peval(p, t):
    v = Fr(0)
    for c in reversed(p):
        v = v * t + c
    return v

def pshift(p, t, J):
    """Coefficients of p(t+z), truncated to z^J (list of J entries)."""
    out = [Fr(0)] * J
    for u, c in enumerate(p):
        if c:
            for j in range(min(u + 1, J)):
                out[j] += c * comb(u, j) * Fr(t) ** (u - j)
    return out


# ---------------------------------------------------------------- coefficient ring
class Ring:
    """Q[V]/(V^ell)[z]/(z^J). Element = dict {(i, s): Fr}, i < J (z-degree), s < ell (V-degree)."""
    def __init__(self, J, ell=1):
        self.J, self.ell = J, ell
        self.zero, self.one = {}, {(0, 0): Fr(1)}

    def const(self, c):
        return {(0, 0): Fr(c)} if c else {}

    def add(self, a, b):
        out = dict(a)
        for k, v in b.items():
            nv = out.get(k, 0) + v
            if nv:
                out[k] = nv
            elif k in out:
                del out[k]
        return out

    def scale(self, c, a):
        return {k: c * v for k, v in a.items()} if c else {}

    def sub(self, a, b):
        return self.add(a, self.scale(Fr(-1), b))

    def mul(self, a, b):
        out = defaultdict(Fr)
        for (i1, s1), v1 in a.items():
            for (i2, s2), v2 in b.items():
                if i1 + i2 < self.J and s1 + s2 < self.ell:
                    out[(i1 + i2, s1 + s2)] += v1 * v2
        return {k: v for k, v in out.items() if v}

    def from_zpoly(self, p):
        return {(i, 0): Fr(c) for i, c in enumerate(p) if c and i < self.J}

    def vmonomial(self, s):
        return {(0, s): Fr(1)} if s < self.ell else {}

    def to_list(self, a, s=0):
        out = [Fr(0)] * self.J
        for (i, ss), v in a.items():
            if ss == s:
                out[i] = v
        return out


# ---------------------------------------------------------------- group algebra of the commuting Pi_s
def ga_mul(a, b):
    out = defaultdict(Fr)
    for m1, c1 in a.items():
        for m2, c2 in b.items():
            out[m1 ^ m2] += c1 * c2
    return {m: c for m, c in out.items() if c}

def ga_add(a, b):
    out = dict(a)
    for m, c in b.items():
        out[m] = out.get(m, 0) + c
    return {m: c for m, c in out.items() if c}


class Construction:
    """Sec. 4.1-4.3 data for (r,Q,R): M0, C^B (as a list of basis-choice tuples), rows P_u(T).
    `broken` is a set of named deliberate defects (see BROKEN list in test_core.py)."""
    def __init__(self, r, Q, R, A0=None, broken=()):
        self.r, self.Q, self.R = r, Q, R
        self.D = r ** (2 * Q)
        self.broken = set(broken)
        if A0 is None:
            mu = Fr(Q * (r - 1), 2 * r)
            A0 = floor(mu - Fr(R - 1, 2))
            A0 = max(0, min(A0, Q - R + 1))
        self.A0 = A0
        self.I = list(range(A0, A0 + R))
        self.gamma = self._make_gamma()
        self.choices = self._basis_per_position()
        self.exceptional = [ch for ch in itertools.product(self.choices, repeat=Q)
                            if self.jval(ch) not in self.I]
        if 'C_drop' in self.broken and self.exceptional:
            self.exceptional = self.exceptional[1:]
        if 'C_empty' in self.broken:
            self.exceptional = []

    # ------- f_I and M0 in the group algebra (eq. 4.7)
    def _f_elem(self):
        Q, R, A0 = self.Q, self.R, self.A0
        W0 = {0: Fr(Q, 2)}
        for s in range(Q):
            W0[1 << s] = Fr(-1, 2)
        result = {}
        term = {0: Fr(1)}                     # binom(W0-A0, 0)
        for j in range(R):
            coef = Fr((-1) ** A0 * (-2) ** j)
            if 'f_wrong' in self.broken and j == R - 1:
                coef += 1                     # wrong interpolation at the top node of I
            result = ga_add(result, {m: coef * c for m, c in term.items()})
            factor = dict(W0)
            factor[0] = factor.get(0, 0) - (A0 + j)
            factor = {m: c * Fr(1, j + 1) for m, c in factor.items()}
            term = ga_mul(term, factor)
        return result

    def _make_gamma(self):
        f = self._f_elem()
        if 'no_V0' in self.broken:
            return f
        full = (1 << self.Q) - 1
        return ga_mul({full: Fr(1)}, f)

    def f_value(self, j):
        """f_I(j), as a rational (used for eigenvalue checks)."""
        A0, R = self.A0, self.R
        v = Fr(0)
        x = Fr(1)  # binom(j-A0, 0)
        for i in range(R):
            coef = Fr((-1) ** A0 * (-2) ** i)
            if 'f_wrong' in self.broken and i == R - 1:
                coef += 1
            v += coef * x
            x = x * (j - A0 - i) / (i + 1)
        return v

    # ------- coordinates
    def all_u(self):
        pairs = [(a, d) for a in range(self.r) for d in range(self.r)]
        return itertools.product(pairs, repeat=self.Q)

    def theta(self, u, mask):
        return tuple((d, a) if (mask >> s) & 1 else (a, d) for s, (a, d) in enumerate(u))

    def M0_row(self, u):
        row = defaultdict(Fr)
        for m, g in self.gamma.items():
            row[self.theta(u, m)] += g
        return {y: c for y, c in row.items() if c}

    def E(self, u, y):
        return [s for s in range(self.Q) if y[s][0] != u[s][1]]

    def phi(self, u, y):
        Es = self.E(u, y)
        if 'phi_drop' in self.broken and Es:
            Es = Es[1:]
        p = [Fr(1)]
        for s in Es:
            p = pmul(p, [Fr(1), Fr(-1, s + 1)])
        return p

    def P_u(self, u):
        """Row P_u(T), eq. (4.10): dict y -> poly(T)."""
        out = defaultdict(lambda: [Fr(0)])
        restore = 'no_restore' not in self.broken
        if restore:
            out[u] = padd(out[u], [Fr(1)])
        for y, c in self.M0_row(u).items():
            if restore:
                out[y] = padd(out[y], [-c])
            out[y] = padd(out[y], pscale(c, self.phi(u, y)))
        return {y: p for y, p in out.items() if p != [Fr(0)]}

    # ------- eigenbasis / measurement rows
    def _basis_per_position(self):
        L = []
        for a in range(self.r):
            L.append(('d', a, a))
        for a in range(self.r):
            for b in range(a + 1, self.r):
                L.append(('p', a, b))
                L.append(('m', a, b))
        return L

    @staticmethod
    def jval(ch):
        return sum(1 for c in ch if c[0] == 'm')

    @staticmethod
    def basis_val(c, x, y):
        kind, a, b = c
        if kind == 'd':
            return 1 if x == a and y == a else 0
        if kind == 'p':
            return 1 if (x, y) in ((a, b), (b, a)) else 0
        if (x, y) == (a, b):
            return 1
        if (x, y) == (b, a):
            return -1
        return 0

    def psi(self, ch, u):
        v = 1
        for c, (a, d) in zip(ch, u):
            v *= self.basis_val(c, a, d)
            if v == 0:
                return 0
        return v


# ---------------------------------------------------------------- formula instance + design
def clause_eval(ring, inputs):
    """Phi_e = 1 - prod(1 - L); inputs = list of (ring element, negbit)."""
    prod = ring.one
    for y, neg in inputs:
        lit = ring.sub(ring.one, y) if neg else y
        prod = ring.mul(prod, ring.sub(ring.one, lit))
    return ring.sub(ring.one, prod)


class Design:
    """Sec. 4.4-4.5 for a concrete CNF. clauses: list of [(var, negbit), ...].
    factor_eval(f, inputs_by_var, ring) evaluates factor f on ring-valued inputs."""
    def __init__(self, C, n, scopes, factor_eval, seed=0, broken=()):
        self.C, self.n, self.scopes, self.factor_eval = C, n, scopes, factor_eval
        self.broken = set(broken)
        rng = random.Random(seed)
        r, Q = C.r, C.Q
        self.av = [tuple(rng.randrange(r) for _ in range(Q)) for _ in range(n)]
        self.df = [tuple(rng.randrange(r) for _ in range(Q)) for _ in scopes]
        counts = defaultdict(int)
        self.copy = {}
        self.label = {}
        self.fill = {}
        for f, scope in enumerate(scopes):
            for v in scope:
                d = self.df[f]
                if 'sigma_split' in self.broken and v == scope[-1] and len(scope) > 1:
                    d = tuple((x + 1) % r for x in d)   # this occurrence uses another group
                u = tuple((self.av[v][s], d[s]) for s in range(Q))
                c = counts[u]
                counts[u] += 1
                self.copy[(f, v)] = c
                self.label[(f, v)] = u
                self.fill[(c, u)] = v
        self.h = max(counts.values()) if counts else 1
        self.M = sum(len(s) for s in scopes)
        # replacement rows on actual variables: (f,v) -> {i: poly(T)}
        self.P = {}
        cache = {}
        for (f, v), u in self.label.items():
            if u not in cache:
                cache[u] = C.P_u(u)
            row = defaultdict(lambda: [Fr(0)])
            for y, p in cache[u].items():
                i = self.fill.get((self.copy[(f, v)], y))
                if i is not None:
                    row[i] = padd(row[i], p)
            self.P[(f, v)] = {i: p for i, p in row.items() if p != [Fr(0)]}
        # measurement rows on actual variables (all copies)
        self.meas = []
        for c in range(self.h):
            for ch in C.exceptional:
                row = defaultdict(int)
                for (cc, y), i in self.fill.items():
                    if cc == c:
                        val = C.psi(ch, y)
                        if val:
                            row[i] += val
                row = {i: x for i, x in row.items() if x}
                if row:
                    self.meas.append(row)
        self._Pt_cache = {}

    # groups at evaluation point t in 1..Q
    def S(self, t, g):
        return [v for v in range(self.n) if self.av[v][t - 1] == g]

    def sigma(self, t, f):
        return self.df[f][t - 1]

    def measurements(self, t, g):
        S = set(self.S(t, g))
        rows = []
        for row in self.meas:
            rr = {i: x for i, x in row.items() if i in S}
            if rr:
                rows.append(rr)
        return rows

    def Pt(self, t):
        if t not in self._Pt_cache:
            self._Pt_cache[t] = {k: {i: peval(p, t) for i, p in row.items()} for k, row in self.P.items()}
        return self._Pt_cache[t]

    def delta(self, t, J):
        """(f,v) -> {i: list of J coeffs of P_i(t+z)-P_i(t)}."""
        out = {}
        for k, row in self.P.items():
            d = {}
            for i, p in row.items():
                sh = pshift(p, t, J)
                sh[0] = Fr(0)
                if any(sh):
                    d[i] = sh
            out[k] = d
        return out

    # direct evaluation of all factors at point t with Boolean x and correction U
    def product_at(self, t, x, U, ring, Pt, Dt, factors):
        result = ring.one
        for f in factors:
            inputs = {}
            for v in self.scopes[f]:
                val = sum((c * x[i] for i, c in Pt[(f, v)].items()), Fr(0))
                elem = ring.const(val)
                for i, poly in Dt[(f, v)].items():
                    if i in U:
                        elem = ring.add(elem, ring.from_zpoly(poly))
                inputs[v] = elem
            result = ring.mul(result, self.factor_eval(f, inputs, ring))
        return result

    def Z_brute(self, t, E, U, ring):
        """Direct sum over all x with x_i=1 on E of G_x(1_U, z), eq. (2.8)."""
        Pt, Dt = self.Pt(t), self.delta(t, ring.J)
        total = ring.zero
        all_factors = range(len(self.scopes))
        for bits in itertools.product((0, 1), repeat=self.n):
            if any(bits[i] != 1 for i in E):
                continue
            total = ring.add(total, self.product_at(t, bits, U, ring, Pt, Dt, all_factors))
        return total

    def Z_factorized(self, t, E, U, ring, tables=None):
        """Lemma 3.2 identity: group sums over X_g(y_g) with fixed measurement tuple.
        Tuples are enumerated over the *achieved* values (the paper skips empty fibres)."""
        r = self.C.r
        Pt, Dt = self.Pt(t), self.delta(t, ring.J)
        tables = tables if tables is not None else self.measure_tables(t)
        groups, y_maps, reps = tables
        factors_of = {g: [f for f in range(len(self.scopes)) if self.sigma(t, f) == g] for g in range(r)}
        memo = {}

        def sigma_g(g, ytuple):
            key = (g, ytuple)
            if key in memo:
                return memo[key]
            x = [0] * self.n
            for h in range(r):
                if h != g:
                    for v, bit in zip(groups[h], reps[h][ytuple[h]]):
                        x[v] = bit
            s = ring.zero
            for xg in y_maps[g][ytuple[g]]:
                ok = True
                for v, bit in zip(groups[g], xg):
                    x[v] = bit
                    if v in E and bit != 1:
                        ok = False
                if ok:
                    s = ring.add(s, self.product_at(t, x, U, ring, Pt, Dt, factors_of[g]))
            memo[key] = s
            return s

        keys = [list(y_maps[g].keys()) for g in range(r)]
        total = ring.zero
        for ytuple in itertools.product(*keys):
            prod = ring.one
            for g in range(r):
                prod = ring.mul(prod, sigma_g(g, ytuple))
                if not prod:
                    break
            total = ring.add(total, prod)
        return total

    def measure_tables(self, t):
        r = self.C.r
        groups, y_maps, reps = [], [], []
        for g in range(r):
            S = self.S(t, g)
            rows = self.measurements(t, g)
            ymap = defaultdict(list)
            for bits in itertools.product((0, 1), repeat=len(S)):
                x = dict(zip(S, bits))
                y = tuple(sum(c * x[i] for i, c in row.items()) for row in rows)
                if 'measure_mod2' in self.broken:
                    y = tuple(v % 2 for v in y)
                ymap[y].append(bits)
            groups.append(S)
            y_maps.append(dict(ymap))
            reps.append({y: lst[0] for y, lst in ymap.items()})
        return groups, y_maps, reps

    def H_poly(self, ring_T):
        """Brute force H(T) as a ring element, ring_T.J > deg_T H. T plays the role of z."""
        total = ring_T.zero
        for bits in itertools.product((0, 1), repeat=self.n):
            prod = ring_T.one
            for f, scope in enumerate(self.scopes):
                inputs = {}
                for v in scope:
                    e = ring_T.zero
                    for i, p in self.P[(f, v)].items():
                        if bits[i]:
                            e = ring_T.add(e, ring_T.from_zpoly(p))
                    inputs[v] = e
                prod = ring_T.mul(prod, self.factor_eval(f, inputs, ring_T))
            total = ring_T.add(total, prod)
        return total

    def taylor_IE(self, t, qE, ring):
        """Eq. (3.13): recover H(t+z) mod z^J from the fixed-input sums, using |E| <= qE."""
        tables = self.measure_tables(t)
        total = ring.zero
        for s in range(0, min(qE, self.n) + 1):
            for E in itertools.combinations(range(self.n), s):
                Eset = set(E)
                for s2 in range(s + 1):
                    for Usub in itertools.combinations(E, s2):
                        sign = Fr((-1) ** (s - s2))
                        z = self.Z_factorized(t, Eset, set(Usub), ring, tables)
                        total = ring.add(total, ring.scale(sign, z))
        return total

    def check_design(self, t):
        """Definition 3.1(4): for each (f,v), g != sigma_f(t): P_{f,v}(t)|S_g lies in the
        row space of C_{t,g}. Returns (number checked, number failed)."""
        r = self.C.r
        Pt = self.Pt(t)
        checked = failed = 0
        for f, scope in enumerate(self.scopes):
            for v in scope:
                for g in range(r):
                    if g == self.sigma(t, f):
                        continue
                    S = self.S(t, g)
                    target = {i: c for i, c in Pt[(f, v)].items() if i in S}
                    checked += 1
                    if not in_rowspace(self.measurements(t, g), target, S):
                        failed += 1
        return checked, failed


def in_rowspace(rows, target, columns):
    """Exact rational test: target (dict col->value) in span of rows (dicts col->value)."""
    if not any(target.values()):
        return True
    cols = list(columns)
    idx = {c: i for i, c in enumerate(cols)}
    n = len(cols)
    mat = []
    for row in rows:
        v = [Fr(0)] * n
        for c, x in row.items():
            v[idx[c]] = Fr(x)
        mat.append(v)
    t = [Fr(0)] * n
    for c, x in target.items():
        t[idx[c]] = Fr(x)
    pivrow = 0
    rank = 0
    for col in range(n):
        piv = None
        for i in range(pivrow, len(mat)):
            if mat[i][col] != 0:
                piv = i
                break
        if piv is None:
            continue
        mat[pivrow], mat[piv] = mat[piv], mat[pivrow]
        pv = mat[pivrow][col]
        mat[pivrow] = [x / pv for x in mat[pivrow]]
        for i in range(len(mat)):
            if i != pivrow and mat[i][col] != 0:
                fac = mat[i][col]
                mat[i] = [a - fac * b for a, b in zip(mat[i], mat[pivrow])]
        if t[col] != 0:
            fac = t[col]
            t = [a - fac * b for a, b in zip(t, mat[pivrow])]
        pivrow += 1
        rank += 1
    return not any(t)


def rank_exact(rows, n):
    """Exact rank of integer/rational row vectors (lists of length n)."""
    mat = [[Fr(x) for x in row] for row in rows]
    rank = 0
    for col in range(n):
        piv = None
        for i in range(rank, len(mat)):
            if mat[i][col] != 0:
                piv = i
                break
        if piv is None:
            continue
        mat[rank], mat[piv] = mat[piv], mat[rank]
        pv = mat[rank][col]
        mat[rank] = [x / pv for x in mat[rank]]
        for i in range(rank + 1, len(mat)):
            if mat[i][col] != 0:
                fac = mat[i][col]
                mat[i] = [a - fac * b for a, b in zip(mat[i], mat[rank])]
        rank += 1
    return rank


def hermite_solve(Q, J, data):
    """data[(t,j)] = [z^j]H(t+z), t in 1..Q, j<J. Returns coefficients of H (length QJ)."""
    N = Q * J
    A = []
    b = []
    for t in range(1, Q + 1):
        for j in range(J):
            row = [Fr(0)] * N
            for u in range(j, N):
                row[u] = Fr(comb(u, j)) * Fr(t) ** (u - j)
            A.append(row)
            b.append(Fr(data[(t, j)]))
    for col in range(N):
        piv = next(i for i in range(col, N) if A[i][col] != 0)
        A[col], A[piv] = A[piv], A[col]
        b[col], b[piv] = b[piv], b[col]
        pv = A[col][col]
        A[col] = [x / pv for x in A[col]]
        b[col] = b[col] / pv
        for i in range(N):
            if i != col and A[i][col] != 0:
                fac = A[i][col]
                A[i] = [a - fac * c for a, c in zip(A[i], A[col])]
                b[i] = b[i] - fac * b[col]
    return b


def random_cnf(n, m, seed, width=3, occ=3):
    """Random k-CNF with each variable occurring at most occ times (duplicates removed)."""
    rng = random.Random(seed)
    used = [0] * n
    clauses = []
    for _ in range(m):
        pool = [v for v in range(n) if used[v] < occ]
        if not pool:
            break
        k = min(width, len(pool))
        k = rng.randint(max(1, k - 1), k)
        vs = rng.sample(pool, k)
        for v in vs:
            used[v] += 1
        clauses.append([(v, rng.randint(0, 1)) for v in vs])
    return clauses


def count_cnf(n, clauses):
    cnt = 0
    for bits in itertools.product((0, 1), repeat=n):
        if all(any((bits[v] == 1) != bool(neg) for v, neg in cl) for cl in clauses):
            cnt += 1
    return cnt


def build_cnf_design(C, n, clauses, seed, broken=()):
    # Dummy constant-one factors for variables in no clause (Sec. 2.1).
    used = set(v for cl in clauses for v, _ in cl)
    scopes = [[v for v, _ in cl] for cl in clauses]
    negs = [dict(cl) for cl in clauses]
    for v in range(n):
        if v not in used:
            scopes.append([v])
            negs.append(None)

    def factor_eval(f, inputs, ring):
        if negs[f] is None:
            return ring.one
        return clause_eval(ring, [(inputs[v], negs[f][v]) for v in scopes[f]])

    return Design(C, n, scopes, factor_eval, seed=seed, broken=broken)
