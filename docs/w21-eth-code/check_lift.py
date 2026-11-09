#!/usr/bin/env python3
"""Exact checks of the Sec. 5 parity lift: Lemma 5.1, Lemma 5.2, and the full common-zero pipeline
with coefficients in A_ell = Q[V]/(V^ell) on small polynomial systems over F_2."""
import itertools, random, sys, time
from fractions import Fraction as Fr
from math import comb
from eth_core import Construction, Design, Ring, hermite_solve, pshift, peval

def p_ell_coeffs(ell):
    # p_ell(Y) = (1-Y)^ell * sum_{j<ell} C(ell+j-1, j) Y^j   (integer coefficients, low-degree first)
    a = [(-1) ** i * comb(ell, i) for i in range(ell + 1)]
    b = [comb(ell + j - 1, j) for j in range(ell)]
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out

def decompose(p):
    """p = sum_{j} e_j(Y) h(Y)^j, h = Y^2 - Y, deg e_j <= 1, by successive division. Integer coefs."""
    p = list(p)
    es = []
    while True:
        while len(p) > 1 and p[-1] == 0:
            p.pop()
        if len(p) <= 2:
            e = p + [0] * (2 - len(p))
            es.append((e[0], e[1]))
            break
        # divide by h=Y^2-Y: quotient q, remainder e of degree <=1
        q = [0] * (len(p) - 2)
        r = list(p)
        for i in range(len(p) - 1, 1, -1):
            c = r[i]
            q[i - 2] = c
            r[i] -= c
            r[i - 1] += c
        e = r[:2]
        es.append((e[0], e[1]))
        p = q
    return es

def lemma51():
    for ell in range(1, 12):
        p = p_ell_coeffs(ell)
        es = decompose(p)
        # recompose
        def h(Y): return Y * (Y - 1)
        for y in range(-40, 41):
            val = sum(p[i] * y ** i for i in range(len(p)))
            rec = sum((a + b * y) * h(y) ** j for j, (a, b) in enumerate(es))
            assert val == rec, ('recompose', ell, y)
            expect = 1 if y % 2 == 0 else 0
            assert (val - expect) % (2 ** ell) == 0, ('congruence', ell, y)
        assert len(es) <= ell + 1
        assert all(isinstance(a, int) and isinstance(b, int) for a, b in es)
    return True

def lemma52(trials=4000, seed=0):
    rng = random.Random(seed)
    for _ in range(trials):
        ell = rng.randint(1, 7)
        m = rng.randint(1, 6)
        es = decompose(p_ell_coeffs(ell))
        ys = [rng.randint(-30, 30) for _ in range(m)]
        h = lambda y: y * (y - 1)
        # product of B_i(V) truncated mod V^ell
        prod = [0] * ell
        prod[0] = 1
        for y in ys:
            B = [(es[j][0] + es[j][1] * y) * h(y) ** j if j < len(es) else 0 for j in range(ell)]
            new = [0] * ell
            for a, x in enumerate(prod):
                if x:
                    for b, w in enumerate(B):
                        if a + b < ell:
                            new[a + b] += x * w
            prod = new
        target = 1
        for y in ys:
            target *= 1 if y % 2 == 0 else 0
        assert (sum(prod) - target) % (2 ** ell) == 0, (ell, m, ys)
    # degree bound: with y_i = Y formal, truncated product has Y-degree <= m + 2(ell-1)
    worst = 0
    for ell in range(2, 8):
        for m in range(1, 7):
            es = decompose(p_ell_coeffs(ell))
            prod = [[1]] + [[] for _ in range(ell - 1)]   # list over V^s of polys in Y
            for _ in range(m):
                new = [[] for _ in range(ell)]
                for s, py in enumerate(prod):
                    if not py:
                        continue
                    for j in range(min(ell, len(es))):
                        if s + j >= ell:
                            continue
                        # factor e_j(Y) h(Y)^j as poly in Y
                        f = [es[j][0], es[j][1]]
                        for _h in range(j):
                            g = [0] * (len(f) + 2)
                            for i, c in enumerate(f):
                                g[i + 2] += c   # * Y^2
                                g[i + 1] -= c   # * (-Y)
                            f = g
                        conv = [0] * (len(py) + len(f) - 1)
                        for i, a in enumerate(py):
                            for k, b in enumerate(f):
                                conv[i + k] += a * b
                        tgt = new[s + j]
                        if len(tgt) < len(conv):
                            tgt.extend([0] * (len(conv) - len(tgt)))
                        for i, c in enumerate(conv):
                            tgt[i] += c
                prod = new
            deg = max((i for py in prod for i, c in enumerate(py) if c != 0), default=0)
            assert deg <= m + 2 * (ell - 1), (ell, m, deg)
            worst = max(worst, deg)
    return True

def random_system(n, m, seed, k=2, mono=3):
    rng = random.Random(seed)
    sys_ = []
    for _ in range(m):
        mons = set()
        for _ in range(rng.randint(1, mono)):
            sz = rng.randint(0, k)
            mons.add(frozenset(rng.sample(range(n), min(sz, n))))
        sys_.append(sorted(sorted(mm) for mm in mons))
    return sys_

def count_zeros(n, system):
    cnt = 0
    for bits in itertools.product((0, 1), repeat=n):
        if all(sum(all(bits[v] for v in mon) for mon in poly) % 2 == 0 for poly in system):
            cnt += 1
    return cnt

def make_design(C, n, system, ell, seed, broken=()):
    # scopes: union of monomials of each equation; dummy factors for unused variables
    scopes = [sorted(set(v for mon in poly for v in mon)) for poly in system]
    used = set(v for s in scopes for v in s)
    extra = [[v] for v in range(n) if v not in used]
    m_test = len(system)
    all_scopes = scopes + extra
    es = decompose(p_ell_coeffs(ell))
    h_of = lambda ring, L: ring.mul(L, ring.sub(L, ring.one))

    def factor_eval(f, inputs, ring):
        if f >= m_test:
            return ring.one
        poly = system[f]
        L = ring.zero
        for mon in poly:
            term = ring.one
            for v in mon:
                term = ring.mul(term, inputs[v])
            L = ring.add(L, term)
        hL = h_of(ring, L)
        result = ring.zero
        hp = ring.one
        for j in range(ring.ell):
            a, b = es[j] if j < len(es) else (0, 0)
            ej = ring.add(ring.const(a), ring.scale(Fr(b), L))
            result = ring.add(result, ring.mul(ring.mul(ej, hp), ring.vmonomial(j)))
            hp = ring.mul(hp, hL)
        return result

    return Design(C, n, all_scopes, factor_eval, seed=seed, broken=broken), m_test

def to_lists(ring, a):
    return [ring.to_list(a, s) for s in range(ring.ell)]

def pipeline(cfg, n, m, seed, k=2, mono=3, broken=()):
    r, Q, R = cfg
    system = random_system(n, m, seed, k=k, mono=mono)
    N = count_zeros(n, system)
    ell = n + 1
    C = Construction(r, Q, R)
    d, m_test = make_design(C, n, system, ell, seed + 7, broken=broken)
    # input degree bound d=k(m_test + 2(ell-1)) (Lemma 5.2) -- with k-degree monomials
    dinp = k * (m_test + 2 * (ell - 1))
    dT = dinp * (R - 1) + 1
    q = (dinp * (R - 1)) // Q
    J = q + 1
    ring_T = Ring(dT + 2, ell)
    HT = d.H_poly(ring_T)
    Hs = to_lists(ring_T, HT)
    # H(0) check: S_ell(H(0)) mod 2^ell = N
    u = sum(int(Hs[s][0]) if Hs[s][0].denominator == 1 else None for s in range(ell))
    h0_ok = (u % (2 ** ell)) == N
    deg_ok = all(all(c == 0 for c in Hs[s][dinp * (R - 1) + 1:]) for s in range(ell))
    # separation at t, values in A_ell
    sep_ok = True
    for t in range(1, Q + 1):
        ring0 = Ring(1, ell)
        z = d.Z_factorized(t, set(), set(), ring0)
        vals = [ring0.to_list(z, s)[0] for s in range(ell)]
        expected = [peval(Hs[s], t) for s in range(ell)]
        if vals != expected:
            sep_ok = False
    # Taylor by IE in A_ell and Hermite per V-coefficient
    tay_ok = True
    data = {s: {} for s in range(ell)}
    for t in range(1, Q + 1):
        ring = Ring(J, ell)
        got = d.taylor_IE(t, q, ring)
        for s in range(ell):
            g = ring.to_list(got, s)
            e = pshift(Hs[s], t, J)
            if g != e:
                tay_ok = False
            for j in range(J):
                data[s][(t, j)] = g[j]
    rec_ok = True
    total = Fr(0)
    for s in range(ell):
        c = hermite_solve(Q, J, data[s])
        total += c[0]
    if total.denominator != 1:
        rec_ok = False
    rec_val = int(total) % (2 ** ell)
    rec_ok = rec_ok and rec_val == N
    return dict(n=n, m=m, N=N, ell=ell, u_mod=u % (2 ** ell), h0_ok=h0_ok, deg_ok=deg_ok,
                sep_ok=sep_ok, tay_ok=tay_ok, rec_ok=rec_ok, rec_val=rec_val, h=d.h, J=J, q=q, M=d.M)

if __name__ == '__main__':
    t0 = time.time()
    print('Lemma 5.1 (p_ell congruence, e_j decomposition):', lemma51())
    print('Lemma 5.2 (truncated product congruence; degree <= m+2(ell-1) for y_i=Y):', lemma52())
    for cfg, n, m, seeds in [((2, 3, 2), 4, 3, range(4)), ((2, 2, 2), 4, 3, range(3))]:
        for s in seeds:
            t1 = time.time()
            rep = pipeline(cfg, n, m, s)
            print(f'  cfg={cfg} seed={s} {rep}  ({time.time()-t1:.1f}s)', flush=True)
            assert all(rep[k] for k in ['h0_ok', 'deg_ok', 'sep_ok', 'tay_ok', 'rec_ok'])
    print('all lift checks pass, total %.1fs' % (time.time() - t0))
