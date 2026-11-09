#!/usr/bin/env python3
"""Partial exact checks of Appendix D: W(T) identity and 2-adic integrality (Lemma D.4),
and the tapered Hermite recovery identity (D.9) over Q. Does NOT test the recursion/mode expansion."""
import random
from fractions import Fraction as Fr
from math import comb
from eth_core import pmul, padd, pshift, peval, ptrim, pscale

def v2(x):
    x = Fr(x)
    if x == 0:
        return 10**9
    v = 0
    n, d = x.numerator, x.denominator
    while n % 2 == 0:
        n //= 2; v += 1
    while d % 2 == 0:
        d //= 2; v -= 1
    return v

def C_poly(L):
    p = [Fr(1)]
    for t in range(-L, L):
        p = pmul(p, [Fr(-t), Fr(1)])
    return p

def deriv(p):
    return [Fr(i) * p[i] for i in range(1, len(p))] or [Fr(0)]

def poly_exact_div(p, g):
    """p / g exactly, polys low-first over Q."""
    p = list(p); out = [Fr(0)] * max(1, len(p) - len(g) + 1)
    for i in range(len(p) - len(g), -1, -1):
        c = p[i + len(g) - 1] / g[-1]
        out[i] = c
        for j, gc in enumerate(g):
            p[i + j] -= c * gc
    assert all(x == 0 for x in p), 'not exact'
    return ptrim(out)

def check_D4(a):
    L = 2 ** a
    alpha = 2 ** (a + 1)
    S = list(range(-L, L))
    C = C_poly(L)
    C0 = peval(deriv(C), 0)
    results = []
    # Wxy(T) = C(T) / (C'(0)(T-(y-x)))
    for x in range(L):
        for y in range(L):
            denom = [Fr(-(y - x)), Fr(1)]
            P = pscale(1 / C0, poly_exact_div(C, denom))
            # W(0)
            w0 = peval(P, 0)
            assert w0 == (1 if x == y else 0), ('W(0) != I', x, y, w0)
            for t in S:
                # coefficients of W(t + alpha z)
                sh = pshift(P, t, len(P) + 1)
                coeffs = [c * Fr(alpha) ** j for j, c in enumerate(sh)]
                for c in coeffs:
                    assert v2(c) >= 0, ('non-integral', a, x, y, t, c, v2(c))
    return True

def hermite_D9(a, u, M, seed=0):
    """Check (D.9) exactly on a random polynomial F of degree <= M(2L-1) with Q coefficients."""
    assert u <= a
    L = 2 ** a
    alpha = Fr(2 ** (a + 1))
    h = -(-3 * M // u)  # ceil(3M/u)
    S = [t for t in range(-L, L)]
    def q_of(t):
        if t == 0:
            return 0
        i = v2(t)
        return h * max(0, u - i)
    rng = random.Random(seed)
    deg = M * (2 * L - 1)
    F = [Fr(rng.randint(-5, 5), rng.choice([1, 3, 5])) for _ in range(deg + 1)]
    nodes = [t for t in S if t != 0 and q_of(t) > 0]
    assert sum(q_of(t) for t in nodes) > deg
    total = Fr(0)
    for t in nodes:
        qt = q_of(t)
        # E_t(T) = prod_{q in S, q!=0,t} ((T-q)/(t-q))^{q_q}, truncated expansions in z with T=t+alpha z
        Fshift = pshift(F, t, qt)  # coefficients in z' = alpha z? F(t + alpha z): scale
        Fz = [c * alpha ** j for j, c in enumerate(Fshift)]
        # E_t(t + alpha z) as series truncated at z^{qt}
        E = [Fr(0)] * qt; E[0] = Fr(1)
        for q in S:
            if q == 0 or q == t or q_of(q) == 0:
                continue
            fact = [Fr(1), alpha / (t - q)]  # (1 + alpha z/(t-q))
            for _ in range(q_of(q)):
                new = [Fr(0)] * qt
                for i, v in enumerate(E):
                    for j, w in enumerate(fact):
                        if i + j < qt:
                            new[i + j] += v * w
                E = new
        # series division F/E mod z^qt
        inv = [Fr(0)] * qt
        inv[0] = 1 / E[0]
        for i in range(1, qt):
            inv[i] = -sum(E[j] * inv[i - j] for j in range(1, i + 1)) / E[0]
        quot = [sum(Fz[j] * inv[i - j] for j in range(i + 1)) for i in range(qt)]
        # Et(0): value of E_t at T=0
        Et0 = Fr(1)
        for q in S:
            if q == 0 or q == t or q_of(q) == 0:
                continue
            Et0 *= (Fr(0 - q) / Fr(t - q)) ** q_of(q)
        # evaluate quot at -t/alpha, degree < qt
        z0 = Fr(-t) / alpha
        val = sum(c * z0 ** j for j, c in enumerate(quot))
        total += Et0 * val
    return total == peval(F, 0), total, F[0]

def check_D10(a, u, h):
    L = 2 ** a
    S = list(range(-L, L))
    def q(t):
        if t == 0:
            return 0
        i = v2(t)
        return h * max(0, u - i)
    ok = True
    for t in S:
        if t == 0 or q(t) == 0:
            continue
        i = v2(t); D = 2 ** (a - i)   # D_t = L/2^i
        lhs = sum(q(c) * (v2(c) - v2(t - c)) for c in S if c not in (0, t))
        rhs = D * sum(Fr(j, 2 ** j) * (q_level(a, u, h, i + j) - q_level(a, u, h, i)) for j in range(1, a - i + 1))
        if lhs != rhs or lhs < -6 * D * h:
            ok = False
    return ok

def q_level(a, u, h, i):
    return h * max(0, u - i)

if __name__ == '__main__':
    print('Lemma D.4 W(0)=I, integrality of W(t+alpha z):', [check_D4(a) for a in (1, 2, 3)])
    ok = True
    for a, u, M in [(2, 1, 1), (2, 2, 2), (3, 2, 3), (3, 3, 2)]:
        for seed in range(3):
            r = hermite_D9(a, u, M, seed)
            ok &= r[0]
            print(f'  D.9 a={a} u={u} M={M} seed={seed}: match={r[0]}', flush=True)
    print('D.9 all match:', ok)
    print('(D.10) valuation identity and bound:', all(check_D10(a,u,h) for a in (2,3,4,5) for u in range(1,a+1) for h in (1,2,5)))
