#!/usr/bin/env python3
"""How close can the Sec. 3-4 machinery get to a GI-type sum-product?

Input: witness bits n, incidences M, max incidence b, max scope w, total degree d.
Search over r, Q (D=r^{2Q} with 2(b+w)D^2 <= M and hD<=2M), interval length R (exact binomial
tail <= tau/(r*b)), and tau (grid). Report the best exponent/n of (3.16) (>=1: no gain over 2^n).
'infeasible' = no (r,Q,R) with R<Q satisfies Lemma 4.7's hypotheses."""
import math
from math import comb

def tail_outside_best_interval(Q, p_num, p_den, R):
    """Exact Pr[Bin(Q,p) outside the best interval of R consecutive integers] as (log value or -inf)."""
    weights = [comb(Q, j) * p_num ** j * (p_den - p_num) ** (Q - j) for j in range(Q + 1)]
    total = sum(weights)
    cur = sum(weights[:R])
    best = cur
    for i in range(R, Q + 1):
        cur += weights[i] - weights[i - R]
        best = max(best, cur)
    outside = total - best
    if outside == 0:
        return float('-inf')
    return math.log(outside) - Q * math.log(p_den)

def best_exponent(n, M, b, w, d):
    best = None
    log2M = math.log2(M)
    for r in [2, 3, 4, 6, 8, 16, 32, 64, 128, 256]:
        Dlog2_per_Q = 2 * math.log2(r)
        Qmax = int((log2M - 1 - math.log2(b + w)) / (2 * Dlog2_per_Q))
        if Qmax < 2:
            continue
        for Q in range(2, min(Qmax, 2000) + 1):
            if 2 * Q * r * r > n:
                break
            p_num, p_den = r - 1, 2 * r
            Dlog2 = Q * Dlog2_per_Q
            for tau in [10 ** (-e) for e in range(1, 12)]:
                if tau > 0.5:
                    continue
                logeps = math.log(tau) - math.log(r * b)
                # smallest R < Q with tail <= eps
                R = None
                for RR in range(1, Q):
                    if tail_outside_best_interval(Q, p_num, p_den, RR) <= logeps:
                        R = RR
                        break
                if R is None:
                    continue
                q = min(n, d * R // Q)
                if q <= 0:
                    expo_taylor = 0.0
                elif q >= n:
                    expo_taylor = math.log2(3) * n
                else:
                    x = q / n
                    expo_taylor = x * n * math.log2(2 * math.e / x)
                expo = (expo_taylor + 2 * tau * n * (Dlog2 + 2) + 2 * n / r) / n
                if best is None or expo < best[0]:
                    best = (expo, r, Q, R, tau, q)
    return best

def show(name, n, M, b, w, d):
    res = best_exponent(n, M, b, w, d)
    if res is None:
        print(f'{name:40s} n={n:.3g} M={M:.3g} b={b:.3g} w={w:.3g} d={d:.3g}: infeasible (no r,Q,R with R<Q)')
    else:
        e, r, Q, R, tau, q = res
        print(f'{name:40s} n={n:.3g} M={M:.3g} b={b:.3g} w={w:.3g} d={d:.3g}: best exponent/n={e:.3f} (r={r},Q={Q},R={R},tau={tau:g},q={q:g})')

if __name__ == '__main__':
    print('--- control: bounded-occurrence 3-SAT at moderate n (the paper regime needs n > 2^(2^36)) ---')
    for lg in (20, 60, 200, 1000):
        n = 2.0 ** lg
        show(f'3-SAT-3, n=2^{lg}', n, 3 * n, 3, 3, 3 * n)
    print('\n--- 3-tensor isomorphism over F_2, witness 3k^2 bits ---')
    for k in (2 ** 10, 2 ** 20, 2 ** 40, 2 ** 80):
        n = 3 * k * k
        # direct: k^3 equations of degree 3, each variable in k^2 equations, scope 3k
        show(f'TI direct, k={k:.2g}', n, 3 * k ** 4, k * k, 3 * k, 3 * k ** 3)
        # Sec. 6-style compression, optimistically with test length 1: O(n) tests, scope 3k, b ~ 3k*sqrt(log n)
        lam = math.log2(n)
        show(f'TI compressed (optimistic), k={k:.2g}', n, 9 * k ** 3, 3 * k * math.sqrt(lam), 3 * k, 3 * 3 * n)
        # Tovey-style copying: n = M, b = w = 3 (now the witness bit count is M, not 3k^2)
        show(f'TI after copying (n=M), k={k:.2g}', 9.0 * k ** 3, 9.0 * k ** 3 * 3, 3, 3, 9.0 * k ** 3 * 3)
    print('\n--- AGL(k,2) string isomorphism, witness k^2+k bits ---')
    for k in (20, 40, 80, 160, 500):
        n = k * k + k
        N = 2.0 ** k
        show(f'AGL direct, k={k}', n, N * k * k / 2, N, k * k, N * k)
        show(f'AGL after copying (n=Nk), k={k}', N * k, 3 * N * k, 3, 3, 3 * N * k)
