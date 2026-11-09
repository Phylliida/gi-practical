#!/usr/bin/env python3
"""Exact arithmetic for Theorem H of w45-quartic.

Evaluates the parameters of the theorem as printed
    s' = min(s, d/2), R = ceil(sqrt(s'/2)), m = ceil((R d + 4)/(s'-1)), b = ceil((d+2)/R), t = 2m+b
and the variants with free integer R and the sharper per-pair bound.
Usage: h_arith.py"""
from fractions import Fraction as Fr
from math import isqrt, sqrt, ceil

def R_printed(sp):
    # ceil(sqrt(sp/2)) exactly: smallest integer R with 2 R^2 >= sp
    R = isqrt(sp // 2)
    while 2 * R * R < sp:
        R += 1
    return R

def t_exact(s, d):
    sp = min(s, d // 2)          # d even assumed for simplicity
    R = R_printed(sp)
    m = ceil(Fr(R * d + 4, sp - 1))
    b = ceil(Fr(d + 2, R))
    return R, m, b, 2 * m + b

def limit_printed(s):
    """lim_{d->oo} t/d for fixed s (so s'=s once d>=2s), printed parameters."""
    R = R_printed(s)
    return R, Fr(2 * R, s - 1) + Fr(1, R)

def limit_best_int_R(s):
    return min((Fr(2 * R, s - 1) + Fr(1, R), R) for R in range(1, 200))

def limit_refined_best_int_R(s):
    """Using Pr <= 2^{R-d} + 2^{-s} = 2^{-s}(1+o(1)) instead of 2^{1-s'}: m ~ R d / s."""
    return min((Fr(2 * R, s) + Fr(1, R), R) for R in range(1, 200))

print("=== fixed s, d -> infinity: limit of t/d (beats w17 iff < 1/4) ===")
print("  s | printed R   t/d      | best int R, s-1 denominator | refined (2^-s) best R")
print("(the rank of an alternating form is even, so only even s can occur; s=129,... listed only to locate the real-number threshold)")
for s in list(range(126, 135)) + [162, 200]:
    R, v = limit_printed(s)
    bv, bR = limit_best_int_R(s)
    rv, rR = limit_refined_best_int_R(s)
    flag = lambda x: "<1/4" if x < Fr(1, 4) else ("=1/4" if x == Fr(1, 4) else ">1/4")
    print(f"{s:4d} | R={R:2d} {float(v):.5f} {flag(v):5s} | R={bR:2d} {float(bv):.5f} {flag(bv):5s} | R={rR:2d} {float(rv):.5f} {flag(rv):5s}")

first = next(s for s in range(4, 1000, 2) if limit_printed(s)[1] < Fr(1, 4))
firstb = next(s for s in range(4, 1000, 2) if limit_best_int_R(s)[0] < Fr(1, 4))
firstr = next(s for s in range(4, 1000, 2) if limit_refined_best_int_R(s)[0] < Fr(1, 4))
print(f"smallest EVEN s with t/d limit < 1/4: printed parameters s={first}, best integer R s={firstb}, sharper pair bound s={firstr}")
print("monotone beyond threshold (even s)? printed:", all(limit_printed(s)[1] < Fr(1,4) for s in range(first, 3000, 2)),
      " best-R:", all(limit_best_int_R(s)[0] < Fr(1,4) for s in range(firstb, 3000, 2)))
print("non-monotone printed? violations of '<1/4' for s>=129 up to 200:", [s for s in range(129, 201) if limit_printed(s)[1] >= Fr(1, 4)])

print("\n=== coefficient c with t ~ c d / sqrt(s') vs claimed 2 sqrt 2 =", round(2*sqrt(2),4), "===")
for s in (2, 8, 32, 50, 128, 129, 131, 200, 1000, 10000):
    R, v = limit_printed(s)
    print(f"s={s:6d} R={R:3d}: t/d limit {float(v):.5f}, coefficient {float(v)*sqrt(s):.4f}")

print("\n=== s' = d/2 (s >= d/2): t and t*d vs d^2/4 ===")
hdr = "  d   s'  R   m   b    t   t*d  d^2/4  beats  4*sqrt(d)"
print(hdr)
for d in (20, 50, 100, 200, 256, 300, 400, 512, 1000, 4096, 10**5):
    s = 10**9
    R, m, b, t = t_exact(s, d)
    print(f"{d:6d} {d//2:5d} {R:4d} {m:4d} {b:6d} {t:6d} {t*d:9d} {d*d//4:9d} {'yes' if t*d < d*d//4 else 'no':4s} {4*sqrt(d):8.1f}")
print("smallest even d such that the printed t*d < d^2/4 when s >= d/2:",
      next(d for d in range(4, 100000, 2) if t_exact(10**9, d)[3] * d < d * d // 4))

print("\n=== cap refinement: s' = min(s, d-R) instead of min(s, d/2) ===")
print("At s = d-O(sqrt d) (random): t ~ 2 sqrt 2 * sqrt d instead of 4 sqrt d (exponent 2.83 d^1.5 vs 4 d^1.5).")

print("\n=== Proposition B count: largest k with #histograms < #orbits for a given d ===")
from math import comb, log2
def count_ok(d, k):
    t = sum(comb(k, i) for i in range(5))
    # log2(#histograms) <= t * log2(2^{kd}+1) <= t*(k*d+1); log2(#orbits) >= C(d,4) - d^2
    # compute log2 of log2 to avoid huge ints: need 2^t*(k*d+1) < C(d,4)-d^2
    return 2 ** t * (k * d + 1) < comb(d, 4) - d * d if t < 2000 else False
for logd in (10, 20, 30, 40, 60, 80, 200, 800):
    d = 2 ** logd
    k = 1
    while count_ok(d, k + 1):
        k += 1
    print(f"d=2^{logd}: largest certified k = {k}; (72 log2 d)^(1/4) = {(72*logd)**0.25:.2f}")

print("\n=== smallest d with t*d < d^2/4 at the printed parameters, fixed s (d >= 2s so s'=s) ===")
for s in (132, 134, 140, 150, 162, 200, 400):
    d = 2 * s
    if d % 2:
        d += 1
    while t_exact(s, d)[3] * d >= d * d // 4:
        d += 2
    print(f"s={s}: d={d}")
