#!/usr/bin/env python3
"""Arithmetic check of the parameter choices (2.19)/(4.17): where do the constraints first hold,
and where does the (3.16) exponent drop below 1 (beating 2^n)? All exact rationals except logs."""
import math
from fractions import Fraction as Fr

def params(lam, nu=None, beta=1):
    nu = nu or math.ceil(math.log2(lam))
    r = math.isqrt(lam // (nu ** 4)) if lam >= nu ** 4 else 0  # r = floor(sqrt(lam)/nu^2)
    Q = lam // (128 * nu)
    Rr = (beta + 3) * math.isqrt(lam + (math.isqrt(lam) ** 2 != lam) * 0)
    if math.isqrt(lam) ** 2 != lam:
        Rr = (beta + 3) * (math.isqrt(lam) + 1)
    return r, Q, Rr, nu

def exponent(lam, beta=1, M_over_n=3, sharp=False):
    """(3.16)-style bound with bounded-occurrence constants: returns (valid?, value)."""
    r, Q, R, nu = params(lam, beta=beta)
    valid = r >= 2 and R >= 32 and 6 * R <= Q
    if r < 2 or Q <= 0:
        return False, None
    D_log2 = 2 * Q * math.log2(r)              # log2 D
    x = min(1.0, M_over_n * (R) / Q)           # q/n with q=floor(M R / Q)
    binary_entropy_term = x * math.log2(2 * math.e / x) if x > 0 else 0
    measure = 2 * (1 / (r * lam)) * (D_log2 + 2)
    group = 2.0 / r
    return valid, binary_entropy_term + measure + group

def main():
    # first lambda (=ceil log2 n) where constraints hold, and where exponent < 1
    lam = 1024
    first_valid = None
    first_beat = None
    while lam < 2 ** 200:
        v, e = exponent(lam)
        if v and first_valid is None:
            first_valid = lam
        if v and e is not None and e < 1 and first_beat is None:
            first_beat = lam
        lam += max(1, lam // 64)
    print('first lam with r>=2, R>=32, 6R<=Q (beta=1):', first_valid, ' log2(lam)=%.1f' % math.log2(first_valid))
    print('first lam where exponent (3.16) < 1:', first_beat, ' log2(lam)=%.1f' % math.log2(first_beat))
    for k in (40, 60, 80, 100, 150, 200, 400, 800):
        v, e = exponent(2 ** k)
        print(f'  lam=2^{k}: valid={v} exponent/n={e}')

if __name__ == '__main__':
    main()
