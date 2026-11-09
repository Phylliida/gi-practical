#!/usr/bin/env python3
"""Exact arithmetic for the numeric claims of docs/w47-mu.md (independent of its path_numbers.py)."""
import math
from fractions import Fraction

def gl(k):
    r = 1
    for i in range(k):
        r *= 2**k - 2**i
    return r

def g2(k):
    return (2**k - 1) * (2**(k - 1) - 1) // 3

def gauss(k, j):
    # number of j-subspaces of F_2^k
    num = den = 1
    for i in range(j):
        num *= 2**(k - i) - 1
        den *= 2**(i + 1) - 1
    return num // den

print("m  n log2n  |W|/|L|  |O_gen|/N   d/n   log2|P|/(log2 n)^2  log2|P|-((m-2)^2)  mu_coord/log2N  mu_unord/log2N  0.288*2^(k^2)<=|P|")
for m in [5, 6, 7, 8, 9, 10, 12, 16, 20, 32, 64, 150, 214]:
    k = m - 2
    pts = 2**m - 1
    L = g2(m)
    n = pts + L
    N = n * n          # HJ sets N <- |Omega| = n^2 (L1145, L596)
    W = (2**m - 4) * (2**m - 8) // 6
    Ogen = W * (2**m - 16) * (2**m - 32) // 6 if m >= 6 else 0
    d = g2(k)
    P = gl(k)
    lgP = math.log2(P)
    lgN = 2 * math.log2(n)
    mu = lgP / math.log2(d) if d > 1 else float("nan")
    d4 = gauss(k, 4) if k >= 5 else 0
    mu4 = lgP / math.log2(d4) if d4 > 1 else float("nan")
    bound = Fraction(288, 1000) * 2**(k * k)
    print(f"{m:4d} {math.log2(n):8.3f} {W/L:8.4f} {Ogen/N:9.4f} {d/n:8.4f} {lgP/math.log2(n)**2:8.4f} {lgP-k*k:9.3f} {mu/lgN:8.4f} {mu4/lgN:8.4f} {P>=bound}")

print()
print("n at m=64: log2 =", math.log2(g2(64) + 2**64 - 1))
print("Unordered-pair tower: degree of the exposed action is |G_4(F_2^k)|; k=5 -> ", gauss(5, 4))

print("\nLargest orbit of H on Omega_1 (per w in W, compare O_gen with others):")
for m in range(6, 13):
    gen = (2**m - 16) * (2**m - 32) // 6
    nonW = 2**m - 1 + 3 * (2**(m - 1) - 2) + 1
    print(m, "gen", gen, "|Gamma\\W|", nonW, "others (6,9,3(2^m-16)/2,9(2^m-16)/2):", 6, 9, 3 * (2**m - 16) // 2, 9 * (2**m - 16) // 2)

print("\nFirst-rectangle threshold |W| > (3/4)|C| (eta=3/4 in Lean/HJ example):")
for m in range(4, 9):
    W = (2**m - 4) * (2**m - 8) // 6
    print(m, W, g2(m), W / g2(m) > 0.75)
print("\nB1 lower-bound exponent m^2/2 vs (m-2)^2: first m >= 3 with (m-2)^2 > m^2/2 (ignoring the O_kappa(m) term): ", next(m for m in range(3, 100) if (m - 2)**2 > m**2 / 2))

# Theorem A': a kappa-set of lines on which GL(V) induces Sym(T), for m = kappa
print("\nFull test in J_2(m,2) at m = kappa: lines {e_i, 1, e_i+1}, 1 = all-ones vector")
for kappa in range(3, 9):
    one = (1 << kappa) - 1
    lines = [frozenset({1 << i, one, (1 << i) ^ one}) for i in range(kappa)]
    ok = all(len(l) == 3 and 0 not in l for l in lines) and len(set(lines)) == kappa
    print(f"kappa={kappa}: distinct lines {ok}; coordinate permutations fix the all-ones vector and permute the lines as Sym(kappa)")

# Small test
print("\nSmall test: ln|P| <= a*(ln d)^2")
for m, a in [(64, 1), (64, 128), (7, 1)]:
    k = m - 2
    print(f"m={m}, a={a}: {math.log(gl(k)):.1f} <= {a*(math.log(g2(k)))**2:.1f}")
