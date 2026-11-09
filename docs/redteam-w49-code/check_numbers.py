#!/usr/bin/env python3
"""Exact arithmetic for the w49 red team: index formula, exponents, n >= 2^?, class counts."""
from fractions import Fraction as Fr
from math import log2
def gl(k):
    o = 1
    for i in range(k): o *= 2**k - 2**i
    return o
def sp(k):
    m = k//2; o = 2**(m*m)
    for i in range(1, m+1): o *= 4**i - 1
    return o
print("index [GL(d,2):Sp(d,2)] vs memo's closed form 2^{d^2/4-d/2} prod_{j<=d/2}(2^{2j-1}-1):")
for d in [2,4,6,8,10,64]:
    idx = Fr(gl(d), sp(d))
    assert idx.denominator == 1
    idx = idx.numerator
    p = 1
    for j in range(1, d//2+1): p *= 2**(2*j-1) - 1
    cf = 2**(d*d//4 - d//2) * p
    # compute log2 exactly enough via integer shifting
    lg = idx.bit_length() - 1 + (idx / 2**(idx.bit_length()-1)) .__class__(idx)/2**(idx.bit_length()-1) if False else (idx.bit_length()-1)
    print(f"  d={d}: index==closed form: {idx==cf}; bit_length-1 = {lg}; d^2/2-d/2 = {d*d/2-d/2}")
print("\nexponent check with N=n^2=2^(2de): log2[GL:Sp] / log2(N)^2 vs 1/(8e^2)  (e=128, d=260,520)")
e=128
for d in [260,520]:
    logN = 2*d*e
    lidx = gl(d).bit_length() - sp(d).bit_length()
    print(f"  d={d}: log2 index ~ {lidx}; log2N={logN}; ratio={lidx/logN**2:.4e}; 1/(8e^2)={1/(8*e*e):.4e}; d^2/2={d*d/2}")
print("\nscale at kappa=64:")
e=128
print(f"  2e+3={2*e+3} (odd), smallest even d >= 2e+3 is {2*e+4}; de = {e*(2*e+3)} vs {e*(2*e+4)}")
print("  so n >= 2^%d, not 2^33152" % (e*(2*e+4)))
print("\nconjugacy class count c(k)=|Cl(GL(k,2))| from prod (1-t^i)/(1-2t^i):")
K=32
c=[0]*(K+1); c[0]=1
for i in range(1,K+1):
    # multiply by (1-t^i)/(1-2 t^i)
    # series for 1/(1-2 t^i)
    new=[0]*(K+1)
    for a in range(K+1):
        if c[a]==0: continue
        j=0
        while a+j*i<=K:
            new[a+j*i]+=c[a]*2**j
            j+=1
    # multiply by (1-t^i)
    for a in range(K,i-1,-1): new[a]-=new[a-i]
    c=new
print("  k: c(k)", [(k,c[k]) for k in range(1,9)])
print("  c(k) <= 2^k for k up to %d: %s" % (K, all(c[k] <= 2**k for k in range(1,K+1))))
print("  double-coset bound for d=2k: c(d/2) children; [GL:Sp] exponent d^2/2, double-coset exponent d/2")
