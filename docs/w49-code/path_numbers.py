#!/usr/bin/env python3
"""w49: exact arithmetic along the trace, for x=Cay(V(x)U, R1 u H), V=F_2^d, U=F_2^e."""
from fractions import Fraction as Fr
from math import log2
def gl(k):
    o=1
    for i in range(k): o*=2**k-2**i
    return o
def sp(k):
    o=2**((k//2)**2)
    for i in range(1,k//2+1): o*=4**i-1
    return o
def inj(d,r):
    o=1
    for i in range(r): o*=2**d-2**i
    return o
for d,e in [(16,4),(32,4),(200,128),(400,128),(1000,128)]:
    n=2**(d*e); W=inj(d,e); R=(2**d-1)*(2**e-1)
    gen=W*inj(d-e,e)*2**(e*e) if False else inj(d,2*e)
    wfrac=Fr(W,n); genfrac=Fr(gen,n*n)
    other=2*W*(n-W)+(n-W)**2
    lidx=log2(gl(d))-log2(sp(d))
    print(f"d={d} e={e} log2n={d*e} W/n={float(wfrac):.6f} (>3/4:{wfrac>Fr(3,4)}) |R1|/n=2^{log2(R)-d*e:.1f}"
          f" Ogen/n^2={float(genfrac):.6f} other/n^2<=2^{log2(other)-2*d*e:.1f}"
          f" log2|GL|={log2(gl(d)):.1f} log2[GL:Sp]={lidx:.1f}"
          f" log2[GL:Sp]/log2(n)={lidx/(d*e):.3f}")
