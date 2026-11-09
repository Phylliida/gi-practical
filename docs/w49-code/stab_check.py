#!/usr/bin/env python3
"""w49: enumerate (g,h) in GL(d,2)xGL(e,2) preserving H cap W (Q on rank-e matrices), action M -> g M h^-1.
Expected: Sp(d,2) x Sp(e,2) (order |Sp(4,2)|*|Sp(2,2)|=720*6=4320 for (4,2))."""
import itertools,sys
sys.path.insert(0,'.')
from construct import Q,rank
d,e=4,2
def invertibles(k):
    out=[]
    for vs in itertools.product(range(1,1<<k),repeat=k):
        # vs = rows as ints
        rows=list(vs); r=0; ok=True; A=rows[:]
        for j in range(k):
            p=None
            for i in range(r,k):
                if A[i]>>j &1: p=i;break
            if p is None: ok=False;break
            A[r],A[p]=A[p],A[r]
            for i in range(k):
                if i!=r and A[i]>>j &1: A[i]^=A[r]
            r+=1
        if ok: out.append(vs)
    return out
GLd=invertibles(d); GLe=invertibles(e)
print(len(GLd),len(GLe))
Mlist=[M for M in range(1,1<<(d*e)) if rank(d,e,M)==e]
print("W size",len(Mlist))
def act(g,h,M):
    # M bits (i,j): i row 0..d-1 (coordinate of V), j column 0..e-1 (coordinate of U)
    # columns c_j in V (d-bit ints); left mult by g on column vectors; right by h on row combos
    cols=[0]*e
    for i in range(d):
        for j in range(e):
            if M>>(i*e+j)&1: cols[j]|=1<<i
    # apply g: new column g*c where (g*c)_i = parity(g[i] & c)
    ncols=[]
    for c in cols:
        nc=0
        for i in range(d):
            if bin(g[i]&c).count('1')%2: nc|=1<<i
        ncols.append(nc)
    # right mult by h: new column j = sum_k h[k]_j ... (M h): column j = sum_k M_col_k h_kj
    rcols=[0]*e
    for j in range(e):
        c=0
        for k in range(e):
            if (h[k]>>j)&1: c^=ncols[k]
        rcols[j]=c
    N=0
    for j in range(e):
        for i in range(d):
            if rcols[j]>>i &1: N|=1<<(i*e+j)
    return N
count=0; goodg=set(); goodh=set()
Qtab={M:Q(d,e,M) for M in range(1<<(d*e))}
for g in GLd:
    for h in GLe:
        ok=True
        for M in Mlist:
            if Qtab[act(g,h,M)]!=Qtab[M]: ok=False;break
        if ok:
            count+=1; goodg.add(g); goodh.add(h)
print("preservers (g,h):",count,"distinct g:",len(goodg),"distinct h:",len(goodh))
