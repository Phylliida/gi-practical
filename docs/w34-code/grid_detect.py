#!/usr/bin/env python3
# grid_detect.py: does T(a,x,.) identify rows/columns of W(V,V)?  For a fixed a, classify x as row/col/other and
# report min_y |T(a,x,y)| and the number of distinct T values.  Pure Python.  Also limit-round shattering at L=2.
import sys, os, random
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'w32-code'))
import gen
from turyn_shatter import base_seidel, Turyn
from turyn_structure import stable_partition

def grid(spec, a=(1,2)):
    V=base_seidel(spec); v=len(V)
    W=gen.turyn(V,V); n=v*v
    ai=a[0]*v+a[1]
    stats={'row':[], 'col':[], 'other':[]}
    Wa=W[ai]
    for x in range(n):
        if x==ai: continue
        g=[Wa[z]*W[x][z] for z in range(n)]
        vals=[sum(g[z]*W[y][z] for z in range(n)) for y in range(n) if y!=ai and y!=x]
        k='row' if x//v==a[0] else ('col' if x%v==a[1] else 'other')
        stats[k].append((min(abs(t) for t in vals), len(set(vals)), max(abs(t) for t in vals)))
    for k,s in stats.items():
        print(f"base {spec} n={n} v={v} {k}: pairs {len(s)} min|T| range [{min(t[0] for t in s)},{max(t[0] for t in s)}], distinct-T range [{min(t[1] for t in s)},{max(t[1] for t in s)}], max|T| range [{min(t[2] for t in s)},{max(t[2] for t in s)}]")

def limit_shatter_L2(spec):
    V=base_seidel(spec); v=len(V)
    TT=Turyn(V,2); m=TT.m; n=v**m
    verts=list(TT.all_vertices())
    W=[[TT.entry_digits(a,b) for b in verts] for a in verts]
    s,t=0,1
    al=next(u for u in range(2,v) if V[u][s]==V[u][t])
    alp=next(u for u in range(2,v) if V[u][s]!=V[u][t])
    z=s; d=m-1
    tests=[]
    for i in range(d):
        a=[al]*m; b=[al]*m; a[i]=alp
        tests.append((TT.index(a),TT.index(b)))
    for rounds in (2,None):
        ok=True
        for mask in range(2**d):
            Y={i for i in range(d) if (mask>>i)&1}
            xs=[z if (j<d and j in Y) else s for j in range(m)]
            ys=[z if (j<d and j in Y) else t for j in range(m)]
            x=TT.index(xs); y=TT.index(ys)
            for i,(a,b) in enumerate(tests):
                col=stable_partition(W,n,[a,b],rounds)
                if (col[x]==col[y])!=(i in Y):
                    ok=False; print("MISMATCH",rounds,mask,i)
        print(f"limit/2-round shatter L=2 base {spec} n={n} d={d} rounds={rounds}: {'OK' if ok else 'FAIL'}")

if __name__=='__main__':
    grid('9'); grid('13')
    limit_shatter_L2('5')
