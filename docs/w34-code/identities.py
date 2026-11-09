#!/usr/bin/env python3
# identities.py: checks equitable-partition identity (Prop 6.1), cell bound, nonsquare parity/trace on real graphs.
import sys, os, random, math
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'w32-code'))
import gen
from fractions import Fraction
from turyn_structure import stable_partition
root='/tmp/claude-1000/-home-bepis-math/117a2777-2472-4276-845a-e0dfeb712755/scratchpad/r4-sources/w32-spence-data'
def check(name,C,n,rng,tries=60):
    bad=0;badp=0;badt=0;badc=0;count=0
    sq=int(round(math.isqrt(n)))**2==n
    for _ in range(tries):
        k=rng.choice([1,1,2,2,3]); S=rng.sample(range(n),k)
        col=stable_partition(C,n,S)
        cells={}
        for i,c in enumerate(col): cells.setdefault(c,[]).append(i)
        L=list(cells.values()); m=len(L)
        ok=True
        tr=0
        singles=sum(1 for R in L if len(R)==1)
        for Q in L:
            x=Q[0]; lhs=Fraction(0)
            for R in L:
                b=sum(C[x][z] for z in R); lhs+=Fraction(b*b,len(R))
                if R is Q: tr+=b
            if lhs!=Fraction(n,len(Q))-1: ok=False
            s_out=singles-(1 if len(Q)==1 else 0)
            if len(Q)>1 and len(Q)*(s_out+1)>n: badc+=1
        count+=1
        if not ok: bad+=1
        if not sq:
            if m%2==0: badp+=1
            if tr!=0: badt+=1
    print(f"{name} n={n} partitions {count}: identity failures {bad}; cell-bound failures {badc}; nonsquare parity failures {badp}, trace failures {badt}{' (n square: parity/trace not asserted)' if sq else ''}")
rng=random.Random(3)
for q in (13,17,29,37,41,25):
    A=gen.paley(q); C=[[0 if i==j else (1 if A[i][j]==0 else -1) for j in range(q)] for i in range(q)]
    check(f"paley{q}",C,q,rng)
p,nv=gen.spence_files(root)[29]
for i,A in enumerate(gen.parse_spence(p,nv)):
    if i>=8: break
    C=[[0 if u==v else (1 if A[u][v]==0 else -1) for v in range(nv)] for u in range(nv)]
    check(f"sp29_{i}",C,nv,rng,tries=40)
