#!/usr/bin/env python3
# turyn_structure.py: checks for w34 Turyn claims (pure Python).
# (1) Row-pair formula for T on W(V,V').  (2) Product partition equitable; stable(W,S) coarser than
# product of stable partitions of projections (r rounds and limit); Thm B (limit-rounds k-tuple shattering).
# (3) Projection-discrete vs discrete on small Turyn graphs.
import sys, os, itertools, random
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'w32-code'))
import gen
from turyn_shatter import base_seidel, Turyn

def turyn_matrix(V1,V2):
    return gen.turyn(V1,V2)

def T_row(W,n,a,b,x):
    return sum(W[a][z]*W[b][z]*W[x][z] for z in range(n))

def stable_partition(W, n, S, rounds=None):
    col=[0]*n
    for i,s in enumerate(S): col[s]=i+1
    cnt=len(set(col))
    while True:
        nw=[]
        for v in range(n):
            nw.append((col[v],tuple(sorted(col[u] for u in range(n) if W[v][u]==1)),tuple(sorted(col[u] for u in range(n) if W[v][u]==-1))))
        # canonicalize
        d={}; newcol=[]
        for sig in nw:
            if sig not in d: d[sig]=len(d)
            newcol.append(d[sig])
        newcnt=len(d)
        col=newcol
        if rounds is not None:
            rounds-=1
            if rounds==0: return col
        if newcnt==cnt: return col
        cnt=newcnt

def cells_of(col):
    cells={}
    for i,c in enumerate(col): cells.setdefault(c,[]).append(i)
    return list(cells.values())

def check_row_formula(spec):
    V=base_seidel(spec); v=len(V)
    if any(V[i][j]!=V[j][i] for i in range(v) for j in range(v)):
        print(spec,"not symmetric; skipping formula check (skew case has sign changes)"); return
    W=turyn_matrix(V,V); n=v*v
    idx=lambda i,j:i*v+j
    rng=random.Random(5); ok=0; total=0; bad=0
    for _ in range(4000):
        a1=rng.randrange(v); a2,x2=rng.sample(range(v),2)
        y1=rng.randrange(v); y2=rng.randrange(v)
        a=idx(a1,a2); x=idx(a1,x2); y=idx(y1,y2)
        if y in (a,x): continue
        eps=V[a2][x2]
        f=lambda z2:V[a2][z2]*V[x2][z2]
        Tp=sum(V[a2][z]*V[x2][z]*V[y2][z] for z in range(v))
        A=-1-v*f(y2)
        B=V[y1][a1]*(-V[y2][a2]-V[y2][x2]-Tp)+(v-1 if y1==a1 else 0)-(1-f(y2) if y2 not in (a2,x2) else 0)
        Ip=(v-1 if y1==a1 else -1)
        C=-eps*(Ip*(V[y2][a2]+V[y2][x2])+2*V[a1][y1])
        pred=A+B+C
        act=T_row(W,n,a,x,y)
        total+=1
        if pred!=act: bad+=1
    print(f"row-pair formula, base {spec}: {total} triples, {bad} mismatches")

def check_equitable_coarsening(spec, ks=(1,2), samples=25):
    V=base_seidel(spec); v=len(V)
    W=turyn_matrix(V,V); n=v*v
    rng=random.Random(9)
    idx=lambda i,j:i*v+j
    bad=0; total=0
    for _ in range(samples):
        for k in ks:
            S=[idx(rng.randrange(v),rng.randrange(v)) for _ in range(k)]
            for rounds in [1,2,3,None]:
                S1=[s//v for s in S]; S2=[s%v for s in S]
                colW=stable_partition(W,n,S,rounds)
                col1=stable_partition(V,v,S1,rounds); col2=stable_partition(V,v,S2,rounds)
                # coarsening: same product cell -> same W color
                prod={}
                for i in range(v):
                    for j in range(v):
                        key=(col1[i],col2[j]); c=colW[idx(i,j)]
                        if key in prod:
                            if prod[key]!=c: bad+=1
                        else: prod[key]=c
                total+=1
    print(f"product-coarsening check, base {spec}: {total} cases, {bad} violations (product cell not monochromatic in W)")

def discreteness_vs_projections(spec, ks=(2,3), samples=400):
    V=base_seidel(spec); v=len(V)
    W=turyn_matrix(V,V); n=v*v
    rng=random.Random(11)
    idx=lambda i,j:i*v+j
    # precompute stable of projections cache
    def is_disc(col): return len(set(col))==len(col)
    stats={}
    for k in ks:
        both=0; proj_disc=0; w_disc=0; count=0; viol=0
        for _ in range(samples):
            S=[idx(rng.randrange(v),rng.randrange(v)) for _ in range(k)]
            if len(set(S))<k: continue
            S1=sorted(set(s//v for s in S)); S2=sorted(set(s%v for s in S))
            pd=is_disc(stable_partition(V,v,S1)) and is_disc(stable_partition(V,v,S2))
            wd=is_disc(stable_partition(W,n,S))
            count+=1
            if pd: proj_disc+=1
            if wd: w_disc+=1
            if pd and not wd: viol+=1
            if wd and not pd: pass
        stats[k]=(count,proj_disc,w_disc,viol)
        print(f"base {spec}, k={k}: samples {count}, projections discrete {proj_disc}, W discrete {w_disc}, proj-discrete-but-W-not (converse failures): {viol}")

def limit_shatter(spec, L=1):
    # Theorem B, limit rounds, k=2: tests are pairs a=(p,q) tuples of vertices of W_L; coordinate j != i: both entries alpha;
    # coordinate i: entries (alpha1,alpha2)
    V=base_seidel(spec); v=len(V)
    TT=Turyn(V,L); m=TT.m; n=v**m
    W=[[0]*n for _ in range(n)]
    verts=list(TT.all_vertices())
    for i,a in enumerate(verts):
        for j,b in enumerate(verts):
            W[i][j]=TT.entry_digits(a,b)
    # find alpha, s,t with V[alpha][s]==V[alpha][t]; alpha' with mismatch; z
    found=None
    for s in range(v):
        for t in range(s+1,v):
            for al in range(v):
                if al in (s,t) or V[al][s]!=V[al][t]: continue
                for alp in range(v):
                    if alp in (s,t) or V[alp][s]==V[alp][t]: continue
                    found=(al,alp,s,t); break
                if found: break
            if found: break
        if found: break
    al,alp,s,t=found; z=s
    d=m-1
    # tests: tuple of two vertices a,b; coordinate j<d: at j=i entries (alp, other), others (al,al)
    # to keep k=2 tuple distinct, use al at second entry coordinate i: (alp,al2) where al2 is any vertex != al,s,t? Use alp at both entries (allowed as multiset) but entries distinct overall if d>=2 thanks to coord differences... take entries a=coord alp at i, b=coord al at i? need b also separated; only one mismatching vertex required.
    tests=[]
    for i in range(d):
        a=[al]*m; b=[al]*m
        a[i]=alp
        # b[i] = al (so a!=b)
        tests.append((TT.index(a),TT.index(b)))
    allok=True
    for mask in range(2**d):
        Y=[i for i in range(d) if (mask>>i)&1]
        xs=[];ys=[]
        for j in range(m):
            if j<d and j in Y: xs.append(z);ys.append(z)
            else: xs.append(s);ys.append(t)
        x=TT.index(xs); y=TT.index(ys)
        res=[]
        for (a,b) in tests:
            col=stable_partition(W,n,[a,b])
            res.append(col[x]==col[y])
        expect=[i in Y for i in range(d)]
        if res!=expect:
            allok=False; print("MISMATCH",mask,res,expect)
    print(f"limit-rounds k=2 shattering: base {spec}, L={L}, m={m}, n={n}, d={d}: {'OK' if allok else 'FAIL'}")

if __name__=='__main__':
    for sp in ['9','13']:
        check_row_formula(sp)
    for sp in ['9','skew3','5']:
        check_equitable_coarsening(sp)
    limit_shatter('5',1)  # n=25, d=1
    limit_shatter('9',1)  # n=81, d=1
    discreteness_vs_projections('9',(2,3),samples=120)
    discreteness_vs_projections('5',(2,3),samples=300)
