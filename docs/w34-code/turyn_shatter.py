#!/usr/bin/env python3
# turyn_shatter.py: verifies the shattering construction (Thm B) on iterated Turyn products.
# Pure Python. Index of a vertex = base-v digits d[0..m-1] big-endian (matches gen.turyn).
import sys, os, itertools, random
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'w32-code'))
import gen

def base_seidel(spec):
    if spec.startswith('skew'):
        return gen.paley_skew(int(spec[4:]))
    return gen.seidel_of_adj(gen.paley(int(spec)))

class Turyn:
    """Iterated Turyn product W_L over base V (symmetric): entries computed by recursion."""
    def __init__(self, V, L):
        self.V=V; self.v=len(V); self.L=L; self.m=2**L
    def entry_digits(self, a, b, m=None):
        """W entry for digit tuples a,b of length m=2^l."""
        if m is None: m=self.m
        if m==1: return self.V[a[0]][b[0]]
        h=m//2
        a1,a2,b1,b2=a[:h],a[h:],b[:h],b[h:]
        return self.entry_digits(a1,b1,h)*self.entry_digits(a2,b2,h)+(1 if a1==b1 else 0)-(1 if a2==b2 else 0)
    def index(self,d):
        x=0
        for c in d: x=x*self.v+c
        return x
    def digits(self,x):
        d=[]
        for _ in range(self.m):
            d.append(x%self.v); x//=self.v
        return tuple(reversed(d))
    def all_vertices(self):
        return itertools.product(range(self.v),repeat=self.m)

def T_base(V,a,b,x):
    return sum(V[a][z]*V[b][z]*V[x][z] for z in range(len(V)))

def collision_base(V,a,b,s,t):
    return a not in (s,t) and b not in (s,t) and V[a][s]==V[a][t] and V[b][s]==V[b][t] and T_base(V,a,b,s)==T_base(V,a,b,t)

def find_config(V):
    """find (alpha,beta,alpha',beta',s,t) with collision(alpha,beta;s,t), sign mismatch of alpha' on (s,t)."""
    v=len(V)
    for s in range(v):
        for t in range(s+1,v):
            for a in range(v):
                if a in (s,t): continue
                for b in range(v):
                    if b in (s,t) or b==a: continue
                    if not collision_base(V,a,b,s,t): continue
                    for ap in range(v):
                        if ap in (s,t): continue
                        if V[ap][s]==V[ap][t]: continue
                        for bp in range(v):
                            if bp in (s,t,ap): continue
                            return (a,b,ap,bp,s,t)
    return None

def verify_shatter(spec, L):
    V=base_seidel(spec); v=len(V)
    cfg=find_config(V)
    print(f"base {spec} order {v}: config {cfg}")
    if cfg is None: return
    al,be,alp,bep,s,t=cfg
    z=s  # value for equal coordinates
    TT=Turyn(V,L); m=TT.m; d=m-1
    tests=[]
    for i in range(d):
        a=[al]*m; b=[be]*m
        a[i]=alp; b[i]=bep
        tests.append((tuple(a),tuple(b)))
    n=v**m
    def rowsum(a,b,x):
        # T = sum over z of W(a,z)W(b,z)W(x,z) -- enumerate all z
        tot=0
        for zdig in TT.all_vertices():
            tot+=TT.entry_digits(a,zdig)*TT.entry_digits(b,zdig)*TT.entry_digits(x,zdig)
        return tot
    def collide(a,b,x,y):
        if x in (a,b) or y in (a,b): return False
        if TT.entry_digits(a,x)!=TT.entry_digits(a,y): return False
        if TT.entry_digits(b,x)!=TT.entry_digits(b,y): return False
        return rowsum(a,b,x)==rowsum(a,b,y)
    sample=list(range(2**d)) if d<=4 else random.sample(range(2**d),16)
    allok=True
    for mask in sample:
        Y=[i for i in range(d) if (mask>>i)&1]
        xs=[]; ys=[]
        for j in range(m):
            if j<d and j in Y:
                xs.append(z); ys.append(z)
            else:
                xs.append(s); ys.append(t)
        x,y=tuple(xs),tuple(ys)
        res=[collide(tests[i][0],tests[i][1],x,y) for i in range(d)]
        expect=[i in Y for i in range(d)]
        if res!=expect:
            allok=False; print("MISMATCH",mask,res,expect)
    print(f"Thm B shattering check (2-round tests): base {spec}, L={L}, m={m}, n={n}, d={d}, patterns tested {len(sample)}: {'OK' if allok else 'FAIL'}")

if __name__=='__main__':
    for spec,L in [('9',1),('13',1),('5',1),('9',2)]:
        V=base_seidel(spec)
        print('---',spec,L)
        verify_shatter(spec,L)
