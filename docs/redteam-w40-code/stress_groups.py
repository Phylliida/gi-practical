"""Group-level stress of luks_canon: orbit invariance, generating-set invariance, Aut exactness, node path coverage,
on structured solvable and non-solvable groups."""
import os, sys as _s
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
_s.path.insert(0, ROOT); _s.path.insert(0, HERE)

import sys, random, time, math
sys.path.insert(0, ROOT)
sys.setrecursionlimit(100000)
from collections import Counter
from gi.group import PermGroup, ActionHom, top_block_system
from gi.luks import luks_canon, luks_canon_group, LimitExceeded, enum_limit_default
from gi.perm import act, mul, inv, sym_gens, alt_gens, cycle, identity

def rand_elem(gens, n, rng, L=40):
    e = identity(n)
    for _ in range(L):
        s = rng.choice(gens)
        e = mul(e, s if rng.random()<.7 else inv(s))
    return e

def agl1(p):
    # affine group of Z_p, p prime (primitive solvable)
    n=p
    g1=tuple((i+1)%p for i in range(p))
    r=None
    for a in range(2,p):
        if all(pow(a,(p-1)//q,p)!=1 for q in range(2,p) if (p-1)%q==0 and all(q%t for t in range(2,q))):
            r=a;break
    if p==2: return n,[g1]
    g2=tuple((r*i)%p for i in range(p))
    return n,[g1,g2]

def agl_d_p(d,p):
    # AGL(d,p) on p^d points, by translations + generators of GL
    n=p**d
    def idx(v):
        r=0
        for x in v: r=r*p+x
        return r
    pts=[]
    def rec(i,cur):
        if i==d: pts.append(tuple(cur)); return
        for x in range(p): rec(i+1,cur+[x])
    rec(0,[])
    gens=[]
    for i in range(d):
        g=[0]*n
        for v in pts:
            w=list(v); w[i]=(w[i]+1)%p
            g[idx(v)]=idx(w)
        gens.append(tuple(g))
    # transvection and a permutation matrix cycle and scalar generators
    def lin(M):
        g=[0]*n
        for v in pts:
            w=[sum(M[i][j]*v[j] for j in range(d))%p for i in range(d)]
            g[idx(v)]=idx(w)
        return tuple(g)
    T=[[1 if i==j else 0 for j in range(d)] for i in range(d)]; T[0][1 if d>1 else 0]=1
    if d>1: gens.append(lin(T))
    C=[[1 if (i+1)%d==j else 0 for j in range(d)] for i in range(d)]
    if d>1: gens.append(lin(C))
    if p>2:
        # generator of multiplicative group on first coordinate
        D=[[1 if i==j else 0 for j in range(d)] for i in range(d)]
        r=next(a for a in range(2,p) if all(pow(a,(p-1)//q,p)!=1 for q in range(2,p) if (p-1)%q==0 and all(q%t for t in range(2,q))))
        D[0][0]=r
        gens.append(lin(D))
    return n,gens

def wreath(g_in, n_in, g_top, k):
    """g_in on n_in points wr g_top on k blocks: imprimitive action on n_in*k points."""
    n=n_in*k
    gens=[]
    for b in range(k):
        for s in g_in:
            p=list(range(n))
            for j in range(n_in): p[b*n_in+j]=b*n_in+s[j]
            gens.append(tuple(p))
    for t in g_top:
        p=list(range(n))
        for b in range(k):
            for j in range(n_in): p[b*n_in+j]=t[b]*n_in+j
        gens.append(tuple(p))
    return n,gens

def direct(a,ga,b,gb):
    n=a+b
    gens=[]
    for s in ga: gens.append(tuple(s)+tuple(range(a,n)))
    for t in gb: gens.append(tuple(range(a))+tuple(a+x for x in t))
    return n,gens

def diag(a,ga,copies):
    """Diagonal action of the group on copies copies of the same set (intransitive, linked)."""
    n=a*copies
    gens=[]
    for s in ga:
        p=list(range(n))
        for c in range(copies):
            for j in range(a): p[c*a+j]=c*a+s[j]
        gens.append(tuple(p))
    return n,gens

def product_action(a,ga,k):
    """Primitive-ish product action of G wr S_k on a^k points (k small)."""
    n=a**k
    def pts_iter():
        import itertools
        return itertools.product(range(a),repeat=k)
    pts=list(pts_iter()); idx={v:i for i,v in enumerate(pts)}
    gens=[]
    for c in range(k):
        for s in ga:
            g=[0]*n
            for v in pts:
                w=list(v); w[c]=s[v[c]]
                g[idx[v]]=idx[tuple(w)]
            gens.append(tuple(g))
    for t in [cycle(k,list(range(k))), cycle(k,[0,1])] if k>1 else []:
        g=[0]*n
        for v in pts:
            w=[0]*k
            for i in range(k): w[t[i]]=v[i]
            g[idx[v]]=idx[tuple(w)]
        gens.append(tuple(g))
    return n,gens

def subset_action(n0, gens0, k):
    """action on k-subsets"""
    import itertools
    sets=list(itertools.combinations(range(n0),k)); idx={s:i for i,s in enumerate(sets)}
    out=[]
    for g in gens0:
        p=[0]*len(sets)
        for s in sets:
            p[idx[s]]=idx[tuple(sorted(g[x] for x in s))]
        out.append(tuple(p))
    return len(sets),out

def sym(n): return n,sym_gens(n,list(range(n)))
def alt(n): return n,alt_gens(n,list(range(n)))
def cyc(n): return n,[cycle(n,list(range(n)))]

def groups():
    L=[]
    L.append(("AGL1(13)",agl1(13)));L.append(("AGL1(17)",agl1(17)))
    L.append(("AGL2,3",agl_d_p(2,3)));L.append(("AGL3,2",agl_d_p(3,2)));L.append(("AGL2,5",agl_d_p(2,5)));L.append(("AGL3,3",agl_d_p(3,3)))
    L.append(("AGL4,2",agl_d_p(4,2)))
    n,g=sym(3); L.append(("S3wrC4",wreath(g,3,cyc(4)[1],4)))
    n,g=sym(4); L.append(("S4wrS3",wreath(g,4,sym(3)[1],3)))
    L.append(("S4wrC5",wreath(g,4,cyc(5)[1],5)))
    n,g=cyc(2); a,ga=wreath(g,2,cyc(2)[1],2); b,gb=wreath(ga,a,cyc(2)[1],2); L.append(("C2wrC2wrC2",(b,gb)))
    c,gc=wreath(gb,b,cyc(3)[1],3); L.append(("(C2w3)wrC3",(c,gc)))
    n,g=agl1(5); L.append(("F20wrS3",wreath(g,5,sym(3)[1],3)))
    n,g=agl1(7); L.append(("F42wrC2",wreath(g,7,cyc(2)[1],2)))
    n,g=sym(3); L.append(("S3xS4",direct(3,g,4,sym(4)[1])))
    L.append(("diagS3x5",diag(3,g,5)))
    n,g=sym(4); L.append(("diagS4x4",diag(4,g,4)))
    n,g=agl1(7); L.append(("diagF42x3",diag(7,g,3)))
    n,g=agl_d_p(3,2); L.append(("diagAGL32x3",diag(8,g,3)))
    n,g=sym(3); L.append(("S3prod3",product_action(3,g,3)))
    n,g=sym(4); L.append(("S4prod2",product_action(4,g,2)))
    n,g=agl1(5); L.append(("F20prod2",product_action(5,g,2)))
    n,g=cyc(2); L.append(("C2prod5",product_action(2,g,5)))
    n,g=sym(6); L.append(("S6nat",(n,g)))
    n,g=sym(7); L.append(("S7pairs",subset_action(7,g,2)))
    n,g=alt(7); L.append(("A7nat",(7,g)))
    n,g=sym(8); L.append(("S8nat",(8,g)))
    # EA kernels: C2^a x|: F20-type lifts: C2 wr AGL1(5)  EA kernel with solvable top
    n,g=agl1(5); L.append(("C2wrF20",wreath(cyc(2)[1],2,g,5)))
    n,g=agl1(13); L.append(("C2wrF13",wreath(cyc(2)[1],2,g,13)))
    n,g=agl_d_p(2,3); L.append(("C2wrAGL23",wreath(cyc(2)[1],2,g,9)))
    n,g=agl1(5); L.append(("C3wrF20",wreath(cyc(3)[1],3,g,5)))
    return L

rng=random.Random(int(sys.argv[1]) if len(sys.argv)>1 else 3)
limit=float(sys.argv[2]) if len(sys.argv)>2 else 300
t0=time.time()
GS=groups()
cov=Counter(); bad=0; per=Counter()
while time.time()-t0<limit:
    name,(n,gens)=rng.choice(GS)
    G=PermGroup(n,gens)
    # string with few values, sometimes structured
    vals=rng.choice([2,2,2,3,4,n])
    if rng.random()<0.3:
        # block structured string
        x=tuple(rng.randrange(2) if i%3 else 0 for i in range(n))
    else:
        x=tuple(rng.randrange(vals) for _ in range(n))
    st=Counter()
    try:
        F,lam,U=luks_canon_group(G,x,st)
    except Exception as e:
        print("EXC",name,type(e),e,flush=True); bad+=1; continue
    for k in st:
        cov[k]+=1
    per[name]+=1
    if act(x,lam)!=F: print("BAD lam",name); bad+=1
    if not G.contains(lam): print("BAD lam not in G",name); bad+=1
    for u in U.gens:
        if not G.contains(u): print("BAD aut not in G",name); bad+=1
        if act(F,u)!=F: print("BAD aut",name,flush=True); bad+=1
    # orbit invariance
    for _ in range(3):
        g=rand_elem(gens,n,rng)
        y=act(x,g)
        F2,_,_=luks_canon_group(G,y,Counter())
        if F2!=F: print("WRONG orbit",name,n,G.order(),x,flush=True); bad+=1
    # gen invariance
    gs=[rand_elem(gens,n,rng) for _ in range(rng.randint(1,4))]+[rand_elem(gens,n,rng) for _ in gens]
    G2=PermGroup(n,gs)
    if G2.order()!=G.order():
        gs=gs+list(gens); rng.shuffle(gs); G2=PermGroup(n,gs)
    if G2.order()==G.order():
        F3,_,U3=luks_canon_group(G2,x,Counter())
        if F3!=F or U3.order()!=U.order(): print("WRONG gens",name,n,G.order(),x,flush=True); bad+=1
    # Aut exact by brute force where cheap
    if G.order()<=50000:
        cnt=sum(1 for g in G.elements() if act(F,g)==F)
        if cnt!=U.order(): print("WRONG Aut order",name,cnt,U.order(),flush=True); bad+=1
print("bad",bad,"coverage",dict(cov))
print(per)
