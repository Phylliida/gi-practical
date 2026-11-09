"""(1) EA detection never misses: at every luks node, EA as a group implies _ea_possible.
(2) exhaustive atlas: forms separate the classes and are relabelling-invariant; colored small graphs."""
import os, sys as _s
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
_s.path.insert(0, ROOT); _s.path.insert(0, HERE)

import sys, random, time, itertools
sys.path.insert(0, ROOT)
sys.setrecursionlimit(100000)
from collections import Counter
src=open(HERE + "/fuzz1.py").read(); src=src[:src.index("rng=random.Random(int(sys.argv[1])")]; exec(src)
import gi.luks as L, gi.canon as C
from gi.ea2 import is_ea2
from gi.group import PermGroup, ActionHom, RestrictionHom
stat=Counter()
orig=L._solve_node
def patched(G,x,run):
    gens=G.gens; w=G.n
    if gens and is_ea2(gens,w):
        stat["ea nodes"]+=1
        if not L._ea_possible(G):
            stat["EA MISSED"]+=1; print("EA MISSED order",G.order(),"gens",len(gens),flush=True)
    return orig(G,x,run)
L._solve_node=patched
origca=C.canon_group
def pca(G,n,*a,**k):
    gens=G.gens
    if gens and not isinstance(G,C.EA2) and is_ea2(gens,n):
        stat["ea canon_group"]+=1
        if not C._ea_possible(G): stat["EA MISSED canon_group"]+=1; print("EA MISSED canon_group",flush=True)
    return origca(G,n,*a,**k)
C.canon_group=pca
rng=random.Random(9); t0=time.time(); limit=float(sys.argv[1])
# random group kernels
for trial in range(200):
    a=rng.randint(2,4); m=1<<a
    # EA group on two copies with a random linear bijection, plus random extra generators
    gens=[]
    n=2*m
    for i in range(a):
        g=list(range(n))
        for x in range(m):
            g[x]=x^(1<<i); g[m+x]=m+(x^(1<<((i+1)%a)))
        gens.append(tuple(g))
    swap=list(range(n))
    for x in range(m): swap[x]=m+x; swap[m+x]=x
    gens2=gens+[tuple(swap)]
    def re(g0):
        e=tuple(range(n))
        for _ in range(12):
            e=mul(e,rng.choice(g0))
        return e
    from gi.perm import mul
    gs=[re(gens2) for _ in range(rng.randint(3,8))]+gens2
    G=PermGroup(n,gs)
    hom=ActionHom(G,2,lambda g:(0 if g[0]<m else 1, 0 if g[m]<m else 1))
    N=hom.kernel()
    if is_ea2(N.gens,n) and N.order()!=1<<len(N.gens):
        print("KERNEL gens redundant",N.order(),len(N.gens),flush=True); stat["kernel redundant"]+=1
    stat["kernels"]+=1
for name,g,col in gen_instances(rng):
    if time.time()-t0>limit: break
    if len(g)>100: continue
    canonical_labeling_lists(g,col)
print(dict(stat))
# atlas
from networkx.generators.atlas import graph_atlas_g
At=graph_atlas_g()
forms={}; bad=0; cnt=0
for G in At:
    nbr=[sorted(G[v]) for v in sorted(G)]
    if nbr and max(map(len,nbr))>5: continue
    f=canonical_form_lists(nbr)
    for _ in range(3):
        h,_c,p=relabel(nbr,None,rng)
        if canonical_form_lists(h)!=f: bad+=1; print("ATLAS DIFF",G.name,flush=True); break
    for kw in ({"layers":"bfs"},{"guarantee":True}):
        fk=canonical_form_lists(nbr,**kw); h,_c,p=relabel(nbr,None,rng)
        if canonical_form_lists(h,**kw)!=fk: bad+=1; print("ATLAS DIFF kw",G.name,kw,flush=True)
    if f in forms: bad+=1; print("ATLAS COLLISION",G.name,forms[f],flush=True)
    forms[f]=G.name; cnt+=1
print("atlas",cnt,"bad",bad)
# all 2-colourings of atlas graphs up to 5 vertices: classes by nauty-with-colors
cl={}
cnt=0
for G in At:
    if G.number_of_nodes()>5 or G.number_of_nodes()==0: continue
    nbr=[sorted(G[v]) for v in sorted(G)]
    n=len(nbr)
    for c in itertools.product(range(2),repeat=n):
        c=list(c); f=canonical_form_lists(nbr,c); h,c2,p=relabel(nbr,c,rng); cnt+=1
        if canonical_form_lists(h,c2)!=f: bad+=1; print("COLOR DIFF",nbr,c,flush=True)
        key=(n,nauty_cert(nbr,c),tuple(sorted(Counter(c).items())))
        if f in cl and cl[f]!=key: bad+=1; print("COLOR COLLISION",flush=True)
        cl[f]=key
print("colored",cnt,"bad",bad,dict(stat))
