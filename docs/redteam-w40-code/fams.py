import os, sys as _s
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
_s.path.insert(0, ROOT); _s.path.insert(0, HERE)
import random, itertools
import networkx as nx

def relabel(nbr, rng):
    n=len(nbr); p=list(range(n)); rng.shuffle(p)
    out=[None]*n
    for v in range(n): out[p[v]]=sorted(p[w] for w in nbr[v])
    return out

def tree(b,k):
    nbr=[[]]; level=[0]
    for _ in range(k):
        nxt=[]
        for p in level:
            for _ in range(b):
                v=len(nbr); nbr.append([p]); nbr[p].append(v); nxt.append(v)
        level=nxt
    return nbr, level

def tail(nbr,v,L):
    prev=v
    for _ in range(L):
        u=len(nbr); nbr.append([prev]); nbr[prev].append(u); prev=u
    return prev

def double_tree(b,k,rng):
    """two b-ary trees of depth k whose leaves are glued by a random bijection (edges)"""
    A,la=tree(b,k); B,lb=tree(b,k)
    off=len(A)
    nbr=A+[[w+off for w in r] for r in B]
    lb=[x+off for x in lb]
    rng.shuffle(lb)
    for u,v in zip(la,lb):
        nbr[u].append(v); nbr[v].append(u)
    tail(nbr,0,3); tail(nbr,off,5)
    return nbr

def tree_cycle(b,k,rng):
    """b-ary tree whose leaves are joined by one random cycle"""
    nbr,lv=tree(b,k)
    rng.shuffle(lv)
    for i in range(len(lv)):
        u,v=lv[i],lv[(i+1)%len(lv)]
        nbr[u].append(v); nbr[v].append(u)
    tail(nbr,0,3)
    return nbr

def tree_cubic(b,k,rng):
    """b-ary tree with a random cubic graph on leaves"""
    nbr,lv=tree(b,k)
    m=len(lv)
    if (3*m)%2: lv=lv[:-1]; m-=1
    G=nx.random_regular_graph(3,m,seed=rng.randrange(1<<30))
    for u,v in G.edges():
        nbr[lv[u]].append(lv[v]); nbr[lv[v]].append(lv[u])
    tail(nbr,0,3)
    return nbr

def hub_tree_matching(k,rng):
    """Binary tree with twin-leaf blocks of size 4 instead of 2 children on the last level (d=5 hub: 4 leaves + parent), matching between leaf groups"""
    nbr,lv=tree(2,k)
    leaves=[]
    for p in lv:
        for _ in range(4):
            v=len(nbr); nbr.append([p]); nbr[p].append(v); leaves.append(v)
    rng.shuffle(leaves)
    for i in range(0,len(leaves)-1,2):
        u,v=leaves[i],leaves[i+1]
        nbr[u].append(v); nbr[v].append(u)
    tail(nbr,0,3)
    return nbr

def layer_sym3(k,rng):
    """Layered cyclic tower: L layers of 3-subgroups: each layer has 3^? ... width w=3, connect by random S3-twisted perfect structure"""
    # path of blocks of size 3 with random bijections between consecutive blocks (degree 2...3)
    pass

def cayley_ext(a,rng):
    """Cayley graph of Z_a x| Z_2^? (dihedral-like) with 3-5 generators: group Z_a^2 x| Z_2 by negation"""
    elts=[(i,j,e) for i in range(a) for j in range(a) for e in range(2)]
    idx={t:i for i,t in enumerate(elts)}
    def mul(x,y):
        s=1 if x[2]==0 else -1
        return ((x[0]+s*y[0])%a,(x[1]+s*y[1])%a,(x[2]+y[2])%2)
    gens=[(1,0,0),(-1%a,0,0),(0,1,0),(0,-1%a,0),(0,0,1)]
    nbr=[]
    for t in elts:
        nbr.append(sorted({idx[mul(t,g)] for g in gens}-{idx[t]}))
    return nbr

def affine_lift(p,rng):
    """Cayley graph on AGL(1,p) with generators translation, inverse, multiplier and inverse (degree 4), p prime"""
    r=next(a for a in range(2,p) if all(pow(a,(p-1)//q,p)!=1 for q in range(2,p) if (p-1)%q==0))
    elts=[(a,b) for a in range(1,p) for b in range(p)]
    idx={t:i for i,t in enumerate(elts)}
    def mul(x,y): return ((x[0]*y[0])%p,(x[0]*y[1]+x[1])%p)
    rinv=pow(r,p-2,p)
    gens=[(1,1),(1,p-1),(r,0),(rinv,0)]
    return [sorted({idx[mul(t,g)] for g in gens}-{idx[t]}) for t in elts]

FAMS={
 "dt2": lambda s,r: double_tree(2,s,r),
 "tc2": lambda s,r: tree_cycle(2,s,r),
 "tc3": lambda s,r: tree_cycle(3,s,r),
 "tc4": lambda s,r: tree_cycle(4,s,r),
 "tq2": lambda s,r: tree_cubic(2,s,r),
 "hub4": lambda s,r: hub_tree_matching(s,r),
 "cay": lambda s,r: cayley_ext(s,r),
 "aff": lambda s,r: affine_lift(s,r),
}

def twin_triples_big_upset(k, rng):
    """Twin blocks of size 3 only, one vertex each of degree k: a binary tree with k leaves s_i (all at one depth) and a
    tail on its root; each leaf carries a twin triple (a_i, b_i, c_i); three vertices w1, w2, w3 are adjacent to all
    a_i, all b_i, all c_i. The up-set {a_1..a_k} of w1 has 3^k images under the group: phase-1 domain 3^k."""
    # binary tree with exactly k leaves at depth ceil(log2 k)
    D=0
    while (1<<D)<k: D+=1
    nbr=[[]]; root=0
    level=[0]
    for depth in range(D):
        nxt=[]
        for p in level:
            for j in range(2):
                v=len(nbr); nbr.append([p]); nbr[p].append(v); nxt.append(v)
        level=nxt
    leaves=level[:k]
    # prune unused leaves: those with no triple (leave them as dead ends: fine, they only reduce symmetry)
    W=[[],[],[]]
    for s in leaves:
        tr=[]
        for j in range(3):
            v=len(nbr); nbr.append([s]); nbr[s].append(v); tr.append(v)
        for j in range(3):
            W[j].append(tr[j])
    for j in range(3):
        w=len(nbr); nbr.append(list(W[j]))
        for a in W[j]: nbr[a].append(w)
    tail(nbr,root,4)
    return nbr

FAMS["ttb"]=twin_triples_big_upset

def twin_blocks_full(k, t, rng, extra=0):
    """Complete binary tree with k=2^D leaves (top group transitive on the k coordinates: the product action of
    Sym(t) wr T on t^k up-sets is primitive), tail on root; each leaf a twin t-set; t vertices w_1..w_t, each adjacent to the
    j-th of every twin set. Degree max(t+1,k). extra: add 'extra' copies to a second tree-side to grow n."""
    D=0
    while (1<<D)<k: D+=1
    assert (1<<D)==k
    nbr=[[]]; level=[0]
    for depth in range(D):
        nxt=[]
        for p in level:
            for j in range(2):
                v=len(nbr); nbr.append([p]); nbr[p].append(v); nxt.append(v)
        level=nxt
    W=[[] for _ in range(t)]
    for s in level:
        tr=[]
        for j in range(t):
            v=len(nbr); nbr.append([s]); nbr[s].append(v); tr.append(v)
        for j in range(t):
            W[j].append(tr[j])
    for j in range(t):
        w=len(nbr); nbr.append(list(W[j]))
        for a in W[j]: nbr[a].append(w)
    tail(nbr,0,4)
    return nbr

FAMS["pa44"]=lambda s,r: twin_blocks_full(4,s,r)   # k=4, t=s: S_s wr D_4 on s^4
FAMS["pa24"]=lambda s,r: twin_blocks_full(2,s,r)
FAMS["pak4"]=lambda s,r: twin_blocks_full(s,4,r)
