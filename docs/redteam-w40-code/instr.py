"""Instrument _transitive on d<=5 runs: every quotient P must be primitive and satisfy the Palfy-Wolf inequality; check generators
of every node group are in a solvable group via the derived series on the quotient, for moderate degrees."""
import os, sys as _s
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
_s.path.insert(0, ROOT); _s.path.insert(0, HERE)

import sys, random, time, math
sys.path.insert(0, ROOT)
sys.setrecursionlimit(100000)
from collections import Counter
src=open(HERE + "/fuzz1.py").read(); src=src[:src.index("rng=random.Random(int(sys.argv[1])")]; exec(src)
import gi.luks as L
from gi.group import PermGroup, ActionHom, top_block_system
from gi.perm import mul, inv
alpha=(3*math.log(48)+math.log(24))/(3*math.log(9)); pw=lambda k: k**(alpha+1)/24**(1/3)
def commutator_closure(G):
    n=G.n; gens=G.gens
    comms=[]
    for a in gens:
        for b in gens:
            c=mul(mul(mul(inv(a),inv(b)),a),b)
            if c!=tuple(range(n)): comms.append(c)
    return comms
def derived_solvable(n,gens):
    G=PermGroup(n,list(gens))
    for _ in range(60):
        if G.order()==1: return True
        o=G.order()
        S=set()
        cs=[]
        gl=G.gens
        for a in gl:
            for b in gl:
                c=mul(mul(mul(inv(a),inv(b)),a),b)
                if c not in S and c!=tuple(range(n)):
                    S.add(c); cs.append(c)
        # normal closure of commutators
        D=PermGroup(n,cs) if cs else PermGroup(n)
        changed=True
        while changed:
            changed=False
            for c in list(D.gens):
                for g in gl:
                    c2=mul(mul(inv(g),c),g)
                    if not D.contains(c2):
                        D=PermGroup(n,list(D.gens)+[c2]); changed=True
        if D.order()==o: return False
        G=D
    return False
orig=L._transitive
stat=Counter(); mxr={}
worst=[0,None]
def patched(G,x,run):
    w=G.n
    blocks=top_block_system(G)
    if blocks is None:
        o=G.order(); k=w
        # giants / lists: check bound
        stat["prim_G"]+=1
        if o>math.factorial(k): stat["BAD order"]+=1
        P=G
    else:
        k=len(blocks)
        where=[0]*w
        for i,B in enumerate(blocks):
            for p in B: where[p]=i
        reps=[B[0] for B in blocks]
        hom=ActionHom(G,k,lambda g: tuple(where[g[p]] for p in reps))
        P=hom.image_group()
        o=P.order()
        stat["quot"]+=1
        if k<=120:
            if top_block_system(P) is not None:
                print("NOT PRIMITIVE quotient",k,o,flush=True); stat["BAD not primitive"]+=1
    r=math.log(o)/math.log(k) if k>1 else 0
    if r>worst[0]: worst[0]=r; worst[1]=(k,o)
    if o>pw(k)*(1+1e-9):
        print("EXCEEDS PW bound",k,o,pw(k),flush=True); stat["BAD pw"]+=1
    if o>k**4: stat["over k4"]+=1
    if P.n<=64 and P.order()<=1<<40:
        if not derived_solvable(P.n,P.gens): print("NON-SOLVABLE P",k,o,flush=True); stat["BAD solv"]+=1
        stat["solv ok"]+=1
    return orig(G,x,run)
L._transitive=patched
rng=random.Random(int(sys.argv[1])); limit=float(sys.argv[2]); t0=time.time(); n=0
for name,g,col in gen_instances(rng):
    if time.time()-t0>limit: break
    if len(g)>120: continue
    st=Counter()
    canonical_labeling_lists(g,col,stats=st); n+=1
    if st['canon_ir'] or st['canon_luks_fallback']: print("BADCOUNT",name)
print("runs",n,dict(stat),"worst log_k|P|",worst)
