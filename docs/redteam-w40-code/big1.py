"""Larger instances: forms under relabelling, |Aut| against nauty, twisted pairs differ."""
import os, sys as _s
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
_s.path.insert(0, ROOT); _s.path.insert(0, HERE)

import sys, random, time, math, signal
sys.path.insert(0, ROOT)
sys.path.insert(0, HERE)
sys.setrecursionlimit(100000)
from collections import Counter
import pynauty
from gi.canon import canonical_labeling_lists, canonical_form_lists, _form_of
from gi.group import PermGroup
from fams import *
from bench import irhard
from bench.adversary import cfi3, tree_matching, add_triple, fam_cfi3, fam_cfit, _fam_tree, fam_nst3, fam_mpi
class TO(Exception): pass
signal.signal(signal.SIGALRM, lambda *a: (_ for _ in ()).throw(TO()))
def rel(nbr,rng):
    n=len(nbr); p=list(range(n)); rng.shuffle(p); out=[None]*n
    for v in range(n): out[p[v]]=sorted(p[w] for w in nbr[v])
    return out
def nauty_aut(nbr):
    g=pynauty.Graph(len(nbr),adjacency_dict={i:list(nbr[i]) for i in range(len(nbr))})
    gens,m,e,orb,no=pynauty.autgrp(g)
    return round(m*10**e) if e<14 else (m,e), pynauty.certificate(g)
rng=random.Random(int(sys.argv[1])); limit=float(sys.argv[2]); t0=time.time()
items=[]
for b in (6,10,14,18):
    for I in fam_cfi3(b,rng): items.append((I["name"],I["X"],I["Y"],I["claim"]))
for b in (4,6,8,10,14):
    for I in fam_cfit(b,rng): items.append((I["name"],I["X"],I["Y"],I["claim"]))
for k in (3,4,5,6):
    for I in _fam_tree(2)(k,rng): items.append((I["name"],I["X"],I["Y"],I["claim"]))
for k in (2,3):
    for I in _fam_tree(3)(k,rng): items.append((I["name"],I["X"],I["Y"],I["claim"]))
    for I in _fam_tree(4)(k,rng): items.append((I["name"],I["X"],I["Y"],I["claim"]))
for k in (6,8,12):
    for I in fam_nst3(k,rng): items.append((I["name"],I["X"],I["Y"],I["claim"]))
for k in (4,6):
    for I in fam_mpi(k,rng): items.append((I["name"],I["X"],I["Y"],I["claim"]))
for s,f in [(4,"dt2"),(5,"dt2"),(5,"tc2"),(6,"tc2"),(3,"tc3"),(4,"tc3"),(2,"tc4"),(3,"tc4"),(4,"tq2"),(3,"hub4"),(4,"hub4"),(3,"pa44"),(5,"cay"),(7,"cay"),(7,"aff"),(11,"aff")]:
    X=FAMS[f](s,rng); items.append((f"{f}-{s}",X,None,True))
print("instances",len(items),flush=True)
bad=0; done=0
for name,X,Y,claim in items:
    if time.time()-t0>limit: print("LIMIT"); break
    try:
        signal.setitimer(signal.ITIMER_REAL,40)
        st=Counter(); lab,gens=canonical_labeling_lists(X,stats=st)
        fx=_form_of(X,lab,None)
        if sorted(lab)!=list(range(len(X))): print("NOT PERM",name,flush=True); bad+=1
        for _ in range(2):
            Xr=rel(X,rng)
            if canonical_form_lists(Xr)!=fx:
                print("WRONG relabel",name,flush=True); bad+=1
        # all gens automorphisms
        E={(u,v) for u in range(len(X)) for v in X[u]}
        for g in gens:
            if any((g[u],g[v]) not in E for u,v in E): print("BAD GEN",name,flush=True); bad+=1; break
        o=PermGroup(len(X),gens).order() if gens else 1
        aut,c=nauty_aut(X)
        if isinstance(aut,int) and o!=aut:
            print("WRONG |Aut|",name,o,aut,flush=True); bad+=1
        if Y is not None:
            fy=canonical_form_lists(Y)
            same=(fy==fx)
            cy=pynauty.certificate(pynauty.Graph(len(Y),adjacency_dict={i:list(Y[i]) for i in range(len(Y))}))
            if same!=(c==cy):
                print("WRONG vs nauty",name,same,c==cy,flush=True); bad+=1
            if claim is not None and same!=claim:
                print("WRONG claim",name,same,claim,flush=True); bad+=1
        signal.setitimer(signal.ITIMER_REAL,0)
        done+=1
        print(f"ok {name:12s} n={len(X):4d} nodes={st['canon_luks_nodes']:6d} fb={st['canon_luks_fallback']} ir={st['canon_ir']} |Aut|={o if o<10**15 else 'big'} t={time.time()-t0:.0f}",flush=True)
    except TO:
        signal.setitimer(signal.ITIMER_REAL,0); print("timeout",name,len(X),flush=True)
print("done",done,"bad",bad)
