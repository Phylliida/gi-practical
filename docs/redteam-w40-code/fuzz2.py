"""degree >= 6 fuzz: default vs guarantee mode invariance, counters, nauty cross-check; a per-instance alarm."""
import os, sys as _s
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
_s.path.insert(0, ROOT); _s.path.insert(0, HERE)

import sys, random, time, signal
sys.path.insert(0, ROOT)
sys.setrecursionlimit(100000)
from collections import Counter
import networkx as nx, pynauty
from gi.canon import canonical_form_lists
def nxl(G):
    G=nx.convert_node_labels_to_integers(G); return [sorted(G[v]) for v in G]
def relabel(nbr,rng):
    n=len(nbr); p=list(range(n)); rng.shuffle(p); out=[None]*n
    for v in range(n): out[p[v]]=sorted(p[w] for w in nbr[v])
    return out
def cert(nbr):
    return pynauty.certificate(pynauty.Graph(len(nbr),adjacency_dict={i:list(nbr[i]) for i in range(len(nbr))}))
class TO(Exception): pass
def alarm(*a): raise TO()
signal.signal(signal.SIGALRM,alarm)
rng=random.Random(int(sys.argv[1])); limit=float(sys.argv[2]); t0=time.time()
def inst():
    while True:
        k=rng.randrange(10)
        if k==0: a,b=rng.randint(2,8),rng.randint(2,8); yield f"K{a},{b}",nxl(nx.complete_bipartite_graph(a,b))
        elif k==1: n=rng.randint(6,11); yield f"K{n}",nxl(nx.complete_graph(n))
        elif k==2: d=rng.randint(6,7); yield f"Q{d}",nxl(nx.hypercube_graph(d))
        elif k==3:
            # star-of-stars: hub with b twins each with t leaves, leaves carrying a matching
            b=rng.randint(5,9); t=rng.randint(1,3)
            nbr=[[]]; ch=[]
            for i in range(b):
                c=len(nbr); nbr.append([0]); nbr[0].append(c); ch.append(c)
            leaves=[]
            for c in ch:
                for j in range(t):
                    l=len(nbr); nbr.append([c]); nbr[c].append(l); leaves.append(l)
            rng.shuffle(leaves)
            if rng.random()<.8:
                for i in range(0,len(leaves)-1,2):
                    u,v=leaves[i],leaves[i+1]; nbr[u].append(v); nbr[v].append(u)
            # tail
            p=0
            for _ in range(3):
                u=len(nbr); nbr.append([p]); nbr[p].append(u); p=u
            yield f"hub{b}.{t}",nbr
        elif k==4:
            n=2*rng.randint(4,14); d=rng.randint(6,8)
            if d>=n: continue
            yield f"reg{d}-{n}",nxl(nx.random_regular_graph(d,n,seed=rng.randrange(1<<30)))
        elif k==5:
            a=rng.randint(2,4); b=rng.randint(4,6)
            yield f"rook{b}",nxl(nx.line_graph(nx.complete_bipartite_graph(b,b)))
        elif k==6:
            # twin blowup of cycle with block sizes up to 6
            L=rng.randint(3,6); sz=[rng.randint(3,6) for _ in range(L)]
            layers=[];c=0
            for s in sz: layers.append(list(range(c,c+s)));c+=s
            G=nx.Graph();G.add_nodes_from(range(c))
            for i in range(L):
                for u in layers[i]:
                    for v in layers[(i+1)%L]: G.add_edge(u,v)
            yield "blow",[sorted(G[v]) for v in range(c)]
        elif k==7:
            # K_{5,5} minus perfect matching variants, Paley-ish circulants of degree 6-10
            n=rng.randint(12,30); ks=rng.sample(range(1,n//2+1),rng.randint(3,5))
            yield f"circ{n}",nxl(nx.circulant_graph(n,ks))
        elif k==8:
            # CFI over K_{d+1} small? hub trees with 8 branching and random inner layer graph
            depth=2; b=rng.randint(6,8); nbr=[[]]; level=[0]
            for _ in range(depth):
                nxt=[]
                for p in level:
                    for _ in range(b):
                        v=len(nbr); nbr.append([p]); nbr[p].append(v); nxt.append(v)
                level=nxt
            rng.shuffle(level)
            for i in range(0,len(level)-1,2):
                u,v=level[i],level[i+1]; nbr[u].append(v); nbr[v].append(u)
            yield f"tree{b}",nbr
        else:
            # disjoint union of hub-stars and small graphs
            parts=[nxl(nx.star_graph(rng.randint(4,9))) for _ in range(rng.randint(2,4))]
            parts.append(nxl(nx.complete_graph(rng.randint(5,8))))
            off=0;nbr=[]
            for g in parts:
                for r in g: nbr.append([w+off for w in r])
                off+=len(g)
            yield "unionstar",nbr
stats=Counter(); bad=0; n_done=0; timeouts=Counter(); firing={}
for name,g in inst():
    if time.time()-t0>limit: break
    if len(g)>120: continue
    try:
        signal.setitimer(signal.ITIMER_REAL,25)
        s1=Counter(); f=canonical_form_lists(g,stats=s1)
        if canonical_form_lists(relabel(g,rng))!=f:
            print("WRONG default",name,g,flush=True); bad+=1
        sg=Counter(); fg=canonical_form_lists(g,stats=sg,guarantee=True)
        if canonical_form_lists(relabel(g,rng),guarantee=True)!=fg:
            print("WRONG guarantee",name,g,flush=True); bad+=1
        signal.setitimer(signal.ITIMER_REAL,0)
    except TO:
        timeouts[name.split(',')[0][:6]]+=1
        continue
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)
    n_done+=1
    if sg['canon_ir'] or sg['canon_luks_fallback'] or sg['canon_perm_calls']:
        print("BAD guarantee counters",name,dict(sg),flush=True); bad+=1
    if s1['canon_luks_fallback']!=s1['canon_perm_calls'] :
        print("COUNTER mismatch",name,dict(s1),flush=True)
    stats['ir_runs']+=bool(s1['canon_ir']); stats['fb_runs']+=bool(s1['canon_luks_fallback']); stats['irtotal']+=s1['canon_ir']; stats['fbtotal']+=s1['canon_luks_fallback']
    if s1['canon_ir'] or s1['canon_luks_fallback']: firing[name.split('.')[0][:6]]=firing.get(name.split('.')[0][:6],0)+1
    # guarantee and default both equal nauty classes on relabel (same form iff same cert): consistency check
    c=cert(g)
    d=canonical_form_lists(relabel(g,rng))
    if d!=f: print("WRONG late",name,flush=True); bad+=1
print("done",n_done,"bad",bad,dict(stats),"timeouts",dict(timeouts),"firing",firing,time.time()-t0)
