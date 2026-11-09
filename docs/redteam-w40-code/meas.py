import os, sys as _s
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
_s.path.insert(0, ROOT); _s.path.insert(0, HERE)
import sys, time
sys.path.insert(0, ROOT)
sys.path.insert(0, ".")
sys.setrecursionlimit(100000)
import random
from collections import Counter
import pynauty
from fams import *
import gi.luks as L
from gi.canon import canonical_labeling_lists
orig=L._list_group
sz=[]
def p(G,x,run):
    sz.append((G.n,G.order()))
    return orig(G,x,run)
L._list_group=p
for name,X in (("pa44-4 (k=4,t=4)",twin_blocks_full(4,4,None)),("ttb k=6",twin_triples_big_upset(6,None)),("ttb k=7",twin_triples_big_upset(7,None)),("ttb k=8",twin_triples_big_upset(8,None))):
    t0=time.perf_counter()
    g=pynauty.Graph(len(X),adjacency_dict={i:list(X[i]) for i in range(len(X))})
    pynauty.certificate(g); t1=time.perf_counter()
    print(name,"n",len(X),"d",max(map(len,X)),"nauty %.4fs"%(t1-t0),flush=True)
    sz.clear()
    st=Counter(); t0=time.perf_counter()
    import signal
    def h(*a): raise TimeoutError
    signal.signal(signal.SIGALRM,h); signal.setitimer(signal.ITIMER_REAL,float(sys.argv[1]))
    try:
        canonical_labeling_lists(X,stats=st); print(" ours %.2fs"%(time.perf_counter()-t0),"p1",st["canon_phase1_max_degree"],"listed",sorted(sz,reverse=True)[:3],"nodes",st["canon_luks_nodes"],flush=True)
    except TimeoutError:
        print(" ours TIMEOUT after",sys.argv[1],"p1",st["canon_phase1_max_degree"],"listing group",sorted(sz,reverse=True)[:1],flush=True)
    signal.setitimer(signal.ITIMER_REAL,0)
