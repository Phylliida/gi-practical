import os, sys as _s
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
_s.path.insert(0, ROOT); _s.path.insert(0, HERE)
import sys, json, random, subprocess
S=HERE
def hub(b,t,seed):
    rng=random.Random(seed)
    nbr=[[]]; ch=[]
    for i in range(b):
        c=len(nbr); nbr.append([0]); nbr[0].append(c); ch.append(c)
    leaves=[]
    for c in ch:
        for j in range(t):
            l=len(nbr); nbr.append([c]); nbr[c].append(l); leaves.append(l)
    rng.shuffle(leaves)
    for i in range(0,len(leaves)-1,2):
        u,v=leaves[i],leaves[i+1]; nbr[u].append(v); nbr[v].append(u)
    p=0
    for _ in range(3):
        u=len(nbr); nbr.append([p]); nbr[p].append(u); p=u
    return nbr
TO=float(sys.argv[1])
for b,t in [(5,2),(6,2),(7,2),(8,2),(9,2),(8,3)]:
    X=hub(b,t,b*10+t)
    for kw in ({}, {"guarantee":True}):
        p=subprocess.run(["nice","-n","19","timeout",str(TO),"python3",S+"/worker.py"],input=json.dumps(dict(X=X,kw=kw)),capture_output=True,text=True)
        if p.returncode==124: print(b,t,kw,len(X),"TIMEOUT",flush=True); continue
        if p.returncode: print(b,t,kw,p.stderr[-300:],flush=True); continue
        o=json.loads(p.stdout.strip().splitlines()[-1]); k=o["keys"]
        print(b,t,kw,"n",len(X),"t %.2f"%o["time"],"nodes",k.get("canon_luks_nodes",0),"cos",k.get("canon_luks_cosets",0),"listed",k.get("canon_luks_listed",0),"ir",k.get("canon_ir",0),"fb",k.get("canon_luks_fallback",0),"permnodes",k.get("canon_perm_nodes",0),"p1",k.get("canon_phase1_max_degree",0),"p2",k.get("canon_phase2_max_degree",0),"deg",k.get("canon_luks_max_degree",0),flush=True)
