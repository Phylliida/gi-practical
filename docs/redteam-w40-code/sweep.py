import os, sys as _s
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
_s.path.insert(0, ROOT); _s.path.insert(0, HERE)
import sys, json, subprocess, random, time
S=HERE
sys.path.insert(0,S)
from fams import FAMS, relabel
plan=sys.argv[1]  # e.g. dt2:2,3,4,5;tc2:...
TO=float(sys.argv[2]) if len(sys.argv)>2 else 60
for item in plan.split(";"):
    fam,sizes=item.split(":")
    for s in map(int,sizes.split(",")):
        rng=random.Random(1000*s+7)
        X=FAMS[fam](s,rng)
        d=max(map(len,X))
        Y=relabel(X,rng)
        p=subprocess.run(["nice","-n","19","timeout",str(TO),"python3",S+"/worker.py"],input=json.dumps(dict(X=X,Y=Y)),capture_output=True,text=True)
        if p.returncode==124:
            print(f"{fam}-{s} n={len(X)} d={d} TIMEOUT",flush=True); break
        if p.returncode!=0:
            print(f"{fam}-{s} ERROR {p.stderr[-400:]}",flush=True); break
        o=json.loads(p.stdout.strip().splitlines()[-1])
        k=o["keys"]
        print(f"{fam}-{s} n={len(X)} d={d} t={o['time']:.2f} same={o.get('same')} nodes={k.get('canon_luks_nodes',0)} cosets={k.get('canon_luks_cosets',0)} ir={k.get('canon_ir',0)} fb={k.get('canon_luks_fallback',0)} luksdeg={k.get('canon_luks_max_degree',0)} p1={k.get('canon_phase1_max_degree',0)} p2={k.get('canon_phase2_max_degree',0)} roots={k.get('canon_roots',0)}",flush=True)
