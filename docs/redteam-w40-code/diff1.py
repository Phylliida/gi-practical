import os, sys as _s
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
_s.path.insert(0, ROOT); _s.path.insert(0, HERE)
import sys, os, random, hashlib, time
sys.path.insert(0, ROOT)
sys.setrecursionlimit(100000)
import importlib.util
src=open(HERE + "/fuzz1.py").read()
src=src[:src.index("rng=random.Random(int(sys.argv[1])")]
exec(src)
from gi.kernel import ck
print("kernel", ck is not None, file=sys.stderr)
rng=random.Random(int(sys.argv[1]))
N=int(sys.argv[2])
out=open(sys.argv[3],"w")
for i,(name,g,col) in enumerate(gen_instances(rng)):
    if i>=N: break
    if len(g)>150: continue
    t0=time.perf_counter()
    f=canonical_form_lists(g,col)
    h,c2,_=relabel(g,col,rng)
    f2=canonical_form_lists(h,c2)
    if f!=f2:
        out.write(f"{i} {name} DIFFER\n")
    out.write(f"{i} {name} {len(g)} {hashlib.sha256(repr(f).encode()).hexdigest()[:16]}\n")
    out.flush()
