import os, sys as _s
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
_s.path.insert(0, ROOT); _s.path.insert(0, HERE)
import sys, json, time
sys.path.insert(0, ROOT)
sys.setrecursionlimit(100000)
from collections import Counter
from gi.canon import canonical_labeling_lists, canonical_form_lists, _form_of
d = json.load(sys.stdin)
st = Counter()
t0 = time.perf_counter()
lab, gens = canonical_labeling_lists(d["X"], d.get("col"), stats=st, **d.get("kw",{}))
t1 = time.perf_counter()
out = dict(time=t1-t0, keys={k: st[k] for k in st if k.startswith("canon_")}, ngens=len(gens))
if d.get("Y") is not None:
    ly, _ = canonical_labeling_lists(d["Y"], d.get("colY"), **d.get("kw",{}))
    out["same"] = _form_of(d["X"], lab, d.get("col")) == _form_of(d["Y"], ly, d.get("colY"))
print(json.dumps(out))
