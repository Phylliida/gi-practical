"""Is the constant 4 in Theorem A' tight?  X = K_b x K_2: vertices (x,e), (x,e)~(y,1-e) iff x!=y.  N_1 = S_b is 2-transitive on coordinate 1
and J={1}; coordinate 2 carries the bipartition and has no 2-transitive kernel (or has b_2=2).  Hypothesis of A' holds."""
import itertools, sys
sys.path.insert(0, '.')
from rtlib import *

for b in range(4, 11):
    verts = [(x, e) for x in range(b) for e in (0, 1)]
    adj = {(x, e): sorted((y, 1 - e) for y in range(b) if y != x) for x, e in verts}
    C = Cycles(adj)
    out = []
    for p in (2, 3, 5):
        for k in (3, 4):
            sp = make_span(p)
            for box in itertools.combinations(range(b), k):
                for cyc in box_cycles(adj, [box, (0, 1)]):
                    sp.addv(C.vector(cyc))
            out.append((p, k, sp.rank))
    rows = []
    for box in itertools.combinations(range(b), 3):
        for cyc in box_cycles(adj, [box, (0, 1)]):
            rows.append(C.vector(cyc))
    rk, inv = smith_invariants(rows, C.rank)
    print(f"b={b} cycle rank {C.rank} (p,k,rank): {out}; Z-span of 3-narrow: rank {rk}, non-unit invariants {inv[:12]}{'...' if len(inv) > 12 else ''}", flush=True)
