"""E2b: folded Johnson graphs F(2t,t) (S_{2t} on t+t partitions): rank of the span of closed walks of length<=4 vs the cycle space.
Deck group Z_2 from the antipodal double cover J(2t,t) -> F(2t,t). Lower bound: closed walk with non-trivial deck value has length >= t and >= (t+1)/2 values."""
import itertools, sys
from gainlib import *
from e2_folded import span_closed_4walks, addwalk


def build(t):
    s = 2 * t
    pts = list(itertools.combinations(range(s), t))
    canon = lambda A: min(A, tuple(sorted(set(range(s)) - set(A))))
    verts = sorted({canon(A) for A in pts})
    idx = {v: i for i, v in enumerate(verts)}
    adj = {}
    for v in verts:
        A = set(v); ns = set()
        for x in A:
            for y in set(range(s)) - A:
                ns.add(idx[canon(tuple(sorted(A - {x} | {y})))])
        ns.discard(idx[v])
        adj[(idx[v],)] = sorted((j,) for j in ns)
    return adj


if __name__ == "__main__":
    for t in (5, 6):
        adj = build(t)
        eid = edge_index(adj)
        target = len(eid) - len(adj) + comps_of(adj)
        for p in (2, 3):
            r = span_closed_4walks(adj, eid, p, target=target)
            print(f"t={t} b={len(adj)} E={len(eid)} p={p} cyc_rank={target} rank(<=4-walks)={r} corank={target-r}", flush=True)
