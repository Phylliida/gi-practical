"""E2c: Odd graphs O_{t+1} (t-subsets of [2t+1], disjoint = adjacent; H=S_{2t+1} almost simple, odd girth 2t+1).
Exact least k for Petersen (t=2) over F_2,F_3; for t=3 (b=35) rank of the span of closed walks of length<=6 vs cycle rank over F_2 and F_3
(walks of length<=6 lie in boxes of <=6 values, so the corank bounds k>=7 at F_2 if nonzero)."""
import itertools, sys
from gainlib import *

def odd_graph(t):
    s = 2 * t + 1
    V = list(itertools.combinations(range(s), t))
    idx = {v: i for i, v in enumerate(V)}
    adj = {(i,): [] for i in range(len(V))}
    for v in V:
        for w in V:
            if not set(v) & set(w):
                adj[(idx[v],)].append((idx[w],))
    return adj

def span_walks_upto(adj, eid, p, L, target):
    sp = F2Span() if p == 2 else FpSpan(p)
    A = {u: set(nb) for u, nb in adj.items()}
    def addcycle(walk):
        vec = vec_of_closed_walk(walk, eid, p)
        if p == 2:
            m = 0
            for e, c in vec.items():
                if c: m ^= 1 << e
            sp.add(m)
        else:
            sp.add(vec)
    # enumerate closed walks by DFS from each start vertex up to length L, no immediate backtrack
    def dfs(path):
        u = path[-1]
        if len(path) - 1 >= L: return
        for v in adj[u]:
            if len(path) >= 2 and v == path[-2]: continue
            if v == path[0] and len(path) >= 3:
                addcycle(path + [v])
            elif v not in path:
                dfs(path + [v])
    for s in adj:
        dfs([s])
        if sp.rank == target: break
    return sp.rank

for t in (2, 3):
    adj = odd_graph(t)
    eid = edge_index(adj)
    target = len(eid) - len(adj) + comps_of(adj)
    if t == 2:
        for p in (2, 3):
            k, tbl = min_k(adj, eid, len(adj), 1, p, kmax=6)
            print(f"Petersen t=2 b={len(adj)} deg={len(adj[(0,)])} p={p} cyc_rank={target} least k={k} tbl={tbl}", flush=True)
    else:
        for L in (5, 6, 8):
            for p in (2, 3):
                r = span_walks_upto(adj, eid, p, L, target)
                print(f"O_4 t=3 b={len(adj)} deg={len(adj[(0,)])} p={p} L<={L} cyc_rank={target} rank={r} corank={target-r}", flush=True)
