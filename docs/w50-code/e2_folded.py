"""E2: folded-cube family (Theorem B of w50). Local graph: Cay(F_2^n/<1>, images of e_1..e_n), n odd, b = 2^(n-1).
Exact checks: (a) M=1: least k over F_2 and F_3; (b) M=2 pattern graphs: corank of the span of closed 4-walks in the
cycle space, compared with dim D (D spanned by the pattern indicator vectors); (c) folded Johnson graph t=4."""
import itertools, sys, time
from gainlib import *


def folded_vertices(n):
    """vertices: canonical reps of F_2^n / <1> as ints (top bit zero)."""
    full = (1 << n) - 1
    reps = {}
    for x in range(1 << n):
        r = min(x, x ^ full)
        reps[x] = r
    return reps, sorted(set(reps.values()))


def folded_local(n):
    reps, vs = folded_vertices(n)
    index = {v: i for i, v in enumerate(vs)}
    nbrs = {}
    for v in vs:
        nbrs[index[v]] = sorted({index[reps[v ^ (1 << i)]] for i in range(n)})
    return index, vs, nbrs


def pattern_graph(n, M, F):
    """F: list of patterns I (tuples of coordinates)."""
    index, vs, nbrs = folded_local(n)
    b = len(vs)
    adj = {}
    for u in itertools.product(range(b), repeat=M):
        nb = set()
        for I in F:
            choices = [nbrs[u[j]] if j in I else [u[j]] for j in range(M)]
            for w in itertools.product(*choices):
                nb.add(w)
        nb.discard(u)
        adj[u] = sorted(nb)
    return adj, b


def span_closed_4walks(adj, eid, p, verts=None, target=None):
    """span of all closed walks of length 3,4 in the graph (cycle vectors); returns rank."""
    sp = F2Span() if p == 2 else FpSpan(p)
    A = {u: set(nb) for u, nb in adj.items()}
    for u in (verts or adj):
        nb = adj[u]
        for i, v in enumerate(nb):
            for w in nb[i + 1:]:
                # triangle
                if w in A[v]:
                    walk = [u, v, w, u]
                    addwalk(sp, walk, eid, p)
                for x in A[v] & A[w]:
                    if x != u:
                        addwalk(sp, [u, v, x, w, u], eid, p)
                if target is not None and sp.rank == target:
                    return sp.rank
    return sp.rank


def addwalk(sp, walk, eid, p):
    vec = vec_of_closed_walk(walk, eid, p)
    if p == 2:
        m = 0
        for e, c in vec.items():
            if c: m ^= 1 << e
        sp.add(m)
    else:
        sp.add(vec)


def gf2rank_dependent(F, M):
    vecs = []
    for I in F:
        m = 0
        for j in I: m |= 1 << j
        vecs.append(m)
    sp = F2Span(); [sp.add(v) for v in vecs]
    return sp.rank


if __name__ == "__main__":
    print("=== (a) M=1 folded n-cube: exact least k ===")
    for n in (3, 5):
        t0 = time.time()
        index, vs, nbrs = folded_local(n)
        b = len(vs)
        adj = {(i,): sorted((j,) for j in nbrs[i]) for i in range(b)}
        eid = edge_index(adj)
        for p in (2, 3):
            k, tbl = min_k(adj, eid, b, 1, p, kmax=n + 1 if n == 5 else 3)
            print(f"n={n} b={b} E={len(eid)} p={p} least k={k} ranks={tbl}", flush=True)
        print(f"  ({time.time() - t0:.1f}s)")

    print("=== (b) M=2 pattern graphs, n=5, b=16: closed 3/4-walk span vs cycle space ===")
    for name, F in [("cartesian", [(0,), (1,)]), ("tensor", [(0, 1)]), ("mix", [(0,), (0, 1)]), ("three", [(0,), (1,), (0, 1)])]:
        t0 = time.time()
        n = 5; M = 2
        adj, b = pattern_graph(n, M, F)
        adj = {u: nb for u, nb in adj.items()}
        eid = edge_index(adj)
        c = comps_of(adj)
        for p in (2, 3):
            target = len(eid) - len(adj) + c
            r = span_closed_4walks(adj, eid, p, target=target)
            print(f"{name}: V={len(adj)} E={len(eid)} comps={c} p={p} cyc_rank={target} rank(<=4-walks)={r} corank={target-r} rank(D)={gf2rank_dependent(F, M)} ({time.time()-t0:.1f}s)", flush=True)

    print("=== (c) folded Johnson t=4 (S_8 on 4+4 partitions, b=35) ===")
    t = 4; s = 2 * t
    pts = list(itertools.combinations(range(s), t))
    canon = lambda A: min(A, tuple(sorted(set(range(s)) - set(A))))
    verts = sorted({canon(A) for A in pts})
    idx = {v: i for i, v in enumerate(verts)}
    nbr = {}
    for v in verts:
        ns = set()
        A = set(v)
        for x in A:
            for y in set(range(s)) - A:
                ns.add(idx[canon(tuple(sorted(A - {x} | {y})))])
        ns.discard(idx[v])
        nbr[idx[v]] = sorted(ns)
    adj = {(i,): sorted((j,) for j in nbr[i]) for i in range(len(verts))}
    eid = edge_index(adj)
    target = len(eid) - len(adj) + comps_of(adj)
    for p in (2, 3):
        r = span_closed_4walks(adj, eid, p, target=target)
        print(f"b={len(verts)} deg={len(nbr[0])} E={len(eid)} p={p} cyc_rank={target} rank(<=4-walks)={r} corank={target-r}", flush=True)
