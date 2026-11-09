"""w50: exact narrow-generation tools. Pure Python (numpy is broken here).
Conventions: a graph is on an explicit vertex list; edges are 2-frozensets (undirected, no loops).
A k-box is a product of k-subsets of [b] per coordinate. Z_box(k) is the span of the cycle spaces of
induced subgraphs on k-boxes; it equals the F_p-span of closed walks with <=k values per coordinate
(a closed walk with <=k values per coordinate lies in a box, and its cycle vector is a cycle of the
induced subgraph; conversely cycles of induced subgraphs are such walks).
"""
import itertools, random
from collections import defaultdict


class F2Span:
    """Row-reduced span of integer bitmasks over F_2."""
    def __init__(self): self.b = {}; self.rank = 0
    def add(self, v):
        while v:
            h = v.bit_length() - 1
            if h in self.b: v ^= self.b[h]
            else:
                self.b[h] = v; self.rank += 1; return True
        return False


class FpSpan:
    """Row-reduced span of sparse dict vectors over F_p."""
    def __init__(self, p): self.p = p; self.b = {}; self.rank = 0
    def add(self, v):
        p = self.p; v = {k: c % p for k, c in v.items() if c % p}
        while v:
            h = max(v)
            if h in self.b:
                c = v[h]; w = self.b[h]
                for k, x in w.items():
                    nv = (v.get(k, 0) - c * x) % p
                    if nv: v[k] = nv
                    else: v.pop(k, None)
            else:
                inv = pow(v[h], -1, p)
                self.b[h] = {k: c * inv % p for k, c in v.items()}
                self.rank += 1; return True
        return False


def cycle_basis(verts, adj):
    """Fundamental cycles of the graph on verts w.r.t. a BFS forest: list of closed vertex sequences."""
    parent = {}; order = []; cycles = []
    vset = set(verts)
    for s in verts:
        if s in parent: continue
        parent[s] = None; q = [s]
        for u in q:
            order.append(u)
            for v in adj[u]:
                if v in vset and v not in parent:
                    parent[v] = u; q.append(v)
    depth = {}
    for u in order:
        depth[u] = 0 if parent[u] is None else depth[parent[u]] + 1
    seen = set()
    for u in order:
        for v in adj[u]:
            if v not in vset: continue
            e = frozenset((u, v))
            if e in seen: continue
            seen.add(e)
            if parent[u] == v or parent[v] == u: continue
            # path from u up to lca and from v up to lca
            a, b = u, v; pa = [a]; pb = [b]
            while a != b:
                if depth[a] >= depth[b]: a = parent[a]; pa.append(a)
                else: b = parent[b]; pb.append(b)
            cycles.append(pa + pb[-2::-1] + [u] if len(pb) > 1 else pa + [u])
    return cycles


def cycle_rank(verts, adj):
    vset = set(verts); seen = set(); comps = 0; ne = 0
    for u in verts:
        for v in adj[u]:
            if v in vset: ne += 1
    ne //= 2
    for s in verts:
        if s in seen: continue
        comps += 1; st = [s]; seen.add(s)
        while st:
            u = st.pop()
            for v in adj[u]:
                if v in vset and v not in seen:
                    seen.add(v); st.append(v)
    return ne - len(verts) + comps


def edge_index(adj):
    es = sorted({tuple(sorted((u, v))) for u in adj for v in adj[u]})
    return {frozenset(e): i for i, e in enumerate(es)}


def vec_of_closed_walk(walk, eid, p):
    v = defaultdict(int)
    for a, c in zip(walk, walk[1:]):
        e = eid[frozenset((a, c))]
        # orientation sign: lower-to-higher +1
        v[e] += 1 if a < c else -1
    return {k: c % p for k, c in v.items() if c % p}


def box_span(adj, eid, b, M, k, p, boxes=None, maxboxes=None, rng=None):
    """F_p span of cycle spaces of induced subgraphs on all (or sampled) k-boxes. Vertices are M-tuples over range(b).
    Returns rank; adj maps vertices to neighbour lists."""
    sp = F2Span() if p == 2 else FpSpan(p)
    subsets = list(itertools.combinations(range(b), k))
    allb = itertools.product(subsets, repeat=M)
    if boxes is not None: allb = boxes
    elif maxboxes is not None:
        nb = len(subsets) ** M
        if nb > maxboxes:
            allb = (tuple(rng.choice(subsets) for _ in range(M)) for _ in range(maxboxes))
    target = sum(1 for _ in eid) - len(adj) + comps_of(adj)
    for B in allb:
        vs = [v for v in itertools.product(*B) if v in adj]
        if len(vs) < 3: continue
        vset = set(vs)
        sub = {u: [w for w in adj[u] if w in vset] for u in vs}
        for cyc in cycle_basis(vs, sub):
            vec = vec_of_closed_walk(cyc, eid, p)
            if p == 2:
                m = 0
                for e, c in vec.items():
                    if c: m ^= 1 << e
                sp.add(m)
            else:
                sp.add(vec)
        if sp.rank == target: break
    return sp.rank, target


def comps_of(adj):
    seen = set(); c = 0
    for s in adj:
        if s in seen: continue
        c += 1; st = [s]; seen.add(s)
        while st:
            u = st.pop()
            for v in adj[u]:
                if v not in seen:
                    seen.add(v); st.append(v)
    return c


def min_k(adj, eid, b, M, p, kmax=None, maxboxes=None, rng=None):
    """Least k such that k-box cycles span the cycle space over F_p; returns (k, rank table)."""
    kmax = kmax or b
    tbl = {}
    for k in range(2, kmax + 1):
        r, t = box_span(adj, eid, b, M, k, p, maxboxes=maxboxes, rng=rng)
        tbl[k] = (r, t)
        if r == t:
            return k, tbl
    return None, tbl


def sum_mod(walk): return walk
