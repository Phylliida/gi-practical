"""Referee harness for docs/w50-gain.md.  Written independently of docs/w50-code/ (does not import it).
Graphs: dict vertex -> sorted list of neighbours.  Cycle vectors are taken in the coordinates of the non-tree
edges of a BFS forest (a cycle vector is determined by those).  Ranks over F_p; integer quotients by Smith form."""
import itertools, math, random
from collections import defaultdict, deque


# ---------------- local graphs ----------------
def complete(b):
    return {x: [y for y in range(b) if y != x] for x in range(b)}


def folded_cube(n):
    """F_2^n / <1>, vertices = representatives with low bit 0 of the n-bit word; adjacent by single bit flips."""
    full = (1 << n) - 1
    rep = lambda x: min(x, x ^ full)
    verts = sorted({rep(x) for x in range(1 << n)})
    index = {v: i for i, v in enumerate(verts)}
    adj = {index[v]: sorted({index[rep(v ^ (1 << i))] for i in range(n)}) for v in verts}
    return adj, verts, index, full


def odd_graph(t):
    """t-subsets of [2t+1], adjacent = disjoint."""
    verts = [frozenset(c) for c in itertools.combinations(range(2 * t + 1), t)]
    return {i: [j for j, y in enumerate(verts) if not (x & y)] for i, x in enumerate(verts)}, verts


def odd_girth(adj):
    """shortest odd closed walk length via BFS parity"""
    best = None
    for s in adj:
        dist = {(s, 0): 0}
        q = deque([(s, 0)])
        while q:
            v, p = q.popleft()
            d = dist[(v, p)]
            if v == s and p == 1:
                best = d if best is None else min(best, d)
                break
            for w in adj[v]:
                st = (w, p ^ 1)
                if st not in dist:
                    dist[st] = d + 1
                    q.append(st)
    return best


# ---------------- pattern graph Gamma_F ----------------
def pattern_graph(local, b, M, F):
    """F: iterable of tuples of coordinates (nonempty).  Vertices are tuples in [b]^M."""
    verts = list(itertools.product(range(b), repeat=M))
    adj = {}
    for u in verts:
        nb = set()
        for I in F:
            opts = [local[u[j]] for j in I]
            for vals in itertools.product(*opts):
                w = list(u)
                for j, x in zip(I, vals):
                    w[j] = x
                nb.add(tuple(w))
        adj[u] = sorted(nb)
    return adj


def num_edges(adj):
    return sum(len(v) for v in adj.values()) // 2


# ---------------- cycle space ----------------
class Cycles:
    def __init__(self, adj):
        self.adj = adj
        self.parent = {}
        self.comps = 0
        for s in adj:
            if s in self.parent:
                continue
            self.comps += 1
            self.parent[s] = None
            q = deque([s])
            while q:
                v = q.popleft()
                for w in adj[v]:
                    if w not in self.parent:
                        self.parent[w] = v
                        q.append(w)
        self.nontree = {}
        for u in adj:
            for v in adj[u]:
                if u < v and self.parent.get(u) != v and self.parent.get(v) != u:
                    self.nontree[(u, v)] = len(self.nontree)
        self.rank = len(self.nontree)

    def word(self, walk):
        """signed generator list of a closed walk (list of vertices, first==last)"""
        out = []
        for a, b in zip(walk, walk[1:]):
            if a < b:
                g = self.nontree.get((a, b))
                if g is not None:
                    out.append(g + 1)
            else:
                g = self.nontree.get((b, a))
                if g is not None:
                    out.append(-(g + 1))
        return out

    def vector(self, walk):
        d = defaultdict(int)
        for s in self.word(walk):
            d[abs(s) - 1] += 1 if s > 0 else -1
        return {k: v for k, v in d.items() if v}


class Span:
    """incremental rank over F_p of sparse integer vectors (dict col->coef)"""

    def __init__(self, p):
        self.p = p
        self.piv = {}
        self.rank = 0

    def add(self, vec):
        p = self.p
        v = {k: c % p for k, c in vec.items() if c % p}
        while v:
            k = min(v)
            if k not in self.piv:
                inv = pow(v[k], -1, p)
                self.piv[k] = {i: c * inv % p for i, c in v.items()}
                self.rank += 1
                return True
            c = v[k]
            for i, e in self.piv[k].items():
                nv = (v.get(i, 0) - c * e) % p
                if nv:
                    v[i] = nv
                else:
                    v.pop(i, None)
        return False


class Span2:
    """F_2 rank with python-int vectors"""

    def __init__(self):
        self.piv = {}
        self.rank = 0

    def add(self, x):
        while x:
            h = x.bit_length() - 1
            if h in self.piv:
                x ^= self.piv[h]
            else:
                self.piv[h] = x
                self.rank += 1
                return True
        return False


def make_span(p):
    if p == 2:
        s = Span2()
        s.addv = lambda vec: s.add(sum(1 << k for k, c in vec.items() if c & 1))
        return s
    s = Span(p)
    s.addv = s.add
    return s


def box_cycles(adj, box_sets):
    """fundamental closed walks of the subgraph induced on the product of box_sets"""
    verts = list(itertools.product(*box_sets))
    vset = set(verts)
    par, dep = {}, {}
    out = []
    for s in verts:
        if s in par:
            continue
        par[s] = None
        dep[s] = 0
        q = deque([s])
        while q:
            x = q.popleft()
            for w in adj[x]:
                if w in vset and w not in par:
                    par[w] = x
                    dep[w] = dep[x] + 1
                    q.append(w)
    for u in verts:
        for v in adj[u]:
            if v in vset and u < v and par[u] != v and par[v] != u:
                out.append(tree_cycle(par, dep, u, v))
    return out


def tree_cycle(par, dep, u, v):
    pu, pv = [u], [v]
    a, b = u, v
    while dep[a] > dep[b]:
        a = par[a]
        pu.append(a)
    while dep[b] > dep[a]:
        b = par[b]
        pv.append(b)
    while a != b:
        a = par[a]
        pu.append(a)
        b = par[b]
        pv.append(b)
    # u .. lca .. v, v->u
    return pu + pv[-2::-1] + [u]


def least_k(adj, b, M, p, kmax=None):
    """exact least k with k-box cycles spanning the cycle space over F_p; adj keys must cover [b]^M"""
    C = Cycles(adj)
    target = C.rank
    tbl = {}
    if target == 0:
        return 1, {1: (0, 0)}
    for k in range(2, (kmax or b) + 1):
        sp = make_span(p)
        for box in itertools.product(itertools.combinations(range(b), k), repeat=M):
            for cyc in box_cycles(adj, box):
                sp.addv(C.vector(cyc))
            if sp.rank == target:
                break
        tbl[k] = (sp.rank, target)
        if sp.rank == target:
            return k, tbl
    return None, tbl


def closed_walks_upto(adj, L):
    """all closed walks of length <=L without immediate backtrack, based at each vertex"""
    for s in adj:
        def rec(path):
            if len(path) > 1 and path[-1] == s and len(path) >= 4:
                yield list(path)
            if len(path) - 1 < L:
                for w in adj[path[-1]]:
                    if len(path) >= 2 and w == path[-2]:
                        continue
                    if w < s:
                        continue
                    path.append(w)
                    yield from rec(path)
                    path.pop()
        yield from rec([s])


# ---------------- integer quotient by Smith form ----------------
def smith_invariants(rows, ncols):
    """non-unit invariant factors and rank of the row space of sparse integer rows (dict)."""
    rows = [dict(r) for r in rows if r]
    rank = 0
    # phase 1: unit pivots, sparse
    bycol = defaultdict(set)
    for i, r in enumerate(rows):
        for c in r:
            bycol[c].add(i)
    alive = set(range(len(rows)))
    progress = True
    while progress:
        progress = False
        for i in sorted(alive, key=lambda i: len(rows[i])):
            if i not in alive:
                continue
            r = rows[i]
            if not r:
                alive.discard(i)
                continue
            unit = [c for c, v in r.items() if abs(v) == 1]
            if not unit:
                continue
            c0 = min(unit, key=lambda c: len(bycol[c]))
            s = r[c0]
            for k in list(bycol[c0]):
                if k == i:
                    continue
                f = rows[k][c0] * s
                for c, v in r.items():
                    nv = rows[k].get(c, 0) - f * v
                    if nv:
                        if c not in rows[k]:
                            bycol[c].add(k)
                        rows[k][c] = nv
                    elif c in rows[k]:
                        del rows[k][c]
                        bycol[c].discard(k)
            for c in r:
                bycol[c].discard(i)
            alive.discard(i)
            rank += 1
            progress = True
    # phase 2: dense residual (rows without unit entries)
    res = [rows[i] for i in alive if rows[i]]
    cols = sorted({c for r in res for c in r})
    idx = {c: i for i, c in enumerate(cols)}
    A = [[r.get(c, 0) for c in cols] for r in res]
    inv = []
    while A and A[0]:
        best = None
        for i, r in enumerate(A):
            for j, v in enumerate(r):
                if v and (best is None or abs(v) < abs(A[best[0]][best[1]])):
                    best = (i, j)
        if best is None:
            break
        i, j = best
        A[0], A[i] = A[i], A[0]
        for r in A:
            r[0], r[j] = r[j], r[0]
        while True:
            a = A[0][0]
            done = True
            for r in A[1:]:
                q = r[0] // a
                if q:
                    for c in range(len(r)):
                        r[c] -= q * A[0][c]
                if r[0]:
                    done = False
            for c in range(1, len(A[0])):
                q = A[0][c] // a
                if q:
                    for r in A:
                        r[c] -= q * r[0]
                if A[0][c]:
                    done = False
            if done:
                # divisibility fix
                bad = None
                for ri, r in enumerate(A[1:], 1):
                    for x in r[1:]:
                        if x % a:
                            bad = ri
                            break
                    if bad:
                        break
                if bad:
                    for c in range(len(A[0])):
                        A[0][c] += A[bad][c]
                    continue
                break
            # choose smaller pivot in first row/col
            bi, bj = 0, 0
            for ri, r in enumerate(A):
                if r[0] and abs(r[0]) < abs(A[bi][bj]):
                    bi, bj = ri, 0
            for c, x in enumerate(A[0]):
                if x and abs(x) < abs(A[bi][bj]):
                    bi, bj = 0, c
            A[0], A[bi] = A[bi], A[0]
            for r in A:
                r[0], r[bj] = r[bj], r[0]
        inv.append(abs(A[0][0]))
        rank += 1
        A = [r[1:] for r in A[1:]]
    return rank, sorted(x for x in inv if x != 1)


# ---------------- Tietze simplification (pi_1 level) ----------------
def free_reduce(w):
    out = []
    for x in w:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    i, j = 0, len(out) - 1
    while i < j and out[i] == -out[j]:
        i += 1
        j -= 1
    return out[i:j + 1]


def tietze_simplify(relators, ngens, maxlen=4000):
    """eliminate generators using relators in which some generator occurs once.  Returns (remaining gens, relators)."""
    rels = {tuple(sorted({tuple(free_reduce(r))})[0]) for r in relators}
    rels = [list(r) for r in rels if r]
    alive = set(range(1, ngens + 1))
    while True:
        rels.sort(key=len)
        chosen = None
        for r in rels:
            cnt = defaultdict(int)
            for x in r:
                cnt[abs(x)] += 1
            onces = [g for g, c in cnt.items() if c == 1]
            if onces:
                g = onces[0]
                chosen = (r, g)
                break
        if chosen is None:
            break
        r, g = chosen
        i = next(k for k, x in enumerate(r) if abs(x) == g)
        rot = r[i:] + r[:i]
        if rot[0] == g:
            sub = [-x for x in reversed(rot[1:])]
        else:
            sub = rot[1:]
        subinv = [-x for x in reversed(sub)]
        new = []
        seen = set()
        for w in rels:
            if w is r:
                continue
            if any(abs(x) == g for x in w):
                nw = []
                for x in w:
                    if x == g:
                        nw.extend(sub)
                    elif x == -g:
                        nw.extend(subinv)
                    else:
                        nw.append(x)
                w = free_reduce(nw)
                if len(w) > maxlen:
                    raise RuntimeError("relator length blow-up")
            if w:
                t = tuple(w)
                if t not in seen:
                    seen.add(t)
                    new.append(w)
        rels = new
        alive.discard(g)
    return alive, rels
