#!/usr/bin/env python
"""Simulate HJ's LocalCertificate window procedure exactly (via nauty) on the
point-line incidence graph of PG(m-1,2), for small test size kappa.

Root: G = Sym(vertices) on ordered pairs, T subset of points.
Level 1: G = Sym(Wt) x H_1 on Wt x P_1, T subset of Q_1 (cosets of D_1).
Reports the sequence of window updates and compares with the theorem.
Usage: hjsim.py root m kappa | level1 m kappa
"""
import sys, itertools, time, math
from pynauty import Graph, autgrp


def span(vecs):
    S = {0}
    for v in vecs:
        S |= {s ^ v for s in S}
    return S


def independent(vecs):
    return len(span(vecs)) == 1 << len(vecs)


def perm_closure(gens):
    idn = tuple(range(len(gens[0]))) if gens else None
    if not gens:
        return None
    seen = {idn}
    frontier = [idn]
    while frontier:
        nxt = []
        for a in frontier:
            for g in gens:
                b = tuple(g[x] for x in a)
                if b not in seen:
                    seen.add(b)
                    nxt.append(b)
        frontier = nxt
    return seen


def parity(p):
    n = len(p)
    seen = [False] * n
    s = 1
    for i in range(n):
        if not seen[i]:
            l = 0
            j = i
            while not seen[j]:
                seen[j] = True
                j = p[j]
                l += 1
            if l % 2 == 0:
                s = -s
    return s


def contains_alt(group, k):
    if group is None:
        return k <= 2
    alt = math.factorial(k) // 2
    return sum(1 for p in group if parity(p) == 1) >= alt


class Pos:
    def __init__(self, pairs):
        self.pairs = pairs


def pts(m):
    return list(range(1, 1 << m))


def lines(m):
    L = set()
    for a in range(1, 1 << m):
        for b in range(a + 1, 1 << m):
            L.add(tuple(sorted((a, b, a ^ b))))
    return sorted(L)


# ------- root simulation --------
def root(m, kappa):
    P = pts(m)
    B = lines(m)
    n = len(P) + len(B)
    pid = {p: i for i, p in enumerate(P)}
    bid = {b: len(P) + i for i, b in enumerate(B)}
    adj = set()
    for b in B:
        for p in b:
            adj.add((pid[p], bid[b]))
            adj.add((bid[b], pid[p]))
    T = [1 << i for i in range(kappa)]
    Tid = [pid[t] for t in T]
    Tset = set(Tid)
    D = span(T)
    Sigma = 0
    for t in T:
        Sigma ^= t
    print(f"root: m={m} n={n} kappa={kappa}, D dim {kappa}, |D|={len(D)}")

    def blocktype(b):
        pts_ = set(b)
        if pts_ & set(T):
            return "Btouch(T)"
        o = pts_ & D
        ostar = {x for x in o if x not in (0, Sigma)}
        if ostar:
            return "Btouch(D*)"
        if o:
            return "Btouch(Sigma)"
        return "Bfree"

    vtype = {}
    for p in P:
        if pid[p] in Tset:
            vtype[pid[p]] = "T"
        elif p == Sigma:
            vtype[pid[p]] = "Sigma"
        elif p in D:
            vtype[pid[p]] = "D*"
        else:
            vtype[pid[p]] = "P1"
    for b in B:
        vtype[bid[b]] = blocktype(b)

    N = n
    window = set()
    allpairs = [(u, v) for u in range(N) for v in range(N) if u != v]

    def auto(colorclasses):
        """Aut of (adj, window) arcs preserving vertex classes."""
        nv = 2 * N
        adjd = {u: [] for u in range(nv)}
        # vertical
        for u in range(N):
            adjd[u].append(u + N)
        # layer0: window and adj; layer1: window
        for (u, v) in window:
            adjd[N + u].append(N + v)
            if (u, v) in adj:
                adjd[u].append(v)
        cols = []
        for c in colorclasses:
            cols.append(set(c))
        for c in colorclasses:
            cols.append({x + N for x in c})
        g = Graph(nv, directed=True, adjacency_dict=adjd, vertex_coloring=cols)
        res = autgrp(g)
        gens = [g2[:N] for g2 in res[0]]
        return gens, res[1], res[2]

    def phi(gens):
        idx = {t: i for i, t in enumerate(Tid)}
        return [tuple(idx[g[t]] for t in Tid) for g in gens]

    def classes(indiv=()):
        indiv = list(indiv)
        s = set(indiv)
        base = [sorted(Tset - s), sorted(set(range(N)) - Tset - s)]
        res = [c for c in base if c]
        res += [[v] for v in indiv]
        return res

    t0 = time.time()
    step = 0
    while True:
        gens, gs1, gs2 = auto(classes())
        img = perm_closure(phi(gens))
        full = contains_alt(img, kappa)
        print(f"step {step}: |A|={gs1:.3g}e{gs2} imageAlt={full} |W|={len(window)}  t={time.time()-t0:.1f}")
        if not full:
            print("NONFULL")
            break
        rest = [p for p in allpairs if p not in window]
        # orbits on remaining positions
        parent = {}

        def find(x):
            while parent.setdefault(x, x) != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        def union(a, b):
            ra, rb = find(a), find(b)
            if ra != rb:
                parent[ra] = rb

        for g in gens:
            for (u, v) in rest:
                union((u, v), (g[u], g[v]))
        orbs = {}
        for p in rest:
            orbs.setdefault(find(p), []).append(p)
        # affected test
        E = []
        for rep, orb in orbs.items():
            u, v = orb[0]
            sg, _, _ = auto(classes((u, v)))
            im = perm_closure(phi(sg)) if sg else {tuple(range(kappa))}
            if not contains_alt(im, kappa):
                E.append(orb)
        V = []
        if E:
            for o in E:
                V += o
            kind = "affected"
        else:
            # K: pointwise stabilizer of U
            Uv = set()
            for (u, v) in rest:
                Uv.add(u)
                Uv.add(v)
            sg, _, _ = auto(classes(Uv))
            im = perm_closure(phi(sg)) if sg else {tuple(range(kappa))}
            if contains_alt(im, kappa):
                print("FULL (K maps onto Alt(T))")
                break
            for rep, orb in orbs.items():
                Dv = set()
                for (u, v) in orb:
                    Dv.add(u)
                    Dv.add(v)
                sg, _, _ = auto(classes(Dv))
                im = perm_closure(phi(sg)) if sg else {tuple(range(kappa))}
                if contains_alt(im, kappa):
                    continue
                triv = len(im) == 1
                if triv:
                    V += orb
            kind = "VISIBLE"
            if not V:
                print("step4: no visible orbit")
                break
        # classify V
        hist = {}
        for (u, v) in V:
            key = (vtype[u], vtype[v])
            hist[key] = hist.get(key, 0) + 1
        print(f"  V[{kind}] size {len(V)}: " + ", ".join(f"{k[0]}x{k[1]}:{c}" for k, c in sorted(hist.items())))
        window |= set(V)
        step += 1
        if step > 12:
            print("step limit")
            break


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "root":
        root(int(sys.argv[2]), int(sys.argv[3]))
