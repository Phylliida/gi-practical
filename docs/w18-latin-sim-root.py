#!/usr/bin/env python
"""Sampled exact simulation of HJ LocalCertificate windows on PG(m-1,2).
Each window step: for every position type pair, nauty-compute stabilizer images
on samples; then either V = affected positions, or (no affected) test step 3 and
step 4 visibility.  Compares actual windows with Theorem B's prediction.
Usage: sim2.py root m kappa [samples] | level1 m kappa [samples]
"""
import sys, time, math, random
from pynauty import Graph, autgrp
random.seed(1)


def span(vs):
    S = {0}
    for v in vs:
        S |= {s ^ v for s in S}
    return S


def perm_closure(gens, k):
    idn = tuple(range(k))
    if not gens:
        return {idn}
    seen = {idn}
    fr = [idn]
    while fr:
        nx = []
        for a in fr:
            for g in gens:
                b = tuple(g[x] for x in a)
                if b not in seen:
                    seen.add(b)
                    nx.append(b)
        fr = nx
    return seen


def even(p):
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
    return s == 1


def alt_size(k):
    return math.factorial(k) // 2


class Sim:
    """Vertices 0..N-1 each doubled in 2 layers; extra gadget vertices appended."""

    def __init__(self, N, adj, gadget_edges, extra_classes, kappa, phi_fn):
        self.N = N
        self.adj = adj  # dict ordered pair -> True (adjacency)
        self.gadget = gadget_edges  # list of (a,b) arcs on vertices in layer0/extra
        self.extra_classes = extra_classes
        self.kappa = kappa
        self.phi_fn = phi_fn
        self.window = set()

    def auto(self, base_classes, indiv=()):
        indiv = list(indiv)
        s = set(indiv)
        N = self.N
        extra_n = sum(len(c) for c in self.extra_classes)
        nv = 2 * N + extra_n
        adjd = {u: [] for u in range(nv)}
        for u in range(N):
            adjd[u].append(u + N)
        for (u, v) in self.window:
            adjd[N + u].append(N + v)
            if (u, v) in self.adj:
                adjd[u].append(v)
        for (a, b) in self.gadget:
            adjd[a].append(b)
        cols = []
        for c in base_classes:
            r = [x for x in c if x not in s]
            if r:
                cols.append(set(r))
        for v in indiv:
            cols.append({v})
        k = len(cols)
        for i in range(k):
            cols.append({x + N for x in cols[i]})
        for c in self.extra_classes:
            cols.append(set(c))
        g = Graph(nv, directed=True, adjacency_dict=adjd, vertex_coloring=cols)
        res = autgrp(g)
        return res[0], res[1], res[2]

    def phi(self, gens):
        ims = [self.phi_fn(g) for g in gens]
        return perm_closure(ims, self.kappa)

    def image_contains_alt(self, gens):
        im = self.phi(gens)
        return sum(1 for p in im if even(p)) >= alt_size(self.kappa)


def run_steps(sim, base_classes, allpos, vtype, posdesc, samples, predicted_kinds=None):
    N = sim.N
    t0 = time.time()
    step = 0
    while step < 12:
        gens, g1, g2 = sim.auto(base_classes)
        full = sim.image_contains_alt(gens)
        print(f"step {step}: |A|~{g1:.3g}e{g2} imageAlt={full} |W|={len(sim.window)} (t={time.time()-t0:.1f})", flush=True)
        if not full:
            print("NONFULL")
            return
        rest = [p for p in allpos if p not in sim.window]
        if not rest:
            print("window complete: FULL")
            return
        # group positions by type signature
        bytype = {}
        for p in rest:
            bytype.setdefault(posdesc(p), []).append(p)
        affected = {}
        for key, plist in sorted(bytype.items()):
            sample = random.sample(plist, min(samples, len(plist)))
            aff = []
            for (u, v) in sample:
                sg, _, _ = sim.auto(base_classes, (u, v))
                aff.append(not sim.image_contains_alt(sg))
            if all(aff):
                affected[key] = True
            elif any(aff):
                affected[key] = "mixed"
        E = [k for k, v in affected.items() if v]
        if E:
            V = []
            for k in E:
                V += bytype[k]
            print(f"  V[affected] types: {[(k, len(bytype[k]), affected[k]) for k in E]}", flush=True)
            sim.window |= set(V)
            step += 1
            continue
        # step 3: K image?
        Uv = set()
        for (u, v) in rest:
            Uv.add(u)
            Uv.add(v)
        sg, _, _ = sim.auto(base_classes, sorted(Uv))
        if sim.image_contains_alt(sg):
            print("FULL at step 3 (K onto Alt(T))")
            return
        # step 4
        print("  step4: testing visible orbits per type")
        vis = {}
        for key, plist in sorted(bytype.items()):
            # treat type as union of orbits; test pointwise stabilizer of whole type
            Dv = set()
            for (u, v) in plist:
                Dv.add(u)
                Dv.add(v)
            sg, _, _ = sim.auto(base_classes, sorted(Dv))
            im = sim.phi(sg)
            vis[key] = (len(im) == 1)
        V = []
        names = [k for k, b in vis.items() if b]
        for k in names:
            V += bytype[k]
        print(f"  V[VISIBLE] types: {[(k, len(bytype[k])) for k in names]}; not visible: {[k for k,b in vis.items() if not b]}", flush=True)
        if not V:
            print("no visible orbit")
            return
        sim.window |= set(V)
        step += 1


def lines(m):
    L = set()
    for a in range(1, 1 << m):
        for b in range(a + 1, 1 << m):
            L.add(tuple(sorted((a, b, a ^ b))))
    return sorted(L)


def root(m, kappa, samples):
    P = list(range(1, 1 << m))
    B = lines(m)
    pid = {p: i for i, p in enumerate(P)}
    bid = {b: len(P) + i for i, b in enumerate(B)}
    N = len(P) + len(B)
    adj = {}
    for b in B:
        for p in b:
            adj[(pid[p], bid[b])] = True
            adj[(bid[b], pid[p])] = True
    T = [1 << i for i in range(kappa)]
    Tset = {pid[t] for t in T}
    D = span(T)
    Sigma = 0
    for t in T:
        Sigma ^= t
    Tid = [pid[t] for t in T]
    idxT = {t: i for i, t in enumerate(Tid)}

    def phi(g):
        return tuple(idxT[g[t]] for t in Tid)

    sim = Sim(N, adj, [], [], kappa, phi)

    def ptype(p):
        if pid[p] in Tset:
            return "T"
        if p == Sigma:
            return "S"
        if p in D:
            return "D*"
        return "P1"

    def btype(b):
        s = set(b)
        if s & set(T):
            return "bT"
        o = {x for x in s & D if x != Sigma}
        if o:
            return "bD*"
        if s & D:
            return "bS"
        return "bF"

    vt = {}
    for p in P:
        vt[pid[p]] = ptype(p)
    for b in B:
        vt[bid[b]] = btype(b)

    def posdesc(pos):
        u, v = pos
        return (vt[u], vt[v])

    allpos = [(u, v) for u in range(N) for v in range(N) if u != v]
    base = [sorted(Tset), sorted(set(range(N)) - Tset)]
    print(f"root m={m} n={N} kappa={kappa} k={2**m} |P1|={2**m-2**kappa}", flush=True)
    run_steps(sim, base, allpos, vt, posdesc, samples)


def level1(m, kappa, samples):
    B = lines(m)
    D1 = span([1 << i for i in range(kappa)])
    Sigma0 = (1 << kappa) - 1
    Z1 = {Sigma0}
    Wt = [b for b in B if not (set(b) & (D1 - Z1 - {0}))]
    P1 = [p for p in range(1, 1 << m) if p not in D1]
    wid = {b: i for i, b in enumerate(Wt)}
    pid = {p: len(Wt) + i for i, p in enumerate(P1)}
    N = len(Wt) + len(P1)
    T1 = [1 << (kappa + i) for i in range(kappa)]
    D2 = span([1 << i for i in range(2 * kappa)])
    coset = {}
    for i, t in enumerate(T1):
        for d in D1:
            coset[t ^ d] = i
    Sigma1 = 0
    for t in T1:
        Sigma1 ^= t
    SigmaSet = {Sigma1 ^ d for d in D1}
    adj = {}
    for b in Wt:
        for p in b:
            if p in pid:
                adj[(wid[b], pid[p])] = True
    # translation gadget: for each basis d of D1, arcs p -> p^d colored midpoint
    gadget = []
    extra_classes = []
    idx = 0
    nextra_start = 2 * N
    for i in range(kappa):
        d = 1 << i
        cls = []
        for p in P1:
            mid = nextra_start + idx
            idx += 1
            cls.append(mid)
            gadget.append((pid[p], mid))
            gadget.append((mid, pid[p ^ d]))
        extra_classes.append(cls)
    tcosVerts = {pid[p] for p in coset}

    def phi(g):
        return tuple(coset[P1[g[pid[T1[i]]] - len(Wt)]] for i in range(kappa))

    # careful: gens from nauty are on 2N+extra; g[pid[..]] index in layer0 ok
    sim = Sim(N, adj, gadget, extra_classes, kappa, phi)

    def ptype(p):
        if p in coset:
            return "pTD"
        if p in SigmaSet:
            return "pS"
        if p in D2:
            return "pD*"
        return "P2"

    def btype(b):
        s = set(b)
        o = s & (set(coset))
        if o:
            return "bTD"
        o = {x for x in s & D2 if x not in SigmaSet and x != Sigma0}
        if o:
            return "bD*"
        if s & (SigmaSet | {Sigma0}):
            return "bS"
        return "bF"

    vt = {}
    for b in Wt:
        vt[wid[b]] = btype(b)
    for p in P1:
        vt[pid[p]] = ptype(p)

    def posdesc(pos):
        return (vt[pos[0]], vt[pos[1]])

    allpos = [(wid[b], pid[p]) for b in Wt for p in P1]
    base = [sorted(wid.values()), sorted(tcosVerts), sorted(set(pid.values()) - tcosVerts)]
    print(f"level1 m={m} kappa={kappa} |Wt|={len(Wt)} |P1|={len(P1)} |Omega|={len(allpos)} |D2|={len(D2)}", flush=True)
    run_steps(sim, base, allpos, vt, posdesc, samples)


if __name__ == "__main__":
    mode, m, kappa = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    samples = int(sys.argv[4]) if len(sys.argv) > 4 else 2
    (root if mode == "root" else level1)(m, kappa, samples)
