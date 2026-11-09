#!/usr/bin/env python
"""Exact (no position types, no sampling) replay of HJ LocalCertificate on model states.

Referee check for docs/w18-latin.md Lemma 1/Lemma 2.  Every window is computed from the
automorphism group of a coloured gadget graph (nauty), one representative per orbit of the
current group: no assumption about which positions are alike.  Affected status, Step 3 and the
Step 4 orbit selection are read off the group action on the test labels.

States are (m, flag): flag = list of bases; D_i = span of first i bases.  Z = union of
(sum of basis i + D_{i-1}).  H = {rho on V\\D : rho(v+d)=rho(v)+tau(d), tau unitriangular on flag}.
Group on W_t x P: Sym(W_t) x H.

usage: redteam-w18-latin-check.py state m "flag" "T"   (level model, flag = list of basis lists)
       redteam-w18-latin-check.py root m "T"          (root model, T = points)
       redteam-w18-latin-check.py lsg m "cells" | block m "lines" | paley q "T"
       redteam-w18-latin-check.py a1 | count
"""
import sys, time, itertools
from pynauty import Graph, autgrp

def vec_str(v, m): return format(v, '0%db' % m)

def perm_closure(gens, k):
    idn = tuple(range(k))
    seen = {idn}; fr = [idn]
    while fr:
        nx = []
        for a in fr:
            for g in gens:
                b = tuple(g[x] for x in a)
                if b not in seen:
                    seen.add(b); nx.append(b)
        fr = nx
    return seen

def is_even(p):
    seen = [False]*len(p); s = 1
    for i in range(len(p)):
        if not seen[i]:
            l = 0; j = i
            while not seen[j]:
                seen[j] = True; j = p[j]; l += 1
            if l % 2 == 0: s = -s
    return s == 1

def alt_size(k):
    import math
    return math.factorial(k)//2

def span(vs):
    S = {0}
    for v in vs:
        S |= {s ^ v for s in S}
    return S

class State:
    """Model state: rows = blocks of PG(m-1,2) disjoint from D\\Z, columns P = V\\D."""
    def __init__(self, m, flag, T):
        self.m = m
        self.flag = flag
        self.T = T          # list of coset representatives (independent mod D)
        V = range(1, 2**m)
        D = {0}
        self.levels = []    # (D_{i-1}, D_i)
        Z = set()
        for basis in flag:
            old = set(D)
            for b in basis:
                D = D | {d ^ b for d in D}
            if basis:
                s = 0
                for b in basis: s ^= b
                Z |= {s ^ d for d in old}
            self.levels.append((old, set(D)))
        self.D = D
        self.Z = Z
        self.P = [v for v in V if v not in D]
        self.pidx = {v: i for i, v in enumerate(self.P)}
        bad = D - Z
        blocks = set()
        for a in range(1, 2**m):
            for b in range(a+1, 2**m):
                c = a ^ b
                if c > b:
                    if not ({a, b, c} & bad):
                        blocks.add((a, b, c))
        self.W = sorted(blocks)
        self.nW, self.nP = len(self.W), len(self.P)
        self.inc = [bytearray(self.nP) for _ in range(self.nW)]
        for i, w in enumerate(self.W):
            for p in w:
                if p in self.pidx:
                    self.inc[i][self.pidx[p]] = 1
        self.window = [bytearray(self.nP) for _ in range(self.nW)]
        # Tcosets: coset (frozenset) of each T element
        self.tcosets = [frozenset(t ^ d for d in D) for t in T]
        self.k = len(T)

    def gadget(self):
        """Common gadget vertices; returns (offset info, base adjacency, base colours)."""
        nW, nP, k = self.nW, self.nP, self.k
        idx = {}
        nv = nW + 2*nP + k
        # P layer 0: nW + p; layer 1: nW+nP+p ; T markers: nW+2nP+t
        self.v_t0 = nW + 2*nP
        adj = {i: [] for i in range(nv)}
        for p in range(nP):
            adj[nW+p].append(nW+nP+p)
        for t, cos in enumerate(self.tcosets):
            for v in cos:
                if v in self.pidx:
                    adj[self.v_t0 + t].append(nW + self.pidx[v])
        cols = [set(range(nW)), {nW+p for p in range(nP)}, {nW+nP+p for p in range(nP)},
                {self.v_t0+t for t in range(k)}]
        # H gadget
        if self.D != {0}:
            Dn = sorted(self.D - {0})
            dhat = {}
            for d in Dn:
                dhat[d] = nv; nv += 1; adj[dhat[d]] = []
            # colour D-hat by (level, coset of D_{level-1})
            colD = {}
            for d in Dn:
                for lv, (old, new) in enumerate(self.levels):
                    if d in new and d not in old:
                        key = (lv, min(d ^ o for o in old))
                        colD.setdefault(key, set()).add(dhat[d])
            cols.extend(colD.values())
            # D lines (triples)
            lineset = []
            seen = set()
            for a in Dn:
                for b in Dn:
                    if a < b:
                        c = a ^ b
                        if c in dhat and c > b:
                            key = (a, b, c)
                            if key not in seen:
                                seen.add(key)
                                lv = nv; nv += 1; adj[lv] = []
                                lineset.append(lv)
                                for x in (a, b, c): adj[dhat[x]].append(lv)
            if lineset: cols.append(set(lineset))
            # translation gadget: for each d, unordered pair {v, v+d} with v,v+d in P (always)
            transv = []
            for d in Dn:
                seen2 = set()
                for v in self.P:
                    u = v ^ d
                    if v < u:
                        key = (v, u)
                        if key in seen2: continue
                        seen2.add(key)
                        tv = nv; nv += 1; adj[tv] = []
                        transv.append(tv)
                        adj[tv] += [nW + self.pidx[v], nW + self.pidx[u], dhat[d]]
            if transv: cols.append(set(transv))
        self.nv = nv
        self.base_adj = adj
        self.base_cols = cols

    def auto(self, indiv_rows=(), indiv_cols=()):
        """Group of colored structure with window; returns (rowgens? ) action data."""
        nW, nP = self.nW, self.nP
        adj = {i: list(v) for i, v in self.base_adj.items()}
        # window edges
        for wi in range(nW):
            rowW = self.window[wi]; rowI = self.inc[wi]
            for p in range(nP):
                if rowW[p]:
                    adj[wi].append(nW + p)
                    if rowI[p]:
                        adj[wi].append(nW + nP + p)
        cols = []
        ir = set(indiv_rows); ic = set(indiv_cols)
        for i, c in enumerate(self.base_cols):
            cc = set(c)
            if i == 0:
                cc -= ir
            elif i == 1:
                cc -= {nW+p for p in ic}
            elif i == 2:
                cc -= {nW+nP+p for p in ic}
            if cc: cols.append(cc)
        for r in indiv_rows: cols.append({r})
        for p in indiv_cols:
            cols.append({nW+p}); cols.append({nW+nP+p})
        g = Graph(self.nv, directed=False, adjacency_dict=adj, vertex_coloring=cols)
        return autgrp(g)

    def image_T(self, gens):
        ims = []
        for g in gens:
            ims.append(tuple(g[self.v_t0+t]-self.v_t0 for t in range(self.k)))
        return perm_closure(ims, self.k)

    def phi_is_alt(self, gens):
        im = self.image_T(gens)
        ev = sum(1 for p in im if is_even(p))
        return ev == alt_size(self.k), ev, len(im)

    def pair_orbits(self, res_gens, orbits_full):
        """Orbit representatives of positions under group given by generators & vertex orbits:
        pairs (w,p), via orbit of w and stabilizer orbit of p (nauty)."""
        nW = self.nW
        row_reps = sorted({orbits_full[i] for i in range(nW)})
        reps = []
        for w in row_reps:
            _, _, _, orb_w, _ = self.auto(indiv_rows=[w])
            prep = sorted({orb_w[nW+p] - nW for p in range(self.nP)})
            for p in prep:
                reps.append((w, p))
        return reps

def run_state(m, flag, T, verbose=True):
    t0 = time.time()
    S = State(m, flag, T)
    k = S.k
    S.gadget()
    print(f"state m={m} flag={flag} T={T}: rows={S.nW} cols={S.nP} |D|={len(S.D)} Z={sorted(S.Z)} nv={S.nv}")
    history = []
    for it in range(30):
        gens, m1, e1, orbs, _ = S.auto()
        grpsize = f"{m1:.3f}e{e1}"
        alt_ok, ev, im = S.phi_is_alt(gens)
        print(f"  iter {it}: |window|={sum(sum(r) for r in S.window)} |A(B)|~{grpsize} phi: even={ev} of {alt_size(k)} (im={im}) time={time.time()-t0:.0f}s")
        if not alt_ok:
            print("  ==> NONFULL")
            return S, history
        # affected positions outside window, exact per orbit
        reps = S.pair_orbits(gens, orbs)
        reps = [(w, p) for (w, p) in reps if not S.window[w][p]]
        print(f"    {len(reps)} position-orbit reps outside window")
        # affected orbit reps
        affected = []
        for (w, p) in reps:
            g2, _, _, _, _ = S.auto(indiv_rows=[w], indiv_cols=[p])
            ok, ev2, im2 = S.phi_is_alt(g2)
            if not ok:
                affected.append((w, p, ev2))
        if affected:
            # expand each affected orbit: orbit of (w,p) under group: all (w',p') with
            # (w',p') in same orbit.  Enumerate images via BFS over generators.
            V = [bytearray(S.nP) for _ in range(S.nW)]
            nW = S.nW; nP = S.nP
            for (w, p, ev2) in affected:
                if V[w][p]: continue
                front = [(w, p)]; V[w][p] = 1
                while front:
                    nxt = []
                    for (a, b) in front:
                        for g in gens:
                            a2 = g[a]; b2 = g[nW+b] - nW
                            if not V[a2][b2]:
                                V[a2][b2] = 1; nxt.append((a2, b2))
                    front = nxt
            history.append(('affected', V))
            nv_ = 0; rows=set(); cols=set()
            for w in range(nW):
                for p in range(nP):
                    if V[w][p]:
                        S.window[w][p] = 1; nv_ += 1; rows.add(w); cols.add(p)
            print(f"    V_{len(history)-1}: {nv_} positions added (affected, {len(affected)} reps); rows touched {len(rows)}, cols touched {len(cols)}")
            continue
        # Step 3/4
        Uset = [(w, p) for w in range(S.nW) for p in range(S.nP) if not S.window[w][p]]
        urows = sorted({a for a, b in Uset}); ucols = sorted({b for a, b in Uset})
        print(f"    no affected; |U|={len(Uset)} rows {len(urows)} cols {len(ucols)}")
        if len(Uset) == 0:
            print("  ==> window exhausted"); return S, history
        g3, _, _, _, _ = S.auto(indiv_rows=urows, indiv_cols=ucols)
        ok, ev3, im3 = S.phi_is_alt(g3)
        print(f"    K=A_(U): phi even={ev3} ==> {'FULL' if ok else 'not full'}")
        if ok:
            print("  ==> FULL certificate"); return S, history
        # visible orbits in U
        Uorbs = []
        seen = [bytearray(S.nP) for _ in range(S.nW)]
        nW = S.nW
        for (w, p) in reps:
            if seen[w][p]: continue
            orb = [(w, p)]; seen[w][p] = 1; front = [(w, p)]
            while front:
                nxt = []
                for (a, b) in front:
                    for g in gens:
                        a2 = g[a]; b2 = g[nW+b]-nW
                        if not seen[a2][b2]:
                            seen[a2][b2] = 1; nxt.append((a2, b2)); orb.append((a2, b2))
                front = nxt
            Uorbs.append(orb)
        vis = [bytearray(S.nP) for _ in range(S.nW)]
        sel = []
        for orb in Uorbs:
            rs = sorted({a for a, b in orb}); cs = sorted({b for a, b in orb})
            g4, _, _, _, _ = S.auto(indiv_rows=rs, indiv_cols=cs)
            im4 = S.image_T(g4)
            ev4 = sum(1 for p in im4 if is_even(p))
            print(f"    orbit size {len(orb)} rows {len(rs)} cols {len(cs)}: phi(pointwise stab) even={ev4}")
            if ev4 == 1:
                sel.append(orb)
                for a, b in orb: vis[a][b] = 1
        print(f"    Step 4 VISIBLE orbits: {len(sel)} total positions {sum(sum(r) for r in vis)}")
        history.append(('visible', vis))
        # Report the structure of selected orbit vs prediction
        for orb in sel:
            rs = {a for a, b in orb}; cs = {b for a, b in orb}
            cosets_T = set().union(*S.tcosets)
            print(f"      selected: rows={len(rs)} cols={len(cs)} product?={len(rs)*len(cs)==len(orb)}")
        for w in range(S.nW):
            for p in range(S.nP):
                if vis[w][p]: S.window[w][p] = 1
        print("  ==> reached Step 4; stopping (recursion would run on selected orbit under kernel)")
        return S, history
    return S, history

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'state':
        m = int(sys.argv[2])
        flag = eval(sys.argv[3])
        T = eval(sys.argv[4])
        run_state(m, flag, T)


# ---------------------------------------------------------------------------
# Root model: Sym(n) acting on ordered pairs of vertices of the incidence graph.
# ---------------------------------------------------------------------------
class Root:
    def __init__(self, m, T):
        self.m = m
        pts = list(range(1, 2**m))
        self.nP = len(pts)
        lines = sorted({tuple(sorted((a, b, a ^ b))) for a in pts for b in pts if a < b})
        self.lines = lines
        n = self.nP + len(lines)
        self.n = n
        self.pidx = {p: p-1 for p in pts}
        self.lidx = {l: self.nP + i for i, l in enumerate(lines)}
        self.adj = [set() for _ in range(n)]
        for i, l in enumerate(lines):
            for p in l:
                self.adj[self.pidx[p]].add(self.nP+i); self.adj[self.nP+i].add(self.pidx[p])
        self.T = [self.pidx[t] for t in T]
        self.k = len(T)
        self.win = [bytearray(n) for _ in range(n)]  # 1 = in window; diagonal ignored

    def auto(self, indiv=()):
        n = self.n
        a = {i: [] for i in range(2*n)}
        for v in range(n): a[v].append(n+v)
        for x in range(n):
            wx = self.win[x]
            for y in range(n):
                if x != y and wx[y]:
                    a[x].append(y)
                    if y in self.adj[x]:
                        a[n+x].append(n+y)
        tset = set(self.T); iset = set(indiv)
        cols = []
        rest0 = set(range(n)) - tset - iset
        if rest0:
            cols.append(rest0); cols.append({n+v for v in rest0})
        if tset - iset:
            cols.append(set(tset - iset)); cols.append({n+v for v in tset-iset})
        for v in indiv:
            cols.append({v}); cols.append({n+v})
        g = Graph(2*n, directed=False, adjacency_dict=a, vertex_coloring=cols)
        return autgrp(g)

    def image_T(self, gens):
        ims = []
        Tpos = {t: i for i, t in enumerate(self.T)}
        for g in gens:
            ims.append(tuple(Tpos[g[t]] for t in self.T))
        return perm_closure(ims, self.k)

    def phi_ok(self, gens):
        im = self.image_T(gens)
        ev = sum(1 for p in im if is_even(p))
        return ev == alt_size(self.k), ev

def run_root(m, T):
    t0 = time.time()
    R = Root(m, T)
    n = R.n; k = R.k
    print(f"root m={m} n={n} T={T}", flush=True)
    for it in range(40):
        gens, m1, e1, orbs, _ = R.auto()
        ok, ev = R.phi_ok(gens)
        wn = sum(sum(1 for y in range(n) if y != x and R.win[x][y]) for x in range(n))
        print(f" iter {it}: |W|={wn} |B|~{m1:.3f}e{e1} phi even={ev}/{alt_size(k)} t={time.time()-t0:.0f}s", flush=True)
        if not ok:
            print(" NONFULL"); return
        # orbit reps on off-diagonal pairs outside window
        vreps = sorted({orbs[i] for i in range(n)})
        reps = []
        for a in vreps:
            g2, _, _, o2, _ = R.auto(indiv=[a])
            for b in sorted({o2[y] for y in range(n) if y != a}):
                if not R.win[a][b]:
                    reps.append((a, b))
        # expansion of orbit from rep via generators
        def expand(a, b, S):
            st = [(a, b)]; S.add((a, b))
            while st:
                nx = []
                for (x, y) in st:
                    for g in gens:
                        q = (g[x], g[y])
                        if q not in S:
                            S.add(q); nx.append(q)
                st = nx
        affected = []
        for (a, b) in reps:
            g2, _, _, _, _ = R.auto(indiv=[a, b])
            ok2, ev2 = R.phi_ok(g2)
            if not ok2:
                affected.append((a, b))
        print(f"   reps {len(reps)} affected {len(affected)}", flush=True)
        if affected:
            S = set()
            for (a, b) in affected:
                if (a, b) in S: continue
                expand(a, b, S)
            for (x, y) in S:
                R.win[x][y] = 1
            # classify vertices touched by this window
            pts = sorted({v for pair in S for v in pair if v < R.nP})
            lns = sorted({v for pair in S for v in pair if v >= R.nP})
            print(f"   V added: {len(S)} pairs (points touched {len(pts)}, lines touched {len(lns)})", flush=True)
            continue
        # Step 3/4
        U = [(x, y) for x in range(n) for y in range(n) if x != y and not R.win[x][y]]
        Uv = sorted({v for pair in U for v in pair})
        print(f"   no affected. |U|={len(U)} vertices in U: {len(Uv)}", flush=True)
        if not U:
            print(" window exhausted"); return
        g3, _, _, _, _ = R.auto(indiv=Uv)
        ok3, ev3 = R.phi_ok(g3)
        print(f"   K=A_(U): phi even={ev3} -> {'FULL' if ok3 else 'not full'}", flush=True)
        if ok3:
            print(" FULL"); return
        # orbits on U and visibility
        seen = set(); orbits = []
        for (a, b) in reps:
            if (a, b) in seen: continue
            S = set(); expand(a, b, S)
            seen |= S; orbits.append(S)
        for S in orbits:
            vs = sorted({v for pair in S for v in pair})
            g4, _, _, _, _ = R.auto(indiv=vs)
            im = R.image_T(g4)
            ev4 = sum(1 for p in im if is_even(p))
            print(f"   orbit size {len(S)} vertices {len(vs)} (points {sum(1 for v in vs if v<R.nP)}, lines {sum(1 for v in vs if v>=R.nP)}): phi(pointwise) even={ev4} {'VISIBLE' if ev4==1 else ''}", flush=True)
        print(" reached Step 4", flush=True)
        return


class RootG(Root):
    """Root model on an arbitrary graph, given adjacency sets and test vertices."""
    def __init__(self, adjsets, T):
        self.n = len(adjsets)
        self.adj = adjsets
        self.nP = self.n  # classification unused
        self.T = list(T)
        self.k = len(T)
        self.win = [bytearray(self.n) for _ in range(self.n)]

def lsg(m):
    N = 2**m; n = N*N
    adj = [set() for _ in range(n)]
    for a in range(N):
        for b in range(N):
            u = a*N + b
            for a2 in range(N):
                for b2 in range(N):
                    v = a2*N + b2
                    if u != v and (a == a2 or b == b2 or (a ^ b) == (a2 ^ b2)):
                        adj[u].add(v)
    return adj

def block_graph(m):
    pts = list(range(1, 2**m))
    lines = sorted({tuple(sorted((a, b, a ^ b))) for a in pts for b in pts if a < b})
    n = len(lines)
    adj = [set() for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i != j and set(lines[i]) & set(lines[j]):
                adj[i].add(j)
    return adj, lines

def paley(q):
    qr = {(x*x) % q for x in range(1, q)}
    adj = [set((i + r) % q for r in qr) for i in range(q)]
    return adj

def run_rootg(R, label):
    t0 = time.time(); n = R.n; k = R.k
    print(f"rootG {label} n={n} T={R.T}", flush=True)
    for it in range(40):
        gens, m1, e1, orbs, _ = R.auto()
        ok, ev = R.phi_ok(gens)
        wn = sum(sum(1 for y in range(n) if y != x and R.win[x][y]) for x in range(n))
        print(f" iter {it}: |W|={wn} |B|~{m1:.2f}e{e1} phi even={ev}/{alt_size(k)} t={time.time()-t0:.0f}s", flush=True)
        if not ok:
            print(" NONFULL", flush=True); return 'nonfull', it
        vreps = sorted({orbs[i] for i in range(n)})
        reps = []
        for a in vreps:
            g2, _, _, o2, _ = R.auto(indiv=[a])
            for b in sorted({o2[y] for y in range(n) if y != a}):
                if not R.win[a][b]:
                    reps.append((a, b))
        def expand(a, b, S):
            st = [(a, b)]; S.add((a, b))
            while st:
                nx = []
                for (x, y) in st:
                    for g in gens:
                        q = (g[x], g[y])
                        if q not in S: S.add(q); nx.append(q)
                st = nx
        affected = [r for r in reps if not R.phi_ok(R.auto(indiv=list(r))[0])[0]]
        print(f"   reps {len(reps)} affected {len(affected)}", flush=True)
        if affected:
            S = set()
            for (a, b) in affected:
                if (a, b) not in S: expand(a, b, S)
            for (x, y) in S: R.win[x][y] = 1
            print(f"   V added {len(S)} pairs", flush=True)
            continue
        U = [(x, y) for x in range(n) for y in range(n) if x != y and not R.win[x][y]]
        if not U:
            print(" window exhausted (full?)", flush=True); return 'exhausted', it
        Uv = sorted({v for p in U for v in p})
        ok3, ev3 = R.phi_ok(R.auto(indiv=Uv)[0])
        print(f"   |U|={len(U)} K=A_(U) phi even={ev3} {'FULL' if ok3 else 'not full'}", flush=True)
        if ok3:
            return 'full', it
        seen = set(); orbits = []
        for (a, b) in reps:
            if (a, b) in seen: continue
            S = set(); expand(a, b, S); seen |= S; orbits.append(S)
        vis = 0
        for S in orbits:
            vs = sorted({v for p in S for v in p})
            im = R.image_T(R.auto(indiv=vs)[0])
            ev4 = sum(1 for p in im if is_even(p))
            if ev4 == 1:
                vis += 1
                print(f"   VISIBLE orbit size {len(S)} on {len(vs)} vertices", flush=True)
        print(f" Step 4 reached, {vis} visible orbits of {len(orbits)}", flush=True)
        return 'step4', it

if __name__ == '__main__':
    if sys.argv[1] == 'root':
        run_root(int(sys.argv[2]), eval(sys.argv[3]))
    if sys.argv[1] == 'lsg':
        m = int(sys.argv[2]); T = eval(sys.argv[3])  # list of (a,b)
        N = 2**m
        R = RootG(lsg(m), [a*N+b for a, b in T])
        print(run_rootg(R, f"LSG(Z2^{m})"))
    if sys.argv[1] == 'block':
        m = int(sys.argv[2]); idx = eval(sys.argv[3])  # list of (a,b,c) lines
        adj, lines = block_graph(m)
        li = {tuple(sorted(l)): i for i, l in enumerate(lines)}
        R = RootG(adj, [li[tuple(sorted(l))] for l in idx])
        print(run_rootg(R, f"blockgraph m={m}"))
    if sys.argv[1] == 'paley':
        q = int(sys.argv[2]); T = eval(sys.argv[3])
        R = RootG(paley(q), T)
        print(run_rootg(R, f"Paley({q})"))


if __name__ == '__main__' and sys.argv[1] == 'count':
    exec(r'''from math import comb, log2, lgamma, log
def bound_log2(m,kappa,c):
    J=(m-c)//kappa
    if J<=0: return J,0.0
    s=0.0
    for j in range(J):
        q=2**(m-j*kappa)-1
        c_=comb(q,kappa)
        s+=log2(c_)-1
    return J,s
# effective enumeration cutoff under Lean params: q! <= q^(b*floor(log2 q)), b=floor(36000*ln2)
b=int(36000*log(2))
def small(q):
    return lgamma(q+1) <= (b*int(log2(q)))*log(q)
# find largest q with small(q) monotone? scan
lo=2064
while small(lo*2): lo*=2
hi=lo*2
while hi-lo>1:
    mid=(lo+hi)//2
    if small(mid): lo=mid
    else: hi=mid
q1=lo
print("b=",b,"effective cutoff q1 (largest q accepted by SmallZ, scan)=",q1,"log2=",log2(q1))
# verify non-monotone near powers of two: check small(q) for q just above powers of 2
bad=[]
for e in range(11,24):
    for q in (2**e-1,2**e,2**e+1):
        if small(q): bad.append((e,q))
print("powers-of-two samples accepted:",bad)
for kappa in (5,64):
  for c in (kappa+3+11, kappa+3+19):
    print("kappa",kappa,"c",c)
    for m in (c+kappa, c+2*kappa, 200, 300, 500, 1000, 2000, 4000):
        if m<c+kappa: continue
        J,s=bound_log2(m,kappa,c)
        n=2**m
        logn=2*m-log2(6)
        print(f"  m={m} J={J} log2(bound)={s:.1f} m^2/2={m*m/2:.0f} ratio={s/(m*m/2):.4f}  (1/8)log2(n)^2={logn**2/8:.1f}  implied O(1)~{(logn**2/8-s)/logn:.2f}")
''')
if __name__ == '__main__' and sys.argv[1] == 'a1':
    exec(r'''"""Bidirectional collision for quasigroup isomorphism: small correctness + chain-length test."""
import random, sys, math
def close(table, gens):
    S=list(gens); seen=set(gens); i=0
    # naive closure with canonical order
    changed=True
    while changed:
        changed=False
        for a in list(S):
            for b in list(S):
                c=table[a][b]
                if c not in seen:
                    seen.add(c); S.append(c); changed=True
    return S
def canon(table, gens):
    """Canonical labelled table given ordered tuple: BFS order."""
    n=len(table); order=[]; seen={}
    for g in gens:
        if g not in seen: seen[g]=len(order); order.append(g)
    i=0
    while i<len(order):
        for a in order[:i+1]:
            for x,y in ((a,order[i]),(order[i],a)):
                c=table[x][y]
                if c not in seen:
                    seen[c]=len(order); order.append(c)
        i+=1
    if len(order)!=n: return None
    return tuple(gens.index(x) if x in gens else -1 for x in gens) and tuple(seen[table[x][y]] for x in order for y in order)
def chains(table, d):
    n=len(table)
    res=[]
    def rec(ch, cl):
        if len(ch)==d: res.append(tuple(ch)); return
        for x in range(n):
            if x not in cl:
                rec(ch+[x], set(close(table, ch+[x])))
    rec([], set())
    return res
def extend_greedy(table, ch):
    tup=list(ch); cl=set(close(table,tup)); n=len(table)
    while len(cl)<n:
        x=min(v for v in range(n) if v not in cl)
        tup.append(x); cl=set(close(table,tup))
    return tuple(tup)
def tails(table, ch):
    n=len(table); out=[]
    def rec(t, cl):
        if len(cl)==n: out.append(tuple(t)); return
        for x in range(n):
            if x not in cl:
                rec(t+[x], set(close(table,t+[x])))
    rec(list(ch), set(close(table,list(ch))))
    return out
def iso_test(A,B):
    n=len(A); d=math.ceil(0.5*(math.log2(n)+1))
    # check small rank by generation
    # Miller branch: A generated by <=d elements?
    import itertools
    gen=None
    for r in range(1,d+1):
        for tup in itertools.product(range(n),repeat=r):
            if len(close(A,list(tup)))==n: gen=list(tup); break
        if gen: break
    if gen is not None:
        target=canon(A,gen)
        for tup2 in itertools.product(range(n),repeat=len(gen)):
            if canon(B,list(tup2))==target: return True
        return False
    alice=chains(A,d)
    # Bob: fix one greedy chain of length d in B
    tup=[]; cl=set()
    while len(tup)<d:
        c=[x for x in range(n) if x not in cl]
        if not c: return False
        tup.append(c[0]); cl=set(close(B,tup))
    bob=set(canon(B,t) for t in tails(B,tup))
    for ch in alice:
        t=extend_greedy(A,ch)
        if canon(A,t) in bob: return True
    return False
def relabel(T,p):
    n=len(T); q=[[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            q[p[i]][p[j]]=p[T[i][j]]
    return q
def steiner(m):
    pts=list(range(1,2**m)); idx={p:i for i,p in enumerate(pts)}
    n=len(pts); t=[[0]*n for _ in range(n)]
    for a in pts:
        for b in pts:
            t[idx[a]][idx[b]]=idx[a] if a==b else idx[a^b]
    return t
def isGroupCase(t):
    pass
def randls(n):
    # random Latin square by hill climbing (simple Jacobson-Matthews not needed: small n)
    while True:
        L=[[None]*n for _ in range(n)]
        ok=True
        for i in range(n):
            perm=list(range(n)); 
            for attempt in range(2000):
                random.shuffle(perm)
                if all(perm[j] not in [L[r][j] for r in range(i)] for j in range(n)):
                    L[i]=perm[:]; break
            else:
                ok=False;break
        if ok: return L
random.seed(3)
# Steiner quasigroup of PG(3,2): order 15; rank m=4 >= d? 
S=steiner(4); n=15
perm=list(range(n)); random.shuffle(perm); S2=relabel(S,perm)
print("steiner15 self-iso via bidirectional:", iso_test(S,S2))
# non-isomorphic: modify by a random intercalate? use 2 random Latin squares
for sz in (8,):
    L1=randls(sz); L2=randls(sz); p=list(range(sz)); random.shuffle(p)
    print(f"random LS {sz}: iso(self relabel)=", iso_test(L1,relabel(L1,p)), " iso(two random)=", iso_test(L1,L2))
# chain length bound: longest strictly increasing chain in Steiner(4)
best=0
for tup in chains(S,3):
    cl=close(S,list(tup))
    best=max(best, len(extend_greedy(S,tup)))
print("max greedy-extended chain length at d=3, steiner15:", best, "bound floor(log2 n)+1 =", math.floor(math.log2(15))+1)
''')


def predict(m, flag, T):
    """Lemma 1 window sizes computed from its formulas, for comparison with the replay."""
    S = State(m, flag, T)
    D = S.D; Z = S.Z
    Tplus = set().union(*[set(c) for c in S.tcosets])
    newD = set(D)
    for t in T:
        newD |= {d ^ t for d in newD}
    sumT = 0
    for t in T: sumT ^= t
    Sigma = {sumT ^ d for d in D}
    Dstar = newD - D - Tplus - Sigma
    Pj = set(S.P)
    Pnext = {v for v in range(1, 2**m) if v not in newD}
    W = S.W
    W1 = [w for w in W if set(w) & Tplus]
    Wempty = [w for w in W if not (set(w) & Tplus)]
    W2 = [w for w in Wempty if set(w) & Dstar]
    Wt = [w for w in Wempty if not (set(w) & Dstar)]
    # lines inside D* with stabilizer image still all of Alt(T) (kappa=3 artifact)
    def idx(v):
        # index set of v modulo D, by solving over T
        for r in range(1, 2**len(T)):
            x = 0
            for i, t in enumerate(T):
                if r >> i & 1: x ^= t
            if (v ^ x) in D:
                return frozenset(i for i in range(len(T)) if r >> i & 1)
    art = [w for w in W2 if set(w) <= Dstar and
           {idx(p) for p in w} == {frozenset(c) for c in itertools.combinations(range(len(T)), 2)}]
    print(f"predict m={m} flag={flag} T={T}: rows={len(W)} cols={len(Pj)}")
    print(f"  V0 = {len(W)}*{len(Tplus)} = {len(W)*len(Tplus)}")
    print(f"  V1 = {len(W1)}*{len(Pj-Tplus)} = {len(W1)*len(Pj-Tplus)}")
    print(f"  V2 = {len(Wempty)}*{len(Dstar)} = {len(Wempty)*len(Dstar)}")
    print(f"  V3 = {len(W2)}*{len(Pnext)+len(Sigma)} = {len(W2)*(len(Pnext)+len(Sigma))}")
    print(f"  Delta = {len(Wt)}*{len(Pnext)} = {len(Wt)*len(Pnext)};  Wt x Sigma = {len(Wt)*len(Sigma)}")
    print(f"  kappa=3 artifact lines (inside D*, index sets all pairs): {len(art)} {art[:3]}")

if __name__ == '__main__' and sys.argv[1] == 'predict':
    predict(int(sys.argv[2]), eval(sys.argv[3]), eval(sys.argv[4]))
