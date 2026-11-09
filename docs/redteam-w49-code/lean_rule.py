#!/usr/bin/env python3
"""Simulate Lean's rectangle-colour rule on the rank scheme of the d-by-e bilinear forms graph.

Lean (read only): Impl/AggRectCertMath.lean, rcCand/rcFind.  The certificate is the first index
t = a*n^2 + b*n + u (a,b,u fiber positions in increasing label order) with
vL = c(x,a), vR = c(x,b), vE = c(u,b), W = {k: c(x,k)=vL}, R = {k: c(x,k)=vR}, passing rcCond.
The source vertex is x = t_0 (first point of the Case-2b source tuple stSrc2b = smallest labels of
Phi, so x is label 0); the Case-2b orbital is the F-orbital of (label 0, label 1).

We run this rule on the rank scheme (the coherent closure of Cay(Phi,R1)), for a labelling in
which label 0 is the zero matrix and label 1 is a pure tensor (i.e. the orbital of (0,1) is R1).
Output: (vL,vR,vE) as rank classes.  Claim to test: the result is (e, 1, e-1) or (e, 1, e),
i.e. B or its bipartite complement, whatever the labelling of the remaining points.
"""
import random, sys
import numpy as np
from common import *

def rank_table(d, e):
    n = 1 << (d*e)
    t = np.zeros(n, dtype=np.int8)
    for M in range(1, n):
        t[M] = rank(M, d, e)
    return t

def simulate(d, e, seed, rk=None):
    random.seed(seed)
    n = 1 << (d*e)
    if rk is None: rk = rank_table(d, e)
    R1 = [int(M) for M in np.nonzero(rk == 1)[0]]
    pts = list(range(1, n))
    first = random.choice(R1)
    pts.remove(first)
    random.shuffle(pts)
    pts = [0, first] + pts          # label -> point
    pts_arr = np.array(pts, dtype=np.int64)
    xp = pts[0]
    cx = rk[pts_arr ^ xp]           # color of (x, label)
    # candidates in lexicographic (a,b,u) order
    for a in range(n):
        vL = int(cx[a])
        if not (3 * n < 4 * int(np.sum(cx == vL))):
            continue
        for b in range(n):
            vR = int(cx[b])
            if vR == vL or vR == int(cx[0]):   # conditions vR != vL, vR != v0 (v0 = c(x,x))
                continue
            for u in range(n):
                if int(cx[u]) != vL:
                    continue
                vE = int(rk[pts[u] ^ pts[b]])
                Wl = pts_arr[cx == vL]; Rl = pts_arr[cx == vR]
                # matrix rows over Wl, columns over Rl: 1 iff rank(w,r)==vE
                Wlocal = Wl
                Bm = (rk[Wlocal[:, None] ^ Rl[None, :]] == vE).astype(np.int8)
                rows = Bm.sum(axis=1); cols = Bm.sum(axis=0)
                ok = rows.min() == rows.max() and cols.min() == cols.max() and cols[0] < Bm.shape[0]
                if ok:
                    # twin bound: at most |W|/2 rows equal to any row
                    _, counts = np.unique(Bm, axis=0, return_counts=True)
                    ok = 2 * counts.max() <= Bm.shape[0]
                ok = ok and (len(Wl) + len(Rl) <= n) and 16 * len(Wl) * len(Rl) <= 3 * n * n
                if ok:
                    return (vL, vR, vE, len(Wl), len(Rl), a, b, u)
    return None

if __name__ == "__main__":
    for (d, e) in [(5, 3), (6, 3), (4, 2), (6, 2), (8, 2)]:
        rk = rank_table(d, e)
        for seed in range(3 if d*e>=18 else 5):
            res = simulate(d, e, seed, rk)
            print(f"(d,e)=({d},{e}) seed {seed}: (vL,vR,vE)={res[:3]} |W|={res[3]} |R|={res[4]} (a,b,u)={res[5:]}", flush=True)
            assert res[0] == e and res[1] == 1 and res[2] in (e-1, e), res
    print("OK: in every run the Lean rule returned W=rank e, R=R1, edge colour rank e-1 or e.")
