#!/usr/bin/env python3
"""2-dimensional WL (coherent closure) on translation-invariant colorings of Phi=F_2^{de}, by
Walsh-Hadamard convolution.  Used to test: (i) closure(Cay(Phi,R1)) is the rank scheme; (ii) what
happens for the OTHER orbitals of F_0=Sp x Sp (choice (a)); (iii) repair R1.

A translation-invariant coloring of Phi^2 is a function c(v)=color of (u,u+v).  One round:
c'(v) = (c(v), [ #{u: c(u)=i, c(u+v)=j} for all color pairs (i,j) ]).  Repeat until stable.
"""
import sys, random
import numpy as np
from common import *

def wht(a):
    n = int(np.log2(len(a))); f = a.astype(np.int64).copy()
    for b in range(n):
        s = 1 << b
        for i in range(0, len(f), 2*s):
            x = f[i:i+s].copy(); y = f[i+s:i+2*s].copy()
            f[i:i+s] = x+y; f[i+s:i+2*s] = x-y
    return f

def refine(c):
    n = len(c)
    while True:
        k = int(c.max()) + 1
        hats = [wht((c == i).astype(np.int64)) for i in range(k)]
        sig = np.zeros((k*k, n), dtype=np.int64)
        for i in range(k):
            for j in range(k):
                sig[i*k+j] = wht(hats[i] * hats[j]) // n
        # combine (old color, signature) into new color ids
        keys = {}
        newc = np.zeros(n, dtype=np.int64)
        for v in range(n):
            t = (int(c[v]),) + tuple(int(x) for x in sig[:, v])
            newc[v] = keys.setdefault(t, len(keys))
        if len(keys) == k:
            return newc
        c = newc

def f0_orbits(d, e):
    """orbits of Sp(V)xSp(U) on F_2^{de} (columns in V), union-find via transvections and row ops."""
    n = 1 << (d*e)
    parent = list(range(n))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]; x = parent[x]
        return x
    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb: parent[max(ra,rb)] = min(ra,rb)
    # Sp(d) transvection for vector v: x -> x + omega(x,v) v, acting on each column of M.
    om_d = omega(d); om_e = omega(e)
    def sym(x, y, om):
        return bin(sum(1 << ((i,j) in om and ((x>>i)&1) & ((y>>j)&1)) for i in range(32) for j in range(32)) ) and 0
    def bil(x, y, k):
        s = 0
        for t in range(k//2):
            s ^= ((x>>(2*t))&1)&((y>>(2*t+1))&1) ^ ((x>>(2*t+1))&1)&((y>>(2*t))&1)
        return s
    def apply_V(M, v):
        # columns c_j (d-bit); c -> c + omega(c,v) v  applied columnwise
        out = M
        for j in range(e):
            c = 0
            for i in range(d):
                if M >> (i*e+j) & 1: c |= 1 << i
            if bil(c, v, d):
                nc = c ^ v
                # write new column j
                for i in range(d):
                    bit = (nc >> i) & 1
                    out = (out & ~(1 << (i*e+j))) | (bit << (i*e+j))
        return out
    def apply_U(M, u):
        # rows r_i (e-bit): transvection on rows
        out = M
        for i in range(d):
            r = (M >> (i*e)) & ((1<<e)-1)
            if bil(r, u, e):
                nr = r ^ u
                out = (out & ~(((1<<e)-1) << (i*e))) | (nr << (i*e))
        return out
    # generators: transvections for all nonzero v (fine for small d,e)
    gens = [('V', v) for v in range(1, 1<<d)] + [('U', u) for u in range(1, 1<<e)]
    for M in range(n):
        for kind, v in gens:
            N = apply_V(M, v) if kind == 'V' else apply_U(M, v)
            union(M, N)
    orb = {}
    for M in range(n):
        orb.setdefault(find(M), []).append(M)
    return sorted(orb.values(), key=len)

def describe(c, n, Q=None, rk=None):
    k = int(c.max())+1
    sizes = np.bincount(c, minlength=k)
    return k, sizes

if __name__ == "__main__":
    mode = sys.argv[1]; d, e = int(sys.argv[2]), int(sys.argv[3])
    n = 1 << (d*e)
    rk = np.array([rank(M, d, e) for M in range(n)], dtype=np.int8)
    if mode == "r1":
        c = np.zeros(n, dtype=np.int64); c[rk == 1] = 1; c[0] = 2
        fin = refine(c)
        k = int(fin.max())+1
        same = all(len(set(rk[fin == i])) == 1 for i in range(k)) and k == e+1
        print(f"closure(Cay(R1)) at ({d},{e}): classes={k}; equals rank scheme: {same}")
    if mode == "orbitals":
        Qt = np.frombuffer(bytes(Q_table(d, e)), dtype=np.uint8)
        orbits = f0_orbits(d, e)
        print(f"F_0 orbits on Phi at ({d},{e}): count={len(orbits)} sizes={[len(o) for o in orbits]}")
        for O in orbits:
            if O == [0]: continue
            c = np.zeros(n, dtype=np.int64); c[np.array(O)] = 1; c[0] = 2
            fin = refine(c)
            k = int(fin.max())+1; sz = np.bincount(fin, minlength=k)
            # does the closure see Q? (Q constant on classes?)
            sees = all(len(set(Qt[fin == i])) == 1 for i in range(k))
            rk_cls = all(len(set(rk[fin == i])) == 1 for i in range(k))
            m0 = O[0]
            frac = sz.max() / n
            print(f"  orbital: rank={int(rk[m0])} Q={int(Qt[m0])} |O|={len(O)} -> closure classes={k} max class frac={frac:.3f} "
                  f"Q-constant-on-classes={sees} rank-constant-on-classes={rk_cls}")
    if mode == "repair":
        Qt = np.frombuffer(bytes(Q_table(d, e)), dtype=np.uint8)
        R1 = (rk == 1)
        H = (Qt == 1)
        # R1 coloring: colors = (in O=R1?, x-value): (1,1)=R1, (0,1)=H, (0,0)=rest
        c = np.zeros(n, dtype=np.int64); c[R1] = 1; c[H] = 2; c[0] = 3
        fin = refine(c); k = int(fin.max())+1; sz = np.bincount(fin, minlength=k)
        print(f"R1 repair at ({d},{e}): classes={k}, max class fraction={sz.max()/n:.4f}, sizes={sorted(sz.tolist())}")
