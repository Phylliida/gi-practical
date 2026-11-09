#!/usr/bin/env python3
"""Exact checks for docs/w47-mu.md section 3: the rectangle of PG(m-1,2).

Usage: python rect_check.py M [M2 ...]   (needs pynauty, sympy)

For V = F_2^m, lines = 2-dim subspaces (triples {a,b,a^b}), ell = {1,2,3}:
W = lines skew to ell, R = lines meeting ell in one point, B = (W, R, meet).
Checks: |W|, |R|; Aut(B) order = |GL(V)_ell|; action on W faithful, unique
nontrivial block system (fibres of w |-> image in V/ell, size 16), block
action primitive of the order of GL(m-2,2).
"""
import sys, itertools, math, functools
import pynauty
from sympy.combinatorics import Permutation, PermutationGroup

def lines_of(m):
    n = 1 << m
    L = set()
    for a in range(1, n):
        for b in range(a + 1, n):
            L.add(tuple(sorted((a, b, a ^ b))))
    return sorted(L)

def gl_order(k):
    r = 1
    for i in range(k):
        r *= (2**k - 2**i)
    return r

def line_count(m):
    return (2**m - 1) * (2**(m - 1) - 1) // 3

def check(m):
    lines = lines_of(m)
    assert len(lines) == line_count(m)
    ell = (1, 2, 3)
    ellset = set(ell)
    W, R = [], []
    for l in lines:
        c = len(set(l) & ellset)
        if c == 0:
            W.append(l)
        elif c == 1:
            R.append(l)
        else:
            assert l == ell
    assert len(W) == (2**m - 4) * (2**m - 8) // 6
    assert len(R) == 3 * (2**(m - 1) - 2)
    nW, nR = len(W), len(R)
    idx_R = {r: i for i, r in enumerate(R)}
    # adjacency: w ~ r iff meet.  Build via points.
    through = {}
    for i, r in enumerate(R):
        for p in r:
            through.setdefault(p, []).append(i)
    adj = {i: [] for i in range(nW + nR)}
    for i, w in enumerate(W):
        s = set()
        for p in w:
            s.update(through.get(p, []))
        for j in s:
            adj[i].append(nW + j)
            adj[nW + j].append(i)
    g = pynauty.Graph(nW + nR, directed=False, adjacency_dict=adj,
                      vertex_coloring=[set(range(nW)), set(range(nW, nW + nR))])
    gens, m1, m2, _, _ = pynauty.autgrp(g)
    aut = int(round(m1 * 10**m2))
    expect = gl_order(m) // line_count(m)  # |GL(V)_ell|
    print(f"m={m}: |W|={nW} |R|={nR} |Aut(B)|={aut} (float) expect |GL_ell|={expect}"
          f" ratio={aut/expect:.6f}")
    if m > 7:
        return
    # exact order via sympy on W-part
    Wgens = [Permutation(g_[:nW]) for g_ in gens]
    A = PermutationGroup(Wgens)
    oA = A.order()
    print(f"   |A on W| = {oA}  faithful on W: {oA == expect} (exact {expect})")
    if m > 6:
        return
    # block system: fibres of the map w |-> w + ell (image in V/ell)
    def cls(l):
        s = set()
        for x in l:
            # coset of x mod ell = {x, x^1, x^2, x^3}
            s.add(min(x, x ^ 1, x ^ 2, x ^ 3))
        return tuple(sorted(s))
    fib = {}
    for i, w in enumerate(W):
        fib.setdefault(cls(w), []).append(i)
    assert all(len(v) == 16 for v in fib.values())
    print(f"   fibres (V/ell-lines): {len(fib)}, size {set(len(v) for v in fib.values())}")
    # uniqueness of nontrivial block system containing point 0
    # minimal_block([0,b]) for all b
    blocks = {}
    for b in range(1, nW):
        mb = A.minimal_block([0, b])
        k = tuple(sorted(set(mb)))
        # minimal_block returns a block labelling for the whole domain: reduce to the block of 0
        lab = mb[0]
        B0 = tuple(sorted(i for i, x in enumerate(mb) if x == lab))
        blocks[B0] = blocks.get(B0, 0) + 1
    print(f"   minimal blocks containing point 0: sizes "
          f"{sorted(len(k) for k in blocks)} (counts {sorted(blocks.values())})")
    B0 = sorted(fib[cls(W[0])])
    # action on fibres
    keys = sorted(fib)
    pos = {k: i for i, k in enumerate(keys)}
    idx = {w: i for i, w in enumerate(W)}
    genP = []
    for g_ in Wgens:
        p = [None] * len(keys)
        for k, v in fib.items():
            w0 = v[0]
            im = g_(w0)
            p[pos[k]] = pos[cls(W[im])]
        genP.append(Permutation(p))
    P = PermutationGroup(genP)
    print(f"   P on fibres: degree {P.degree}, order {P.order()}, "
          f"primitive {P.is_primitive()}, expect |GL({m-2},2)|={gl_order(m-2)}")

if __name__ == "__main__":
    for arg in sys.argv[1:]:
        check(int(arg))
