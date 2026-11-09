#!/usr/bin/env python3
"""Exact checks of Lemma 3.2 (docs/w47-mu.md): codegree values of R in B.
Usage: python lambda_check.py M [M2 ...]"""
import sys
from collections import Counter

def lines_of(m):
    n = 1 << m; L = set()
    for a in range(1, n):
        for b in range(a + 1, n):
            L.add(tuple(sorted((a, b, a ^ b))))
    return sorted(L)

def check(m):
    lines = lines_of(m); ell = (1, 2, 3); es = set(ell)
    W = [l for l in lines if not set(l) & es]
    R = [l for l in lines if len(set(l) & es) == 1]
    Rid = {r: i for i, r in enumerate(R)}
    pts_r = [set(r) for r in R]
    def u_of(r):            # the class in V/ell of the points of r outside ell
        x = next(a for a in r if a not in es)
        return min(x, x ^ 1, x ^ 2, x ^ 3)
    def p_of(r):
        return next(a for a in r if a in es)
    N = [set() for _ in R]
    for wi, w in enumerate(W):
        for ri, r in enumerate(R):
            if pts_r[ri] & set(w):
                N[ri].add(wi)
    cnt = Counter()
    for i in range(len(R)):
        for j in range(i + 1, len(R)):
            same_u = u_of(R[i]) == u_of(R[j])
            same_p = p_of(R[i]) == p_of(R[j])
            cnt[(same_u, same_p, len(N[i] & N[j]))] += 1
    print(f"m={m}: (same_u, same_p, codegree) -> #pairs:")
    for k, v in sorted(cnt.items()):
        print("   ", k, v)
    print(f"   predicted: u equal & p equal -> 0; u equal & p differ -> {2**(m-1)-4}; u differ -> 4")
    # triple check on one fibre: 8 triples with distinct p, 4 concurrent
    by_u = {}
    for i, r in enumerate(R):
        by_u.setdefault(u_of(r), []).append(i)
    tr = Counter()
    for u, ids in by_u.items():
        assert len(ids) == 6
        for i in ids:
            for j in ids:
                for k in ids:
                    if i < j < k and len({p_of(R[i]), p_of(R[j]), p_of(R[k])}) == 3:
                        conc = bool(pts_r[i] & pts_r[j] & pts_r[k])
                        tr[(conc, len(N[i] & N[j] & N[k]))] += 1
    print("   triples with distinct p over a fibre (concurrent, common nbrs) -> count:", dict(tr))
    print(f"   predicted: concurrent -> {2**(m-1)-4}, else 0; {4*(2**(m-2)-1)} concurrent, same number not")

if __name__ == "__main__":
    for a in sys.argv[1:]:
        check(int(a))
