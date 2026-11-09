"""Exact p and P at n = 625, 6561 using W = V(x)V + I(x)J - J(x)I as a fast matvec.

This uses only the matrix identity defining W (never Lemma 4.1).  Exact p/P for one pair costs one
matvec per a in V, about 2-3 s at n=6561.  Stage 1 estimates over all (0,y) with S random tests.
Vertex-transitivity (pairs (0,y) suffice) follows from Aut(W) >= Aut(V) x Aut(V).
p  : memo sec 3.1 (T-only, degenerate (a,b) count as non-tests, /n^2)
pc : what docs/w32-code computes: Pr[T equal | a != b, a,b not in {x,y}]
P  : memo sec 4.2 (collision: distinct, T equal, both signs equal, /n^2)
"""
import sys, time
sys.path.insert(0, '.')
from rt_common import *

def matvec(V, v, g):
    """(W g) where g has shape (n,) or (n, m); returns same shape as g"""
    H = g.reshape(v, v).astype(np.float64)
    out = V @ H @ V + H.sum(axis=1, keepdims=True) - H.sum(axis=0, keepdims=True)
    return out

def exact_pair(Wmat, V, v, x, y):
    n = v * v
    Cx = Wmat[x].astype(np.int8); Cy = Wmat[y].astype(np.int8)
    dif = (Cx.astype(np.int64) - Cy.astype(np.int64)).astype(np.float64)
    Vf = V.astype(np.float64)
    agree = Cx == Cy                    # a with C_a(x) = C_a(y), i.e. entry x and y of row a agree; C symmetric
    tests = 0; coll = 0; eq_nd = 0; tot_nd = 0
    bx = np.ones(n, dtype=bool); bx[x] = bx[y] = False
    for a in range(n):
        if a == x or a == y: continue
        h = Wmat[a].astype(np.float64) * dif
        D = matvec(Vf, v, h).reshape(n)
        D = np.rint(D).astype(np.int64)
        allowed = bx.copy(); allowed[a] = False
        zero = (D == 0) & allowed
        tests += int(((D != 0) & allowed).sum())
        eq_nd += int(zero.sum()); tot_nd += int(allowed.sum())
        if agree[a]:
            coll += int((zero & agree).sum())
    return (n * n - tests, coll, eq_nd, tot_nd)

def stage1(Wmat, V, v, S, seed):
    rng = np.random.default_rng(seed)
    n = v * v; Vf = V.astype(np.float64)
    eq = np.zeros(n, dtype=np.int64); coll = np.zeros(n, dtype=np.int64); tot = np.zeros(n, dtype=np.int64)
    C0 = Wmat[0].astype(np.int64)
    for s in range(S):
        a, b = rng.integers(1, n, size=2)
        if a == b: continue
        g = (Wmat[a].astype(np.int64) * Wmat[b]).astype(np.float64)
        T = np.rint(matvec(Vf, v, g).reshape(n)).astype(np.int64)
        ok = np.ones(n, dtype=bool); ok[a] = ok[b] = ok[0] = False
        tot[ok] += 1
        same = (T == T[0]) & ok
        eq += same
        # sign conditions on (a,b) for pair (0,y)
        sa = (Wmat[a].astype(np.int64) == Wmat[a, 0]) & (Wmat[b].astype(np.int64) == Wmat[b, 0])
        coll += same & sa
    return eq, coll, tot

