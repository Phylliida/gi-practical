#!/usr/bin/env python3
"""Sanity check of Theorem B (flag+bidirectional collision) for AGL(k,2), k=3,4.

Enumerates AGL(k,2), verifies the exact factorization G = S1 * B * S2 with S1 reps of
G/H (H = stabilizer of W0 = <e1..em>, plus translations), B = unitriangular + translations
(a 2-group fixing the standard flag), S2 = reps of B\\H, and checks that the collision
test  canon_B(f o s) == canon_B(g o t^{-1})  (s in S1, t in S2) decides f ~ g correctly on
random pairs, against brute force over all of AGL(k,2).  canon_B is lexmin over B.
Run: python3 -I bidirectional_check.py
"""
import itertools, random, sys
sys.setrecursionlimit(10000)

def rank(cols, k):
    cols = list(cols); r = 0
    for b in range(k):
        p = None
        for i in range(r, len(cols)):
            if cols[i] >> b & 1:
                p = i; break
        if p is None: continue
        cols[r], cols[p] = cols[p], cols[r]
        for i in range(len(cols)):
            if i != r and cols[i] >> b & 1:
                cols[i] ^= cols[r]
        r += 1
    return r

def gl(k):
    for cols in itertools.product(range(1, 1 << k), repeat=k):
        if rank(cols, k) == k:
            yield cols

def apply(cols, x):
    r = 0
    i = 0
    while x:
        if x & 1: r ^= cols[i]
        x >>= 1; i += 1
    return r

def compose(a, b):  # a o b, matrices as column tuples
    return tuple(apply(a, c) for c in b)

def mat_inv(a, k):
    # Gauss via lookup in GL by simple search of images: solve a x = e_j
    n = 1 << k
    table = {}
    for x in range(n):
        table[apply(a, x)] = x
    return tuple(table[1 << j] for j in range(k))

class Aff:
    __slots__ = ("m", "t", "k")
    def __init__(self, m, t, k): self.m, self.t, self.k = m, t, k
    def __call__(self, x): return apply(self.m, x) ^ self.t
    def compose(self, other):  # self o other
        return Aff(compose(self.m, other.m), apply(self.m, other.t) ^ self.t, self.k)
    def inv(self):
        mi = mat_inv(self.m, self.k)
        return Aff(mi, apply(mi, self.t), self.k)
    def key(self): return (self.m, self.t)

def span(vs):
    s = {0}
    for v in vs:
        s |= {x ^ v for x in s}
    return frozenset(s)

def flag_of(mat, k):
    return tuple(span(mat[:i]) for i in range(1, k + 1))

def setup(k):
    m = k // 2
    GL = list(gl(k))
    n = 1 << k
    I = tuple(1 << i for i in range(k))
    U = [c for c in GL if all(((c[j] >> i) & 1) == (1 if i == j else 0) for j in range(k) for i in range(j, k))]
    # U: unitriangular with c[j] having bits i<j free ... choose lower/upper consistent:
    # columns c[j] = e_j + span(e_0..e_{j-1}) -> preserves flag span(e0..ej).
    U = [c for c in GL if all(((c[j] >> j) & 1) == 1 and (c[j] >> (j + 1)) == 0 for j in range(k))]
    assert len(U) == 2 ** (k * (k - 1) // 2)
    W0 = span(I[:m])
    H0 = [c for c in GL if span(c[:m]) == W0]
    B = [Aff(c, t, k) for c in U for t in range(n)]
    # S1: reps of GL/H0 (left cosets sH <-> s(W0)), with t=0; translations lie in B
    S1 = {}
    for c in GL:
        key = span(c[:m])
        if key not in S1:
            S1[key] = Aff(c, 0, k)
    S1 = list(S1.values())
    # S2: reps t of B\H (right cosets Bt <-> flag t^{-1}(F0)); here H = H0 + translations,
    # but translations are in B so reps may be linear; compare flags of inverse.
    S2 = {}
    for c in H0:
        inv = mat_inv(c, k)
        key = flag_of(inv, k)
        if key not in S2:
            S2[key] = Aff(c, 0, k)
    S2 = list(S2.values())
    return GL, B, S1, S2

def full_agl(GL, n, k):
    return [Aff(c, t, k) for c in GL for t in range(n)]

def pull(f, A):  # f o A
    return bytes(f[A(x)] for x in range(len(f)))

def canon_B(f, B):
    best = None
    for b in B:
        s = pull(f, b)
        if best is None or s < best:
            best = s
    return best

def check(k, rounds, seed=1):
    random.seed(seed)
    GL, B, S1, S2 = setup(k)
    n = 1 << k
    print(f"k={k}: |GL|={len(GL)} |B|={len(B)} |S1|={len(S1)} |S2|={len(S2)}")
    print("  |S1|*|B|*|S2| =", len(S1) * len(B) * len(S2), " |AGL| =", len(GL) * n)
    assert len(S1) * len(B) * len(S2) == len(GL) * n
    # exact factorization: every AGL element is s o b o t for a unique triple
    if k <= 3:
        seen = set()
        for s in S1:
            for b in B:
                for t in S2:
                    seen.add((s.compose(b).compose(t)).key())
        assert len(seen) == len(GL) * n
        print("  factorization exact (all products distinct and cover AGL)")
    agl = full_agl(GL, n, k)
    agreed = 0
    for it in range(rounds):
        f = bytes(random.randrange(2) for _ in range(n))
        if random.random() < 0.5:
            h = random.choice(agl)
            g = pull(f, h)
        else:
            g = bytes(random.randrange(2) for _ in range(n))
        truth = any(pull(f, a) == g for a in agl)
        A = {canon_B(pull(f, s), B) for s in S1}
        C = {canon_B(pull(g, t.inv()), B) for t in S2}
        res = bool(A & C)
        assert res == truth, (f, g, res, truth)
        agreed += 1
    print(f"  bidirectional collision agreed with brute force on {agreed} random pairs")

if __name__ == "__main__":
    check(3, 300)
    check(4, 6)
