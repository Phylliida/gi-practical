#!/usr/bin/env python3
# gen.py: conference-graph families and Spence-data parser; writes the text format read by conf.c.
# Pure Python (the repo venv has pynauty, no numpy).
import itertools, random, sys

def is_prime(m):
    if m < 2: return False
    for d in range(2, int(m**0.5)+1):
        if m % d == 0: return False
    return True

def prime_power(q):
    for p in range(2, q+1):
        if is_prime(p) and q % p == 0:
            e, x = 0, q
            while x % p == 0: x //= p; e += 1
            return (p, e) if x == 1 else None
    return None

class GF:
    """F_{p^e}: elements are ints 0..q-1 in base p (poly coefficients)."""
    def __init__(self, q):
        self.q = q; pe = prime_power(q)
        if pe is None: raise ValueError("not a prime power")
        self.p, self.e = pe
        self.mod = self._irr() if self.e > 1 else None
        self.mul_t = None
    def _digits(self, x):
        d = []
        for _ in range(self.e): d.append(x % self.p); x //= self.p
        return d
    def _undigits(self, d):
        x = 0
        for c in reversed(d): x = x*self.p + c
        return x
    def _polymul(self, a, b, mod):
        r = [0]*(2*self.e-1)
        for i, x in enumerate(a):
            for j, y in enumerate(b): r[i+j] = (r[i+j] + x*y) % self.p
        for i in range(2*self.e-2, self.e-1, -1):
            c = r[i]
            if c:
                for j in range(self.e+1):
                    r[i-self.e+j] = (r[i-self.e+j] - c*mod[j]) % self.p
        return r[:self.e]
    def _irr(self):
        # brute-force a monic polynomial such that x generates a field (primitive), simple test
        p, e = self.p, self.e; q = self.q
        for coeffs in itertools.product(range(p), repeat=e):
            mod = list(coeffs)+[1]
            # test x has order q-1
            x = [0]*e; x[1 % e] = 1
            cur = [1]+[0]*(e-1); order = 0; seen = set()
            for k in range(q):
                t = tuple(cur)
                if t in seen: break
                seen.add(t); cur = self._polymul(cur, x, mod)
            if len(seen) == q-1 and tuple(cur) == tuple([1]+[0]*(e-1)):
                return mod
        raise RuntimeError("no primitive polynomial")
    def add(self, a, b):
        if self.e == 1: return (a+b) % self.p
        return self._undigits([(x+y)%self.p for x, y in zip(self._digits(a), self._digits(b))])
    def sub(self, a, b):
        if self.e == 1: return (a-b) % self.p
        return self._undigits([(x-y)%self.p for x, y in zip(self._digits(a), self._digits(b))])
    def mul(self, a, b):
        if self.e == 1: return (a*b) % self.p
        return self._undigits(self._polymul(self._digits(a), self._digits(b), self.mod))
    def gen(self):
        if self.e > 1: return self._undigits([0,1]+[0]*(self.e-2)) if self.e>1 else 2
        for g in range(2, self.q):
            x, k = g, 1
            while x != 1: x = x*g % self.q; k += 1
            if k == self.q-1: return g
        return 1
    def logtable(self):
        """returns dict element -> discrete log"""
        g = self.gen(); x = 1; log = {}
        for i in range(self.q-1):
            log[x] = i; x = self.mul(x, g)
        return log

def from_connection_additive(field_or_pairs, n, conn, sub):
    A = [[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i != j and sub(i, j) in conn: A[i][j] = 1
    return A

def paley(q):
    F = GF(q); log = F.logtable()
    S = {x for x, k in log.items() if k % 2 == 0}
    return from_connection_additive(F, q, S, F.sub)

def peisert(q):
    F = GF(q); log = F.logtable()
    assert F.p % 4 == 3 and F.e % 2 == 0
    S = {x for x, k in log.items() if k % 4 in (0, 1)}
    return from_connection_additive(F, q, S, F.sub)

def cyclotomic_union(q, N, classes):
    F = GF(q); log = F.logtable()
    S = {x for x, k in log.items() if (k % N) in classes}
    return from_connection_additive(F, q, S, F.sub)

def peisert_type_lines(q, lineset):
    """F_q^2; connection set = union of lines through 0 indexed by lineset in PG(1,q) (points 0..q, q = infinity)."""
    F = GF(q); n = q*q
    def idx(x, y): return x*q + y
    def unidx(z): return z//q, z%q
    S = set()
    for L in lineset:
        for t in range(1, q):
            if L == q: S.add(idx(0, t))
            else: S.add(idx(t, F.mul(L, t)))
    def sub(a, b):
        ax, ay = unidx(a); bx, by = unidx(b)
        return idx(F.sub(ax, bx), F.sub(ay, by))
    return from_connection_additive(F, n, S, sub)

def is_conference(A):
    n = len(A)
    if n % 4 != 1: return False
    k = (n-1)//2; lam = (n-5)//4; mu = (n-1)//4
    for i in range(n):
        if A[i][i] or sum(A[i]) != k: return False
        for j in range(n):
            if i != j:
                if A[i][j] != A[j][i]: return False
                c = sum(a & b for a, b in zip(A[i], A[j]))
                if c != (lam if A[i][j] else mu): return False
    return True

def parse_spence(path, n):
    """Yields adjacency matrices from Spence's files: rows of 0/1 of length n, separated arbitrarily."""
    import re, bz2
    op = bz2.open if path.endswith('.bz2') else open
    with op(path, 'rt', errors='replace') as f:
        rows = []
        for line in f:
            m = re.findall(r'[01]{%d}' % n, line)
            if m and len(m[-1]) == n:
                rows.append([int(c) for c in m[-1]])
                if len(rows) == n:
                    yield rows; rows = []

def parse_conf2graph(path, nvert):
    """conf2graph.m lists two-graphs by greatest descendant (order m-1): one adjacency matrix per two-graph."""
    return parse_spence(path, nvert)

def nauty_info(A):
    from pynauty import Graph, autgrp
    n = len(A)
    g = Graph(n, adjacency_dict={i:[j for j in range(n) if A[i][j]] for i in range(n)})
    gens, m, e, orbits, ot = autgrp(g)
    order = m*(10**e)
    return order, orbits, gens

def write_graph(out, name, A, reps=None, reps2=None):
    n = len(A)
    out.write(f"G {name}\n{n}\n")
    out.write("NREP " + " ".join(str(r) for r in (reps if reps is not None else range(n))) + "\n")
    out.write("NREP2 " + " ".join(str(r) for r in (reps2 if reps2 is not None else [])) + "\n")
    for r in A: out.write("".join(map(str, r)) + "\n")

def spence_files(root):
    return {
        25: (f"{root}/25-12-5-6", 25),
        29: (f"{root}/29-14-6-7", 29),
        37: (f"{root}/37-18-8-9.bz2", 37),
        41: (f"{root}/conf2graph.42", 41),
        45: (f"{root}/conf2graph.46", 45),
        49: (f"{root}/conf2graph.50", 49),
    }

# ---- Turyn product (Mathon 1978, eq. 1.10; attributed to Turyn 1971) ----
def seidel_of_adj(A):
    n = len(A)
    return [[0 if i == j else (1 if A[i][j] else -1) for j in range(n)] for i in range(n)]

def adj_of_seidel(B):
    n = len(B)
    return [[0 if i == j else (1 if B[i][j] == 1 else 0) for j in range(n)] for i in range(n)]

def paley_skew(q):
    """Seidel-type matrix of the Paley tournament for q = 3 (mod 4): V(x,y) = chi(y - x), skew, VV^T = qI - J."""
    F = GF(q); log = F.logtable()
    V = [[0]*q for _ in range(q)]
    for i in range(q):
        for j in range(q):
            if i != j:
                d = F.sub(j, i)
                V[i][j] = 1 if log[d] % 2 == 0 else -1
    return V

def turyn(V1, V2):
    """W = V1 (x) V2 + I (x) J - J (x) I, V1, V2 of the same order v; order v^2 symmetric conference if
    V1V1^T = V2V2^T = vI - J, both symmetric or both skew."""
    v = len(V1); assert len(V2) == v
    N = v*v; W = [[0]*N for _ in range(N)]
    for i in range(v):
        for j in range(v):
            for k in range(v):
                for l in range(v):
                    W[i*v+j][k*v+l] = V1[i][k]*V2[j][l] + (1 if i == k else 0) - (1 if j == l else 0)
    return W

def turyn_family(base, levels):
    """Yield (name, adjacency) for iterated Turyn products starting from Seidel/skew matrix base."""
    V = base
    for L in range(levels):
        V = turyn(V, V)
        yield L+1, adj_of_seidel(V)
