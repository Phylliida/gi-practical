"""Independent harness for the red team of docs/w32-conference.md.

Written from the memo's statements, not its scripts (no import of docs/w32-code/).
Finite fields are built by trial division for an irreducible polynomial, the Paley connection
set by squaring, 1-WL exactly (np.unique on signatures, no hashing).  C = J - I - 2A throughout.
"""
import bz2, itertools, re, sys
import numpy as np

SPENCE = '/tmp/claude-1000/-home-bepis-math/117a2777-2472-4276-845a-e0dfeb712755/scratchpad/r4-sources/w32-spence-data'

def is_prime(m):
    if m < 2: return False
    i = 2
    while i * i <= m:
        if m % i == 0: return False
        i += 1
    return True

def factor_pp(q):
    for p in range(2, q + 1):
        if is_prime(p) and q % p == 0:
            e = 0; x = q
            while x % p == 0: x //= p; e += 1
            return (p, e) if x == 1 else None
    return None

def _polys(p, d):
    """all monic polys of degree d over F_p as coefficient tuples low..high"""
    for low in itertools.product(range(p), repeat=d):
        yield list(low) + [1]

def _polymod(a, m, p):
    a = list(a)
    while len(a) >= len(m):
        c = a[-1] % p
        if c:
            s = len(a) - len(m)
            for i, x in enumerate(m):
                a[s + i] = (a[s + i] - c * x) % p
        a.pop()
    return a

def irreducible(p, e):
    for f in _polys(p, e):
        ok = True
        for d in range(1, e // 2 + 1):
            for g in _polys(p, d):
                if not any(x % p for x in _polymod(f, g, p)):
                    ok = False; break
            if not ok: break
        if ok: return f
    raise RuntimeError

class Field:
    """F_q, elements are ints 0..q-1 in base p."""
    def __init__(self, q):
        self.q = q; self.p, self.e = factor_pp(q)
        p, e = self.p, self.e
        self.mod = irreducible(p, e) if e > 1 else None
        self.digits = np.zeros((q, e), dtype=np.int64)
        for x in range(q):
            y = x
            for i in range(e): self.digits[x, i] = y % p; y //= p
        self.power = p ** np.arange(e)
    def add(self, a, b):
        return ((self.digits[a] + self.digits[b]) % self.p).dot(self.power)
    def neg(self, a):
        return ((-self.digits[a]) % self.p).dot(self.power)
    def mul1(self, a, b):
        p = self.p; e = self.e
        if e == 1: return a * b % p
        r = [0] * (2 * e - 1)
        for i in range(e):
            for j in range(e):
                r[i + j] = (r[i + j] + int(self.digits[a, i]) * int(self.digits[b, j])) % p
        r = _polymod(r, self.mod, p)
        r += [0] * (e - len(r))
        return int(np.array(r).dot(self.power))
    def sub_table(self):
        q = self.q
        d = (self.digits[:, None, :] - self.digits[None, :, :]) % self.p
        return d.dot(self.power)
    def squares(self):
        return {self.mul1(x, x) for x in range(1, self.q)}
    def order_of(self, x):
        y = x; k = 1
        while y != 1:
            y = self.mul1(y, x); k += 1
        return k
    def generator(self):
        for g in range(2, self.q) if self.q > 2 else [1]:
            if self.order_of(g) == self.q - 1: return g

def paley_adj(q, field=None):
    F = field or Field(q)
    sq = np.zeros(q, dtype=bool)
    sq[list(F.squares())] = True
    D = F.sub_table()
    return sq[D].astype(np.uint8)

def seidel(A):
    """C = J - I - 2A (-1 on edges, +1 on non-edges, 0 on the diagonal)."""
    return (1 - np.eye(len(A), dtype=np.int64) - 2 * A.astype(np.int64)).astype(np.int8)

def adj_of_C(C):
    """A with C = J - I - 2A"""
    return ((1 - np.eye(len(C), dtype=np.int64) - C.astype(np.int64)) // 2).astype(np.uint8)

def paley_tournament_V(q):
    """skew V of order q = 3 mod 4: V(x,y) = chi(y - x), V V^T = qI - J, V1 = 0."""
    F = Field(q)
    sq = F.squares()
    D = F.sub_table()
    V = np.zeros((q, q), dtype=np.int8)
    for i in range(q):
        for j in range(q):
            d = int(D[j, i])  # j - i
            if d != 0: V[i, j] = 1 if d in sq else -1
    return V

def turyn(V1, V2):
    """W = V1 (x) V2 + I (x) J - J (x) I.  Index (i,j) -> i*v + j."""
    v = len(V1); assert len(V2) == v
    W = np.kron(V1.astype(np.int64), V2.astype(np.int64)) \
        + np.kron(np.eye(v, dtype=np.int64), np.ones((v, v), dtype=np.int64)) \
        - np.kron(np.ones((v, v), dtype=np.int64), np.eye(v, dtype=np.int64))
    return W.astype(np.int8)

def turyn_iterates(V, levels):
    """[W_1, ..., W_levels]"""
    out = []
    for _ in range(levels):
        V = turyn(V, V); out.append(V)
    return out

def check_conf_matrix(C):
    """symmetric, zero diagonal, entries +-1 off-diagonal, C1=0, C^2 = nI - J. Returns True/False."""
    n = len(C)
    C2 = C.astype(np.int64)
    if not np.array_equal(C2, C2.T): return False
    if np.any(np.diag(C2) != 0): return False
    off = C2[~np.eye(n, dtype=bool)]
    if not np.all(np.abs(off) == 1): return False
    if np.any(C2.sum(axis=1) != 0): return False
    if not np.array_equal(C2 @ C2, n * np.eye(n, dtype=np.int64) - 1): return False
    return True

def is_conference_graph(A):
    """exact SRG(n,(n-1)/2,(n-5)/4,(n-1)/4) test by A^2 = kI + lam A + mu(J-I-A)."""
    n = len(A)
    if n % 4 != 1: return False
    A2 = A.astype(np.int64)
    if not np.array_equal(A2, A2.T) or np.any(np.diag(A2)): return False
    k, l, m = (n - 1) // 2, (n - 5) // 4, (n - 1) // 4
    if np.any(A2.sum(axis=1) != k): return False
    lhs = A2 @ A2
    rhs = k * np.eye(n, dtype=np.int64) + l * A2 + m * (1 - np.eye(n, dtype=np.int64) - A2)
    return np.array_equal(lhs, rhs)

def rank2(M):
    """F_2 rank of a 0/1 matrix (numpy), by python-int Gaussian elimination."""
    rows = [int(''.join('1' if x else '0' for x in r), 2) for r in M]
    rank = 0
    for col in range(len(M[0]) - 1, -1, -1):
        piv = next((i for i in range(rank, len(rows)) if rows[i] >> col & 1), None)
        if piv is None: continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        for i in range(len(rows)):
            if i != rank and rows[i] >> col & 1: rows[i] ^= rows[rank]
        rank += 1
    return rank

# ---- 1-WL, exact --------------------------------------------------------------------------
def refine(A, colors):
    """stable colouring refining `colors`; signatures compared exactly. Returns (colors, rounds)."""
    n = len(A)
    colors = np.unique(colors, return_inverse=True)[1].ravel()
    A64 = A.astype(np.int32)
    rounds = 0
    while True:
        c = colors.max() + 1
        sig = np.zeros((n, c + 1), dtype=np.int32)
        sig[:, 0] = colors
        for j in range(c):
            sig[:, j + 1] = A64[:, colors == j].sum(axis=1)
        _, new = np.unique(sig, axis=0, return_inverse=True)
        new = new.ravel()
        rounds += 1
        if new.max() + 1 == c:
            return new, rounds
        colors = new

def individualize(A, S):
    n = len(A)
    col = np.zeros(n, dtype=np.int64)
    for i, s in enumerate(S): col[s] = i + 1
    return refine(A, col)[0]

def is_discrete(A, S):
    c = individualize(A, S)
    return c.max() + 1 == len(A)

def stable_cells(A, S):
    c = individualize(A, S)
    return int(c.max()) + 1

# ---- Spence files (own parser) -------------------------------------------------------------
def _read(path):
    if path.endswith('.bz2'):
        return bz2.open(path, 'rt', errors='replace').read()
    return open(path, 'rt', errors='replace').read()

def parse_rows(path, n):
    """All runs of exactly n binary digits (a word, not a substring of a longer digit run)."""
    txt = _read(path)
    rows = re.findall(r'(?<![01])[01]{%d}(?![01])' % n, txt)
    assert len(rows) % n == 0, (path, n, len(rows))
    out = []
    for i in range(0, len(rows), n):
        out.append(np.array([[int(c) for c in r] for r in rows[i:i+n]], dtype=np.uint8))
    return out

def descendants(A):
    """A a conference graph on n vertices.  Two-graph on n+1 points: add isolated point oo.
    Yields the n+1 graphs (delete point p after switching p isolated)."""
    n = len(A)
    C = seidel(A).astype(np.int64)           # S = J - I - 2A, -1 for edges
    S = np.zeros((n + 1, n + 1), dtype=np.int64)
    S[:n, :n] = C
    S[:n, n] = 1; S[n, :n] = 1
    for p in range(n + 1):
        # switch: multiply row/col x by S[p,x] for x != p (so S[p,x] becomes +1, i.e. nonadjacent)
        sign = S[p].copy(); sign[p] = 1
        T = S * np.outer(sign, sign)
        keep = [x for x in range(n + 1) if x != p]
        sub = T[np.ix_(keep, keep)]
        yield ((1 - np.eye(n, dtype=np.int64) - sub) // 2).astype(np.uint8)
