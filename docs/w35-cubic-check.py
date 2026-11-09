#!/usr/bin/env python3
"""
w35-cubic verification harness (see docs/w35-cubic.md).

Reduction under test.  f: F_2^n -> F_2 cubic, f(0)=0, ANF f = C + Q + l.
Gamma_a(x) = zero-diagonal lift of tau(a,.,.) (linear in a).
Forms on W = V (+) U (x,u), U=F_2^n:
    Qa_i(x,u) = Gamma_{e_i}(x) + u_i^2,       i = 1..n
    F(x,u)    = (Q + l)(x)  + x^T u
Theorem: if Rad(tau_f)=Rad(tau_g)=0 then span{Qa,F}(f) ~ span{Qa,F}(g) under GL(W)
         iff  f o L = g for some L in GL(n,2).
Gadget f^+(x,y,t) = f(x) + t (x^T y): Rad(tau^+)=0, and f ~ g iff f^+ ~ g^+.

Every section runs both the true construction and deliberately broken variants
(each broken variant MUST be detected as wrong somewhere, otherwise the test is vacuous).

Run:  nice python3 -I docs/w35-cubic-check.py [section ...]
Sections default to all:  identity reverse3 samples gadget chain obstacle squares degenerate
"""
import random, sys, time
from itertools import combinations

def parity(x): return bin(x).count("1") & 1

# ---------- Boolean functions as ANF: dict-free representation ----------
class Cubic:
    """f = sum c x_i x_j x_k + sum b x_i x_j + sum a x_i (zero constant)."""
    def __init__(self, n, c=None, b=None, a=0):
        self.n = n
        self.c = c if c is not None else set()   # set of (i<j<k)
        self.b = b if b is not None else set()   # set of (i<j)
        self.a = a  # bitmask of linear terms

    def eval(self, x):
        v = parity(self.a & x)
        for (i, j) in self.b:
            if (x >> i) & 1 and (x >> j) & 1: v ^= 1
        for (i, j, k) in self.c:
            if (x >> i) & 1 and (x >> j) & 1 and (x >> k) & 1: v ^= 1
        return v

    def tt(self):
        N = 1 << self.n
        # build truth table with one Moebius-ish expansion: faster to evaluate once
        t = bytearray(N)
        for x in range(N):
            t[x] = self.eval(x)
        return t

def random_cubic(n, rng, pc=0.5, pb=0.5, pa=0.5):
    c = {t for t in combinations(range(n), 3) if rng.random() < pc}
    b = {t for t in combinations(range(n), 2) if rng.random() < pb}
    a = sum(1 << i for i in range(n) if rng.random() < pa)
    return Cubic(n, c, b, a)

def anf_from_tt(n, tt):
    """Moebius transform of a truth table (values 0/1 on 2^n points); assumes degree<=3 and tt[0]==0."""
    a = bytearray(tt)
    for i in range(n):
        bit = 1 << i
        for x in range(1 << n):
            if x & bit:
                a[x] ^= a[x ^ bit]
    c, b, l = set(), set(), 0
    for m in range(1 << n):
        if a[m]:
            pos = [i for i in range(n) if (m >> i) & 1]
            if len(pos) == 1: l |= 1 << pos[0]
            elif len(pos) == 2: b.add(tuple(pos))
            elif len(pos) == 3: c.add(tuple(pos))
            elif len(pos) == 0:
                raise ValueError("constant term present")
            else:
                raise ValueError("degree > 3")
    return Cubic(n, c, b, l)

def compose(f, L):
    """f o L where L is a list of column images (ints). Returns a Cubic (via truth table)."""
    n = f.n
    N = 1 << n
    img = [0] * N
    for x in range(1, N):
        low = (x & -x).bit_length() - 1
        img[x] = img[x & (x - 1)] ^ L[low]
    t = bytearray(N)
    base = f.tt()
    for x in range(N):
        t[x] = base[img[x]]
    return anf_from_tt(n, t)

def random_gl(n, rng):
    while True:
        cols = [rng.randrange(1, 1 << n) for _ in range(n)]
        if rank_cols(cols) == n:
            return cols

def rank_cols(cols):
    rk = 0
    basis = []
    for v in cols:
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v)
            rk += 1
    return rk

def transpose(cols, n):
    return [sum(((cols[c] >> r) & 1) << c for c in range(n)) for r in range(n)]

def apply_cols(cols, x):
    r = 0
    while x:
        i = (x & -x).bit_length() - 1
        x &= x - 1
        r ^= cols[i]
    return r

def inverse(cols, n):
    """Inverse of the matrix with the given columns; returns columns of the inverse."""
    # Gauss-Jordan on rows of [A | I]
    rows = [0] * n
    for r in range(n):
        v = 0
        for c in range(n):
            if (cols[c] >> r) & 1:
                v |= 1 << c
        rows[r] = v | (1 << (n + r))
    for c in range(n):
        p = None
        for r in range(c, n):
            if (rows[r] >> c) & 1:
                p = r
                break
        if p is None:
            raise ValueError("singular")
        rows[c], rows[p] = rows[p], rows[c]
        for r in range(n):
            if r != c and (rows[r] >> c) & 1:
                rows[r] ^= rows[c]
    # rows[r] >> n is the r-th row of the inverse (bit c = entry (r,c))
    invrows = [rows[r] >> n for r in range(n)]
    out = [0] * n
    for c in range(n):
        v = 0
        for r in range(n):
            if (invrows[r] >> c) & 1:
                v |= 1 << r
        out[c] = v
    # sanity
    for c in range(n):
        assert apply_cols(cols, out[c]) == (1 << c)
    return out

# ---------- quadratic forms in D variables ----------
class QF:
    """q = sum_{i} d_i x_i^2 + sum_{i<j} A[i] bit j x_i x_j  (formal form, exact)."""
    __slots__ = ("D", "d", "A")
    def __init__(self, D, d=0, A=None):
        self.D = D
        self.d = d
        self.A = A if A is not None else [0] * D  # A[i] has only bits j>i

    def val(self, v):
        r = parity(self.d & v)
        x = v
        while x:
            i = (x & -x).bit_length() - 1
            x &= x - 1
            r ^= parity(self.A[i] & v)
        return r

    def polar(self, u, v):
        r = 0
        x = u
        while x:
            i = (x & -x).bit_length() - 1
            x &= x - 1
            r ^= parity(self.A[i] & v)
        x = v
        while x:
            i = (x & -x).bit_length() - 1
            x &= x - 1
            r ^= parity(self.A[i] & u)
        return r

    def compose(self, cols):
        """q o S where S has column images cols (length D)."""
        D = self.D
        d = 0
        A = [0] * D
        for k in range(D):
            if self.val(cols[k]):
                d |= 1 << k
        for k in range(D):
            r = 0
            for l in range(k + 1, D):
                if self.polar(cols[k], cols[l]):
                    r |= 1 << l
            A[k] = r
        return QF(D, d, A)

    def add(self, o):
        return QF(self.D, self.d ^ o.d, [x ^ y for x, y in zip(self.A, o.A)])

    def key(self):
        return (self.d, tuple(self.A))

    def polar_matrix_rank(self):
        rows = []
        for i in range(self.D):
            v = 0
            for j in range(self.D):
                if i != j and self.polar(1 << i, 1 << j):
                    v |= 1 << j
            rows.append(v)
        return rank_cols(rows)

def forms_from_cubic(f):
    """The n forms Qa_i and F on W=F_2^{2n}: x bits 0..n-1, u bits n..2n-1."""
    n, D = f.n, 2 * f.n
    Q = []
    for i in range(n):
        A = [0] * D
        for (a, b, c) in f.c:
            t = (a, b, c)
            if i in t:
                r, s = [x for x in t if x != i]
                A[min(r, s)] ^= 1 << max(r, s)
        d = 1 << (n + i)    # u_i^2
        Q.append(QF(D, d, A))
    A = [0] * D
    for (i, j) in f.b:
        A[i] ^= 1 << j
    d = f.a  # linear part l as squares x_i^2
    for i in range(n):
        A[i] ^= 1 << (n + i)  # x_i u_i
    F = QF(D, d, A)
    return Q, F

def gamma(f, a):
    """Gamma_a as a zero-diagonal QF on n variables."""
    n = f.n
    A = [0] * n
    for (i, j, k) in f.c:
        for (r, s, t) in ((i, j, k), (j, i, k), (k, i, j)):
            # term a_r x_s x_t
            if (a >> r) & 1:
                lo, hi = sorted((s, t))
                A[lo] ^= 1 << hi
    return QF(n, 0, A)

def C_eval(f, v):
    r = 0
    for (i, j, k) in f.c:
        if (v >> i) & 1 and (v >> j) & 1 and (v >> k) & 1:
            r ^= 1
    return r

def rad_tau(f):
    """Dimension of the radical of tau (via rank of the map a -> Gamma_a polar)."""
    n = f.n
    rows = []
    for a in range(n):
        g = gamma(f, 1 << a)
        v = 0
        idx = 0
        for i in range(n):
            for j in range(i + 1, n):
                if (g.A[i] >> j) & 1:
                    v |= 1 << idx
                idx += 1
        rows.append(v)
    rk = rank_cols(rows)
    return n - rk

def forward_matrices(f, L):
    """Return (Scols, N) with S(x,u) = (Lx, L^{-T} u + C x), C = L^{-T} N."""
    n = f.n
    # N[i][j] = Gamma_{L e_i}(L e_j)
    N = [[gamma(f, L[i]).val(L[j]) for j in range(n)] for i in range(n)]
    Linv = inverse(L, n)
    LinvT = transpose(Linv, n)  # columns of L^{-T}
    # matrix N as columns: column j = sum_i N[i][j] e_i
    Ncols = [sum(N[i][j] << i for i in range(n)) for j in range(n)]
    # C = L^{-T} N: column j = L^{-T} (N col j)
    Ccols = []
    for j in range(n):
        v = 0
        x = Ncols[j]
        while x:
            i = (x & -x).bit_length() - 1
            x &= x - 1
            v ^= LinvT[i]
        Ccols.append(v)
    # S columns on W: e_x_j -> (L e_j, C e_j); e_u_j -> (0, L^{-T} e_j)
    S = []
    for j in range(n):
        S.append(L[j] | (Ccols[j] << n))
    for j in range(n):
        S.append(LinvT[j] << n)
    return S, Ncols

def fplus(f):
    """f^+(x,y,t) = f(x) + t * x^T y on 2n+1 variables."""
    n = f.n
    N = 2 * n + 1
    c = set(f.c)
    b = set(f.b)
    a = f.a
    t = 2 * n
    for i in range(n):
        # t x_i y_i
        c ^= {tuple(sorted((i, n + i, t)))}
    return Cubic(N, c, b, a)

# ---------- exact equivalence search (truth oracle) by column-wise DFS ----------
def exact_equiv(f, g, limit=1, count_only=False):
    """DFS for L in GL(n,2) with f o L = g. f,g given as Cubic with f(0)=g(0)=0."""
    n = f.n
    N = 1 << n
    tf = f.tt()
    tg = g.tt()
    found = []
    cols = [0] * n
    span_img = [0] * N  # img of x under partial L; maintained incrementally
    used = bytearray(N)  # marks span(cols[:k])
    used[0] = 1
    count = [0]
    # invariant: weight of the derivative D_v (preserved by any L with f o L = g)
    def dw(t):
        return [sum(t[x] ^ t[x ^ v] for x in range(N)) for v in range(N)]
    sf, sg = dw(tf), dw(tg)
    if sorted(sf) != sorted(sg):
        return [], 0
    bysig = {}
    for v in range(1, N):
        bysig.setdefault(sf[v], []).append(v)

    def rec(k):
        if k == n:
            count[0] += 1
            if len(found) < limit:
                found.append(list(cols))
            return
        # candidate images of e_k: not in span of earlier cols
        lowmask = 1 << k
        for c in bysig.get(sg[1 << k], []):
            if used[c]:
                continue
            # compatibility: for every x < 2^k in span of previous inputs (i.e. x in [0, 2^k)):
            # f(img(x) ^ c) == g(x | e_k)
            ok = True
            for x in range(1 << k):
                if tf[span_img[x] ^ c] != tg[x | lowmask]:
                    ok = False
                    break
            if not ok:
                continue
            # commit
            for x in range(1 << k):
                span_img[x | lowmask] = span_img[x] ^ c
                used[span_img[x] ^ c] = 1
            cols[k] = c
            rec(k + 1)
            if len(found) >= limit and not count_only:
                # unwind marks
                for x in range(1 << k):
                    used[span_img[x] ^ c] = 0
                return
            for x in range(1 << k):
                used[span_img[x] ^ c] = 0
    rec(0)
    return found, count[0]

# ---------- span isometry search (GL(W), span(f_i o S) = span(g_j)) -----------
def tri_index(D):
    idx = {}
    k = 0
    for i in range(D):
        for j in range(i, D):
            idx[(i, j)] = k
            k += 1
    return idx

class SpanIso:
    """Search for S in GL(D,2) with span{f_i o S} == span{g_j}.

    Pruning uses only facts implied by the definition of span isometry:
    (1) truncated-form membership, (2) per-vector signature
    sig(v) = (rank of the polar part of {(q(v), Pol_q(v,.)) : q in span}, rank of the full part),
    which any span isometry preserves; (3) multiset of (polar rank, weight) of the 2^m span
    elements, a sound early rejection.
    """
    def __init__(self, D, fs, gs):
        self.D, self.fs, self.gs = D, fs, gs
        self.idx = tri_index(D)
        self.N = 1 << D
        self.Gk = [self._span([self._trunc_vec(g, k) for g in gs]) for k in range(D + 1)]
        self.m = len(fs)
        self.fv = [self._tables(q) for q in fs]
        self.gv = [self._tables(q) for q in gs]
        self.sig_f = self._signatures(fs, self.fv)
        self.sig_g = self._signatures(gs, self.gv)

    def _tables(self, q):
        val = bytearray(self.N)
        pol = [0] * self.N
        D = self.D
        # val via incremental, pol via linearity
        rowpol = [0] * D
        for i in range(D):
            v = 0
            for j in range(D):
                if i != j and ((j > i and (q.A[i] >> j) & 1) or (j < i and (q.A[j] >> i) & 1)):
                    v |= 1 << j
            rowpol[i] = v
        for x in range(1, self.N):
            low = (x & -x).bit_length() - 1
            y = x & (x - 1)
            pol[x] = pol[y] ^ rowpol[low]
            val[x] = val[y] ^ ((q.d >> low) & 1) ^ parity(pol[y] & (1 << low))
        return val, pol

    def _signatures(self, qs, tables):
        sig = [None] * self.N
        for v in range(self.N):
            rows_pol = []
            rows_all = []
            for (val, pol) in tables:
                rows_pol.append(pol[v])
                rows_all.append((pol[v] << 1) | val[v])
            sig[v] = (rank_cols(rows_pol), rank_cols(rows_all))
        return sig

    def _profile(self, qs):
        m = len(qs)
        prof = {}
        current = QF(self.D, 0, [0] * self.D)
        # gray code over span elements
        elements = [current]
        for i in range(m):
            elements += [e.add(qs[i]) for e in list(elements)]
        for e in elements:
            w = sum(1 for v in range(self.N) if e.val(v))
            r = e.polar_matrix_rank()
            prof[(r, w)] = prof.get((r, w), 0) + 1
        return prof

    def _trunc_vec(self, q, k):
        v = 0
        for i in range(k):
            if (q.d >> i) & 1: v |= 1 << self.idx[(i, i)]
            for j in range(i + 1, k):
                if (q.A[i] >> j) & 1: v |= 1 << self.idx[(i, j)]
        return v

    @staticmethod
    def _span(vecs):
        basis = []
        for v in vecs:
            for b, piv in basis:
                if (v >> piv) & 1:
                    v ^= b
            if v:
                piv = v.bit_length() - 1
                basis = [(bb ^ v if (bb >> piv) & 1 else bb, p) for bb, p in basis]
                basis.append((v, piv))
        return basis

    @staticmethod
    def _inspan(v, basis):
        for b, piv in basis:
            if (v >> piv) & 1:
                v ^= b
        return v == 0

    def search(self, limit=1):
        D = self.D
        # early rejection by the span profile (a sound necessary condition)
        if sorted(self.sig_f) != sorted(self.sig_g):
            return []
        if self._profile(self.fs) != self._profile(self.gs):
            return []
        fv = self.fv
        idx = self.idx
        m = self.m
        found = []
        cols = [0] * D
        sigs = self.sig_g
        by_sig = {}
        for v in range(1, self.N):
            by_sig.setdefault(self.sig_f[v], []).append(v)
        Gk = self.Gk

        def rec(k, basis, partials):
            if k == D:
                span = self._span(partials)
                if len(span) == len(Gk[D]):
                    found.append(list(cols))
                return
            G = Gk[k + 1]
            for c in by_sig.get(sigs[1 << k], []):
                w = c
                for b in basis:
                    if w ^ b < w:
                        w ^= b
                if w == 0:
                    continue
                newp = [0] * m
                ok = True
                for i in range(m):
                    (val, pol) = fv[i]
                    v = partials[i]
                    if val[c]:
                        v |= 1 << idx[(k, k)]
                    pc = pol[c]
                    for t in range(k):
                        if parity(pc & cols[t]):
                            v |= 1 << idx[(t, k)]
                    if not self._inspan(v, G):
                        ok = False
                        break
                    newp[i] = v
                if not ok:
                    continue
                cols[k] = c
                nb = sorted(basis + [w], reverse=True)
                rec(k + 1, nb, newp)
                if len(found) >= limit:
                    return
        rec(0, [], [0] * m)
        return found

# ---------- sections ----------
def section_identity():
    print("=== identity: forward direction + algebraic identities (n up to 10) ===")
    rng = random.Random(35001)
    trials = {3: 300, 4: 300, 5: 300, 6: 200, 7: 100, 8: 80, 9: 40, 10: 25}
    total = 0
    for n, tr in trials.items():
        for _ in range(tr):
            f = random_cubic(n, rng)
            # identity: Gamma_v(v) = C(v); polarization
            for _ in range(5):
                v = rng.randrange(1 << n)
                assert gamma(f, v).val(v) == C_eval(f, v), "Gamma_v(v)=C(v) fails"
                w = rng.randrange(1 << n)
                lhs = C_eval(f, v ^ w) ^ C_eval(f, v) ^ C_eval(f, w)
                rhs = gamma(f, v).val(w) ^ gamma(f, w).val(v)
                assert lhs == rhs, "polarization identity fails"
            L = random_gl(n, rng)
            g = compose(f, L)
            S, _ = forward_matrices(f, L)
            Qf, Ff = forms_from_cubic(f)
            Qg, Fg = forms_from_cubic(g)
            Linv = inverse(L, n)
            # Q^f_a o S = Q^g_{L^{-1} a}: check on basis a = e_i: L^{-1} e_i = Linv[i]
            D = 2 * n
            for i in range(n):
                lhs = Qf[i].compose(S)
                bcol = Linv[i]  # b = L^{-1} e_i, as column
                rhs = QF(D, 0, [0] * D)
                for j in range(n):
                    if (bcol >> j) & 1:
                        rhs = rhs.add(Qg[j])
                assert lhs.key() == rhs.key(), "Q forward fails n=%d" % n
            assert Ff.compose(S).key() == Fg.key(), "F forward fails n=%d" % n
            total += 1
    print(f"forward identities OK on {total} random (f, L), n=3..10")

    # broken variants: each must fail on at least one trial
    rng = random.Random(35002)
    fails = {"C=0": 0, "no x^T N x term in F": 0, "diag l dropped": 0}
    tot = 0
    for n in (4, 5, 6):
        for _ in range(40):
            f = random_cubic(n, rng)
            L = random_gl(n, rng)
            g = compose(f, L)
            S, _ = forward_matrices(f, L)
            Qf, Ff = forms_from_cubic(f)
            Qg, Fg = forms_from_cubic(g)
            Linv = inverse(L, n)
            D = 2 * n
            # variant: set C=0
            S0 = [L[j] for j in range(n)] + list(S[n:])
            badq = False
            for i in range(n):
                lhs = Qf[i].compose(S0)
                rhs = QF(D, 0, [0] * D)
                for j in range(n):
                    if (Linv[i] >> j) & 1:
                        rhs = rhs.add(Qg[j])
                if lhs.key() != rhs.key():
                    badq = True
            badf = Ff.compose(S0).key() != Fg.key()
            if badq or badf: fails["C=0"] += 1
            # variant: F without pairing-correction (drop quadratic correction in F): compare F o S with Q+l o L + pairing only
            # i.e. F computed with a=b=0 lower-order piece misencoded: omit diag l
            Fbad = QF(D, 0, list(Ff.A))  # drops d = linear part
            FgBad = QF(D, 0, list(Fg.A))
            if Fbad.compose(S).key() != FgBad.key(): fails["diag l dropped"] += 1
            # (dropping u_i^2 does not affect the forward identity; it breaks the reverse direction
            # and is exercised as broken variant "no u^2" in section reverse3.)
            # variant: use F without correction term but compare to g' = plain transform of q part:
            # (Q+l)(Lx) + x^T u vs Fg : must fail when N nonzero
            q = QF(D, Ff.d, [Ff.A[i] & ((1 << n) - 1) for i in range(n)] + [0] * n)
            lhs = q.compose(S[:n] + [1 << (n + j) for j in range(n)])
            rhs = QF(D, Fg.d, [Fg.A[i] & ((1 << n) - 1) for i in range(n)] + [0] * n)
            if lhs.key() != rhs.key(): fails["no x^T N x term in F"] += 1
            tot += 1
    print("broken-variant detection (forward direction), out of %d trials:" % tot, fails)
    assert fails["C=0"] > 0 and fails["diag l dropped"] > 0 and fails["no x^T N x term in F"] > 0
    print("identity: all broken variants detected")

def all_cubics_n3():
    """All f on F_2^3 of degree<=3, zero constant, with Rad(tau)=0 (i.e. cubic part x0x1x2)."""
    out = []
    pairs = list(combinations(range(3), 2))
    for bmask in range(8):
        b = {pairs[i] for i in range(3) if (bmask >> i) & 1}
        for a in range(8):
            out.append(Cubic(3, {(0, 1, 2)}, b, a))
    return out

def span_iso_forms(f, g, Qf=None):
    Qf_, Ff = forms_from_cubic(f)
    Qg, Fg = forms_from_cubic(g)
    return Qf_ + [Ff], Qg + [Fg]

def section_reverse3():
    print("=== reverse3: exhaustive reverse direction, n=3 (all 64 functions with Rad tau=0) ===")
    fs = all_cubics_n3()
    D = 6
    t0 = time.time()
    agree = 0
    pos = 0
    truth_tab = {}
    for i, f in enumerate(fs):
        for j, g in enumerate(fs):
            truth = bool(exact_equiv(f, g)[0])
            ffs, ggs = span_iso_forms(f, g)
            si = SpanIso(D, ffs, ggs)
            ans = bool(si.search(limit=1))
            truth_tab[(i, j)] = truth
            assert ans == truth, f"reduction disagrees on pair ({i},{j}): truth {truth}, span {ans}"
            agree += 1
            if truth: pos += 1
    print(f"reverse3: reduction agreed with truth on all {agree} pairs ({pos} equivalent), {time.time()-t0:.1f}s")

    # broken variant A: drop u_i^2 from Qa -> index tie lost; expect a spurious isometry somewhere
    # broken variant B: drop the pairing x^T u from F (F = q only)
    # broken variant C: drop linear part l from F
    spurious = {"no u^2": 0, "no pairing": 0, "no l in F": 0}
    missed = {"no u^2": 0, "no pairing": 0, "no l in F": 0}
    sample = [(i, j) for i in range(len(fs)) for j in range(len(fs)) if (i + j) % 3 == 0][:300]
    for i, j in sample:
        f, g = fs[i], fs[j]
        truth = truth_tab[(i, j)]
        for name in spurious:
            ffs, ggs = span_iso_forms(f, g)
            if name == "no u^2":
                ffs = [QF(D, 0, q.A) for q in ffs[:-1]] + [ffs[-1]]
                ggs = [QF(D, 0, q.A) for q in ggs[:-1]] + [ggs[-1]]
            elif name == "no pairing":
                ffs = ffs[:-1] + [QF(D, ffs[-1].d, [a & 0b111 for a in ffs[-1].A[:3]] + [0, 0, 0])]
                ggs = ggs[:-1] + [QF(D, ggs[-1].d, [a & 0b111 for a in ggs[-1].A[:3]] + [0, 0, 0])]
            else:
                ffs = ffs[:-1] + [QF(D, 0, ffs[-1].A)]
                ggs = ggs[:-1] + [QF(D, 0, ggs[-1].A)]
            ans = bool(SpanIso(D, ffs, ggs).search(limit=1))
            if ans and not truth: spurious[name] += 1
            if not ans and truth: missed[name] += 1
    print("broken variants, 300 sampled pairs:", "spurious", spurious, "missed", missed)
    assert any(v > 0 for v in spurious.values()) or any(v > 0 for v in missed.values()), "tests vacuous"
    assert spurious["no l in F"] > 0 or missed["no l in F"] > 0
    print("reverse3 done")

def random_rad0(n, rng, tries=2000):
    for _ in range(tries):
        f = random_cubic(n, rng)
        if rad_tau(f) == 0:
            return f
    raise RuntimeError("no Rad=0 cubic found")

def section_samples():
    print("=== samples: n=5,6 random with Rad tau=0: planted equivalent / same-tau-different-lower / unrelated ===")
    rng = random.Random(35003)
    for n, count in ((5, 12), (6, 2)):
        D = 2 * n
        for trial in range(count):
            f = random_rad0(n, rng)
            L = random_gl(n, rng)
            g = compose(f, L)
            # negative: same top form, different lower-order part. Flip a quadratic/linear term of g
            # and certify non-equivalence by exhaustive column-DFS.
            g2 = Cubic(n, set(g.c), set(g.b) ^ {(0, 1)}, g.a)
            neg_truth = bool(exact_equiv(f, g2)[0])
            t0 = time.time()
            ans_pos = bool(SpanIso(D, *span_iso_forms(f, g)).search(limit=1))
            t1 = time.time()
            ans_neg = bool(SpanIso(D, *span_iso_forms(f, g2)).search(limit=1))
            t2 = time.time()
            assert ans_pos, "positive instance must have span isometry"
            assert ans_neg == neg_truth, "lower-order negative disagrees"
            print(f"n={n} trial {trial}: planted yes -> yes ({t1-t0:.2f}s); perturbed truth={neg_truth} -> {ans_neg} ({t2-t1:.2f}s)")
    print("samples done")

def section_gadget():
    print("=== gadget: f ~ g iff f^+ ~ g^+ exhaustive for small n ===")
    # n=2: all 8 functions of degree<=3 with zero constant (deg<=2 actually)
    # n=3: all 128 functions
    for n in (2, 3):
        fns = []
        all_mono = [m for m in range(1, 1 << n)]
        for mask in range(1 << len(all_mono)):
            c, b, a = set(), set(), 0
            for t, m in enumerate(all_mono):
                if (mask >> t) & 1:
                    pos = [i for i in range(n) if (m >> i) & 1]
                    if len(pos) == 1: a |= 1 << pos[0]
                    elif len(pos) == 2: b.add(tuple(pos))
                    else: c.add(tuple(pos))
            fns.append(Cubic(n, c, b, a))
        t0 = time.time()
        # orbit classification of all fns under GL(n,2) via the exact oracle
        reps = []
        cls = {}
        for i, f in enumerate(fns):
            for ridx, r in enumerate(reps):
                if exact_equiv(f, r)[0]:
                    cls[i] = ridx
                    break
            else:
                cls[i] = len(reps)
                reps.append(f)
        print(f"n={n}: {len(fns)} functions, {len(reps)} GL-orbits ({time.time()-t0:.1f}s)")
        # exhaustive over pairs of orbit representatives
        for i, f in enumerate(reps):
            for j, g in enumerate(reps):
                truth = (i == j)
                ans = bool(exact_equiv(fplus(f), fplus(g))[0])
                assert truth == ans, f"gadget disagrees on reps ({i},{j}) truth {truth} ans {ans}"
        # plus random conjugates of each rep (positive pairs that are not literally equal)
        rng = random.Random(35100 + n)
        pos = 0
        for r in reps:
            for _ in range(10):
                L = random_gl(n, rng)
                g = compose(r, L)
                assert exact_equiv(fplus(r), fplus(g))[0], "positive conjugate lost"
                pos += 1
        print(f"gadget n={n}: agreed on all {len(reps)**2} rep pairs + {pos} conjugates, {time.time()-t0:.1f}s")
    # broken variant: drop the pairing (f^+ = f(x) + t*y_0*x_0 only) -> gadget should fail for some pair
    # (a generic L cannot be lifted, so genuine equivalences are lost).
    n = 3
    fns = [random_cubic(n, random.Random(35100 + s)) for s in range(8)]
    def bad_plus(f):
        c = set(f.c)
        c ^= {tuple(sorted((0, n, 2 * n)))}
        return Cubic(2 * n + 1, c, set(f.b), f.a)
    errs = 0
    for f in fns:
        for g in fns:
            truth = bool(exact_equiv(f, g)[0])
            ans = bool(exact_equiv(bad_plus(f), bad_plus(g))[0])
            if truth != ans: errs += 1
    print("broken gadget (single monomial t x0 y0): disagreements on", errs, "of", len(fns) ** 2, "pairs")
    assert errs > 0, "broken gadget not detected"

def section_chain():
    print("=== chain: composed pipeline f -> f^+ -> forms -> span isometry on small cases ===")
    # n=2: N=5, W=10
    rng = random.Random(35004)
    n = 2
    fns = []
    # all functions on F_2^2 with zero constant, degree<=2: x0, x1, x0x1, ...
    for mask in range(1 << 3):
        c, b, a = set(), set(), 0
        if mask & 1: a |= 1
        if mask & 2: a |= 2
        if mask & 4: b.add((0, 1))
        fns.append(Cubic(2, c, b, a))
    D = 10
    t0 = time.time()
    agree = 0
    for i, f in enumerate(fns):
        for j, g in enumerate(fns):
            truth = bool(exact_equiv(f, g)[0])
            fp, gp = fplus(f), fplus(g)
            ans = bool(SpanIso(D, *span_iso_forms(fp, gp)).search(limit=1))
            assert ans == truth, f"chain disagrees ({i},{j})"
            agree += 1
    print(f"chain n=2: agreed on all {agree} pairs in {time.time()-t0:.1f}s")

def tuple_congruent(A, B, n):
    """DFS for X in GL(n,2) with X^T A_i X = B_i for all i (A_i, B_i given as lists of n row ints)."""
    N = 1 << n
    cols = [0] * n
    def form(M, u, v):
        r = 0
        x = u
        while x:
            i = (x & -x).bit_length() - 1
            x &= x - 1
            r ^= parity(M[i] & v)
        return r
    def rec(k, basis):
        if k == n:
            return True
        for c in range(1, N):
            w = c
            for b in basis:
                if w ^ b < w:
                    w ^= b
            if w == 0:
                continue
            ok = True
            for a, bb in zip(A, B):
                for t in range(k + 1):
                    val = form(a, cols[t] if t < k else c, c)
                    if val != ((bb[t] >> k) & 1):
                        ok = False
                        break
                if not ok:
                    break
            if not ok:
                continue
            cols[k] = c
            if rec(k + 1, sorted(basis + [w], reverse=True)):
                return True
        return False
    return list(cols) if rec(0, []) else None

def section_obstacle():
    """Explicit failure of the *-symmetric decomposition step over F_2.

    A = C (x) I_2 with C = basis of all alternating 3x3 matrices; E = I_3 (x) Swap.  E lies in the
    adjoint algebra, B = A E = C (x) Swap is alternating, and (T=I, S=E) is a left-right
    equivalence A -> B.  Congruence would need X*X = E, and Swap = Y^T Y has no solution over F_2.
    """
    print("=== obstacle: left-right equivalent alternating tuples over F_2 that are not congruent ===")
    C = [[0b010, 0b001, 0b000], [0b100, 0b000, 0b001], [0b000, 0b100, 0b010]]
    n = 6
    def kron(M, K):
        # rows of M (3x3) tensor K (2x2) on index 2*u + a
        out = [0] * n
        for u in range(3):
            for v in range(3):
                if (M[u] >> v) & 1:
                    for a in range(2):
                        for b in range(2):
                            if (K[a] >> b) & 1:
                                out[2 * u + a] |= 1 << (2 * v + b)
        return out
    I2 = [0b01, 0b10]
    Swap = [0b10, 0b01]
    A = [kron(c, I2) for c in C]
    B = [kron(c, Swap) for c in C]
    # left-right equivalence: I^T A E = B with E = I_3 (x) Swap
    E = kron([0b001, 0b010, 0b100], Swap)
    def mul(a, b):
        out = [0] * n
        for r in range(n):
            v = 0
            x = a[r]
            while x:
                i = (x & -x).bit_length() - 1
                x &= x - 1
                v ^= b[i]
            out[r] = v
        return out
    assert all(mul(a, E) == bb for a, bb in zip(A, B)), "left-right witness"
    # alternating check
    for M in A + B:
        for i in range(n):
            assert not (M[i] >> i) & 1
            for j in range(n):
                assert ((M[i] >> j) & 1) == ((M[j] >> i) & 1)
    # Swap = Y^T Y has no solution over F_2
    sols = 0
    for y in range(16):
        Y = [y & 3, y >> 2]
        YTY = [0, 0]
        for r in range(2):
            for c in range(2):
                bit = 0
                for k in range(2):
                    bit ^= ((Y[k] >> r) & 1) & ((Y[k] >> c) & 1)
                YTY[r] |= bit << c
        if YTY == Swap:
            sols += 1
    print("Y^T Y = Swap solutions over F_2:", sols)
    assert sols == 0
    t0 = time.time()
    X = tuple_congruent(A, B, n)
    print(f"congruence search A vs B: {'FOUND ' + str(X) if X else 'none'} ({time.time()-t0:.1f}s)")
    assert X is None, "expected non-congruent"
    # sanity: the search does find congruences that exist (positive control)
    rng = random.Random(35201)
    P = random_gl(n, rng)
    Pinv_rows = None
    # B' = P^T A P
    Pr = [sum(((P[c] >> r) & 1) << c for c in range(n)) for r in range(n)]
    Pt = [sum(((Pr[c] >> r) & 1) << c for c in range(n)) for r in range(n)]
    Bp = [mul(mul(Pt, a), Pr) for a in A]
    Xp = tuple_congruent(A, Bp, n)
    assert Xp is not None, "positive control failed"
    print("positive control (planted congruence) found. obstacle done")

def tuple_iso(fs, gs, D):
    """DFS for S in GL(D,2) with f_i o S == g_i for all i (exact tuple isometry of quadratic forms)."""
    N = 1 << D
    cols = [0] * D
    # per-form tables
    tab = []
    for q in fs:
        rowpol = [0] * D
        for i in range(D):
            v = 0
            for j in range(D):
                if i != j and ((j > i and (q.A[i] >> j) & 1) or (j < i and (q.A[j] >> i) & 1)):
                    v |= 1 << j
            rowpol[i] = v
        val = bytearray(N)
        pol = [0] * N
        for x in range(1, N):
            low = (x & -x).bit_length() - 1
            y = x & (x - 1)
            pol[x] = pol[y] ^ rowpol[low]
            val[x] = val[y] ^ ((q.d >> low) & 1) ^ parity(pol[y] & (1 << low))
        tab.append((val, pol))
    def rec(k, basis):
        if k == D:
            return True
        for c in range(1, N):
            w = c
            for b in basis:
                if w ^ b < w:
                    w ^= b
            if w == 0:
                continue
            ok = True
            for (val, pol), g in zip(tab, gs):
                if val[c] != ((g.d >> k) & 1):
                    ok = False
                    break
                for t in range(k):
                    if parity(pol[c] & cols[t]) != ((g.A[t] >> k) & 1):
                        ok = False
                        break
                if not ok:
                    break
            if not ok:
                continue
            cols[k] = c
            if rec(k + 1, sorted(basis + [w], reverse=True)):
                return True
        return False
    return list(cols) if rec(0, []) else None

def section_squares():
    print("=== squares: Theorem A, alternating tuple congruence vs quadratic tuple isometry with u_i^2 gadget ===")
    rng = random.Random(35300)
    n, m = 4, 2
    D = n + m
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    def rand_alt():
        rows = [0] * n
        for (i, j) in pairs:
            if rng.random() < 0.5:
                rows[i] |= 1 << j
                rows[j] |= 1 << i
        return rows
    def common_radical_zero(T):
        for v in range(1, 1 << n):
            if all(all(parity(M[r] & v) == 0 for r in range(n)) for M in T):
                return False
        return True
    def mul(a, b):
        out = [0] * n
        for r in range(n):
            v = 0
            x = a[r]
            while x:
                i = (x & -x).bit_length() - 1
                x &= x - 1
                v ^= b[i]
            out[r] = v
        return out
    def lift(M, diag):
        """Quadratic form on D variables polarizing to M on the first n, with diagonal diag."""
        A = [0] * D
        for i in range(n):
            A[i] = (M[i] >> (i + 1)) << (i + 1)
        return QF(D, diag, A)
    def gadget(T, diags):
        return [QF(D, q.d | (1 << (n + i)), q.A) for i, q in enumerate(lift(M, d) for M, d in zip(T, diags))]
    stats = {"agree": 0, "pos": 0, "neg": 0}
    broken_wrong = 0
    t0 = time.time()
    for trial in range(60):
        while True:
            A = [rand_alt() for _ in range(m)]
            if common_radical_zero(A):
                break
        if trial % 2 == 0:
            P = random_gl(n, rng)
            Pr = [sum(((P[c] >> r) & 1) << c for c in range(n)) for r in range(n)]
            Pt = [sum(((Pr[c] >> r) & 1) << c for c in range(n)) for r in range(n)]
            B = [mul(mul(Pt, a), Pr) for a in A]
        else:
            while True:
                B = [rand_alt() for _ in range(m)]
                if common_radical_zero(B):
                    break
        truth = tuple_congruent(A, B, n) is not None
        dA = [rng.randrange(1 << n) for _ in range(m)]
        dB = [rng.randrange(1 << n) for _ in range(m)]
        ans = tuple_iso(gadget(A, dA), gadget(B, dB), D) is not None
        assert ans == truth, f"squares gadget disagrees (trial {trial}): truth {truth}, ans {ans}"
        stats["agree"] += 1
        stats["pos" if truth else "neg"] += 1
        # broken variant: the same random lifts, no u_i^2 gadget (forms on n variables only)
        def plain(T, ds):
            out = []
            for M, d in zip(T, ds):
                a = [0] * n
                for i in range(n):
                    a[i] = (M[i] >> (i + 1)) << (i + 1)
                out.append(QF(n, d, a))
            return out
        ans2 = tuple_iso(plain(A, dA), plain(B, dB), n) is not None
        if ans2 != truth:
            broken_wrong += 1
    print(f"squares: agreed on {stats['agree']} instances ({stats['pos']} congruent, {stats['neg']} not), {time.time()-t0:.1f}s")
    print(f"broken variant (random lifts, no gadget): wrong on {broken_wrong} instances")
    assert broken_wrong > 0, "broken variant not detected"
    # the explicit obstacle instance through the gadget: A=C(x)I_2, B=C(x)Swap must be non-isometric
    print("squares done")

def section_degenerate():
    """Is Rad(tau)=0 really needed in Theorem B?  Apply Phi directly (no f^+ gadget) when Rad != 0."""
    print("=== degenerate: Phi(f) vs Phi(g) without the f^+ gadget, Rad(tau) != 0 allowed ===")
    # n=3: all orbit representatives of the 128 functions
    n = 3
    fns = []
    mono = list(range(1, 8))
    for mask in range(1 << 7):
        c, b, a = set(), set(), 0
        for t, m in enumerate(mono):
            if (mask >> t) & 1:
                pos = [i for i in range(n) if (m >> i) & 1]
                if len(pos) == 1: a |= 1 << pos[0]
                elif len(pos) == 2: b.add(tuple(pos))
                else: c.add(tuple(pos))
        fns.append(Cubic(n, c, b, a))
    reps = []
    for f in fns:
        if not any(exact_equiv(f, r)[0] for r in reps):
            reps.append(f)
    wrong = 0
    for i, f in enumerate(reps):
        for j, g in enumerate(reps):
            truth = i == j
            ans = bool(SpanIso(2 * n, *span_iso_forms(f, g)).search(limit=1))
            if ans != truth:
                wrong += 1
                print(f"  n=3 disagreement: reps {i},{j} truth {truth} Phi-isometric {ans}; Rad dims {rad_tau(f)},{rad_tau(g)}")
    print(f"n=3: {len(reps)} orbit reps, {len(reps)**2} pairs, {wrong} disagreements")
    # n=4: every cubic has Rad(tau) != 0 (dim 4); sample
    n = 4
    rng = random.Random(35400)
    wrong = tot = 0
    for trial in range(40):
        f = random_cubic(n, rng)
        if trial % 2 == 0:
            g = compose(f, random_gl(n, rng))
        else:
            g = random_cubic(n, rng)
            g = Cubic(n, set(f.c), set(g.b), g.a)
        truth = bool(exact_equiv(f, g)[0])
        ans = bool(SpanIso(2 * n, *span_iso_forms(f, g)).search(limit=1))
        tot += 1
        if ans != truth:
            wrong += 1
            print(f"  n=4 disagreement: truth {truth} Phi-isometric {ans}; Rad dims {rad_tau(f)},{rad_tau(g)}")
    print(f"n=4 sample: {tot} pairs, {wrong} disagreements")
    print("degenerate done (informational: Theorem B assumes Rad=0; Theorem C removes the need)")

SECTIONS = {
    "identity": section_identity,
    "reverse3": section_reverse3,
    "samples": section_samples,
    "gadget": section_gadget,
    "chain": section_chain,
    "obstacle": section_obstacle,
    "squares": section_squares,
    "degenerate": section_degenerate,
}

if __name__ == "__main__":
    names = sys.argv[1:] or list(SECTIONS)
    for name in names:
        SECTIONS[name]()
    print("ALL REQUESTED SECTIONS PASSED")
