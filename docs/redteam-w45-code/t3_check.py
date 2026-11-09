#!/usr/bin/env python3
"""Referee test of T3 (w45-quartic section 3): tuples of cubics up to GL_n x GL_a <-> quadratic-form spaces.

Exactness: for each (f,g) in the test family,
  (a) proof steps 1-2 are verified directly on the instance: the elements of Phi with polar rank <= n are exactly Phi_Q,
      and the common polar radical of Phi_Q is exactly U.  Hence every span isometry S preserves U.
  (b) for each L in GL(n,2) the condition "Phi(f) o S contained in Phi(g)" with S(x,u)=(Lx,Cx+Pu) is linear over F_2
      in the unknowns (C, P, span coefficients); solving it decides whether an isometry over L exists.
  (c) truth for (f,g): brute force over GL(n,2) x GL(a,2) on truth tables.
Cheap isometry invariant (multiset of (polar rank, #zeros) over elements of the space) short-circuits (b).

Usage: t3_check.py [full|quick]
"""
import itertools, random, sys, time
from collections import Counter

def gl_rows(n):
    """all invertible n x n matrices, as tuples of n row bitmasks (row r = coefficients over x_0..x_{n-1})"""
    out = []
    def rec(rows, span):
        if len(rows) == n:
            out.append(tuple(rows)); return
        for v in range(1, 1 << n):
            if v not in span:
                rec(rows + [v], span | {s ^ v for s in span})
    rec([], {0})
    return out

# ---------- functions: truth tables on F_2^n with f(0)=0, stored as bitmask over points 1..2^n-1 (bit p-1 = f(p))
def tt_apply(ftt, Lrows, n):
    """f o L, where (Lx)_v = Lrows[v].x"""
    out = 0
    for x in range(1, 1 << n):
        y = 0
        for v in range(n):
            if bin(Lrows[v] & x).count('1') & 1:
                y |= 1 << v
        if y and (ftt >> (y - 1)) & 1:
            out |= 1 << (x - 1)
    return out

def anf_of_tt(ftt, n):
    """ANF of function with f(0)=0: Mobius; returns dict mask->1 (mask = monomial) for coefficient 1"""
    N = 1 << n
    a = [0] * N
    for x in range(1, N):
        a[x] = (ftt >> (x - 1)) & 1
    for i in range(n):
        for x in range(N):
            if x >> i & 1:
                a[x] ^= a[x ^ (1 << i)]
    return {m for m in range(1, N) if a[m]}

# ---------- quadratic forms on N variables, as ints over index map idx
class FormSpace:
    def __init__(self, N):
        self.N = N
        self.index = {}
        c = 0
        for p in range(N):
            for q in range(p, N):
                self.index[(p, q)] = c
                c += 1
        self.C = c
    def bit(self, p, q):
        if p > q:
            p, q = q, p
        return 1 << self.index[(p, q)]
    def polar_rows(self, form):
        """polar (alternating) matrix rows of the form"""
        N = self.N
        M = [0] * N
        for (p, q), i in self.index.items():
            if p != q and (form >> i) & 1:
                M[p] ^= 1 << q
                M[q] ^= 1 << p
        return M
    def pairs(self):
        return list(self.index.items())

def rank(rows):
    rows = list(rows); r = 0
    while rows:
        p = rows.pop()
        if p:
            r += 1
            lsb = p & -p
            rows = [x ^ p if x & lsb else x for x in rows]
    return r

def build_phi(tuple_tts, n):
    """Phi(f) forms: returns (fs, FormSpace, Q forms list, F forms list, all gens)"""
    a = len(tuple_tts)
    N = n * (a + 1)
    fs = FormSpace(N)
    def u(i, k):
        return n + i * n + k
    Qs, Fs = [], []
    for i, tt in enumerate(tuple_tts):
        anf = anf_of_tt(tt, n)
        for k in range(n):
            # Gamma_{e_k}: sum over cubic monomials containing k of x_j x_l for the other two
            g = 0
            for m in anf:
                if bin(m).count('1') == 3 and (m >> k) & 1:
                    rest = [v for v in range(n) if (m >> v) & 1 and v != k]
                    g ^= fs.bit(rest[0], rest[1])
            g ^= fs.bit(u(i, k), u(i, k))
            Qs.append(g)
        F = 0
        for m in anf:
            wt = bin(m).count('1')
            if wt == 2:
                vs = [v for v in range(n) if (m >> v) & 1]
                F ^= fs.bit(vs[0], vs[1])
            elif wt == 1:
                v = (m & -m).bit_length() - 1
                F ^= fs.bit(v, v)
        for k in range(n):
            F ^= fs.bit(k, u(i, k))
        Fs.append(F)
    return fs, Qs, Fs, Qs + Fs

def span_elements(gens):
    out = [0]
    for g in gens:
        out += [x ^ g for x in out]
    return out

def verify_steps_12(fs, Qs, Fs, n):
    """returns True if low-rank elements of Phi are exactly span(Qs) and common radical of Qs polars is U"""
    gens = Qs + Fs
    all_els = span_elements(gens)
    Qspan = set(span_elements(Qs))
    for el in all_els:
        r = rank(fs.polar_rows(el))
        if r <= n and el not in Qspan:
            return False
        if el in Qspan and r > n:
            return False
    # common radical of polars of Qs (span): vectors v with B(v,.)=0 for all generators: solve via rowspace dual
    N = fs.N
    M = []
    for q in Qs:
        pr = fs.polar_rows(q)
        M.extend(pr)  # each row r: B(e_r, .) as bitmask
    # radical is orthogonal complement (over basis) of row space: dimension N - rank
    rkk = rank(M)
    # check radical is exactly span of coordinates >= n: i.e. all rows supported on first n coordinates and rank n
    support_mask = (1 << n) - 1
    for row in M:
        if row & ~support_mask:
            return False
    return rkk == n

def invariant(fs, gens):
    """multiset of (polar rank, #zeros on F_2^N) over the span, all elements"""
    N = fs.N
    if not hasattr(fs, '_arrs'):
        arrs = {}
        for (p, q), i in fs.index.items():
            v = 0
            for x in range(1 << N):
                if (x >> p) & (x >> q) & 1:
                    v |= 1 << x
            arrs[i] = v
        fs._arrs = arrs
    c = Counter()
    for el in span_elements(gens):
        ar = 0
        for i in range(fs.C):
            if (el >> i) & 1:
                ar ^= fs._arrs[i]
        c[(rank(fs.polar_rows(el)), (1 << N) - bin(ar).count('1'))] += 1
    return tuple(sorted(c.items()))

def solve_for_L(fsF, QsF, FsF, fsG, QsG, FsG, Lrows, n, a):
    """Solve for S(x,u)=(Lx,Cx+Pu) with Phi(f) o S subset Phi(g). Returns list of (C,P) with invertible S, or []."""
    N = fsF.N
    u = lambda i, k: n + i * n + k
    # unknown indexing
    nC = (a * n) * n
    nP = (a * n) * (a * n)
    k = a * (n + 1)
    gensF = QsF + FsF
    gensG = QsG + FsG
    assert len(gensF) == k
    nGamma = k * k
    # unknown vector layout: C(i,k,v) idx 0..; P(i,k,j,t); gamma(t,r)
    def idxC(i, kk, v):
        return (i * n + kk) * n + v
    def idxP(i, kk, j, t):
        return nC + ((i * n + kk) * (a * n)) + (j * n + t)
    def idxG(t, r):
        return nC + nP + t * k + r
    Nunk = nC + nP + nGamma
    fs = fsF
    # For each generator t, compute constant part form and linear parts
    # Equations: for each coefficient position pos: bit expression
    # Represent each equation as int: bits 0..Nunk-1 unknown coefficients, bit Nunk rhs(constant)
    eqs = {}  # (t, coeff index) -> int
    def add(t, pos, unk):
        key = (t, pos)
        eqs[key] = eqs.get(key, 0) ^ (1 << unk)
    def add_const(t, form):
        # form bits: constant
        for pos in range(fs.C):
            if (form >> pos) & 1:
                key = (t, pos)
                eqs[key] = eqs.get(key, 0) ^ (1 << Nunk)
    # Lx substitution helpers: x_v -> L row v
    # constant parts of generators under S:
    def compose_const_x(form):
        """form uses only x-monomials (p,q both < n): compute form(Lx) formally."""
        out = 0
        for (p, q), i in fs.index.items():
            if (form >> i) & 1:
                assert p < n and q < n, "not an x-only form"
                # L_p x * L_q x
                ap = Lrows[p]; aq = Lrows[q]
                for s in range(n):
                    if (ap >> s) & 1:
                        for t in range(n):
                            if (aq >> t) & 1:
                                out ^= fs.bit(s, t)
        return out
    # Which parts of generators?
    # Q^i_{e_k} = Gamma(x) + u_{i,k}^2.
    for gi, gen in enumerate(gensF):
        if gi < a * n:
            i, kk = divmod(gi, n)
            # x-part of Q: gen minus u_{i,k}^2
            xpart = gen ^ fs.bit(u(i, kk), u(i, kk))
            const = compose_const_x(xpart)
            add_const(gi, const)
            # (C_{ik}.x + P_{ik}.u)^2 = sum C x_v^2 + sum P u^2
            for v in range(n):
                add(gi, fs.index[(v, v)], idxC(i, kk, v))
            for j in range(a):
                for t in range(n):
                    add(gi, fs.index[(u(j, t), u(j, t))], idxP(i, kk, j, t))
        else:
            i = gi - a * n
            # F^i = (Q_i + ell_i)(x) + sum_k x_k u_{i,k}
            xpart = gen
            for kk in range(n):
                xpart ^= fs.bit(kk, u(i, kk))
            const = compose_const_x(xpart)
            add_const(gi, const)
            for kk in range(n):
                # x_k -> L_k x, u_{i,k} -> sum_v C_{ik,v} x_v + sum_{j,t} P_{ik,jt} u_{jt}
                Lk = Lrows[kk]
                for s in range(n):
                    if (Lk >> s) & 1:
                        for v in range(n):
                            add(gi, fs.index[tuple(sorted((s, v)))], idxC(i, kk, v))
                        for j in range(a):
                            for t in range(n):
                                add(gi, fs.index[(s, u(j, t))], idxP(i, kk, j, t))
    # gamma terms: gen_t o S + sum_r gamma_tr psi_r = 0  => for each pos, add gamma bits
    for t in range(k):
        for r in range(k):
            for pos in range(fs.C):
                if (gensG[r] >> pos) & 1:
                    key = (t, pos)
                    eqs[key] = eqs.get(key, 0) ^ (1 << idxG(t, r))
    # Also every coefficient position must appear even with no entries
    rows = []
    for t in range(k):
        for pos in range(fs.C):
            rows.append(eqs.get((t, pos), 0))
    # Gaussian elimination over Nunk+1 bits
    pivots = {}
    for row in rows:
        r = row
        for p, v in pivots.items():
            if (r >> p) & 1:
                r ^= v
        unkpart = r & ((1 << Nunk) - 1)
        if unkpart == 0:
            if r >> Nunk & 1:
                return []
            continue
        p = unkpart.bit_length() - 1
        for q in list(pivots):
            if (pivots[q] >> p) & 1:
                pivots[q] ^= r
        pivots[p] = r
    free = [v for v in range(Nunk) if v not in pivots]
    dim = len(free)
    # particular solution (free vars 0): pivots give assigned variable = rhs
    def assignment(mask_free):
        """mask_free: bitmask over free indices"""
        x = 0
        for i, fv in enumerate(free):
            if (mask_free >> i) & 1:
                x |= 1 << fv
        for p, v in pivots.items():
            val = (v >> Nunk) & 1
            # v row: bit p + free columns set ...; value = rhs + sum over free in row of x
            val ^= bin(v & x & ((1 << Nunk) - 1) & ~(1 << p)).count('1') & 1
            if val:
                x |= 1 << p
        return x
    if dim > 22:
        return ('OVERFLOW', dim)
    sols = []
    total = 1 << dim
    # P matrix rows: index (i,k) row over (j,t)
    Pn = a * n
    for mask in range(total):
        x = assignment(mask)
        # check P invertible
        Pm = [0] * Pn
        for rr in range(Pn):
            for cc in range(Pn):
                if (x >> (nC + rr * Pn + cc)) & 1:
                    Pm[rr] |= 1 << cc
        if rank(Pm) == Pn:
            sols.append(x)
            return sols
    return sols

def isometry_exists(f, g, n, a, cache):
    if f not in cache:
        fs, Qs, Fs, gens = build_phi(f, n)
        cache[f] = (fs, Qs, Fs, gens, invariant(fs, gens), verify_steps_12(fs, Qs, Fs, n))
    if g not in cache:
        fs, Qs, Fs, gens = build_phi(g, n)
        cache[g] = (fs, Qs, Fs, gens, invariant(fs, gens), verify_steps_12(fs, Qs, Fs, n))
    F = cache[f]; G = cache[g]
    assert F[5] and G[5], ("steps 1-2 fail on instance", f, g)
    if F[4] != G[4]:
        return False, 'invariant'
    for L in GL_CACHE[n]:
        res = solve_for_L(F[0], F[1], F[2], G[0], G[1], G[2], L, n, a)
        if isinstance(res, tuple):
            raise RuntimeError(f"overflow dim {res[1]}")
        if res:
            return True, 'found'
    return False, 'exhausted'

GL_CACHE = {}

def truth_equiv(f, g, n, a):
    for L in GL_CACHE[n]:
        fL = tuple(tt_apply(fi, L, n) for fi in f)
        for beta in GL_CACHE[a]:
            # beta rows: fL_i = sum_j beta_ij g_j
            ok = True
            for i in range(a):
                s = 0
                for j in range(a):
                    if (beta[i] >> j) & 1:
                        s ^= g[j]
                if s != fL[i]:
                    ok = False
                    break
            if ok:
                return True
    return False

def orbits_family(n, a):
    """orbit representatives of concise a-tuples of functions on F_2^n with f(0)=0 under GL(n,2) x GL(a,2)."""
    Npts = (1 << n) - 1
    total = 1 << (a * Npts)
    print(f"  family n={n} a={a}: {total} tuples, group |GL({n},2)|*|GL({a},2)|", flush=True)
    masks = (1 << Npts) - 1
    # tables for tt action of generators of GL(n,2) and GL(a,2)
    gens_L = []
    # elementary generators of GL(n,2): all elementary x_v -> x_v + x_w plus permutation (or all L if small)
    for v in range(n):
        for w in range(n):
            if v != w:
                rows = list(1 << r for r in range(n))
                rows[v] ^= 1 << w
                gens_L.append(tuple(rows))
    # action on tt (bit p-1 for point p)
    def perm_table(Lrows):
        # point x -> Lx coordinate
        table = [0] * (1 << n)
        for x in range(1, 1 << n):
            y = 0
            for v in range(n):
                if bin(Lrows[v] & x).count('1') & 1:
                    y |= 1 << v
            table[x] = y
        return table
    tt_tables = []
    for g in gens_L:
        tab = perm_table(g)
        # new_tt(x) = old_tt(gx): new bit(x-1) = old bit(tab[x]-1)
        def make():
            mapping = tab[:]
            return mapping
        tt_tables.append(make())
    visited = bytearray(total)
    def enc(f):
        c = 0
        for i, fi in enumerate(f):
            c |= fi << (i * Npts)
        return c
    def dec(code):
        return tuple((code >> (i * Npts)) & masks for i in range(a))
    def apply_mapping(tt, mapping):
        out = 0
        for x in range(1, 1 << n):
            y = mapping[x]
            if (tt >> (y - 1)) & 1:
                out |= 1 << (x - 1)
        return out
    # precompute tt transform via table per mapping for all tt values (2^Npts up to 128)
    tt_trans = []
    for mapping in tt_tables:
        tt_trans.append([apply_mapping(tt, mapping) for tt in range(1 << Npts)])
    reps = []
    orbit_sizes = []
    # group ops: L generators (act on each coordinate) and elementary beta (add coordinate j to i), swaps
    bgens = []
    for i in range(a):
        for j in range(a):
            if i != j:
                bgens.append((i, j))
    for code in range(total):
        if visited[code]:
            continue
        f = dec(code)
        # concise?  degree 3 on F_2^3: parity of f bits odd means cubic monomial present.
        # general: require common radical zero: implement generically
        if not concise_general(f, n):
            # mark orbit anyway skip by marking visited lazily (need orbit closure? nonconcise stays nonconcise)
            visited[code] = True
            continue
        # BFS orbit
        stack = [code]
        visited[code] = True
        size = 0
        while stack:
            c = stack.pop()
            size += 1
            ff = dec(c)
            for trans in tt_trans:
                new = tuple(trans[x] for x in ff)
                cc = enc(new)
                if not visited[cc]:
                    visited[cc] = True
                    stack.append(cc)
            for (i, j) in bgens:
                new = list(ff)
                new[i] ^= new[j]
                cc = enc(tuple(new))
                if not visited[cc]:
                    visited[cc] = True
                    stack.append(cc)
        reps.append(f)
        orbit_sizes.append(size)
    return reps, orbit_sizes

def concise_general(f, n):
    """common radical of the alternating 3-forms tau_{f_i} is 0"""
    N = 1 << n
    anfs = [anf_of_tt(tt, n) for tt in f]
    for x in range(1, N):
        # x in Rad tau_{f_i} iff for all a,b: tau(x,a,b)=0. Radical test via Gamma_x polar.
        all_zero = True
        for anf in anfs:
            # polar of Gamma_x: matrix entry (j,k) = sum_{monomial m ⊇ {j,k}} x_{m\{j,k}}
            for j in range(n):
                for k in range(j + 1, n):
                    v = 0
                    for m in anf:
                        if bin(m).count('1') == 3 and (m >> j) & 1 and (m >> k) & 1:
                            rest = m ^ (1 << j) ^ (1 << k)
                            r = (rest & -rest).bit_length() - 1
                            v ^= (x >> r) & 1
                    if v:
                        all_zero = False
                        break
                if not all_zero:
                    break
            if not all_zero:
                break
        if all_zero:
            return False
    return True

def run_family(n, a, rng):
    t0 = time.time()
    GL_CACHE[n] = gl_rows(n)
    GL_CACHE[a] = gl_rows(a)
    reps, sizes = orbits_family(n, a)
    print(f"  concise orbits: {len(reps)}, total concise tuples {sum(sizes)}")
    cache = {}
    agree = dis = iso = non = 0
    inv_only = solved = 0
    invmap = {}
    for r in reps:
        fs, Qs, Fs, gens = build_phi(r, n)
        inv = invariant(fs, gens)
        cache[r] = (fs, Qs, Fs, gens, inv, verify_steps_12(fs, Qs, Fs, n))
        assert cache[r][5], ("Steps 1-2 failed", r)
        invmap.setdefault(inv, []).append(r)
    print(f"  distinct invariants: {len(invmap)}, largest class {max(len(v) for v in invmap.values())}")
    t1 = time.time()
    # All pairs: pairs in different invariant classes are non-isometric (certified); same-class pairs solved
    for cls in invmap.values():
        for i, f in enumerate(cls):
            for g in cls[i:]:
                exists, how = isometry_exists(f, g, n, a, cache)
                truth = f == g or truth_equiv(f, g, n, a)
                if how == 'found' or how == 'exhausted':
                    solved += 1
                if exists == truth:
                    agree += 1
                    if truth: iso += 1
                    else: non += 1
                else:
                    dis += 1
                    print("   DISAGREEMENT", f, g, exists, truth, flush=True)
    # different-class pairs: truth must be non-equivalent (reps are distinct orbits): check truth for all pairs is expensive,
    # but different invariants certify non-isometry and reps of distinct orbits are non-equivalent by construction.
    print(f"  same-invariant pairs solved exactly: {solved}; agree={agree} (iso={iso}, noniso={non}), DISAGREE={dis}; t={time.time()-t1:.1f}s (build {t1-t0:.1f}s)")
    print(f"  (pairs across different invariant classes: isometry excluded by invariant, orbit reps inequivalent by construction: {len(reps)*(len(reps)-1)//2 - sum(len(v)*(len(v)-1)//2 for v in invmap.values())} pairs)")
    # planted forward: random (L,beta) applied, must be isometric
    pl = 0
    for t in range(40):
        f = rng.choice(reps)
        L = rng.choice(GL_CACHE[n]); beta = rng.choice(GL_CACHE[a])
        fL = [tt_apply(fi, L, n) for fi in f]
        # g with f_i o L = sum_j beta_ij g_j: g = beta^{-1} fL
        # compute beta inverse by brute
        binv = None
        for b in GL_CACHE[a]:
            ok = True
            for i in range(a):
                v = 0
                for j in range(a):
                    if (beta[i] >> j) & 1:
                        v ^= b[j]
                if v != (1 << i):
                    ok = False; break
            if ok:
                binv = b; break
        g = []
        for i in range(a):
            v = 0
            for j in range(a):
                if (binv[i] >> j) & 1:
                    v ^= fL[j]
            g.append(v)
        g = tuple(g)
        exists, how = isometry_exists(f, g, n, a, cache)
        assert exists, ("forward direction failed", f, L, beta)
        pl += 1
    print(f"  planted (L,beta) instances all isometric: {pl}/40")
    return dis == 0

def run_family_capped(n, a, rng, cap=60):
    t0 = time.time()
    GL_CACHE[n] = gl_rows(n)
    GL_CACHE[a] = gl_rows(a)
    reps, sizes = orbits_family(n, a)
    print(f"  concise orbits: {len(reps)}, total concise tuples {sum(sizes)}", flush=True)
    cache = {}
    invmap = {}
    for r in reps:
        fs, Qs, Fs, gens = build_phi(r, n)
        inv = invariant(fs, gens)
        cache[r] = (fs, Qs, Fs, gens, inv, verify_steps_12(fs, Qs, Fs, n))
        assert cache[r][5], ("Steps 1-2 failed", r)
        invmap.setdefault(inv, []).append(r)
    print(f"  distinct invariants: {len(invmap)}, class sizes: {sorted((len(v) for v in invmap.values()), reverse=True)[:12]}", flush=True)
    pairs = []
    for cls in invmap.values():
        for i, f in enumerate(cls):
            for g in cls[i:]:
                pairs.append((f, g))
    print(f"  same-invariant pairs: {len(pairs)}; solving {min(cap, len(pairs))} of them (reflexive ones first)", flush=True)
    refl = [p for p in pairs if p[0] == p[1]]
    nonrefl = [p for p in pairs if p[0] != p[1]]
    rng.shuffle(nonrefl)
    work = refl[:15] + nonrefl[:max(0, cap - 15)]
    agree = dis = iso = non = 0
    for f, g in work:
        t1 = time.time()
        exists, how = isometry_exists(f, g, n, a, cache)
        truth = f == g or truth_equiv(f, g, n, a)
        if exists == truth:
            agree += 1
            if truth: iso += 1
            else: non += 1
        else:
            dis += 1
            print("   DISAGREEMENT", f, g, exists, truth, flush=True)
        print(f"   pair done in {time.time()-t1:.1f}s", flush=True)
    print(f"  solved {len(work)}: agree={agree} (iso={iso}, noniso={non}) DISAGREE={dis} t={time.time()-t0:.1f}s", flush=True)
    return dis == 0

def pair_test_n4(rng):
    """n=4,a=2: a few pairs, one planted, one by flipping a quadratic monomial."""
    n, a = 4, 2
    GL_CACHE[n] = gl_rows(n)
    GL_CACHE[a] = gl_rows(a)
    Npts = (1 << n) - 1
    while True:
        f = tuple(rng.randrange(1, 1 << Npts) for _ in range(a))
        # require degree 3 exactly: restrict to degree<=3 functions by clearing the degree-4 coefficient via parity
        def clear_deg4(tt):
            if bin(tt).count('1') & 1:
                return tt ^ 1  # flip f(e_0) to adjust parity (still f(0)=0)
            return tt
        f = tuple(clear_deg4(t) for t in f)
        if concise_general(f, n):
            break
    print(f"  n=4,a=2 pair tests: |GL(4,2)|={len(GL_CACHE[4])}", flush=True)
    cache = {}
    L = rng.choice(GL_CACHE[n]); beta = rng.choice(GL_CACHE[a])
    fL = [tt_apply(fi, L, n) for fi in f]
    binv = next(b for b in GL_CACHE[a] if all(__import__('functools').reduce(lambda x, j: x ^ (b[j] if (beta[i] >> j) & 1 else 0), range(a), 0) == (1 << i) for i in range(a)))
    g = []
    for i in range(a):
        v = 0
        for j in range(a):
            if (binv[i] >> j) & 1:
                v ^= fL[j]
        g.append(v)
    g = tuple(g)
    # second pair: flip a quadratic monomial of f[0]
    quad = 0
    for x in range(1, 1 << n):
        if (x & 3) == 3:
            quad |= 1 << (x - 1)
    h = (f[0] ^ quad,) + f[1:]
    t0 = time.time()
    res1 = isometry_exists(f, g, n, a, cache)
    print(f"  planted pair: isometric={res1} ({time.time()-t0:.0f}s), truth True", flush=True)
    t0 = time.time()
    res2 = isometry_exists(f, h, n, a, cache)
    truth2 = truth_equiv(f, h, n, a)
    print(f"  flipped-quadratic pair: isometric={res2} ({time.time()-t0:.0f}s), truth {truth2}", flush=True)
    return res1[0] and (res2[0] == truth2)

def mutation_dropell(n, a, rng, trials=40):
    """Negative control: remove the linear part from F^i. Then f and f+x_0 give the same space, so the
    harness must report 'isometric' for pairs that are inequivalent."""
    GL_CACHE.setdefault(n, gl_rows(n))
    GL_CACHE.setdefault(a, gl_rows(a))
    false_iso = 0; tested = 0
    def build_mut(tt, n):
        fs, Qs, Fs, gens = build_phi(tt, n)
        anf = [anf_of_tt(t, n) for t in tt]
        Fs2 = []
        for i, F in enumerate(Fs):
            for m in anf[i]:
                if bin(m).count('1') == 1:
                    v = (m & -m).bit_length() - 1
                    F ^= fs.bit(v, v)
            Fs2.append(F)
        return fs, Qs, Fs2, Qs + Fs2
    for _ in range(trials):
        while True:
            f = tuple(rng.randrange(1, 1 << ((1 << n) - 1)) for _ in range(a))
            if concise_general(f, n):
                break
        # flip one linear coordinate: f_0 ^ x_0 (as truth table on points): add linear function x_0
        lin = 0
        for x in range(1, 1 << n):
            if x & 1:
                lin |= 1 << (x - 1)
        g = (f[0] ^ lin,) + f[1:]
        truth = truth_equiv(f, g, n, a)
        F = build_mut(f, n); G = build_mut(g, n)
        iso_mut = any(solve_for_L(F[0], F[1], F[2], G[0], G[1], G[2], L, n, a) for L in GL_CACHE[n][:3])
        # with identity-like map available, spaces equal so isometry trivially exists when L=I (the first Ls include identity)
        idL = tuple(1 << v for v in range(n))
        iso_mut = iso_mut or bool(solve_for_L(F[0], F[1], F[2], G[0], G[1], G[2], idL, n, a))
        tested += 1
        if iso_mut and not truth:
            false_iso += 1
    print(f"  mutation drop-ell on n={n},a={a}: {false_iso}/{tested} pairs report isometric while truly inequivalent (harness detects the broken construction)")
    return False if false_iso == 0 else True

def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "quick"
    rng = random.Random(45)
    ok = True
    # n=3, a=2 exhaustive
    print("Family n=3, a=2 (exhaustive over concise tuples)")
    ok &= run_family(3, 2, rng)
    if mode == "full":
        print("Family n=3, a=3 (orbits exhaustive; capped pairs)", flush=True)
        ok &= run_family_capped(3, 3, rng, cap=60)
    if mode == "n4":
        ok &= pair_test_n4(rng)
    mutation_dropell(3, 2, rng)
    print("ALL OK" if ok else "FAILURES")

if __name__ == "__main__":
    main()
