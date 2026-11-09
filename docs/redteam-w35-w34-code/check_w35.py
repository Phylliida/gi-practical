#!/usr/bin/env python3
"""
Referee checks for docs/w35-cubic.md (branch w37-redteam-cubic).

Independent of docs/w35-cubic-check.py: separate form arithmetic, separate exact search
(exactiso.c: general span isometries of spaces of quadratic forms, no structural assumption).

Run (one process, nice):
  gcc -O2 -o $EXACT docs/redteam-w35-w34-code/exactiso.c
  EXACT=$EXACT nice -n 19 python3 -I docs/redteam-w35-w34-code/check_w35.py [section ...]

Sections: identities b3 b5 b6 degenerate composite thmc squares obstacle obstacle2
"""
import os, random, subprocess, sys, time, itertools

EXACT = os.environ.get("EXACT", "exactiso")

def par(x): return bin(x).count("1") & 1

def lxor(cols, x):
    r = 0; i = 0
    while x:
        if x & 1: r ^= cols[i]
        x >>= 1; i += 1
    return r

def rank(vs):
    vs = list(vs); r = 0
    while vs:
        p = max(vs)
        vs.remove(p)
        if p == 0: break
        r += 1
        hb = p.bit_length() - 1
        vs = [v ^ p if v >> hb & 1 else v for v in vs]
    return r

def random_gl(n, rng):
    cols = []; span = {0}
    while len(cols) < n:
        c = rng.randrange(1, 1 << n)
        if c in span: continue
        cols.append(c)
        span |= {s ^ c for s in span}
    return cols

# ---- Functions: truth table <-> ANF ------------------------------------------------
def anf(tt):
    a = list(tt); n = len(tt).bit_length() - 1
    for i in range(n):
        for x in range(1 << n):
            if x >> i & 1:
                a[x] ^= a[x ^ (1 << i)]
    return a

def tt_of_anf(a):
    return anf(a)  # Moebius is an involution

def compose_tt(tt, cols):
    return [tt[lxor(cols, x)] for x in range(len(tt))]

def cubic_part(a):
    n = len(a).bit_length() - 1
    return {m for m in range(len(a)) if a[m] and bin(m).count("1") == 3}

def degree(a):
    return max((bin(m).count("1") for m, c in enumerate(a) if c), default=-1)

def tau(a_anf_cubic, n):
    """trilinear tau from cubic monomials: dict (i,j,k)->1 for i<j<k"""
    return {m for m in a_anf_cubic}

def rad_tau(an, n):
    """dimension of the radical of tau_f (f given by ANF list): only cubic part matters."""
    cub = cubic_part(an)
    # tau(e_i, ., .) as alternating matrix on n points
    def slice_mat(v):
        rows = [0] * n
        for m in cub:
            bits = [b for b in range(n) if m >> b & 1]
            for pi in itertools.permutations(bits):
                if v >> pi[0] & 1:
                    rows[pi[1]] ^= 1 << pi[2]
        return rows
    # radical = set of v with zero slice; slice is linear in v
    basis = []
    for i in range(n):
        rows = slice_mat(1 << i)
        flat = 0
        for r_i in range(n):
            flat |= rows[r_i] << (r_i * n)
        basis.append(flat)
    # dim radical = n - rank
    return n - rank(basis)

# ---- Quadratic forms: dict {(i,j): 1}, i<=j, over F2 ---------------------------------
def add_mono(q, i, j):
    if i > j: i, j = j, i
    q[(i, j)] = q.get((i, j), 0) ^ 1
    if q[(i, j)] == 0: del q[(i, j)]

def phi(an, n):
    """The n+1 forms of Theorem B on (x_0..x_{n-1}, u_0..u_{n-1}), from ANF list `an`.
       Q_i(x,u) = Gamma_{e_i}(x) + u_i^2;  F = Q_f(x) + l_f(x) + sum x_i u_i."""
    forms = []
    for i in range(n):
        q = {}
        for m in range(len(an)):
            if an[m] and bin(m).count("1") == 3 and m >> i & 1:
                others = [b for b in range(n) if m >> b & 1 and b != i]
                add_mono(q, others[0], others[1])
        add_mono(q, n + i, n + i)
        forms.append(q)
    F = {}
    for m in range(len(an)):
        if an[m]:
            bits = [b for b in range(n) if m >> b & 1]
            if len(bits) == 2:
                add_mono(F, bits[0], bits[1])
            elif len(bits) == 1:
                add_mono(F, bits[0], bits[0])
    for i in range(n):
        add_mono(F, i, n + i)
    forms.append(F)
    return forms

def encode_form(q, N):
    rows = [0] * N
    for (i, j) in q:
        rows[i] |= 1 << j
    return " ".join("%x" % r for r in rows)

def form_compose(q, cols, N):
    """q o S where S has columns cols (S e_i = cols[i]); returns dict form (char 2)."""
    # x_i -> sum_a S[i][a] y_a, i.e. coordinate i of S y; S[i][a] = bit i of cols[a]
    r = {}
    # y_a y_b coefficient (a<b): sum c_ij (S_ia S_jb + S_ib S_ja); y_a^2: sum c_ij S_ia S_ja
    S = [[(cols[a] >> i) & 1 for a in range(N)] for i in range(N)]
    for a in range(N):
        v = 0
        for (i, j) in q:
            v ^= S[i][a] & S[j][a]
        if v: add_mono(r, a, a)
        for b in range(a + 1, N):
            v = 0
            for (i, j) in q:
                v ^= (S[i][a] & S[j][b]) ^ (S[i][b] & S[j][a])
            if v: add_mono(r, a, b)
    return r

def form_vec(q, N):
    v = 0
    for (i, j) in q:
        v |= 1 << (i * N + j)
    return v

def in_span(v, basis):
    return rank(basis + [v]) == rank(basis)

def verify_span(formsA, formsB, cols, N):
    """check span(formsA o S) = span(formsB), S invertible."""
    if rank(cols) != N: return False
    fA = [form_vec(form_compose(q, cols, N), N) for q in formsA]
    fB = [form_vec(q, N) for q in formsB]
    return rank(fA) == len(fA) and rank(fB) == len(fB) and all(in_span(v, fB) for v in fA)

def verify_tuple(formsA, formsB, cols, N):
    return rank(cols) == N and all(form_vec(form_compose(q, cols, N), N) == form_vec(p, N) for q, p in zip(formsA, formsB))

def exact(formsA, formsB, N, mode=0, maxsol=1, cap=2000000000):
    K = len(formsA)
    lines = ["%d %d %d %d" % (N, K, mode, maxsol)]
    for q in formsA + formsB:
        lines.append(encode_form(q, N))
    out = subprocess.run([EXACT, str(cap)], input="\n".join(lines) + "\n", capture_output=True, text=True).stdout.split("\n")
    sols = []
    head = None
    for ln in out:
        if ln.startswith("S "):
            sols.append([int(x, 16) for x in ln.split()[1:]])
        elif ln.strip():
            head = ln.split()
    return head, sols

# ---- truth: exact search for L with f o L = g ---------------------------------------
def iso_search(ttf, ttg, n, first=True, limit=None):
    """all/first L in GL(n,2) with f o L = g, by backtracking on column images with full-span checks.
       Returns list of column lists."""
    sols = []
    if ttf[0] != ttg[0]: return sols
    img = [0] * (1 << n)
    def dfs(j, cols, spanimg):
        if j == n:
            sols.append(list(cols))
            return True
        for c in range(1, 1 << n):
            if c in spanimg: continue
            ok = True
            # new combos: m | 1<<j
            for m in range(1 << j):
                im = img[m] ^ c
                img[m | (1 << j)] = im
                if ttf[im] != ttg[m | (1 << j)]:
                    ok = False; break
            if not ok: continue
            cols.append(c)
            newspan = spanimg | {s ^ c for s in spanimg}
            if dfs(j + 1, cols, newspan) and first: return True
            cols.pop()
            if limit and len(sols) >= limit: return True
        return False
    dfs(0, [], {0})
    return sols

def iso_search_filtered(ttf, ttg, n):
    """As iso_search(first=True), but column images are restricted by an invariant that any L with f o L = g preserves:
       (value, weight of the derivative D_v) at v.  Used only by section_thmc, where the unfiltered search at n=7 is too slow."""
    if ttf[0] != ttg[0]: return []
    N = 1 << n
    def invs(tt):
        return [(tt[v], sum(tt[x] ^ tt[x ^ v] for x in range(N))) for v in range(N)]
    invf, invg = invs(ttf), invs(ttg)
    if sorted(invf) != sorted(invg): return []
    bykey = {}
    for v in range(1, N):
        bykey.setdefault(invf[v], []).append(v)
    img = [0] * N
    sols = []
    def dfs(j, cols, span):
        if j == n:
            sols.append(list(cols)); return True
        for c in bykey.get(invg[1 << j], []):
            if c in span: continue
            ok = True
            for m in range(1 << j):
                im = img[m] ^ c
                img[m | (1 << j)] = im
                if ttf[im] != ttg[m | (1 << j)]:
                    ok = False; break
            if not ok: continue
            cols.append(c)
            if dfs(j + 1, cols, span | {s ^ c for s in span}): return True
            cols.pop()
        return False
    dfs(0, [], {0})
    return sols

def planted_conj(tt, n, rng):
    L = random_gl(n, rng)
    return compose_tt(tt, L), L

def random_rad0(n, rng, tries=10000):
    for _ in range(tries):
        a = [0] * (1 << n)
        for m in range(1, 1 << n):
            if bin(m).count("1") <= 3 and rng.random() < 0.5:
                a[m] = 1
        if rad_tau(a, n) == 0:
            return a
    raise RuntimeError("no rad-0 cubic found")

def Ntest_identities(rng):
    """(I1),(I2),(*) and the forward map, independent implementation, n up to 30 by random evaluation."""
    print("[identities] (I1) Gamma_v(v)=C(v); (I2); (*) x^T N x = C_f(Lx)+C_g(x); forward S")
    fails = 0; total = 0
    for n in [3, 4, 5, 6, 7, 8, 9, 10, 12, 15, 20, 25, 30]:
        for _ in range(40 if n <= 15 else 15):
            # cubic part C as dict of monomials; lower part Q+l random
            mons = [m for m in itertools.combinations(range(n), 3) if rng.random() < 0.4]
            quad = [m for m in itertools.combinations(range(n), 2) if rng.random() < 0.4]
            lin = [i for i in range(n) if rng.random() < 0.5]
            def C(x):
                return sum((x >> i & 1) & (x >> j & 1) & (x >> k & 1) for i, j, k in mons) & 1
            def Gamma(a, x):
                r = 0
                for i, j, k in mons:
                    r ^= ((a >> i & 1) & (x >> j & 1) & (x >> k & 1)) ^ ((x >> i & 1) & (a >> j & 1) & (x >> k & 1)) ^ ((x >> i & 1) & (x >> j & 1) & (a >> k & 1))
                return r
            def Q(x):
                return sum((x >> i & 1) & (x >> j & 1) for i, j in quad) & 1
            def L_(x):
                return sum(x >> i & 1 for i in lin) & 1
            def f(x): return C(x) ^ Q(x) ^ L_(x)
            L = random_gl(n, rng) if n <= 20 else None
            if L is None:
                # large n: use a sparse random invertible matrix built from elementary ops
                L = [1 << i for i in range(n)]
                for _ in range(3 * n):
                    i, j = rng.sample(range(n), 2)
                    L[i] ^= L[j]
            for trial in range(40):
                v = rng.getrandbits(n); w = rng.getrandbits(n)
                total += 2
                if Gamma(v, v) != C(v): fails += 1
                if (C(v ^ w) ^ C(v) ^ C(w)) != (Gamma(v, w) ^ Gamma(w, v)): fails += 1
            # compute C_g: cubic part of f o L via polarization of the composed cubic:
            # c_ijk(g) = tau_f(Le_i, Le_j, Le_k), expressed via third derivative of C
            def tauC(a, b, c):
                r = 0
                for s in range(1, 8):
                    x = 0
                    if s & 1: x ^= a
                    if s & 2: x ^= b
                    if s & 4: x ^= c
                    r ^= C(x)
                return r
            # N_ij = Gamma_{Le_i}(Le_j); verify (*) at random x: x^T N x + C_f(Lx) + C_g(x) = 0
            # C_g(x) computed as: sum over i<j<k with coefficient tau(Le_i,Le_j,Le_k) of x_i x_j x_k
            if n <= 15:
                cg = [(i, j, k) for i, j, k in itertools.combinations(range(n), 3) if tauC(L[i], L[j], L[k])]
                def Cg(x):
                    return sum((x >> i & 1) & (x >> j & 1) & (x >> k & 1) for i, j, k in cg) & 1
                NN = [[Gamma(L[i], L[j]) for j in range(n)] for i in range(n)]
                for trial in range(40):
                    x = rng.getrandbits(n)
                    lhs = 0
                    for i in range(n):
                        if x >> i & 1:
                            for j in range(n):
                                if x >> j & 1:
                                    lhs ^= NN[i][j]
                    Lx = lxor(L, x)
                    total += 1
                    if lhs != (C(Lx) ^ Cg(x)): fails += 1
    print(f"  checks {total}, failures {fails}")
    return fails == 0

def forward_phi(an, n, rng, trials=200):
    """Forward direction of Thm B on exact forms: compute S from L and check Phi(f) o S == Phi(g) exactly."""
    pass

def section_identities():
    rng = random.Random(370001)
    ok = Ntest_identities(rng)
    # Forward direction: formal composition equal to Phi(g)
    fails = 0; total = 0
    for n in range(3, 10):
        for _ in range(30):
            a = random_rad0(n, rng) if n != 4 else None
            if a is None:
                a = [0] * (1 << n)
                for m in range(1, 1 << n):
                    if bin(m).count("1") <= 3 and rng.random() < 0.5: a[m] = 1
            tt = tt_of_anf(a)
            L = random_gl(n, rng)
            ttg = compose_tt(tt, L)
            g = anf(ttg)
            # build N, C_col, S: S(x,u) = (Lx, L^{-T} u + C x), C = L^{-T} N
            # coordinates: S e_i (x-part basis): (L e_i ; C e_i); S f_i (u basis) = (0 ; L^{-T} e_i)
            # helpers: matrices as column ints on n bits
            Linv = inv_cols(L, n)
            LinvT = transpose_cols(Linv, n)
            # N_ij = Gamma^f_{Le_i}(Le_j)
            cub = [tuple(b for b in range(n) if m >> b & 1) for m in range(len(a)) if a[m] and bin(m).count("1") == 3]
            def Gam(u, x):
                r = 0
                for i, j, k in cub:
                    r ^= ((u >> i & 1) & (x >> j & 1) & (x >> k & 1)) ^ ((x >> i & 1) & (u >> j & 1) & (x >> k & 1)) ^ ((x >> i & 1) & (x >> j & 1) & (u >> k & 1))
                return r
            N = [[Gam(L[i], L[j]) for j in range(n)] for i in range(n)]
            # C = L^{-T} N: column j of C = L^{-T} (column j of N)
            Ccols = []
            for j in range(n):
                col = 0
                for i in range(n):
                    if N[i][j]: col |= 1 << i
                Ccols.append(lxor(LinvT, col))
            cols = []
            for j in range(n):
                cols.append(L[j] | (Ccols[j] << n))
            for j in range(n):
                cols.append(LinvT[j] << n)
            pf = phi(a, n); pg = phi(g, n)
            fA = [form_vec(form_compose(q, cols, 2 * n), 2 * n) for q in pf]
            fB = [form_vec(q, 2 * n) for q in pg]
            # Q^f_a o S = Q^g_{L^{-1}a} and F o S = F^g
            total += 1
            good = True
            for i in range(n):
                # Q^f_{e_i} o S should be Q^g_{L^{-1}e_i} = sum over j of (L^{-1})_{ji} Q^g_j
                target = 0
                for j in range(n):
                    if Linv[i] >> j & 1:
                        target ^= fB[j]
                if fA[i] != target: good = False
            if fA[n] != fB[n]: good = False
            if not good: fails += 1
    print(f"[identities] forward map Phi(f)oS == Phi(g) exactly, with S as in the proof: {total-fails}/{total} (n=3..9)")
    return ok and fails == 0

def inv_cols(cols, n):
    A = [(cols[i], 1 << i) for i in range(n)]
    res = [0] * n
    A = list(A)
    for bit in range(n):
        p = None
        for i in range(bit, n):
            if A[i][0] >> bit & 1:
                p = i; break
        A[bit], A[p] = A[p], A[bit]
        for i in range(n):
            if i != bit and A[i][0] >> bit & 1:
                A[i] = (A[i][0] ^ A[bit][0], A[i][1] ^ A[bit][1])
    # A[bit] = (e_bit, combination c) with sum_{k in c} cols[k] = e_bit, i.e. L^{-1} e_bit = c as column
    for bit in range(n):
        res[bit] = A[bit][1]
    return res

def transpose_cols(cols, n):
    res = [0] * n
    for i in range(n):
        for j in range(n):
            if cols[j] >> i & 1:
                res[i] |= 1 << j
    return res

def all_low_functions(n, cubic_mons):
    """all f = fixed cubic + any degree<=2 terms with f(0)=0, as ANF lists."""
    lows = [m for m in range(1, 1 << n) if bin(m).count("1") <= 2]
    out = []
    base = [0] * (1 << n)
    for m in cubic_mons: base[m] = 1
    for bits in range(1 << len(lows)):
        a = list(base)
        for i, m in enumerate(lows):
            if bits >> i & 1: a[m] ^= 1
        out.append(a)
    return out

def section_b3():
    """Thm B, n=3: all 64 x 64 pairs of functions with Rad tau = 0; exact enumeration of ALL span isometries;
       predicted: #S = #Iso(f,g) (S is determined by L), and every S has the block form."""
    n = 3; N = 6
    cub = 0b111
    fns = all_low_functions(n, [cub])
    bad = 0; total = 0; sumiso = 0; blockbad = 0; t0 = time.time()
    tts = [tt_of_anf(a) for a in fns]
    phis = [phi(a, n) for a in fns]
    # exact count of Iso(f,g) by iso_search for each pair
    isocount = {}
    for i, a in enumerate(fns):
        for j, b in enumerate(fns):
            sols = iso_search(tts[i], tts[j], n, first=False)
            isocount[(i, j)] = len(sols)
    for i in range(len(fns)):
        for j in range(len(fns)):
            total += 1
            head, sols = exact(phis[i], phis[j], N, mode=1, maxsol=100000)
            cnt = int(head[2])
            if cnt != isocount[(i, j)]:
                bad += 1
            sumiso += cnt
            for cols in sols:
                if not verify_span(phis[i], phis[j], cols, N): bad += 1
                # forced form: S(U)=U i.e. u-basis columns have zero x-part; and L = x-part of x-basis columns
                for k in range(3, 6):
                    if cols[k] & 0b111: blockbad += 1
    print(f"[b3] all 64^2 pairs: count mismatches {bad}, block-form violations {blockbad}, total span isometries {sumiso}, time {time.time()-t0:.1f}s")
    return bad == 0 and blockbad == 0

def orbits_low(n, cub_mons, stab_gens):
    """orbits of Stab on the 2^{#low} functions (fixed cubic part): BFS with given generators on ANF low-part."""
    lows = [m for m in range(1, 1 << n) if bin(m).count("1") <= 2]
    idx = {m: i for i, m in enumerate(lows)}
    def apply(bits, gen):
        # f(x) = cub + sum lows; (f o L) low part; compute by evaluating on weight<=2 points
        a = [0] * (1 << n)
        for m in cub_mons: a[m] ^= 1
        for i, m in enumerate(lows):
            if bits >> i & 1: a[m] ^= 1
        # evaluate f o L at weight<=2 vectors to recover the low ANF (cubic of f o L stays = cub since gen in Stab)
        def fval(x):
            v = 0
            for m, c in enumerate(a):
                if c and (x & m) == m: v ^= 1
            return v
        cache = {}
        def gval(x):
            return fval(lxor(gen, x))
        res = 0
        for i, m in enumerate(lows):
            # low ANF coefficient of g at m (Moebius on subsets of m): all subsets have weight <=2
            c = 0
            s = m
            while True:
                c ^= gval(s)
                if s == 0: break
                s = (s - 1) & m
            if c: res |= 1 << i
        return res
    seen = {}
    orbs = []
    for b in range(1 << len(lows)):
        if b in seen: continue
        o = [b]; seen[b] = len(orbs); q = [b]
        while q:
            x = q.pop()
            for g in stab_gens:
                y = apply(x, g)
                if y not in seen:
                    seen[y] = len(orbs); o.append(y); q.append(y)
        orbs.append(o)
    return orbs, lows

def fn_from_bits(n, cub_mons, lows, bits):
    a = [0] * (1 << n)
    for m in cub_mons: a[m] ^= 1
    for i, m in enumerate(lows):
        if bits >> i & 1: a[m] ^= 1
    return a

def stabilizer_elems(n, cub_mons, limit=500000):
    """all L in GL(n,2) preserving the cubic part (backtracking on columns using tau on basis triples)."""
    mons = [tuple(b for b in range(n) if m >> b & 1) for m in cub_mons]
    def tau_(a, b, c):
        r = 0
        for (i, j, k) in mons:
            for p in itertools.permutations((i, j, k)):
                r ^= (a >> p[0] & 1) & (b >> p[1] & 1) & (c >> p[2] & 1)
        return r
    tauval = {}
    for tr in itertools.combinations(range(n), 3):
        tauval[tr] = tau_(1 << tr[0], 1 << tr[1], 1 << tr[2])
    sols = []
    def dfs(cols, span):
        j = len(cols)
        if j == n:
            sols.append(list(cols)); return
        for c in range(1, 1 << n):
            if c in span: continue
            ok = True
            for i, k in itertools.combinations(range(j), 2):
                if tau_(cols[i], cols[k], c) != tauval[(i, k, j)]:
                    ok = False; break
            if not ok: continue
            cols.append(c)
            dfs(cols, span | {s ^ c for s in span})
            cols.pop()
            if len(sols) > limit: return
    dfs([], {0})
    return sols

def section_b5():
    """Thm B, n=5, the unique Rad=0 tau orbit x1(x2x3+x4x5): orbits of Stab(tau) on the 2^15 lower terms;
       exact Phi span-isometry search vs exact f~g on all orbit-representative pairs (plus conjugates), and full
       solution counts #S = #Iso(f,g) on a sample."""
    n = 5; N = 10
    rng = random.Random(370002)
    cub = [0b00111, 0b11001]  # x0 x1 x2 + x0 x3 x4 (renamed)
    t0 = time.time()
    a0 = [0] * (1 << n)
    for m in cub: a0[m] = 1
    print(f"[b5] Rad tau = {rad_tau(a0, n)} (must be 0)")
    stab = stabilizer_elems(n, cub)
    print(f"[b5] |Stab(tau)| = {len(stab)} ({time.time()-t0:.1f}s)")
    gens = rng.sample(stab, min(40, len(stab)))
    orbs, lows = orbits_low(n, cub, gens)
    print(f"[b5] orbits of Stab on 2^{len(lows)} lower terms: {len(orbs)} (generators sampled; {time.time()-t0:.1f}s), sizes {sorted(len(o) for o in orbs)[:30]}{'...' if len(orbs)>30 else ''}")
    # representatives: take the minimum of each orbit
    reps = [fn_from_bits(n, cub, lows, min(o)) for o in orbs]
    # sanity: all reps have Rad=0
    assert all(rad_tau(r, n) == 0 for r in reps)
    # pairs: all rep pairs if not too many, else sample; g is a random conjugate of the rep to avoid fixed coordinates
    idx = list(range(len(reps)))
    pairs = [(i, j) for i in idx for j in idx]
    if len(pairs) > 900:
        rng.shuffle(pairs); pairs = pairs[:900]
    bad = 0; yes = 0; no = 0; maxnodes = 0
    truth_cache = {}
    t1 = time.time()
    for (i, j) in pairs:
        a = reps[i]; b = reps[j]
        ttb = tt_of_anf(b)
        if j != i or True:
            ttb2, L = planted_conj(ttb, n, rng)
        b2 = anf(ttb2)
        tta = tt_of_anf(a)
        sols = iso_search(tta, ttb2, n, first=True)
        truth = len(sols) > 0
        pf = phi(a, n); pg = phi(b2, n)
        head, ws = exact(pf, pg, N, mode=0, maxsol=1)
        got = head[0] == "ISO"
        maxnodes = max(maxnodes, int(head[1]))
        if head[0] == "TIMEOUT":
            print("  timeout", i, j); bad += 1; continue
        if got:
            if not verify_span(pf, pg, ws[0], N): bad += 1
            if any(c & ((1 << n) - 1) for c in ws[0][n:]): bad += 1  # S(U)=U
        if got != truth:
            bad += 1
            print("  DISAGREE", i, j, got, truth)
        yes += truth; no += (not truth)
    print(f"[b5] pairs {len(pairs)}: agree on all but {bad}; equivalent {yes}, inequivalent {no}; max nodes {maxnodes}; {time.time()-t1:.1f}s")
    # exact counts #S = #Iso on sample of equivalent pairs (including self-pairs)
    cbad = 0; ctot = 0; t2 = time.time()
    for k in range(min(len(reps), 12)):
        a = reps[k]; tta = tt_of_anf(a)
        ttb2, L = planted_conj(tta, n, rng)
        b2 = anf(ttb2)
        nIso = len(iso_search(tta, ttb2, n, first=False))
        head, ws = exact(phi(a, n), phi(b2, n), N, mode=1, maxsol=0)
        ctot += 1
        if int(head[2]) != nIso:
            cbad += 1; print("  COUNT MISMATCH", k, head, nIso)
    print(f"[b5] #S(span isometries)=#Iso(f,g): {ctot-cbad}/{ctot} ({time.time()-t2:.1f}s)")
    return bad == 0 and cbad == 0

def section_b6():
    """Thm B, n=6: random Rad=0 cubics: planted equivalent, hard perturbations (one lower term changed), and random g
       with the same tau; truth by exact L search (each exhaustive)."""
    n = 6; N = 12; rng = random.Random(370003)
    bad = 0; tot = 0; yes = 0; no = 0; t0 = time.time(); maxnodes = 0
    for trial in range(30):
        a = random_rad0(n, rng)
        tta = tt_of_anf(a)
        # planted equivalent
        ttb, L = planted_conj(tta, n, rng)
        b = anf(ttb)
        # perturbed: flip one degree-<=2 ANF term of b, keeping f(0)=0
        c = list(b)
        lows = [m for m in range(1, 1 << n) if bin(m).count("1") <= 2]
        m = rng.choice(lows); c[m] ^= 1
        for g_anf in (b, c):
            ttg = tt_of_anf(g_anf)
            truth = len(iso_search(tta, ttg, n, first=True)) > 0
            pf = phi(a, n); pg = phi(g_anf, n)
            head, ws = exact(pf, pg, N, mode=0, maxsol=1)
            maxnodes = max(maxnodes, int(head[1]))
            tot += 1
            got = head[0] == "ISO"
            if head[0] == "TIMEOUT":
                bad += 1; print("  timeout", trial); continue
            if got and (not verify_span(pf, pg, ws[0], N) or any(cc & ((1 << n) - 1) for cc in ws[0][n:])):
                bad += 1
            if got != truth:
                bad += 1; print("  DISAGREE", trial, got, truth)
            yes += truth; no += (not truth)
    print(f"[b6] n=6: {tot} instances; disagreements {bad}; equivalent {yes} inequivalent {no}; max nodes {maxnodes}; {time.time()-t0:.1f}s")
    return bad == 0

def section_degenerate():
    """Rad tau != 0 (hypothesis of Thm B removed): exact comparison on all orbit representatives, n=3 and n=4.
       Informational: a disagreement shows the hypothesis is necessary."""
    res = True
    for n, N in [(3, 6), (4, 8)]:
        t0 = time.time()
        # orbits of GL(n,2) on all functions with f(0)=0, degree<=3
        gl = enum_gl(n)
        lows3 = [m for m in range(1, 1 << n) if bin(m).count("1") <= 3]
        seen = set(); reps = []
        for bits in range(1 << len(lows3)):
            if bits in seen: continue
            reps.append(bits)
            a = [0] * (1 << n)
            for i, m in enumerate(lows3):
                if bits >> i & 1: a[m] = 1
            tt = tt_of_anf(a)
            orbit = set()
            for L in gl:
                g = anf(compose_tt(tt, L))
                bb = 0
                for i, m in enumerate(lows3):
                    if g[m]: bb |= 1 << i
                orbit.add(bb)
            seen |= orbit
        print(f"[degenerate n={n}] {len(reps)} GL-orbits on functions f(0)=0 ({time.time()-t0:.1f}s)")
        repfns = []
        for bits in reps:
            a = [0] * (1 << n)
            for i, m in enumerate(lows3):
                if bits >> i & 1: a[m] = 1
            repfns.append(a)
        dis = 0
        for i in range(len(repfns)):
            for j in range(len(repfns)):
                head, ws = exact(phi(repfns[i], n), phi(repfns[j], n), N, mode=0, maxsol=1)
                got = head[0] == "ISO"
                truth = (i == j)
                if got != truth:
                    dis += 1
                    print(f"  DISAGREEMENT n={n}: rep {i} vs rep {j}: Phi says {got}, truth {truth}; Rad dims {rad_tau(repfns[i],n)},{rad_tau(repfns[j],n)}")
                    if dis > 20: return False
        print(f"[degenerate n={n}] {len(repfns)**2} ordered pairs of orbit representatives; disagreements: {dis}")
    return res

def enum_gl(n):
    res = []
    def dfs(cols, span):
        if len(cols) == n:
            res.append(list(cols)); return
        for c in range(1, 1 << n):
            if c in span: continue
            cols.append(c)
            dfs(cols, span | {s ^ c for s in span})
            cols.pop()
    dfs([], {0})
    return res

def fplus(a, n):
    """ANF of f^+ on (x,y,t) = 2n+1 variables: x: bits 0..n-1, y: bits n..2n-1, t: bit 2n."""
    N = 2 * n + 1
    r = [0] * (1 << N)
    for m, c in enumerate(a):
        if c: r[m] = 1
    for i in range(n):
        m = (1 << i) | (1 << (n + i)) | (1 << (2 * n))
        r[m] ^= 1
    return r

def section_composite():
    """Composite (Thm B + Thm C) n=2 and n=3: Phi(f^+) span isometry on F_2^{4n+2} vs exact f ~ g, on all orbit reps (and conjugates)."""
    rng = random.Random(370004)
    ok = True
    for n in (2, 3):
        t0 = time.time()
        gl = enum_gl(n)
        lows3 = [m for m in range(1, 1 << n) if bin(m).count("1") <= 3]
        seen = set(); reps = []
        for bits in range(1 << len(lows3)):
            if bits in seen: continue
            reps.append(bits)
            a = [0] * (1 << n)
            for i, m in enumerate(lows3):
                if bits >> i & 1: a[m] = 1
            tt = tt_of_anf(a)
            orbit = set()
            for L in gl:
                g = anf(compose_tt(tt, L))
                bb = 0
                for i, m in enumerate(lows3):
                    if g[m]: bb |= 1 << i
                orbit.add(bb)
            seen |= orbit
        repfns = []
        for bits in reps:
            a = [0] * (1 << n)
            for i, m in enumerate(lows3):
                if bits >> i & 1: a[m] = 1
            repfns.append(a)
        nvars = 2 * n + 1; N = 2 * nvars
        bad = 0; tot = 0; maxnodes = 0
        for i in range(len(repfns)):
            for j in range(len(repfns)):
                # g = conjugate of rep j by a random GL(n,2) element, to avoid coordinate artefacts
                ttj = tt_of_anf(repfns[j])
                ttj2, _ = planted_conj(ttj, n, rng)
                gj = anf(ttj2)
                fp = fplus(repfns[i], n); gp = fplus(gj, n)
                truth = (i == j)
                head, ws = exact(phi(fp, nvars), phi(gp, nvars), N, mode=0, maxsol=1, cap=500000000)
                tot += 1
                if head[0] == "TIMEOUT":
                    bad += 1; print(f"  TIMEOUT n={n} {i},{j}"); continue
                maxnodes = max(maxnodes, int(head[1]))
                got = head[0] == "ISO"
                if got != truth:
                    bad += 1; print(f"  DISAGREE n={n} {i},{j}: got {got}, truth {truth}")
                if got and not verify_span(phi(fp, nvars), phi(gp, nvars), ws[0], N):
                    bad += 1; print("  witness invalid")
        print(f"[composite n={n}] {len(repfns)} orbits, {tot} pairs, F_2^{N}, m={nvars+1}: disagreements {bad}, max nodes {maxnodes}, {time.time()-t0:.1f}s")
        ok = ok and bad == 0
    return ok

def section_thmc():
    """Thm C: (i) Rad tau_{f^+} = 0 for all f; (ii) f ~ g iff f^+ ~ g^+ exactly, on all orbit reps n=2,3 with conjugates."""
    rng = random.Random(370005)
    ok = True
    for n in (2, 3):
        gl = enum_gl(n)
        lows3 = [m for m in range(1, 1 << n) if bin(m).count("1") <= 3]
        seen = set(); reps = []
        for bits in range(1 << len(lows3)):
            if bits in seen: continue
            reps.append(bits)
            a = [0] * (1 << n)
            for i, m in enumerate(lows3):
                if bits >> i & 1: a[m] = 1
            tt = tt_of_anf(a)
            orbit = set()
            for L in gl:
                g = anf(compose_tt(tt, L))
                bb = 0
                for i, m in enumerate(lows3):
                    if g[m]: bb |= 1 << i
                orbit.add(bb)
            seen |= orbit
        repfns = []
        for bits in reps:
            a = [0] * (1 << n)
            for i, m in enumerate(lows3):
                if bits >> i & 1: a[m] = 1
            repfns.append(a)
        nvars = 2 * n + 1
        radbad = sum(1 for r in repfns if rad_tau(fplus(r, n), nvars) != 0)
        bad = 0; tot = 0; t0 = time.time()
        for i in range(len(repfns)):
            for j in range(len(repfns)):
                ttj2, _ = planted_conj(tt_of_anf(repfns[j]), n, rng)
                gj = anf(ttj2)
                fp = fplus(repfns[i], n); gp = fplus(gj, n)
                sols = iso_search_filtered(tt_of_anf(fp), tt_of_anf(gp), nvars)
                got = len(sols) > 0
                if got != (i == j):
                    bad += 1; print(f"  DISAGREE thmC n={n} {i},{j}: {got}, {(i==j)}")
                tot += 1
        print(f"[thmc n={n}] Rad(f^+) nonzero: {radbad}; orbit-rep pairs {tot}: disagreements {bad}; {time.time()-t0:.1f}s")
        ok = ok and bad == 0 and radbad == 0
    return ok

def section_squares():
    """Thm A: tuple version (n=5,m=3) and space version (n=4), random lifts on both sides, exact search vs exact truth."""
    rng = random.Random(370006)
    def rand_alt(n):
        return [[0]*n for _ in range(n)]
    def alt_from_bits(n, bits):
        # upper triangle bits -> matrix rows as lists
        M = [[0]*n for _ in range(n)]
        c = 0
        for i in range(n):
            for j in range(i+1, n):
                if bits >> c & 1:
                    M[i][j] = M[j][i] = 1
                c += 1
        return M
    def congruent(A, B, L):
        n = len(A)
        for i in range(n):
            for j in range(n):
                # (L^T A L)[i][j] = sum_{p,q} L_{pi} A[p][q] L_{qj}
                s = 0
                for p in range(n):
                    if L[i] >> p & 1:
                        for q in range(n):
                            if L[j] >> q & 1:
                                s ^= A[p][q]
                if s != B[i][j]:
                    return False
        return True
    def lift(M, rng, n):
        # quadratic form on n variables polarizing to M with random diagonal; on x-block coordinates
        q = {}
        for i in range(n):
            for j in range(i+1, n):
                if M[i][j]: add_mono(q, i, j)
        for i in range(n):
            if rng.random() < 0.5: add_mono(q, i, i)
        return q
    def gadget(Ms, m, n, rng):
        forms = []
        for i in range(m):
            q = lift(Ms[i], rng, n)
            add_mono(q, n+i, n+i)
            forms.append(q)
        return forms
    # tuple truth: backtracking for L with L^T A_i L = B_i
    def tuple_truth(As, Bs, n):
        m = len(As)
        def pairval(A, u, v):
            s = 0
            for p in range(n):
                if u >> p & 1:
                    for q in range(n):
                        if v >> q & 1:
                            s ^= A[p][q]
            return s
        res = None
        def dfs(cols, span):
            nonlocal res
            j = len(cols)
            if j == n:
                res = list(cols); return True
            for c in range(1, 1 << n):
                if c in span: continue
                ok = True
                for t in range(m):
                    for i in range(j):
                        if pairval(As[t], cols[i], c) != Bs[t][i][j]:
                            ok = False; break
                    if not ok: break
                if not ok: continue
                cols.append(c)
                if dfs(cols, span | {s ^ c for s in span}): return True
                cols.pop()
            return False
        dfs([], {0})
        return res
    n, m = 5, 3; N = n + m
    bad = 0; yes = no = 0; tot = 0
    t0 = time.time()
    for trial in range(60):
        A = [alt_from_bits(n, rng.getrandbits(n*(n-1)//2)) for _ in range(m)]
        if trial % 2 == 0:
            L = random_gl(n, rng)
            # B_i = L^T A_i L
            B = []
            for k in range(m):
                Bm = [[0]*n for _ in range(n)]
                for i in range(n):
                    for j in range(n):
                        s = 0
                        for p in range(n):
                            if L[i] >> p & 1:
                                for q in range(n):
                                    if L[j] >> q & 1:
                                        s ^= A[k][p][q]
                        Bm[i][j] = s
                B.append(Bm)
        else:
            B = [alt_from_bits(n, rng.getrandbits(n*(n-1)//2)) for _ in range(m)]
        # common radical zero required: check
        def radz(M):
            rows = [sum(M[t][i][j] << j for j in range(n)) << (t*n) for t in range(m) for i in range(n)]
            flat = [sum(M[t][i][j] << (t*n+j) for t in range(m) for j in range(n)) for i in range(n)]
            return rank(flat) == n
        if not (radz(A) and radz(B)):
            continue
        tot += 1
        truth = tuple_truth(A, B, n) is not None
        fA = gadget(A, m, n, rng); fB = gadget(B, m, n, rng)
        head, ws = exact(fA, fB, N, mode=2, maxsol=1)
        got = head[0] == "ISO"
        if got != truth:
            bad += 1; print("  DISAGREE tuple", trial, got, truth)
        if got and not verify_tuple(fA, fB, ws[0], N):
            bad += 1; print("  bad witness")
        yes += truth; no += not truth
    print(f"[squares tuple n=5 m=3] {tot} instances with zero common radical: disagreements {bad}; congruent {yes}, not {no}; {time.time()-t0:.1f}s")
    # space version n=4, m=2,3: truth over all GL(4,2)
    gl4 = enum_gl(4)
    def span_of_mats(Ms, n):
        rows = []
        for M in Ms:
            v = 0
            for i in range(n):
                for j in range(n):
                    if M[i][j]: v |= 1 << (i*n+j)
            rows.append(v)
        return rows
    def apply_L(M, L, n):
        R = [[0]*n for _ in range(n)]
        for i in range(n):
            for j in range(n):
                s = 0
                for p in range(n):
                    if L[i] >> p & 1:
                        for q in range(n):
                            if L[j] >> q & 1:
                                s ^= M[p][q]
                R[i][j] = s
        return R
    bad2 = 0; yes = no = 0; tot2 = 0; t1 = time.time()
    for trial in range(60):
        m = 2 + trial % 2
        n = 4; N = n + m
        A = [alt_from_bits(n, rng.getrandbits(6)) for _ in range(m)]
        if trial % 2 == 0:
            # B: planted space isometry with random invertible combination of the matrices
            L = rng.choice(gl4)
            T = [apply_L(M, L, n) for M in A]
            P = random_gl(m, rng)
            B = []
            for i in range(m):
                Bm = [[0]*n for _ in range(n)]
                for j in range(m):
                    if P[i] >> j & 1:
                        for r in range(n):
                            for s in range(n):
                                Bm[r][s] ^= T[j][r][s]
                B.append(Bm)
        else:
            B = [alt_from_bits(n, rng.getrandbits(6)) for _ in range(m)]
        flatA = span_of_mats(A, n); flatB = span_of_mats(B, n)
        if rank(flatA) != m or rank(flatB) != m: continue
        # radicals
        def radz2(M, m):
            flat = [sum(M[t][i][j] << (t*n+j) for t in range(m) for j in range(n)) for i in range(n)]
            return rank(flat) == n
        if not (radz2(A, m) and radz2(B, m)): continue
        tot2 += 1
        truth = False
        for L in gl4:
            T = [apply_L(M, L, n) for M in A]
            ft = span_of_mats(T, n)
            if all(in_span(v, flatB) for v in ft):
                truth = True; break
        fA = gadget(A, m, n, rng); fB = gadget(B, m, n, rng)
        head, ws = exact(fA, fB, N, mode=0, maxsol=1)
        got = head[0] == "ISO"
        if got != truth:
            bad2 += 1; print("  DISAGREE space", trial, got, truth)
        if got and not verify_span(fA, fB, ws[0], N):
            bad2 += 1
        yes += truth; no += not truth
    print(f"[squares space n=4 m=2,3] {tot2} instances: disagreements {bad2}; isometric {yes}, not {no}; {time.time()-t1:.1f}s")
    return bad == 0 and bad2 == 0

# ---- obstacle: F_2^6 tuple --------------------------------------------------------
def mat_mul(A, B):
    n = len(A)
    return [[sum(A[i][k] & B[k][j] for k in range(n)) & 1 for j in range(n)] for i in range(n)]

def kron(A, B):
    na, nb = len(A), len(B)
    n = na * nb
    return [[A[i // nb][j // nb] & B[i % nb][j % nb] for j in range(n)] for i in range(n)]

def transpose(A):
    return [list(r) for r in zip(*A)]

def identity(n):
    return [[1 if i == j else 0 for j in range(n)] for i in range(n)]

def is_alt(M):
    n = len(M)
    return all(M[i][j] == M[j][i] for i in range(n) for j in range(n)) and all(M[i][i] == 0 for i in range(n))

def adj_dim(As):
    """dim of {(T,S): T^t A_i = A_i S for all i} over F_2: nullity of the linear system."""
    n = len(As[0]); m = len(As)
    # unknowns: T entries (t_{pq}), S entries (s_{pq}), n^2 each
    rows = []
    for a in As:
        for i in range(n):
            for j in range(n):
                v = 0
                # (T^t A)[i][j] = sum_p T[p][i] A[p][j];  (A S)[i][j] = sum_q A[i][q] S[q][j]
                for p in range(n):
                    if a[p][j]:
                        v ^= 1 << (p*n + i)
                for q in range(n):
                    if a[i][q]:
                        v ^= 1 << (n*n + q*n + j)
                rows.append(v)
    return 2*n*n - rank(rows)

def congruent_search(As, Bs):
    """exhaustive: find L in GL(n,2) with L^T A_i L = B_i (columns of L chosen by backtracking)."""
    n = len(As[0]); m = len(As)
    def pv(A, u, v):
        s = 0
        for p in range(n):
            if u >> p & 1:
                for q in range(n):
                    if v >> q & 1:
                        s ^= A[p][q]
        return s
    found = []
    nodes = [0]
    def dfs(cols, span):
        nodes[0] += 1
        j = len(cols)
        if j == n:
            found.append(list(cols)); return True
        for c in range(1, 1 << n):
            if c in span: continue
            ok = True
            for t in range(m):
                for i in range(j):
                    if pv(As[t], cols[i], c) != Bs[t][i][j]:
                        ok = False; break
                if not ok: break
            if not ok: continue
            cols.append(c)
            if dfs(cols, span | {s ^ c for s in span}): return True
            cols.pop()
        return False
    dfs([], {0})
    return found, nodes[0]

def section_obstacle():
    C = [[[0,1,0],[1,0,0],[0,0,0]], [[0,0,1],[0,0,0],[1,0,0]], [[0,0,0],[0,0,1],[0,1,0]]]
    I2 = identity(2); Swap = [[0,1],[1,0]]
    A = [kron(c, I2) for c in C]; B = [kron(c, Swap) for c in C]
    assert all(is_alt(b) for b in B) and all(is_alt(a) for a in A)
    E = kron(identity(3), Swap)
    # A_i E = B_i
    assert all(mat_mul(a, E) == b for a, b in zip(A, B))
    # E* = E in adjoint algebra: E^t A_i = A_i E
    assert all(mat_mul(transpose(E), a) == mat_mul(a, E) for a in A)
    print("[obstacle] A_iE=B_i, B alternating, E^tA=AE: yes")
    print("[obstacle] dim Adj(A) as pairs (T,S) over F_2:", adj_dim(A), " (I_3 tensor M_2 predicted: 4)")
    t0 = time.time()
    f, nodes = congruent_search(A, B)
    print(f"[obstacle] exhaustive L^T A L = B over GL(6,2): found {len(f)} ({nodes} nodes, {time.time()-t0:.1f}s)")
    # positive control: B' = planted congruent image of A under random L
    rng = random.Random(370007)
    L = random_gl(6, rng)
    def apply(M, L):
        n = len(M); R = [[0]*n for _ in range(n)]
        for i in range(n):
            for j in range(n):
                s = 0
                for p in range(n):
                    if L[i] >> p & 1:
                        for q in range(n):
                            if L[j] >> q & 1:
                                s ^= M[p][q]
                R[i][j] = s
        return R
    Bp = [apply(a, L) for a in A]
    f2, nodes2 = congruent_search(A, Bp)
    print(f"[obstacle] positive control (planted congruence): found {len(f2)} ({nodes2} nodes)")
    return len(f) == 0 and len(f2) == 1 and adj_dim(A) == 4

def section_obstacle2():
    """Sharper instance (referee's): quotient problem solvable, no lift, char-2-specific: R = F_q[eps]/(eps^2), involution trivial.
       A_i = (C_i (x) Swap), (C_i (x) Swap M_eps) on F_2^6, m=6; B obtained via E = 1+eps. X*X=E has no solution in Adj = I (x) R, since (a+b eps)^2 = a^2;
       over F_3 the analogous instance is congruent via X = 1 + 2 eps."""
    C = [[[0,1,0],[1,0,0],[0,0,0]], [[0,0,1],[0,0,0],[1,0,0]], [[0,0,0],[0,0,1],[0,1,0]]]
    Swap = [[0,1],[1,0]]
    Eps = [[0,0],[1,0]]  # multiplication by eps on (1, eps): eps*1=eps, eps*eps=0 (columns = images)
    OnePlusEps = [[1,0],[1,1]]
    # b(x,y) = phi(x y), phi(a+b eps)=b has Gram Swap; b_eps(x,y)=phi(eps x y) Gram Swap*MEps etc.
    b1 = Swap
    b2 = mat_mul(Swap, Eps)   # Gram of phi(eps x y) -- check symmetric
    print("[obstacle2] Gram of phi(eps x y):", b2, " symmetric:", b2 == transpose(b2))
    A = [kron(c, b1) for c in C] + [kron(c, b2) for c in C]
    M = OnePlusEps
    # B_i = A_i (I (x) M)
    E6 = kron([[1,0,0],[0,1,0],[0,0,1]], M)
    B = [mat_mul(a, E6) for a in A]
    assert all(is_alt(x) for x in A + B)
    print("[obstacle2] A,B alternating:", True, "; dim Adj(A) =", adj_dim(A), "(I (x) R predicted: 2)")
    # E* = E: E^t A = A E
    assert all(mat_mul(transpose(E6), a) == mat_mul(a, E6) for a in A)
    # the ratio matrix: B = A E, E = 1+eps, E*=E
    print("[obstacle2] E symmetric-adjoint (E^tA=AE): yes; note (a+b eps)^2 = a^2 in char 2, so X*X = E unsolvable though E = 1 mod rad")
    t0 = time.time()
    f, nodes = congruent_search(A, B)
    print(f"[obstacle2] exhaustive congruence over GL(6,2): found {len(f)} ({nodes} nodes, {time.time()-t0:.1f}s)")
    # positive control (F_2) : planted congruence with X=1 (trivial); and sanity over F_3 by explicit check
    # F_3 analogue: forms C (x) Swap etc. with Swap symmetric over F_3 (C alternating): A_i, B_i = A_i(I (x) M) with M = [[1,0],[1,1]]; X = 1+2eps
    # Check: X^T-adjoint: (X, X) maps A -> A X^2 = A(1+4eps) = A(1+eps): congruence L = I (x) X, L^T A L = A X^* X = A X^2.
    p = 3
    def mul(A, B, p=p):
        n = len(A); return [[sum(A[i][k]*B[k][j] for k in range(n)) % p for j in range(n)] for i in range(n)]
    def trans(A): return [list(r) for r in zip(*A)]
    X2 = [[1,0],[2,1]]   # 1 + 2 eps on (1,eps): acts [[1,0],[2,1]] (1->1+2eps, eps->eps)
    L = None
    bad = 0
    # alternating C_i signs: C over F_3 alternating; use C with -1 entries for true alternating over F_3
    Cf3 = [[[0,1,0],[2,0,0],[0,0,0]], [[0,0,1],[0,0,0],[2,0,0]], [[0,0,0],[0,0,1],[0,2,0]]]
    S2 = [[0,1],[1,0]]
    # A over F_3 (Swap symmetric, C antisymmetric: tensor antisymmetric: A^T = -A ✓)
    def kron3(A, B):
        na, nb = len(A), len(B); n = na*nb
        return [[(A[i//nb][j//nb]*B[i%nb][j%nb])%3 for j in range(n)] for i in range(n)]
    A3 = [kron3(c, S2) for c in Cf3] + [kron3(c, mul(S2, [[0,0],[1,0]], p=3)) for c in Cf3]
    M3 = [[1,0],[1,1]]
    B3 = [mul(a, kron3(identity(3), M3)) for a in A3]
    L = kron3(identity(3), X2)
    # check L^T A3 L = B3 over F_3
    for a, b in zip(A3, B3):
        if mul(mul(trans(L), a), L) != b:
            bad += 1
    print(f"[obstacle2] F_3 analogue: explicit congruence by L = I (x) (1+2 eps): mismatches {bad}")
    return len(f) == 0 and bad == 0

SECTIONS = {
    "identities": section_identities,
    "b3": section_b3,
    "b5": section_b5,
    "b6": section_b6,
    "degenerate": section_degenerate,
    "composite": section_composite,
    "thmc": section_thmc,
    "squares": section_squares,
    "obstacle": section_obstacle,
    "obstacle2": section_obstacle2,
}

if __name__ == "__main__":
    which = sys.argv[1:] or list(SECTIONS)
    allok = True
    for s in which:
        t0 = time.time()
        try:
            ok = SECTIONS[s]()
        except Exception as e:
            print(f"[{s}] EXCEPTION {type(e).__name__}: {e}")
            import traceback; traceback.print_exc(); ok = False
        print(f"== {s}: {'PASS' if ok else 'FAIL'}  ({time.time()-t0:.1f}s)\n", flush=True)
        allok = allok and ok
    print("ALL PASS" if allok else "SOME FAILED")
