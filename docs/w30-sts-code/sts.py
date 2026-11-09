"""Steiner triple system constructions and closure tools (w30-sts).

An STS is a pair (n, triple) where points are 0..n-1 and `triple` is an n x n
numpy array with triple[x,y]=third point of the block through x,y, and
triple[x,x]=x (the Steiner quasigroup).
"""
import itertools, random


def from_blocks(n, blocks):
    Q = [[-1] * n for _ in range(n)]
    for i in range(n):
        Q[i][i] = i
    for a, b, c in blocks:
        for (x, y, z) in ((a, b, c), (a, c, b), (b, a, c), (b, c, a), (c, a, b), (c, b, a)):
            if Q[x][y] != -1 and Q[x][y] != z:
                raise ValueError(f"pair {x,y} covered twice: {Q[x][y]}, {z}")
            Q[x][y] = z
    if any(-1 in row for row in Q):
        raise ValueError("not all pairs covered")
    return Q


def is_sts(Q):
    n = len(Q)
    for x in range(n):
        if Q[x][x] != x:
            return False
    for x in range(n):
        for y in range(n):
            if x != y:
                z = Q[x][y]
                if z == x or z == y or Q[x][z] != y or Q[y][z] != x:
                    return False
    return True


def blocks_of(Q):
    n = len(Q)
    return [(x, y, Q[x][y]) for x in range(n) for y in range(x + 1, n) if Q[x][y] > y]


def pg(m):
    """PG(m-1,2): points 1..2^m-1 (bitmasks) relabelled to 0..n-1."""
    n = 2 ** m - 1
    return from_blocks(n, [(x - 1, y - 1, (x ^ y) - 1)
                           for x in range(1, n + 1) for y in range(x + 1, n + 1) if (x ^ y) > y])


def _vecs(p, d):
    return list(itertools.product(range(p), repeat=d))


def ag3(m):
    """AG(m,3)."""
    vs = _vecs(3, m)
    idx = {v: i for i, v in enumerate(vs)}
    bl = set()
    for a, b in itertools.combinations(vs, 2):
        c = tuple((-x - y) % 3 for x, y in zip(a, b))
        bl.add(tuple(sorted((idx[a], idx[b], idx[c]))))
    return from_blocks(len(vs), sorted(bl))


def hts81():
    """Non-affine Hall triple system of order 81, from Bruck's commutative Moufang loop of exponent 3.

    Product on F_3^4: (a,x)*(b,y) = (a+b+(x1-y1)(x2*y3-x3*y2), x+y), blocks {u,v,(u*v)^-1}."""
    pts = _vecs(3, 4)
    idx = {v: i for i, v in enumerate(pts)}

    def mul(u, v):
        a, x1, x2, x3 = u
        b, y1, y2, y3 = v
        return ((a + b + (x1 - y1) * (x2 * y3 - x3 * y2)) % 3, (x1 + y1) % 3, (x2 + y2) % 3, (x3 + y3) % 3)

    def inv(u):
        # solve u*v=0 by search (the loop is small)
        for v in pts:
            if mul(u, v) == (0, 0, 0, 0):
                return v
        raise ValueError

    invs = {u: inv(u) for u in pts}
    bl = set()
    for u, v in itertools.combinations(pts, 2):
        w = invs[mul(u, v)]
        bl.add(tuple(sorted((idx[u], idx[v], idx[w]))))
    return from_blocks(len(pts), sorted(bl))


def bose_general(G_elems, op):
    """Bose construction from a commutative idempotent quasigroup (G, op) of odd order.

    Points (g,i), i in Z_3; blocks {(g,0),(g,1),(g,2)} and {(g,i),(h,i),(g o h,i+1)}."""
    t = len(G_elems)
    pos = {g: k for k, g in enumerate(G_elems)}
    def pt(k, i):
        return k * 3 + i
    bl = []
    for k in range(t):
        bl.append((pt(k, 0), pt(k, 1), pt(k, 2)))
    for k, l in itertools.combinations(range(t), 2):
        for i in range(3):
            bl.append((pt(k, i), pt(l, i), pt(pos[op(G_elems[k], G_elems[l])], (i + 1) % 3)))
    return from_blocks(3 * t, bl)


def bose_zp(p, d):
    """Bose construction over Z_p^d with g o h = (g+h)/2."""
    half = (p + 1) // 2
    G = _vecs(p, d)
    return bose_general(G, lambda u, v: tuple(((a + b) * half) % p for a, b in zip(u, v)))


def skolem(t):
    """A Skolem-type construction on 6t+1 points: half-idempotent commutative quasigroup on Z_{2t}.

    Points: infty and (g,i), g in Z_{2t}, i in Z_3."""
    n = 2 * t
    # half-idempotent quasigroup: g o h = sigma(g+h) with sigma on Z_{2t}
    def op(g, h):
        s = (g + h) % n
        if s % 2 == 0:
            return s // 2
        return (s + n - 1) // 2 % n if False else ((s - 1) // 2 + t) % n
    # verify half-idempotency
    for g in range(t):
        assert op(g, g) == g
    for g in range(t, n):
        assert op(g, g) == g - t
    INF = 3 * n
    def pt(g, i):
        return g * 3 + i
    bl = []
    for g in range(t):
        bl.append((pt(g, 0), pt(g, 1), pt(g, 2)))
    for g in range(t):
        for i in range(3):
            bl.append((INF, pt(t + g, i), pt(g, (i + 1) % 3)))
    for g, h in itertools.combinations(range(n), 2):
        for i in range(3):
            bl.append((pt(g, i), pt(h, i), pt(op(g, h), (i + 1) % 3)))
    return from_blocks(3 * n + 1, bl)


def product(Q1, Q2):
    """Direct product of Steiner quasigroups."""
    n1, n2 = len(Q1), len(Q2)
    n = n1 * n2
    Q = [[0] * n for _ in range(n)]
    for a in range(n1):
        for b in range(n2):
            for c in range(n1):
                for d in range(n2):
                    Q[a * n2 + b][c * n2 + d] = Q1[a][c] * n2 + Q2[b][d]
    return Q


def doubling(Q, rng, seed_fact=None):
    """Double Q (n -> 2n+1) with a random 1-factorization of K_{n+1} (via random Z_n-rotation-free hillclimb).

    Uses the patterned 1-factorization of K_{n+1} on Z_n + infinity, randomly relabelled, assigning factors to points of Q."""
    n = len(Q)
    bl = list(blocks_of(Q))
    m = n + 1  # K_{n+1}, n odd
    outer = list(range(n, n + m))
    perm = outer[:]
    rng.shuffle(perm)
    factor_labels = list(range(n))
    rng.shuffle(factor_labels)
    for i in range(n):
        s = factor_labels[i]
        bl.append((s, perm[i], perm[n]))
        for j in range(1, (n + 1) // 2):
            a, b = (i + j) % n, (i - j) % n
            bl.append((s, perm[a], perm[b]))
    return from_blocks(2 * n + 1, bl)


def random_sts_hillclimb(n, rng, max_iter=None):
    """Stinson's hill-climbing."""
    assert n % 6 in (1, 3)
    third = [[-1] * n for _ in range(n)]
    live = [set(range(n)) - {x} for x in range(n)]  # live[x] = {y : pair xy uncovered}
    livepts = [x for x in range(n) if live[x]]
    pos = {x: i for i, x in enumerate(livepts)}

    def add(x, y, z):
        for (a, b, c) in ((x, y, z), (x, z, y), (y, x, z), (y, z, x), (z, x, y), (z, y, x)):
            third[a][b] = c
        for (a, b) in ((x, y), (x, z), (y, z)):
            live[a].discard(b)
            live[b].discard(a)

    def rem(x, y, z):
        for (a, b) in ((x, y), (x, z), (y, z)):
            third[a][b] = -1
            third[b][a] = -1
            live[a].add(b)
            live[b].add(a)

    target = n * (n - 1) // 6
    blocks = 0
    it = 0
    while blocks < target:
        it += 1
        if max_iter and it > max_iter:
            return None
        # pick a live point
        x = rng.randrange(n)
        while not live[x]:
            x = rng.randrange(n)
        if len(live[x]) < 2:
            continue
        y, z = rng.sample(sorted(live[x]), 2)
        w = third[y][z]
        if w == -1:
            add(x, y, z)
            blocks += 1
        else:
            rem(y, z, w)
            add(x, y, z)
    for i in range(n):
        third[i][i] = i
    return third


# --- closure tools ---

def closure(Q, seeds):
    """Return boolean mask of the subsystem generated by seeds."""
    n = len(Q)
    inS = [False] * n
    S = []
    for x in seeds:
        if not inS[x]:
            inS[x] = True
            S.append(x)
    i = 0
    while i < len(S):
        x = S[i]
        Qx = Q[x]
        for j in range(i + 1):
            z = Qx[S[j]]
            if not inS[z]:
                inS[z] = True
                S.append(z)
        i += 1
    return inS


def closure_size(Q, seeds):
    return sum(closure(Q, seeds))


def exact_rank(Q, maxr=8):
    """Exact minimum generating-set size, by exhaustive search up to maxr; None if larger."""
    n = len(Q)
    if n == 1:
        return 1
    # fix first point WLOG? (not WLOG for non-transitive); use full search but with early pruning
    for r in range(2, maxr + 1):
        for T in itertools.combinations(range(n), r):
            if closure_size(Q, T) == n:
                return r
    return None


def greedy_chain(Q, rng, pick_max=True, samples=None):
    """A greedy chain of closures; returns list of (rank-step, size).

    pick_max: at each step choose the point maximizing the closure growth (over all or `samples` candidates)."""
    n = len(Q)
    start = rng.randrange(n)
    cur = closure(Q, [start])
    chain = [(1, sum(cur))]
    gens = [start]
    while sum(cur) < n:
        rest = [x for x in range(n) if not cur[x]]
        if samples is not None and len(rest) > samples:
            cand = rng.sample(rest, samples)
        else:
            cand = rest
        best, bx = -1, None
        for x in cand:
            s = closure_size(Q, gens + [x])
            if s > best:
                best, bx = s, x
            if not pick_max:
                break
        gens.append(bx)
        cur = closure(Q, gens)
        chain.append((len(gens), sum(cur)))
    return chain, gens


def char_space_dim(Q):
    """Dimension of {f: X -> F_2 : f(a)+f(b)+f(c)=0 on every block} = n - 2-rank."""
    n = len(Q)
    bl = blocks_of(Q)
    return n - gf_rank([sum(1 << v for v in b) for b in bl])


def gf_rank(rows):
    basis = {}
    r = 0
    for v in rows:
        while v:
            h = v.bit_length() - 1
            if h in basis:
                v ^= basis[h]
            else:
                basis[h] = v
                r += 1
                break
    return r


def char_space_dim_3(Q):
    """Dimension of {f: X -> F_3 : f(a)+f(b)+f(c)=0 on every block} = n - 3-rank."""
    n = len(Q)
    bl = blocks_of(Q)
    return n - gf3_rank(bl, n)


def gf3_rank(blocks, n):
    M = []
    for b in blocks:
        row = [0] * n
        for v in b:
            row[v] = 1
        M.append(row)
    rk = 0
    rows = len(M)
    for c in range(n):
        piv = None
        for r in range(rk, rows):
            if M[r][c] % 3:
                piv = r
                break
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        if M[rk][c] % 3 == 2:
            M[rk] = [(2 * v) % 3 for v in M[rk]]
        for r in range(rows):
            if r != rk and M[r][c] % 3:
                f = M[r][c]
                M[r] = [(a - f * b) % 3 for a, b in zip(M[r], M[rk])]
        rk += 1
        if rk == rows:
            break
    return rk


# --- PG fibrations (Theorem 2 gadget and central extensions) ---

def patterned_factorization_k8(rng):
    """Patterned 1-factorization of K_8 on Z_7 + infinity, relabelled to Z=F_2^3 (points 0..7)
    and with factors labelled by Z\\{0}. Returns dict z -> list of 8-set pairs."""
    perm = list(range(8))
    rng.shuffle(perm)
    labels = list(range(1, 8))
    rng.shuffle(labels)
    F = {}
    for i in range(7):
        pairs = [(perm[7], perm[i])]
        for j in range(1, 4):
            pairs.append((perm[(i + j) % 7], perm[(i - j) % 7]))
        F[labels[i]] = pairs
    return F


def f0_factorization(k):
    """The translation 1-factorization on Z=F_2^k: F_z = {a, a+z}."""
    return {z: [(a, a ^ z) for a in range(1 << k) if a < (a ^ z)] for z in range(1, 1 << k)}


def x_fib(d, k, chi, F1, g=None):
    """PG(d-1,2)-fibration with hole Z = F_2^k \\ 0.

    Points: Z\\0 (indices 0..2^k-2) and (c,a), c in F_2^d\\0, a in Z.
    chi(c) in {0,1}: fibre over c uses F^0 (translation) if 0, else F1.
    g: optional dict {(c1,c2,c3) sorted line: int in Z}: line cochain.
    Blocks: (i) lines of Z\\0; (ii) {z,(c,a),(c,b)}; (iii) {(c1,a),(c2,b),(c3,a^b^g)}."""
    nZ = (1 << k) - 1
    def pz(z):
        return z - 1
    def pc(c, a):
        return nZ + (c - 1) * (1 << k) + a
    n = nZ + ((1 << d) - 1) * (1 << k)
    bl = []
    for z in range(1, 1 << k):
        for w in range(z + 1, 1 << k):
            if (z ^ w) > w:
                bl.append((pz(z), pz(w), pz(z ^ w)))
    F0 = f0_factorization(k)
    for c in range(1, 1 << d):
        F = F0 if chi(c) == 0 else F1
        for z, pairs in F.items():
            for a, b in pairs:
                bl.append((pz(z), pc(c, a), pc(c, b)))
    for c1 in range(1, 1 << d):
        for c2 in range(c1 + 1, 1 << d):
            c3 = c1 ^ c2
            if c3 > c2:
                gv = 0 if g is None else g.get((c1, c2, c3), 0)
                for a in range(1 << k):
                    for b in range(1 << k):
                        bl.append((pc(c1, a), pc(c2, b), pc(c3, a ^ b ^ gv)))
    return from_blocks(n, bl)


def f1_acceptable(F1, k=3):
    """Check: (i) T^1 = Z\\0 + Z with F1 is an STS non-isomorphic to PG (exists non-Fano triangle);
    (ii) span condition: {a^b^z : {a,b} in F1_z} spans Z."""
    Q = x_fib_t1(F1, k)
    n = len(Q)
    # non-Fano triangle?
    nonfano = False
    for x in range(n):
        for y in range(x + 1, n):
            for z in range(y + 1, n):
                if Q[x][y] != z and closure_size(Q, [x, y, z]) != 7:
                    nonfano = True
                    break
            if nonfano:
                break
        if nonfano:
            break
    # span
    vecs = []
    for z, pairs in F1.items():
        for a, b in pairs:
            vecs.append(a ^ b ^ z)
    rank = gf_rank(vecs)
    return nonfano, rank == k, Q


def x_fib_t1(F1, k=3):
    """The STS on Z\\0 u Z whose coset factorization is F1 (the T^1 of the writeup)."""
    nZ = (1 << k) - 1
    bl = []
    for z in range(1, 1 << k):
        for w in range(z + 1, 1 << k):
            if (z ^ w) > w:
                bl.append((z - 1, w - 1, (z ^ w) - 1))
    for z, pairs in F1.items():
        for a, b in pairs:
            bl.append((z - 1, nZ + a, nZ + b))
    return from_blocks(nZ + (1 << k), bl)


def random_g(d, k, rng, density=0.5):
    """Random line cochain on PG(d-1,2) with values in F_2^k (nonzero with probability `density`)."""
    g = {}
    for c1 in range(1, 1 << d):
        for c2 in range(c1 + 1, 1 << d):
            c3 = c1 ^ c2
            if c3 > c2:
                if rng.random() < density:
                    g[(c1, c2, c3)] = rng.randrange(1, 1 << k)
    return g


def pasch_switch_pg(m, ops, rng):
    """PG(m-1,2) with `ops` random Pasch switches.

    Each operation picks a random plane-like set {a,b,a^b,d,a^d,b^d} forming the Pasch with missing
    point a^b^d, inside the current system, and if its 4 blocks are still blocks, replaces
    {a,b,a^b},{a,d,a^d},{b^d,b,d},{b^d,a^b,a^d} by the standard switch."""
    n = 2 ** m - 1
    Q = pg(m)
    done = 0
    tries = 0
    while done < ops and tries < 100000:
        tries += 1
        a, b, d = rng.randrange(1, n + 1), rng.randrange(1, n + 1), rng.randrange(1, n + 1)
        if len({a, b, d, a ^ b, a ^ d, b ^ d, a ^ b ^ d, 0}) < 8:
            continue
        ai, bi, di = a - 1, b - 1, d - 1
        abi, adi, bdi = (a ^ b) - 1, (a ^ d) - 1, (b ^ d) - 1
        blocks = [(ai, bi, abi), (ai, di, adi), (bdi, bi, di), (bdi, abi, adi)]
        if not all(Q[x][y] == z for x, y, z in blocks):
            continue
        # Pasch: {a,b,c},{a,d,e},{f,b,d},{f,c,e} with c=ab,e=ad,f=bd; switch to {a,b,d},{a,c,e},{b,c,f},{d,e,f}.
        c, e, f = abi, adi, bdi
        for x, y, z in blocks:
            pass
        new = [(ai, bi, di), (ai, c, e), (bi, c, f), (di, e, f)]
        for x, y, z in new:
            for (p, q, r) in ((x, y, z), (x, z, y), (y, x, z), (y, z, x), (z, x, y), (z, y, x)):
                Q[p][q] = r
        done += 1
    return Q
