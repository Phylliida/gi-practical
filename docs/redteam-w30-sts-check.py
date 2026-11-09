#!/usr/bin/env python3
"""Referee checks for docs/w30-sts.md (report: docs/redteam-w30-sts.md).

Run from the repository root with an interpreter that has pynauty:
    nice -n 19 python -I docs/redteam-w30-sts-check.py [section ...]
Sections: gadget t2 t2d4 t2d5 nauty alt trace t1 t3 t5 c4 iso aut   (default: all; about 15 min, one process.)
Standard library plus pynauty. docs/w30-sts-code/sts.py is imported only for cross-comparison of constructions.

Exact tools (no hashing anywhere; invariants are compared as exact interned integer tuples):
  * build(): X_chi from the definition in w30 Section 6, written from scratch.
  * pair_inv()/point_inv(): cycle types of x -> p*(q*x) and multisets thereof.  Trivially isomorphism-invariant.
  * iso_search(): exact Miller-style generator enumeration with closure propagation; returns a verified witness
    or exhausts the search.  With node_limit=None it is a decision procedure.  Colours from invariants are safe
    because any isomorphism preserves them.
  * nauty_cert(): canonical form of the point-block incidence graph, optionally with the invariant colouring.
"""
import sys, os, itertools, random, math, time, signal
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "w30-sts-code"))
sys.setrecursionlimit(100000)
import sts as memo  # the memo's code: used only to compare constructions and for exact-cover-free helpers
import pynauty

FTABLE = {1: "05 12 34 67", 2: "02 16 37 45", 3: "07 15 24 36", 4: "04 17 23 56",
          5: "01 27 35 46", 6: "06 13 25 47", 7: "03 14 26 57"}


def memo_F1():
    return {z: [(int(p[0]), int(p[1])) for p in s.split()] for z, s in FTABLE.items()}


# ---------- construction of X_chi (referee's own)

def build(d, chi, F1, k=3):
    """chi: list of length 2^d indexed by c (chi[0] ignored); points z-1 (z in Z\\0) then (c,a)."""
    Zs = 1 << k
    nZ = Zs - 1
    def pz(z): return z - 1
    def pc(c, a): return nZ + (c - 1) * Zs + a
    n = nZ + ((1 << d) - 1) * Zs
    blocks = []
    for z in range(1, Zs):
        for w in range(z + 1, Zs):
            if (z ^ w) > w:
                blocks.append((pz(z), pz(w), pz(z ^ w)))
    F0 = {z: [(a, a ^ z) for a in range(Zs) if a < (a ^ z)] for z in range(1, Zs)}
    for c in range(1, 1 << d):
        F = F0 if chi[c] == 0 else F1
        for z, pairs in F.items():
            for a, b in pairs:
                blocks.append((pz(z), pc(c, a), pc(c, b)))
    for c1 in range(1, 1 << d):
        for c2 in range(c1 + 1, 1 << d):
            c3 = c1 ^ c2
            if c3 > c2:
                for a in range(Zs):
                    for b in range(Zs):
                        blocks.append((pc(c1, a), pc(c2, b), pc(c3, a ^ b)))
    assert len(blocks) == n * (n - 1) // 6, "block count"
    Q = [[-1] * n for _ in range(n)]
    for x in range(n):
        Q[x][x] = x
    for a, b, c in blocks:
        for x, y, z in ((a, b, c), (b, a, c), (a, c, b), (c, a, b), (b, c, a), (c, b, a)):
            if Q[x][y] != -1:
                raise ValueError("pair covered twice")
            Q[x][y] = z
    if any(Q[x][y] == -1 for x in range(n) for y in range(n)):
        raise ValueError("pair not covered")
    return Q


def gl_matrices(d):
    res = []
    def rec(cols, span):
        if len(cols) == d:
            res.append(tuple(cols))
            return
        for v in range(1, 1 << d):
            if v not in span:
                rec(cols + [v], span | {s ^ v for s in span})
    rec([], {0})
    return res


def apply_mat(A, x):
    r = 0
    i = 0
    while x:
        if x & 1:
            r ^= A[i]
        x >>= 1
        i += 1
    return r


def transform(chi, A, d):
    """chi' with chi'(Ac)=chi(c)."""
    r = [0] * (1 << d)
    for c in range(1, 1 << d):
        r[apply_mat(A, c)] = chi[c]
    return r


def orbits_of(d, GL):
    seen = {}
    orbs = []
    for bits in itertools.product([0, 1], repeat=(1 << d) - 1):
        chi = (0,) + bits
        if chi in seen:
            continue
        orb = {tuple(transform(list(chi), A, d)) for A in GL}
        i = len(orbs)
        for o in orb:
            seen[o] = i
        orbs.append(sorted(orb))
    return seen, orbs


def nonconstant(chi):
    return 0 < sum(chi[1:]) < len(chi) - 1


# ---------- exact invariants and exact search

CTX = {}


def intern(t):
    v = CTX.get(t)
    if v is None:
        v = len(CTX)
        CTX[t] = v
    return v


def pair_inv(Q):
    n = len(Q)
    inv = [[0] * n for _ in range(n)]
    for p in range(n):
        Qp = Q[p]
        for q in range(n):
            Qq = Q[q]
            seen = [False] * n
            cyc = []
            for x in range(n):
                if not seen[x]:
                    l = 0
                    y = x
                    while not seen[y]:
                        seen[y] = True
                        y = Qp[Qq[y]]
                        l += 1
                    cyc.append(l)
            cyc.sort()
            inv[p][q] = intern(tuple(cyc))
    return inv


def point_inv(pi):
    n = len(pi)
    return [intern(("p", tuple(sorted(pi[p][q] for q in range(n))))) for p in range(n)]


def iso_search(Q1, Q2, pi1=None, pi2=None, col1=None, col2=None, node_limit=None):
    """Exact decision by generator enumeration with closure propagation. Returns (witness|None, nodes, exhausted)."""
    n = len(Q1)
    assert len(Q2) == n
    if pi1 is None:
        pi1 = pair_inv(Q1)
    if pi2 is None:
        pi2 = pair_inv(Q2)
    if col1 is None:
        col1 = point_inv(pi1)
    if col2 is None:
        col2 = point_inv(pi2)
    if Counter(col1) != Counter(col2):
        return None, 0, True
    classes = Counter(col1)
    gens = []
    inC = [False] * n
    C = []

    def add(s):
        stack = [s]
        while stack:
            x = stack.pop()
            if inC[x]:
                continue
            inC[x] = True
            C.append(x)
            for y in list(C):
                z = Q1[x][y]
                if not inC[z]:
                    stack.append(z)

    while len(C) < n:
        rest = [x for x in range(n) if not inC[x]]
        g = min(rest, key=lambda x: (classes[col1[x]], x))
        gens.append(g)
        add(g)
    cand = {g: [y for y in range(n) if col2[y] == col1[g]] for g in gens}
    nodes = 0
    f = [-1] * n
    finv = [-1] * n

    def extend(p, q):
        added = []
        stack = [(p, q)]
        while stack:
            u, v = stack.pop()
            if f[u] != -1:
                if f[u] != v:
                    return added, False
                continue
            if finv[v] != -1 or col1[u] != col2[v]:
                return added, False
            f[u] = v
            finv[v] = u
            added.append(u)
            for w in range(n):
                fw = f[w]
                if fw == -1:
                    continue
                if pi1[u][w] != pi2[v][fw] or pi1[w][u] != pi2[fw][v]:
                    return added, False
                x = Q1[u][w]
                y = Q2[v][fw]
                if f[x] != -1:
                    if f[x] != y:
                        return added, False
                else:
                    stack.append((x, y))
        return added, True

    def undo(added):
        for u in added:
            finv[f[u]] = -1
            f[u] = -1

    witness = None
    aborted = False

    def rec(i):
        nonlocal nodes, witness, aborted
        if i == len(gens):
            witness = list(f)
            return True
        g = gens[i]
        if f[g] != -1:
            return rec(i + 1)
        for y in cand[g]:
            nodes += 1
            if node_limit is not None and nodes > node_limit:
                aborted = True
                return False
            if finv[y] != -1:
                continue
            added, ok = extend(g, y)
            if ok and rec(i + 1):
                return True
            undo(added)
            if aborted:
                return False
        return False

    rec(0)
    if witness is not None:
        assert sorted(witness) == list(range(n))
        for x in range(n):
            for y in range(n):
                assert Q2[witness[x]][witness[y]] == witness[Q1[x][y]]
    return witness, nodes, not aborted


def nauty_cert(Q, col=None):
    n = len(Q)
    bl = memo.blocks_of(Q)
    v = n + len(bl)
    adj = {i: [] for i in range(v)}
    for j, b in enumerate(bl):
        for x in b:
            adj[x].append(n + j)
            adj[n + j].append(x)
    if col is None:
        vc = [set(range(n)), set(range(n, v))]
    else:
        cls = {}
        for p, c in enumerate(col):
            cls.setdefault(c, set()).add(p)
        vc = [cls[c] for c in sorted(cls)] + [set(range(n, v))]
    return pynauty.certificate(pynauty.Graph(number_of_vertices=v, directed=False, adjacency_dict=adj, vertex_coloring=vc))


def char_space(Q):
    """Basis of {f:X->F_2, sum 0 on every block}, as n-bit ints."""
    n = len(Q)
    rows = []
    for x in range(n):
        for y in range(x + 1, n):
            z = Q[x][y]
            if z > y:
                rows.append((1 << x) | (1 << y) | (1 << z))
    piv = {}
    for r in rows:
        v = r
        while v:
            h = v.bit_length() - 1
            if h in piv:
                v ^= piv[h]
            else:
                piv[h] = v
                break
    free = [i for i in range(n) if i not in piv]
    basis = []
    for fr in free:
        f = 1 << fr
        for h in sorted(piv):
            r = piv[h]
            lower = r & ~(1 << h)
            if bin(f & lower).count("1") & 1:
                f |= 1 << h
        basis.append(f)
    for f in basis:
        for r in rows:
            assert bin(f & r).count("1") % 2 == 0
    return basis


def plain_latin_cert(T):
    """Nauty certificate of a Latin square up to isotopy (rows, columns, symbols, cells as four colour classes)."""
    n = len(T)
    v = 3 * n + n * n
    adj = {i: [] for i in range(v)}
    for r in range(n):
        for c in range(n):
            cell = 3 * n + r * n + c
            for u in (r, n + c, 2 * n + T[r][c]):
                adj[cell].append(u)
                adj[u].append(cell)
    col = [set(range(n)), set(range(n, 2 * n)), set(range(2 * n, 3 * n)), set(range(3 * n, v))]
    return pynauty.certificate(pynauty.Graph(number_of_vertices=v, directed=False, adjacency_dict=adj, vertex_coloring=col))


def factor_square(F):
    """M_1: symmetric unipotent square of a labelled 1-factorization of K_8."""
    T = [[0] * 8 for _ in range(8)]
    for z, ps in F.items():
        for a, b in ps:
            T[a][b] = z
            T[b][a] = z
    return T


# ---------- Section: gadget properties

def s_gadget():
    print("=== gadget: the displayed table F^1 ===")
    F1 = memo_F1()
    pairs = sorted(tuple(sorted(p)) for z in F1 for p in F1[z])
    print(" 1-factorization of K_8:", pairs == sorted(itertools.combinations(range(8), 2)),
          all(sorted(sum(F1[z], ())) == list(range(8)) for z in F1))
    nf, sp, T = memo.f1_acceptable(F1, 3)
    print(" (a) T^1 has a non-Fano triangle:", nf, "| (b) span condition:", sp, "| T^1 is an STS:", memo.is_sts(T))
    rng = random.Random(7)
    while True:
        Fs = memo.patterned_factorization_k8(rng)
        a, b, _ = memo.f1_acceptable(Fs, 3)
        if a and b:
            break
    norm = lambda F: {k: sorted(tuple(sorted(p)) for p in v) for k, v in F.items()}
    print(" table equals seed-7 output of the memo's script:", norm(Fs) == norm(F1))
    print(" T^1 2-rank char dim:", memo.char_space_dim(T))


# ---------- Section: T2 exhaustive, d=2,3

def s_t2():
    print("=== T2: exhaustive decisions, d=2,3 (all pairs of colourings, both directions) ===")
    F1 = memo_F1()
    for d in (2, 3):
        GL = gl_matrices(d)
        seen, orbs = orbits_of(d, GL)
        print(f" d={d}: |GL|={len(GL)} colourings={len(seen)} orbits={len(orbs)} sizes={sorted(len(o) for o in orbs)}")
        for t in seen:
            assert build(d, list(t), F1) == memo.x_fib(d, 3, lambda c: t[c], F1)
        print("  referee build == memo x_fib on every colouring")
        keys = sorted(seen)
        t0 = time.time()
        Qs = {k: build(d, list(k), F1) for k in keys}
        for k in keys:
            assert memo.is_sts(Qs[k])
        pis = {k: pair_inv(Qs[k]) for k in keys}
        cols = {k: point_inv(pis[k]) for k in keys}
        res = Counter()
        wit = 0
        total_nodes = 0
        for i, a in enumerate(keys):
            for b in keys[i:]:
                exp = seen[a] == seen[b]
                w, nodes, ex = iso_search(Qs[a], Qs[b], pis[a], pis[b], cols[a], cols[b])
                assert ex
                got = w is not None
                total_nodes += nodes
                wit += got
                nc = nonconstant(a) and nonconstant(b)
                res[("agree" if got == exp else "MISMATCH", got, nc)] += 1
                if got != exp:
                    print("  MISMATCH", a, b, got, exp)
        print(f"  all {len(keys)*(len(keys)+1)//2} unordered pairs: {dict(res)}; witnesses verified {wit}; nodes {total_nodes}; {time.time()-t0:.1f}s")
        # forward map, every chi and every A
        t0 = time.time()
        cnt = 0
        for chi in keys:
            for A in GL:
                chi2 = tuple(transform(list(chi), A, d))
                Q = Qs[chi]
                Q2 = Qs[chi2]
                def phi(p):
                    if p < 7:
                        return p
                    p -= 7
                    c = p // 8 + 1
                    a = p % 8
                    return 7 + (apply_mat(A, c) - 1) * 8 + a
                assert all(Q2[phi(x)][phi(y)] == phi(Q[x][y]) for x in range(len(Q)) for y in range(len(Q)))
                cnt += 1
        print(f"  explicit forward map verified block-by-block for every (chi,A): {cnt} pairs; {time.time()-t0:.1f}s")


def s_t2d4():
    print("=== T2: d=4 (46 GL(4,2)-orbits) ===")
    F1 = memo_F1()
    rng = random.Random(33)
    d = 4
    GL = gl_matrices(d)
    seen, orbs = orbits_of(d, GL)
    print(f" orbits={len(orbs)}, of which nonconstant={sum(1 for o in orbs if nonconstant(o[0]))}")
    t0 = time.time()
    reps = [o[0] for o in orbs]
    Qs = [build(d, list(r), F1) for r in reps]
    pis = [pair_inv(Q) for Q in Qs]
    cols = [point_inv(p) for p in pis]
    sigs = [tuple(sorted(Counter(c).items())) for c in cols]
    print(" exact point-invariant multisets distinct on all reps:", len(set(sigs)) == len(reps), f"({len(set(sigs))}/{len(reps)})")
    for i, j in itertools.combinations(range(len(reps)), 2):
        if sigs[i] == sigs[j]:
            w, nodes, ex = iso_search(Qs[i], Qs[j], pis[i], pis[j], cols[i], cols[j])
            print("  coincident invariants at", i, j, "iso?", w is not None, "exhausted", ex)
    ok = 0
    for t in range(40):
        i = rng.randrange(len(reps))
        A = rng.choice(GL)
        chi = list(rng.choice(orbs[i]))
        chi2 = transform(chi, A, d)
        Q = build(d, chi, F1)
        Q2 = build(d, chi2, F1)
        w, nodes, ex = iso_search(Q, Q2, node_limit=500000)
        assert w is not None
        ok += 1
    print(f" independent search found verified isomorphisms on {ok} random equivalent pairs; {time.time()-t0:.0f}s")


def s_t2d5():
    print("=== T2: d=5 sample (n=255), nauty with invariant colouring ===")
    F1 = memo_F1()
    rng = random.Random(1010)
    d = 5

    def rand_gl():
        while True:
            cols = [rng.randrange(1, 1 << d) for _ in range(d)]
            span = {0}
            ok = True
            for c in cols:
                if c in span:
                    ok = False
                    break
                span |= {s ^ c for s in span}
            if ok:
                return tuple(cols)

    def walsh(chi):
        N = 1 << d
        return tuple(sorted(sum((-1) ** (chi[x] ^ (bin(x & u).count("1") & 1)) for x in range(N)) for u in range(N)))

    def cert_of(chi):
        Q = build(d, chi, F1)
        return nauty_cert(Q, point_inv(pair_inv(Q)))

    t0 = time.time()
    for t in range(3):
        chi = [0] + [rng.randrange(2) for _ in range(31)]
        chi2 = transform(chi, rand_gl(), d)
        assert cert_of(chi) == cert_of(chi2)
    print(f" 3 planted positives: certificates equal; {time.time()-t0:.0f}s", flush=True)
    for t in range(3):
        while True:
            chi = [0] + [rng.randrange(2) for _ in range(31)]
            chi2 = list(chi)
            ones = [i for i in range(1, 32) if chi[i]]
            zeros = [i for i in range(1, 32) if not chi[i]]
            chi2[rng.choice(ones)] = 0
            chi2[rng.choice(zeros)] = 1
            if walsh(chi) != walsh(chi2):
                break
        assert cert_of(chi) != cert_of(chi2)
    print(f" 3 negatives (equal weight, |Walsh| multiset differs, so not GL-equivalent): certificates differ; {time.time()-t0:.0f}s")


def s_nauty():
    print("=== T2: nauty cross-validation of the exact search ===")
    F1 = memo_F1()
    keys = [(0,) + b for b in itertools.product([0, 1], repeat=3)]
    Qs = {k: build(2, list(k), F1) for k in keys}
    certs = {k: nauty_cert(Qs[k]) for k in keys}
    agree = 0
    for a in keys:
        for b in keys:
            w, _, ex = iso_search(Qs[a], Qs[b])
            assert ex and (w is not None) == (certs[a] == certs[b]), (a, b)
            agree += 1
    print(f" d=2: search agrees with plain nauty on all {agree} ordered pairs (no invariant colouring)")
    # d=3 and a d=4 sample with invariant colouring
    rng = random.Random(2)
    for d, extra in ((3, 0), (4, 150)):
        GL = gl_matrices(d)
        seen, orbs = orbits_of(d, GL)
        chk = [o[rng.randrange(len(o))] for o in orbs] + [rng.choice(sorted(seen)) for _ in range(extra)]
        t0 = time.time()
        cls = {}
        for key in chk:
            Q = build(d, list(key), F1)
            c = nauty_cert(Q, point_inv(pair_inv(Q)))
            cls.setdefault(c, []).append(seen[key])
        print(f" d={d}: {len(chk)} colourings -> {len(cls)} nauty certificate classes; every class one GL-orbit: {all(len(set(v))==1 for v in cls.values())}; every orbit one class: {len({tuple(sorted(set(v))) for v in cls.values()})==len(orbs)}; {time.time()-t0:.0f}s", flush=True)


def s_alt():
    print("=== T2: other gadgets, and negative controls ===")
    rng = random.Random(4242)
    pts = list(range(8))

    def pms():
        res = []
        def rec(rem, cur):
            if not rem:
                res.append(tuple(cur))
                return
            a = rem[0]
            for b in rem[1:]:
                rec([x for x in rem[1:] if x != b], cur + [(a, b)])
        rec(pts, [])
        return res

    pm = pms()
    edge_pm = {}
    for i, m in enumerate(pm):
        for e in m:
            edge_pm.setdefault(e, []).append(i)
    pm_edges = [set(m) for m in pm]
    edges = list(itertools.combinations(pts, 2))
    sols = []

    def rec(cov, cur):
        for e in edges:
            if e not in cov:
                break
        else:
            sols.append(list(cur))
            return
        for i in edge_pm[e]:
            if pm_edges[i] & cov:
                continue
            rec(cov | pm_edges[i], cur + [i])

    rec(frozenset(), [])
    print(" 1-factorizations of K_8:", len(sols))

    def ftype(sol):
        Fs = [pm[i] for i in sol]
        cts = []
        for a, b in itertools.combinations(Fs, 2):
            adj = {p: [] for p in pts}
            for x, y in a + b:
                adj[x].append(y)
                adj[y].append(x)
            seen = set()
            cyc = []
            for p in pts:
                if p in seen:
                    continue
                l = 0
                st = [p]
                seen.add(p)
                while st:
                    u = st.pop()
                    l += 1
                    for w in adj[u]:
                        if w not in seen:
                            seen.add(w)
                            st.append(w)
                cyc.append(l)
            cts.append(tuple(sorted(cyc)))
        return tuple(sorted(cts))

    types = Counter(ftype(s) for s in sols)
    print(" isomorphism-type sizes (via union cycle-type invariant):", sorted(types.values()))
    typeindex = {t: i for i, t in enumerate(sorted(types))}

    def test_F(F, d=3):
        GL = gl_matrices(d)
        seen, orbs = orbits_of(d, GL)
        nc = [o[0] for o in orbs if nonconstant(o[0])]
        Qs = [build(d, list(r), F) for r in nc]
        pis = [pair_inv(Q) for Q in Qs]
        cols = [point_inv(p) for p in pis]
        bad = coll = 0
        for i in range(len(nc)):
            for j in range(i + 1, len(nc)):
                w, nodes, ex = iso_search(Qs[i], Qs[j], pis[i], pis[j], cols[i], cols[j])
                assert ex
                coll += Counter(cols[i]) == Counter(cols[j])
                bad += w is not None
        return len(nc), coll, bad

    t0 = time.time()
    tested = Counter()
    total_bad = 0
    for s in rng.sample(sols, min(1500, len(sols))):
        perm = list(range(1, 8))
        rng.shuffle(perm)
        F = {perm[i]: list(pm[s[i]]) for i in range(7)}
        nf, sp, _ = memo.f1_acceptable(F, 3)
        ty = typeindex[ftype(s)]
        if not (nf and sp):
            tested[(ty, "rejected")] += 1
            continue
        if tested[(ty, "ok")] >= 8:
            continue
        _, coll, bad = test_F(F, 3)
        tested[(ty, "ok")] += 1
        total_bad += bad
    print(f" sampled F^1 per type (type,'ok'/'rejected by (a),(b)'): {dict(tested)}; non-equivalent pairs isomorphic: {total_bad}; {time.time()-t0:.0f}s", flush=True)
    F0 = {z: [(a, a ^ z) for a in range(8) if a < (a ^ z)] for z in range(1, 8)}
    cnt = rej = bad = 0
    for trial in range(400):
        pi = list(range(1, 8))
        rng.shuffle(pi)
        F = {z: F0[pi[z - 1]] for z in range(1, 8)}
        nf, sp, _ = memo.f1_acceptable(F, 3)
        if not (nf and sp):
            rej += 1
            continue
        cnt += 1
        bad += test_F(F, 3)[2]
        if cnt >= 10:
            break
    print(f" adversarial: Cayley factorization relabelled by non-linear pi (Latin square of F^1 isotopic to Z_2^3 Cayley) tested {cnt} (rejected by (a),(b): {rej}); isomorphic non-equivalent pairs: {bad}", flush=True)
    # controls: (i) F^1=F^0 makes the gadget invisible: tester must report all isomorphic.
    d = 3
    GL = gl_matrices(d)
    seen, orbs = orbits_of(d, GL)
    nc = [o[0] for o in orbs if nonconstant(o[0])]
    Qs = [build(d, list(r), F0) for r in nc]
    pis = [pair_inv(Q) for Q in Qs]
    cols = [point_inv(p) for p in pis]
    alls = all(iso_search(Qs[i], Qs[j], pis[i], pis[j], cols[i], cols[j])[0] is not None for i in range(len(nc)) for j in range(i + 1, len(nc)))
    print(" control F^1=F^0 (invisible gadget): all non-equivalent nonconstant pairs reported isomorphic:", alls)
    # control (ii): F^1 = linear relabel of F^0 (T^1 = PG(3,2), (a) false): test colour-complement collapse
    A = (3, 5, 7)
    assert len({apply_mat(A, z) for z in range(1, 8)}) == 7
    Flin = {z: F0[apply_mat(A, z)] for z in range(1, 8)}
    print(" control (a)-false gadget F^1_z=F^0_{Az}: (a),(b)=", memo.f1_acceptable(Flin, 3)[:2])
    qs = {o[0]: build(d, list(o[0]), Flin) for o in orbs if nonconstant(o[0])}
    # is X_chi iso to X_{complement of chi}? compare invariants of chi and of its complement
    results = Counter()
    for chi, Q in qs.items():
        comp = (0,) + tuple(1 - b for b in chi[1:])
        Q2 = build(d, list(comp), Flin)
        w, _, ex = iso_search(Q, Q2)
        results[("complement isomorphic" if w is not None else "complement not isomorphic", seen[chi] == seen[comp])] += 1
    print("  complement results over nonconstant orbit reps ((isomorphic?, complement equivalent?), count):", dict(results))
    # (b)-failing gadget, (a) true
    found = None
    rng2 = random.Random(2)
    for s in rng2.sample(sols, 2000):
        p = list(range(1, 8))
        rng2.shuffle(p)
        F = {p[i]: list(pm[s[i]]) for i in range(7)}
        a, b, _ = memo.f1_acceptable(F, 3)
        if a and not b:
            found = F
            break
    if found:
        Qs = [build(3, list(r), found) for r in nc]
        pis = [pair_inv(Q) for Q in Qs]
        cols = [point_inv(p) for p in pis]
        bad = sum(iso_search(Qs[i], Qs[j], pis[i], pis[j], cols[i], cols[j])[0] is not None for i in range(len(nc)) for j in range(i + 1, len(nc)))
        print(f" (b)-false gadget: char dims of nonconstant X_chi {sorted({len(char_space(Q)) for Q in Qs})}; isomorphic non-equivalent pairs {bad}")
    print(" also: the proof step 'character space dimension is exactly d' fails for (b)-false gadgets (dimension d+1 above), so (b) is a real proof hypothesis even though no collision occurred.")
    # condition (c) of Prop. A, one representative of each isomorphism type
    cay = plain_latin_cert([[x ^ y for y in range(8)] for x in range(8)])
    byt = {}
    for s in sols:
        byt.setdefault(typeindex[ftype(s)], s)
    sizes = {typeindex[t]: v for t, v in types.items()}
    for ty in sorted(byt):
        F = {z + 1: list(pm[byt[ty][z]]) for z in range(7)}
        print(f" type {ty} (labelled count {sizes[ty]}): M_1 isotopic to the Cayley table of F_2^3: {plain_latin_cert(factor_square(F)) == cay}")


def s_trace():
    print("=== T2: proof trace on instances (characters, kernel S, cosets, colour recovery) ===")
    F1 = memo_F1()

    def trace(d, chi, Q):
        n = len(Q)
        basis = char_space(Q)
        if len(basis) != d:
            return ("chardim", len(basis))
        S = [x for x in range(n) if all((f >> x) & 1 == 0 for f in basis)]
        if S != list(range(7)):
            return ("kernel", S)
        sig = {}
        for x in range(n):
            if x in S:
                continue
            sig.setdefault(tuple((f >> x) & 1 for f in basis), []).append(x)
        if len(sig) != (1 << d) - 1 or any(len(v) != 8 for v in sig.values()):
            return ("classes",)
        if {frozenset(v) for v in sig.values()} != {frozenset(range(7 + (c - 1) * 8, 7 + c * 8)) for c in range(1, 1 << d)}:
            return ("fibres",)
        for c in range(1, 1 << d):
            pts = list(range(7)) + list(range(7 + (c - 1) * 8, 7 + c * 8))
            idx = {p: i for i, p in enumerate(pts)}
            sub = [[idx[Q[a][b]] for b in pts] for a in pts]
            isPG = all(memo.closure_size(sub, [x, y, z]) == 7 for x, y, z in itertools.combinations(range(15), 3) if sub[x][y] != z)
            if isPG != (chi[c] == 0):
                return ("colour", c)
        return "ok"

    for d in (2, 3, 4):
        GL = gl_matrices(d)
        seen, orbs = orbits_of(d, GL)
        res = Counter()
        for o in orbs:
            if nonconstant(o[0]):
                res[str(trace(d, o[0], build(d, list(o[0]), F1)))] += 1
        print(f" d={d}: nonconstant orbit reps, proof-step results: {dict(res)}", flush=True)
    for d in (2, 3, 4):
        for b in (0, 1):
            chi = [0] + [b] * ((1 << d) - 1)
            print(f" constant chi={b}, d={d}: char dim {len(char_space(build(d, chi, F1)))}")


# ---------- Section: T1, Lemma 1, exact subsystem lattices

LAM0 = math.log2(9) / 3
LAM1 = math.log2(10) / 3


def closure_add(Q, mask, x):
    if mask >> x & 1:
        return mask
    n = len(Q)
    members = [i for i in range(n) if mask >> i & 1]
    S = mask | (1 << x)
    new = [x]
    while new:
        y = new.pop()
        Qy = Q[y]
        for z in members:
            w = Qy[z]
            if not S >> w & 1:
                S |= 1 << w
                new.append(w)
        members.append(y)
    return S


def lattice(Q, maxlevels=20, limit=2000000):
    n = len(Q)
    rho = {0: 0}
    level = [0]
    r = 0
    while level and r < maxlevels:
        r += 1
        nxt = []
        for T in level:
            for x in range(n):
                if T >> x & 1:
                    continue
                S = closure_add(Q, T, x)
                if S not in rho:
                    rho[S] = r
                    nxt.append(S)
            if len(rho) > limit:
                raise RuntimeError("too many subsystems")
        level = nxt
    return rho


def is_subsystem(Q, mask):
    n = len(Q)
    ms = [i for i in range(n) if mask >> i & 1]
    return all(mask >> Q[a][b] & 1 for a in ms for b in ms)


def check_T1(Q, lams, rho):
    n = len(Q)
    full = (1 << n) - 1
    r = rho[full]
    ell = math.log2(n + 1)
    c = ell - r
    bad = []
    for T, rT in rho.items():
        sz = bin(T).count("1")
        if not (r <= rT + math.floor(math.log2((n + 1) / (sz + 1))) + 1e-12):
            bad.append(("L1", T))
        if not (sz + 1 <= 2 ** (rT + c) + 1e-9):
            bad.append(("size-bound", T))
    res = []
    for lam in lams:
        psi = lambda T: math.log2(bin(T).count("1") + 1) - lam * rho[T]
        best = max(psi(T) for T in rho)
        maxers = [T for T in rho if abs(psi(T) - best) < 1e-9]
        forced = lam * r > ell + 1e-9
        for S in maxers:
            s = bin(S).count("1")
            if forced and S == full:
                bad.append(("S=X though lam r>ell", lam))
            if S == full:
                continue
            outside = [x for x in range(n) if not S >> x & 1]
            cos = {}
            classes = []
            for x in outside:
                if x in cos:
                    continue
                T = closure_add(Q, S, x)
                C = T & ~S
                mem = [i for i in range(n) if C >> i & 1]
                if len(mem) < s + 1:
                    bad.append(("coset too small", lam))
                for v in mem:
                    if v in cos:
                        bad.append(("overlap", lam))
                    cos[v] = len(classes)
                classes.append(C)
                if not is_subsystem(Q, S | C):
                    bad.append(("T_x not subsystem", lam))
            sizes = {bin(C).count("1") for C in classes}
            if len(sizes) != 1:
                bad.append(("coset sizes differ", lam, sizes))
                continue
            a = sizes.pop()
            p = len(classes)
            third = {}
            ok = True
            for i in range(p):
                mi = [v for v in outside if cos[v] == i]
                for j in range(i + 1, p):
                    mj = [v for v in outside if cos[v] == j]
                    ts = {cos.get(Q[x][y], -1) for x in mi for y in mj}
                    if len(ts) != 1 or -1 in ts or i in ts or j in ts:
                        bad.append(("third coset", lam))
                        ok = False
                        break
                    third[(i, j)] = ts.pop()
                if not ok:
                    break
            if not ok:
                continue
            P = [[(i if i == j else third[(min(i, j), max(i, j))]) for j in range(p)] for i in range(p)]
            if not memo.is_sts(P):
                bad.append(("quotient not STS", lam))
                continue
            d = math.log2(p + 1)
            if abs(d - round(d)) > 1e-9:
                bad.append(("p+1 not 2-power", lam, p))
                continue
            d = int(round(d))
            for i, j, k in itertools.combinations(range(p), 3):
                if P[i][j] != k and memo.closure_size(P, [i, j, k]) != 7:
                    bad.append(("quotient triangle not Fano", lam))
                    break
            if n != s + a * (2 ** d - 1):
                bad.append(("count", lam))
            rS = rho[S]
            if not rS <= c / (lam - 1) + 1e-9:
                bad.append(("rho(S) bound", lam))
            if not math.log2(s + 1) <= rS + c + 1e-9:
                bad.append(("log s bound", lam))
            if not r <= rS + d:
                bad.append(("rk<=rho+d", lam))
            if not d >= r - c / (lam - 1) - 1e-9:
                bad.append(("d lower bound", lam))
            if not 2 ** d * (s + 1) <= n + 1:
                bad.append(("2^d(s+1)", lam))
            res.append((lam, s, rS, a, p, d))
    return r, c, bad, res, len(rho)


def s_t1():
    print("=== T1/Lemma 1: exact subsystem lattices, every maximizer ===")
    print(f" lambda_0=(log2 9)/3={LAM0:.6f}  1/lambda_0={1/LAM0:.6f}  1/(lambda_0-1)={1/(LAM0-1):.4f}")
    print(f" lambda_1=(log2 10)/3={LAM1:.6f}  1/lambda_1={1/LAM1:.6f}  1/(lambda_1-1)={1/(LAM1-1):.4f}")
    rng = random.Random(30)
    F1 = memo_F1()
    LAMS = [1.001, 1.02, 1.05, 1.0566, 1.08, 1.10, 1.1072]
    fam = []
    for m in range(2, 7):
        fam.append((f"PG({m-1},2)", memo.pg(m)))
    fam.append(("AG(2,3)", memo.ag3(2)))
    fam.append(("AG(3,3)", memo.ag3(3)))
    for d in (2, 3):
        GL = gl_matrices(d)
        seen, orbs = orbits_of(d, GL)
        for o in orbs:
            fam.append((f"X_chi d={d} chi={''.join(map(str,o[0][1:]))}", build(d, list(o[0]), F1)))
    for d in (3, 4, 5):
        for t in range(4):
            g = memo.random_g(d, 1, rng)
            fam.append((f"X_g d={d} k=1 #{t}", memo.x_fib(d, 1, lambda c: 0, {1: [(0, 1)]}, g)))
    for t in range(3):
        fam.append((f"double(PG(3,2))#{t}", memo.doubling(memo.pg(4), rng)))
    for t in range(6):
        n = rng.choice([15, 19, 27, 31, 33, 39])
        fam.append((f"hillclimb({n})#{t}", memo.random_sts_hillclimb(n, rng)))
    seen15 = {}
    for t in range(1500):
        Q = memo.random_sts_hillclimb(15, rng)
        k = tuple(sorted(Counter(point_inv(pair_inv(Q))).items()))
        seen15.setdefault(k, Q)
    print(f" sampled {len(seen15)} point-invariant types of STS(15)")
    for i, Q in enumerate(seen15.values()):
        fam.append((f"STS15#{i}", Q))
    nontriv = Counter()
    fails = 0
    t0 = time.time()
    summary = {}
    for name, Q in fam:
        if not memo.is_sts(Q):
            print("NOT STS", name)
            continue
        rho = lattice(Q)
        r, c, bad, res, sz = check_T1(Q, LAMS, rho)
        if bad:
            fails += 1
            print("FAIL", name, bad[:5], flush=True)
        for rr in res:
            nontriv[rr[1:]] += 1
        summary[name.split("#")[0]] = (len(Q), r, round(c, 3), sz, len(res))
    for k, v in list(summary.items())[:40]:
        print(f"  {k:30s} n={v[0]:3d} rank={v[1]} c={v[2]} #subsystems={v[3]} #maximizers(S!=X)={v[4]}")
    print(f" fails: {fails} of {len(fam)} systems; nontrivial S (s,rhoS,a,p,d) histogram {dict(nontriv)}; {time.time()-t0:.0f}s")
    # sharpness of (log2 10)/3
    Q = memo.ag3(2)
    rho = lattice(Q)
    full = (1 << 9) - 1
    for lam in (1.1072, 1.1074, 1.2):
        psi = lambda T: math.log2(bin(T).count("1") + 1) - lam * rho[T]
        best = max(psi(T) for T in rho)
        ms = [T for T in rho if abs(psi(T) - best) < 1e-9]
        print(f" AG(2,3), lambda={lam}: maximizers (|S|,rho)={[(bin(T).count('1'),rho[T]) for T in ms][:3]}")
    print(" => at lambda just above (log2 10)/3 the maximizer of AG(2,3) is S=empty and the quotient is AG(2,3), not PG. Conclusion of T1 false there.")
    # exact ranks of the reduction instances
    for d in (2, 3):
        GL = gl_matrices(d)
        seen, orbs = orbits_of(d, GL)
        rs = Counter()
        for o in orbs:
            if nonconstant(o[0]):
                rs[lattice(build(d, list(o[0]), F1))[(1 << ((1 << (d + 3)) - 1)) - 1]] += 1
        print(f" exact rank of nonconstant X_chi, d={d} (n={2**(d+3)-1}, l={d+3}): histogram {dict(rs)} (T2 claims only rank >= d)")


# ---------- Section: T3

def check_T3(Q, q, lam):
    rho = lattice(Q)
    n = len(Q)
    full = (1 << n) - 1
    nonempty = [T for T in rho if T]
    psi = lambda T: math.log(bin(T).count("1"), q) - lam * rho[T]
    best = max(psi(T) for T in nonempty)
    maxers = [T for T in nonempty if abs(psi(T) - best) < 1e-9]
    out = Counter()
    for S in maxers:
        if S == full:
            out["S=X"] += 1
            continue
        s = bin(S).count("1")
        supers = [T for T in rho if T & S == S]
        if not all(bin(R2).count("1") >= q * bin(R).count("1") for R in supers for R2 in supers if R != R2 and R & R2 == R):
            out["index gap fails"] += 1
            continue
        outside = [x for x in range(n) if not S >> x & 1]
        cos = {}
        classes = []
        for x in outside:
            if x in cos:
                continue
            T = closure_add(Q, S, x)
            C = T & ~S
            for v in range(n):
                if C >> v & 1:
                    assert v not in cos
                    cos[v] = len(classes)
            classes.append(C)
        p = len(classes)
        linesets = {}
        for i, j in itertools.combinations(range(p), 2):
            x = next(v for v in outside if cos[v] == i)
            y = next(v for v in outside if cos[v] == j)
            U = closure_add(Q, closure_add(Q, S, x), y)
            linesets[frozenset((i, j))] = frozenset(cos[v] for v in outside if U >> v & 1)
        planes = set()
        for i, j, k in itertools.combinations(range(p), 3):
            if k in linesets[frozenset((i, j))]:
                continue
            x, y, z = [next(v for v in outside if cos[v] == t) for t in (i, j, k)]
            W = closure_add(Q, closure_add(Q, closure_add(Q, S, x), y), z)
            planes.add(frozenset(cos[v] for v in outside if W >> v & 1))
        out[f"s={s}: p={p}, line sizes {sorted({len(m) for m in linesets.values()})}, plane sizes {sorted({len(pp) for pp in planes})}"] += 1
    return dict(out)


def s_t3():
    print("=== T3: examples ===")
    for name, Q, q, lams in [("PG(3,2)", memo.pg(4), 2, [1.01, 1.05]), ("PG(4,2)", memo.pg(5), 2, [1.01, 1.05]),
                             ("AG(2,3)", memo.ag3(2), 3, [1.01, 1.02]), ("AG(3,3)", memo.ag3(3), 3, [1.01, 1.02]),
                             ("X_g d=4 trivial cochain=PG(4,2)", memo.x_fib(4, 1, lambda c: 0, {1: [(0, 1)]}, {}), 2, [1.02, 1.05])]:
        for lam in lams:
            print(f" {name} q={q} lambda={lam}: {check_T3(Q, q, lam)}")
    for q in (2, 3, 4, 5, 7, 8, 9):
        lq = min(0.5 * math.log(q * q + q - 1, q), math.log(q ** 3 + q - 1, q) / 3, math.log(q + 1 - 1 / q, q))
        lq2 = min(0.5 * math.log(q * q + q - 1, q), math.log(q ** 3 + q ** 2 - q, q) / 3, math.log(q + 1 - 1 / q, q))
        print(f" q={q}: lambda_q(memo)={lq:.5f} (binding term index {[0.5*math.log(q*q+q-1,q),math.log(q**3+q-1,q)/3,math.log(q+1-1/q,q)].index(lq)}), lambda_q(with divisibility)={lq2:.5f}")


# ---------- Section: T5

def s_t5():
    print("=== T5: near-PG decoding and decision ===")
    rng = random.Random(5)

    def pg_table(m):
        n = 2 ** m - 1
        return [[(x if x == y else ((x + 1) ^ (y + 1)) - 1) for y in range(n)] for x in range(n)]

    def pasch_switch(Q, a, b, d):
        A, B, D = a + 1, b + 1, d + 1
        c = (A ^ B) - 1
        e = (A ^ D) - 1
        f = (B ^ D) - 1
        blocks = [(a, b, c), (a, d, e), (f, b, d), (f, c, e)]
        for x, y, z in blocks:
            assert Q[x][y] == z
        new = [(a, b, d), (a, c, e), (f, b, c), (f, d, e)]
        for x, y, z in new:
            for p, q, r in ((x, y, z), (y, x, z), (x, z, y), (z, x, y), (y, z, x), (z, y, x)):
                Q[p][q] = r
        return Q

    def random_pasch(n):
        while True:
            a, b, d = rng.sample(range(n), 3)
            A, B, D = a + 1, b + 1, d + 1
            if len({0, A, B, D, A ^ B, A ^ D, B ^ D, A ^ B ^ D}) == 8:
                return a, b, d

    def decode_M(Q):
        n = len(Q)
        M = [[None] * n for _ in range(n)]
        for x in range(n):
            for y in range(x + 1, n):
                cnt = Counter()
                for z in range(n):
                    if z != x and z != y:
                        cnt[Q[Q[x][z]][Q[y][z]]] += 1
                v = cnt.most_common(1)[0][0]
                M[x][y] = M[y][x] = v
        return M

    for m, nsw in ((7, 1), (8, 2), (9, 5)):
        n = 2 ** m - 1
        Q = pg_table(m)
        used = set()
        done = 0
        while done < nsw:
            a, b, d = random_pasch(n)
            A, B, D = a + 1, b + 1, d + 1
            pts = {a, b, d, (A ^ B) - 1, (A ^ D) - 1, (B ^ D) - 1}
            if pts & used:
                continue
            Q = pasch_switch(Q, a, b, d)
            used |= pts
            done += 1
        D = 4 * nsw
        t0 = time.time()
        assert D < (n - 2) / 24 and memo.is_sts(Q)
        M = decode_M(Q)
        ok = all(M[x][y] == ((x + 1) ^ (y + 1)) - 1 for x in range(n) for y in range(n) if x != y)
        print(f" m={m} n={n} D={D} < {(n-2)/24:.1f}: M = XOR on all pairs: {ok}; {time.time()-t0:.1f}s", flush=True)

    def t5_decide(Qa, Qb):
        n = len(Qa)
        Ma, Mb = decode_M(Qa), decode_M(Qb)
        def base(M):
            return {tuple(sorted((x, y, M[x][y]))) for x in range(n) for y in range(x + 1, n)}
        Ba, Bb = base(Ma), base(Mb)
        Xa = {tuple(sorted(t)) for t in memo.blocks_of(Qa)}
        Xb = {tuple(sorted(t)) for t in memo.blocks_of(Qb)}
        Da, Db = Xa ^ Ba, Xb ^ Bb
        if len(Da) != len(Db):
            return False, 0
        defa = sorted({p for t in Da for p in t})
        defb = sorted({p for t in Db for p in t})
        if len(defa) != len(defb):
            return False, 0
        vec = lambda p: p + 1
        basis = []
        span = {0}
        for p in defa:
            v = vec(p)
            if v not in span:
                basis.append(p)
                span |= {s ^ v for s in span}
        count = 0
        for images in itertools.product(defb, repeat=len(basis)):
            count += 1
            mp = {0: 0}
            ok = True
            for b, img in zip(basis, images):
                bv, iv = vec(b), vec(img)
                for s, t in list(mp.items()):
                    nv, nt = s ^ bv, t ^ iv
                    if nv in mp:
                        ok = ok and mp[nv] == nt
                    mp[nv] = nt
            if not ok or len(set(mp.values())) != len(mp):
                continue
            im = set()
            good = True
            for t in Da:
                r = []
                for p in t:
                    v = vec(p)
                    if v not in mp:
                        good = False
                        break
                    r.append(mp[v] - 1)
                if not good:
                    break
                im.add(tuple(sorted(r)))
            if good and im == Db:
                return True, count
        return False, count

    def random_linear(m):
        while True:
            cols = [rng.randrange(1, 2 ** m) for _ in range(m)]
            span = {0}
            ok = True
            for c in cols:
                if c in span:
                    ok = False
                    break
                span |= {s ^ c for s in span}
            if ok:
                return cols

    def relabel(Qa, cols, m):
        n = 2 ** m - 1
        perm = [apply_mat(cols, p + 1) - 1 for p in range(n)]
        pinv = [0] * n
        for i, p in enumerate(perm):
            pinv[p] = i
        return [[perm[Qa[pinv[x]][pinv[y]]] for y in range(n)] for x in range(n)]

    m = 7
    n = 2 ** m - 1
    for t in range(4):
        Qa = pasch_switch(pg_table(m), *random_pasch(n))
        Qb = relabel(Qa, random_linear(m), m)
        dec, c = t5_decide(Qa, Qb)
        w, nd, ex = iso_search(Qa, Qb)
        assert dec == (w is not None) and ex
        print(f" m=7 positive #{t}: decision {dec} (enumerated {c}); exact search agrees")
    # m=8: two different 2-switch configurations
    m = 8
    n = 2 ** m - 1

    def two_switch(shared):
        while True:
            Q = pg_table(m)
            a, b, d = random_pasch(n)
            A, B, D = a + 1, b + 1, d + 1
            Q = pasch_switch(Q, a, b, d)
            pts1 = {a, b, d, (A ^ B) - 1, (A ^ D) - 1, (B ^ D) - 1}
            if shared:
                F = B ^ D
                f = F - 1
                for tr in range(5000):
                    w = rng.randrange(n)
                    W = w + 1
                    if len({0, A, F, W, A ^ F, A ^ W, F ^ W, A ^ F ^ W}) != 8 or W in (B, D, A ^ B, A ^ D):
                        continue
                    Q2 = [r[:] for r in Q]
                    try:
                        return pasch_switch(Q2, a, f, w)
                    except AssertionError:
                        continue
            else:
                for tr in range(10000):
                    a2, b2, d2 = random_pasch(n)
                    A2, B2, D2 = a2 + 1, b2 + 1, d2 + 1
                    pts2 = {a2, b2, d2, (A2 ^ B2) - 1, (A2 ^ D2) - 1, (B2 ^ D2) - 1}
                    if pts1 & pts2:
                        continue
                    span = {0}
                    for v in [A, B, D, A2, B2, D2]:
                        if v not in span:
                            span |= {s ^ v for s in span}
                    if len(span) == 64:
                        return pasch_switch(Q, a2, b2, d2)

    Qa = two_switch(False)
    Qb = two_switch(True)
    dec, c = t5_decide(Qa, Qb)
    w, nd, ex = iso_search(Qa, Qb)
    print(f" m=8 (span-6 pair vs shared-line pair): decision {dec} (enumerated {c}); exact search iso={w is not None}, exhausted {ex}")
    assert dec == (w is not None)
    Qc = relabel(Qa, random_linear(m), m)
    dec2, c2 = t5_decide(Qa, Qc)
    w2, nd2, ex2 = iso_search(Qa, Qc)
    print(f" m=8 (span-6 pair vs relabelled copy): decision {dec2} (enumerated {c2}); exact search iso={w2 is not None}")
    assert dec2 == (w2 is not None)


# ---------- Section: C4 and cocycle claims

def s_c4():
    print("=== C4 and the cocycle claims ===")
    lines = [(1, 2, 3), (1, 4, 5), (1, 6, 7), (2, 4, 6), (2, 5, 7), (3, 4, 7), (3, 5, 6)]
    assert sorted(tuple(sorted(p)) for l in lines for p in itertools.combinations(l, 2)) == sorted(itertools.combinations(range(1, 8), 2))

    def loop16(g):
        def mul(a, b):
            ua, al = a >> 1, a & 1
            ub, be = b >> 1, b & 1
            if ua == 0:
                return (ub << 1) | (al ^ be)
            if ub == 0:
                return (ua << 1) | (al ^ be)
            if ua == ub:
                return al ^ be
            gamma = 0
            for i, l in enumerate(lines):
                if ua in l and ub in l:
                    gamma = g[i]
            return ((ua ^ ub) << 1) | (al ^ be ^ gamma)
        return [[mul(a, b) for b in range(16)] for a in range(16)]

    def is_group(M):
        n = len(M)
        return all(M[M[a][b]][c] == M[a][M[b][c]] for a in range(n) for b in range(n) for c in range(n))

    def is_moufang(M):
        n = len(M)
        return all(M[z][M[x][M[z][y]]] == M[M[M[z][x]][z]][y] for x in range(n) for y in range(n) for z in range(n))

    vs = {(0,) * 7}
    for h in range(1, 8):
        g = tuple(1 if h in l else 0 for l in lines)
        vs |= {tuple(a ^ b for a, b in zip(v, g)) for v in vs}
    cob = vs
    print(" coboundary space dimension:", int(math.log2(len(cob))))
    counts = Counter()
    formula_ok = True
    for g in itertools.product([0, 1], repeat=7):
        M = loop16(g)
        assert all(M[x][x] == 0 and M[x][y] == M[y][x] and M[x][M[x][y]] == y for x in range(16) for y in range(16))
        counts[(g in cob, is_group(M), is_moufang(M))] += 1
        def gon(c1, c2):
            for i, l in enumerate(lines):
                if c1 in l and c2 in l:
                    return g[i]
            return 0
        for x in range(1, 8):
            for y in range(1, 8):
                for z in range(1, 8):
                    if len({0, x, y, z, x ^ y, y ^ z, x ^ z, x ^ y ^ z}) < 8:
                        continue
                    lhs = M[M[x << 1][y << 1]][z << 1] ^ M[x << 1][M[y << 1][z << 1]]
                    a = gon(x, y) ^ gon(x ^ y, z) ^ gon(y, z) ^ gon(x, y ^ z)
                    w = x ^ z
                    pasch = 0
                    for i, l in enumerate(lines):
                        if w not in l:
                            pasch ^= g[i]
                    if lhs != a or a != pasch:
                        formula_ok = False
    print(" (coboundary, associative, Moufang) over all 128 cochains on a Fano plane:", dict(counts))
    print(" associator = Pasch sum missing x+z on all cochains and all bases:", formula_ok)

    def principal_isotope(T, a=0, b=0):
        n = len(T)
        Lainv = [0] * n
        Rbinv = [0] * n
        for x in range(n):
            Lainv[T[a][x]] = x
            Rbinv[T[x][b]] = x
        return [[T[Rbinv[x]][Lainv[y]] for y in range(n)] for x in range(n)]

    def steiner_quasi_from_loop(M):
        return [[(x - 1) if x == y else M[x][y] - 1 for y in range(1, 16)] for x in range(1, 16)]

    res = Counter()
    for g in itertools.product([0, 1], repeat=7):
        if g in cob:
            continue
        P = principal_isotope(steiner_quasi_from_loop(loop16(g)), 0, 1)
        res[(is_group(P), is_moufang(P))] += 1
    print(" order-15 Steiner quasigroup of a non-coboundary cochain: principal loop isotope (assoc,Moufang):", dict(res))
    for m, name in ((3, "PG(2,2)"), (4, "PG(3,2)")):
        P = principal_isotope(memo.pg(m), 0, 1)
        print(f" {name} Steiner quasigroup: principal loop isotope (assoc,Moufang): ({is_group(P)},{is_moufang(P)})")
    # bilinear / trilinear claims
    ok = True
    for bits in itertools.product([0, 1], repeat=6):
        pairs = list(itertools.combinations(range(4), 2))
        B = {(i, j): b for (i, j), b in zip(pairs, bits)}
        def bil(x, y):
            s = 0
            for i, j in pairs:
                if B[(i, j)]:
                    s ^= ((x >> i & 1) & (y >> j & 1)) ^ ((x >> j & 1) & (y >> i & 1))
            return s
        def Qf(x):
            s = 0
            for i, j in pairs:
                if B[(i, j)]:
                    s ^= (x >> i & 1) & (x >> j & 1)
            return s
        for x in range(16):
            for y in range(16):
                if x != y and x and y:
                    if bil(x, y) != Qf(x) ^ Qf(y) ^ Qf(x ^ y):
                        ok = False
    print(" alternating bilinear g on F_2^4 equals delta(quadratic form) on all pairs:", ok)
    ok = True
    for g in itertools.product([0, 1], repeat=7):
        M = loop16(g)
        # associator on an ordered basis (x,y,z), with lifts: a nonzero alternating trilinear associator would be constant on all bases
        a = {}
        for x, y, z in itertools.permutations(range(1, 8), 3):
            if z == x ^ y:
                continue
            a[(x, y, z)] = (M[M[x << 1][y << 1]][z << 1] ^ M[x << 1][M[y << 1][z << 1]]) & 1
        vals = set(a.values())
        if vals == {1}:
            ok = False
    print(" no nonzero cochain has an associator constant = 1 on all ordered bases (no alternating trilinear associator):", ok)


# ---------- Section: Latin-square isotopy of the gadget

def s_iso():
    print("=== Quasigroup / Latin-square level ===")
    F1 = memo_F1()

    def latin_cert(T):
        n = len(T)
        v = 3 * n + n * n
        adj = {i: [] for i in range(v)}
        for r in range(n):
            for c in range(n):
                cell = 3 * n + r * n + c
                for u in (r, n + c, 2 * n + T[r][c]):
                    adj[cell].append(u)
                    adj[u].append(cell)
        # isotopy-invariant colouring of rows, columns, symbols by row-permutation cycle types (exact)
        def sig(Tb):
            N = len(Tb)
            invs = [[0] * N for _ in range(N)]
            for i in range(N):
                for j, x in enumerate(Tb[i]):
                    invs[i][x] = j
            out = []
            for i in range(N):
                ms = []
                for j in range(N):
                    if j == i:
                        continue
                    perm = [invs[i][Tb[j][x]] for x in range(N)]
                    seen = [False] * N
                    cyc = []
                    for a in range(N):
                        if not seen[a]:
                            l = 0
                            b = a
                            while not seen[b]:
                                seen[b] = True
                                b = perm[b]
                                l += 1
                            cyc.append(l)
                    cyc.sort()
                    ms.append(tuple(cyc))
                ms.sort()
                out.append(intern(("r", tuple(ms))))
            return out
        Tt = [[T[j][i] for j in range(n)] for i in range(n)]
        Ts = [[0] * n for _ in range(n)]
        for r in range(n):
            for c in range(n):
                Ts[T[r][c]][c] = r
        vc = {}
        for r, c in enumerate(sig(T)):
            vc.setdefault(("R", c), set()).add(r)
        for r, c in enumerate(sig(Tt)):
            vc.setdefault(("C", c), set()).add(n + r)
        for r, c in enumerate(sig(Ts)):
            vc.setdefault(("S", c), set()).add(2 * n + r)
        col = [vc[k] for k in sorted(vc)] + [set(range(3 * n, v))]
        return pynauty.certificate(pynauty.Graph(number_of_vertices=v, directed=False, adjacency_dict=adj, vertex_coloring=col))

    def loop_table(Q):
        n = len(Q)
        T = [[0] * (n + 1) for _ in range(n + 1)]
        for i in range(n + 1):
            T[0][i] = i
            T[i][0] = i
        for x in range(n):
            for y in range(n):
                T[x + 1][y + 1] = 0 if x == y else Q[x][y] + 1
        return T

    # Gadget Latin subsquares
    def m1_square(F):
        T = [[0] * 8 for _ in range(8)]
        for z, ps in F.items():
            for a, b in ps:
                T[a][b] = z
                T[b][a] = z
        return T

    Z23 = [[a ^ b for b in range(8)] for a in range(8)]
    def plain_lat_cert(T):
        n = len(T)
        v = 3 * n + n * n
        adj = {i: [] for i in range(v)}
        for r in range(n):
            for c in range(n):
                cell = 3 * n + r * n + c
                for u in (r, n + c, 2 * n + T[r][c]):
                    adj[cell].append(u)
                    adj[u].append(cell)
        col = [set(range(n)), set(range(n, 2 * n)), set(range(2 * n, 3 * n)), set(range(3 * n, v))]
        return pynauty.certificate(pynauty.Graph(number_of_vertices=v, directed=False, adjacency_dict=adj, vertex_coloring=col))
    print(" memo F^1 subsquare M_1 isotopic to Z_2^3:", plain_lat_cert(m1_square(F1)) == plain_lat_cert(Z23))
    F0 = {z: [(a, a ^ z) for a in range(8) if a < (a ^ z)] for z in range(1, 8)}
    adv = {z: F0[[3, 5, 7, 4, 1, 6, 2][z - 1]] for z in range(1, 8)}
    print(" adversarial relabelled-Cayley gadget (a),(b):", memo.f1_acceptable(adv, 3)[:2], "| its M_1 isotopic to Z_2^3:", plain_lat_cert(m1_square(adv)) == plain_lat_cert(Z23))

    def run(F, label):
        for d in (2, 3):
            GL = gl_matrices(d)
            seen, orbs = orbits_of(d, GL)
            nc = [o[0] for o in orbs if nonconstant(o[0])]
            for kind, mk in (("Steiner quasigroup", lambda Q: [list(r) for r in Q]), ("Steiner loop", loop_table)):
                t0 = time.time()
                cs = [latin_cert(mk(build(d, list(c), F))) for c in nc]
                print(f"  {label} d={d} {kind}: {len(nc)} nonconstant orbit reps -> {len(set(cs))} isotopy classes; {time.time()-t0:.0f}s", flush=True)

    run(F1, "memo gadget")
    run(adv, "relabelled-Cayley gadget")
    # A deliberately non-trivial test of the isotopy argument: constant colourings too
    GL = gl_matrices(3)
    seen, orbs = orbits_of(3, GL)
    cs = {}
    for o in orbs:
        c = latin_cert(loop_table(build(3, list(o[0]), F1)))
        cs.setdefault(c, []).append(o[0][1:])
    print(" d=3 all orbit reps incl. constants, Steiner loops: isotopy classes =", len(cs), "of", len(orbs))



# ---------- Section: exact structure of Aut(X_chi): stabilizer times gauge

def s_aut():
    print("=== T2: Aut(X_chi) = Stab_GL(chi) . K, K = Hom(V / <supp chi>, Z) for the memo's F^1 ===")
    F1 = memo_F1()
    GLZ = gl_matrices(3)
    fsets = {z: {frozenset(p) for p in F1[z]} for z in F1}
    stab = []
    for M in GLZ:
        for t in range(8):
            if all(frozenset((apply_mat(M, a) ^ t, apply_mat(M, b) ^ t)) in fsets[apply_mat(M, z)] for z in F1 for a, b in F1[z]):
                stab.append((M, t))
    print(f" Stab(F^1) in GL(3,2) x translations: order {len(stab)}")

    def aut_order(Q):
        n = len(Q)
        bl = memo.blocks_of(Q)
        v = n + len(bl)
        adj = {i: [] for i in range(v)}
        for j, b in enumerate(bl):
            for x in b:
                adj[x].append(n + j)
                adj[n + j].append(x)
        cls = {}
        for p, c in enumerate(point_inv(pair_inv(Q))):
            cls.setdefault(c, set()).add(p)
        vc = [cls[c] for c in sorted(cls)] + [set(range(n, v))]
        gens, m, e, orbs, no = pynauty.autgrp(pynauty.Graph(number_of_vertices=v, directed=False, adjacency_dict=adj, vertex_coloring=vc))
        return round(m * 10 ** e)

    for d in (2, 3, 4):
        GL = gl_matrices(d)
        seen, orbs = orbits_of(d, GL)
        allok = True
        count = 0
        for o in orbs:
            chi = o[0]
            if not nonconstant(chi):
                continue
            a = aut_order(build(d, list(chi), F1))
            W = [c for c in range(1, 1 << d) if chi[c]]
            K = 0
            for M, ti in stab:
                allowed = {t for MM, t in stab if MM == M}
                for ims in itertools.product(range(8), repeat=d):
                    if all(apply_mat(ims, c) in allowed for c in W):
                        K += 1
            pred = (len(GL) // len(o)) * K
            count += 1
            if a != pred:
                allok = False
                print(f"  MISMATCH d={d} chi={chi[1:]}: |Aut|={a} predicted {pred}")
        print(f" d={d}: |Aut(X_chi)| = |Stab_GL(chi)|*|K| for all {count} nonconstant orbit reps: {allok}", flush=True)

SECTIONS = {
    "gadget": s_gadget, "t2": s_t2, "t2d4": s_t2d4, "t2d5": s_t2d5, "nauty": s_nauty,
    "alt": s_alt, "trace": s_trace, "t1": s_t1, "t3": s_t3, "t5": s_t5, "c4": s_c4, "iso": s_iso, "aut": s_aut,
}

if __name__ == "__main__":
    args = sys.argv[1:] or list(SECTIONS)
    T0 = time.time()
    for a in args:
        print(flush=True)
        SECTIONS[a]()
        print(f"[{a} done at {time.time()-T0:.0f}s]", flush=True)
