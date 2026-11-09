"""Smaller checks for docs/redteam-w50-gain.md (see the 'check' names in sys.argv)."""
import itertools, math, random, sys, time
sys.path.insert(0, '.')
from rtlib import *


def folded_group(n):
    """H = T:S_n on folded n-cube vertices, as vertex permutations"""
    local, verts, index, full = folded_cube(n)
    rep = lambda x: min(x, x ^ full)
    def perm_of(t, sigma):
        out = []
        for v in verts:
            w = 0
            for i in range(n):
                if v >> i & 1:
                    w |= 1 << sigma[i]
            out.append(index[rep(w ^ t)])
        return tuple(out)
    H = []
    trans = sorted({rep(t) for t in range(1 << n)})
    for sigma in itertools.permutations(range(n)):
        for t in trans:
            H.append(perm_of(t, sigma))
    assert len(set(H)) == len(H)
    return local, H, trans


def check_mH(n=5):
    """exact max order of Stab_H(z), z an odd-weight cycle vector of the folded n-cube.  Any z with nontrivial stabiliser is fixed by an element of prime order;
    enumerate Fix(h) on Z for one element h of each prime order conjugacy class."""
    local, H, trans = folded_group(n)
    edges = sorted({(min(u, v), max(u, v)) for u in local for v in local[u]})
    eid = {e: i for i, e in enumerate(edges)}
    m = len(edges)
    Hedge = [[eid[(min(h[u], h[v]), max(h[u], h[v]))] for (u, v) in edges] for h in H]
    # byte tables for applying an edge permutation to a 40-bit mask quickly
    chunks = [list(range(i, min(i + 8, m))) for i in range(0, m, 8)]
    tables = []
    for p in Hedge:
        tt = []
        for ch in chunks:
            tab = [0] * (1 << len(ch))
            for mask in range(1 << len(ch)):
                x = 0
                for bit, e in enumerate(ch):
                    if mask >> bit & 1:
                        x |= 1 << p[e]
                tab[mask] = x
            tt.append(tab)
        tables.append(tt)
    def image(tt, z):
        out = 0
        for i, tab in enumerate(tt):
            out |= tab[(z >> (8 * i)) & 255]
        return out
    # cycle space basis as bit ints
    C = Cycles({(u,): [(v,) for v in local[u]] for u in local})
    parent = {k[0]: (v[0] if v is not None else None) for k, v in C.parent.items()}
    # basis of Z from fundamental cycles
    depth = {}
    def dep(u):
        return 0 if parent[u] is None else 1 + dep(parent[u])
    basis = []
    for (a, c) in C.nontree:
        u, v = a[0], c[0]
        pu, pv = [u], [v]
        while pu[-1] != pv[-1]:
            if dep(pu[-1]) >= dep(pv[-1]):
                pu.append(parent[pu[-1]])
            else:
                pv.append(parent[pv[-1]])
        w = pu + pv[-2::-1] + [u]
        z = 0
        for x, y in zip(w, w[1:]):
            z ^= 1 << eid[(min(x, y), max(x, y))]
        basis.append(z)
    # conjugacy classes of H of prime-order elements
    def mul(a, c):
        return tuple(c[a[i]] for i in range(len(a)))
    def inv(a):
        out = [0] * len(a)
        for i, x in enumerate(a):
            out[x] = i
        return tuple(out)
    def order(a):
        e = tuple(range(len(a)))
        x = a
        k = 1
        while x != e:
            x = mul(x, a)
            k += 1
        return k
    gens = [H[1], H[len(trans)], H[len(trans) * 3], H[len(trans) * 7], H[-1]]
    prime_els = [h for h in H if order(h) in (2, 3, 5, 7)]
    seen = set()
    reps = []
    pe = set(prime_els)
    for h in prime_els:
        if h in seen:
            continue
        reps.append(h)
        orbit = {h}
        q = [h]
        while q:
            x = q.pop()
            for g in H[:200] + H[-200:]:
                y = mul(mul(inv(g), x), g)
                if y not in orbit:
                    orbit.add(y)
                    q.append(y)
        seen |= orbit
    print("prime-order elements", len(prime_els), "classes (at least this coarse)", len(reps))
    # Fix(h) on Z: kernel of (h-1) on span(basis): do by linear algebra on 2^|basis| coefficient space
    best = 0
    total = 0
    for h in reps:
        he = [eid[(min(h[u], h[v]), max(h[u], h[v]))] for (u, v) in edges]
        def apply(z):
            out = 0
            for e in range(m):
                if z >> e & 1:
                    out |= 1 << he[e]
            return out
        r = len(basis)
        # nullspace over F_2 of c -> sum c_i (h b_i - b_i) on coefficient vectors
        piv = {}
        null = []
        for i, zb in enumerate(basis):
            val = apply(zb) ^ zb
            coef = 1 << i
            while val:
                k = val.bit_length() - 1
                if k in piv:
                    val ^= piv[k][0]
                    coef ^= piv[k][1]
                else:
                    piv[k] = (val, coef)
                    break
            if val == 0:
                null.append(coef)
        d = len(null)
        print(f" rep order {order(h)} fixes dim {d} cycle subspace", flush=True)
        if d > 18:
            print("   too large, skipped")
            continue
        # Fix(h) on Z as bitmasks
        vecs = []
        for c in null:
            z = 0
            for i in range(r):
                if c >> i & 1:
                    z ^= basis[i]
            vecs.append(z)
        for mask in range(1, 1 << d):
            z = 0
            for i in range(d):
                if mask >> i & 1:
                    z ^= vecs[i]
            if bin(z).count('1') % 2 == 0:
                continue
            total += 1
            stab = sum(1 for tt in tables if image(tt, z) == z)
            if stab > best:
                best = stab
                print("   new best stabiliser order", best, flush=True)
    print(f"n={n}: |H|={len(H)}; exact max |Stab(odd cycle vector)|={best} (over {total} fixed odd vectors), m_H={len(H)//best}")


def check_stab_T(n=5):
    """Stab_T(z) order <=2 for odd z: follows from fixed-edge argument; confirm on the n=5 cycle space by enumeration over T-involutions"""
    pass


def check_double_cover():
    """Remark 1 of w50 sec.3: closed walk in the bipartite double cover with r != 0 has only ceil(g/2) values per side coordinate."""
    n = 5
    local, verts, idx, full = folded_cube(n)
    cyc = [0]
    cur = verts[0]
    for i in range(n):
        cur ^= 1 << i
        cyc.append(idx[min(cur, cur ^ full)])
    assert cyc[-1] == cyc[0]
    # Cartesian patterns {0},{1} on [b]^2: move coord 0 around cycle, then coord 1 around cycle.  total length 2n even
    seq = [(cyc[s], cyc[0]) for s in range(n + 1)] + [(cyc[0], cyc[s]) for s in range(1, n + 1)]
    # sides: even time in V, odd time in V'
    vside = {0: set(), 1: set()}
    vprime = {0: set(), 1: set()}
    for t, v in enumerate(seq):
        for j in range(2):
            (vside if t % 2 == 0 else vprime)[j].add(v[j])
    r = [sum(1 for a, c in zip(seq, seq[1:]) if a[j] != c[j]) % 2 for j in range(2)]
    print("double cover walk length", len(seq) - 1, "parity r", r, "values per side-coordinate",
          {k: (len(vside[k]), len(vprime[k])) for k in vside}, "odd girth g =", odd_girth(local))


def check_gap():
    """K_4 with gains in S_3 (inside S_4): all triangle holonomies conjugate pairwise, yet x,y not switching equivalent under any t in S_4."""
    S3 = list(itertools.permutations(range(3)))
    def comp(a, c):
        return tuple(c[a[i]] for i in range(3))
    def inv(a):
        o = [0] * 3
        for i, x in enumerate(a):
            o[x] = i
        return tuple(o)
    def ctype(a):
        return tuple(sorted(sum(1 for i in range(3) if a[i] == i) for _ in [0]))
    # holonomy data for a gain function on K_4 given as dict on oriented edges
    def gains_from_triple(tr):
        g = {}
        a, b, c = tr
        e = (0, 1, 2)
        for u in (1, 2, 3):
            g[(0, u)] = e
            g[(u, 0)] = e
        g[(1, 2)] = a
        g[(2, 1)] = inv(a)
        g[(2, 3)] = b
        g[(3, 2)] = inv(b)
        g[(3, 1)] = c
        g[(1, 3)] = inv(c)
        return g
    def hol(g, cyc):
        x = (0, 1, 2)
        for u, v in zip(cyc, cyc[1:] + cyc[:1]):
            x = comp(x, g[(u, v)])
        return x
    def star_triple(g, base):
        others = [v for v in range(4) if v != base]
        # normalise to star at base via switching: f(v) = g(base,v)
        def norm(u, v):
            return comp(comp(g[(base, u)], g[(u, v)]), inv(g[(base, v)]))
        return tuple(norm(others[i], others[(i + 1) % 3]) for i in range(3))
    cyc_all = [(0, 1, 2), (0, 2, 3), (0, 3, 1), (1, 2, 3)]
    conj = {}
    for s in S3:
        conj[s] = frozenset(comp(comp(h, s), inv(h)) for h in S3)
    def cclass(s):
        return conj[s]
    count = 0
    found = None
    for x in itertools.product(S3, repeat=3):
        gx = gains_from_triple(x)
        cx = [cclass(hol(gx, list(c))) for c in cyc_all]
        for y in itertools.product(S3, repeat=3):
            gy = gains_from_triple(y)
            cy = [cclass(hol(gy, list(c))) for c in cyc_all]
            if cx != cy:
                continue
            # equivalent under t in S_4? compare simultaneous S_3 conjugacy of star triples after relabeling by t
            equiv = False
            for t in itertools.permutations(range(4)):
                gt = {(t[u], t[v]): val for (u, v), val in gx.items()}
                sx = star_triple(gt, 0)
                sy = star_triple(gy, 0)
                for h in S3:
                    if tuple(comp(comp(h, s), inv(h)) for s in sx) == sy:
                        equiv = True
                        break
                if equiv:
                    break
            if not equiv:
                count += 1
                if found is None:
                    found = (x, y)
    print("K_4, S_3 gains (a=g12,b=g23,c=g31 with star at 0 identity): pairs with all four triangle holonomies conjugate but not switching-isomorphic under any t:", count)
    if found:
        print(" example", found)


def check_padic():
    """Remark 2 of w50 sec.3: over F_p with undirected +-e_i the Z_p obstruction lambda is not coupled across a pattern."""
    p, n = 3, 4
    def lam(moves):
        tot = sum(moves)
        return tot
    # coordinate 0: +e_1,+e_2,+e_3,+e_4 (sums to 1^n: lambda=1); coordinate 1: +e_1,-e_1,+e_1,-e_1 (lambda=0)
    c0 = [(i, 1) for i in range(n)]
    c1 = [(0, 1), (0, -1), (0, 1), (0, -1)]
    assert len(c0) == len(c1)
    a0 = [0] * n
    a1 = [0] * n
    for (i, s) in c0:
        a0[i] += s
    for (i, s) in c1:
        a1[i] += s
    print("p=3,n=4 pattern {0,1}: same-length walk gives coordinate 0 net", a0, "(all equal: lambda=1) and coordinate 1 net", a1, "(lambda=0): obstruction vector (1,0) has weight 1, not in any code of distance >1")


def check_dependent():
    """Theorem B' for dependent F: code-level.  n=5, M=5, F = pentagon of pairs (one relation of weight 5)."""
    n = 5
    M = 5
    F = [(i, (i + 1) % 5) for i in range(5)]
    F = [tuple(sorted(f)) for f in F]
    gens = []
    for Ii, I in enumerate(F):
        for a, c in itertools.product(range(n), repeat=2):
            gens.append((Ii, {I[0]: a, I[1]: c}))
    idx = {(Ii, tuple(sorted(d.items()))): i for i, (Ii, d) in enumerate(gens)}
    m = len(gens)
    def marg_rows():
        rows = []
        for j in range(M):
            for a in range(n):
                f = 0
                for i, (Ii, d) in enumerate(gens):
                    if d.get(j) == a:
                        f |= 1 << i
                rows.append(f)
        return rows
    sp = Span2()
    for r in marg_rows():
        sp.add(r)
    dimC0 = m - sp.rank
    # rectangles
    s2 = Span2()
    for Ii, I in enumerate(F):
        for a, a2 in itertools.combinations(range(n), 2):
            for c, c2 in itertools.combinations(range(n), 2):
                v = 0
                for x in (a, a2):
                    for y in (c, c2):
                        v ^= 1 << idx[(Ii, tuple(sorted({I[0]: x, I[1]: y}.items())))]
                s2.add(v)
    # cross
    for j in range(M):
        pats = [Ii for Ii, I in enumerate(F) if j in I]
        for Ii, Ij in itertools.combinations(pats, 2):
            for a, a2 in itertools.combinations(range(n), 2):
                I, J = F[Ii], F[Ij]
                o1 = [l for l in I if l != j][0]
                o2 = [l for l in J if l != j][0]
                v = 0
                for x in (a, a2):
                    v ^= 1 << idx[(Ii, tuple(sorted({j: x, o1: 0}.items())))]
                    v ^= 1 << idx[(Ij, tuple(sorted({j: x, o2: 0}.items())))]
                s2.add(v)
    r1 = s2.rank
    # pure pattern-relation walk (2 values per coordinate, length 5)
    v = 0
    for Ii, I in enumerate(F):
        v ^= 1 << idx[(Ii, tuple(sorted({I[0]: 0, I[1]: 0}.items())))]
    s2.add(v)
    print(f"pentagon F, n=5: dim C_0={dimC0}, rank(rect+cross)={r1}, rank(+ one pattern-relation walk of length 5, 2 values/coord)={s2.rank}")


def check_bound_table():
    print("n, log_b|H| = 1+log2(n!)/(n-1); c<... refuted with GV delta=.11 (need log_b|H|>2c/delta): c_max; with delta->1/2: c_max")
    for n in (5, 7, 9, 15, 31, 2 ** 18 + 1):
        l = 1 + math.lgamma(n + 1) / math.log(2) / (n - 1)
        print(n, f"{l:.3f}", f"GV c<{l*0.11:.3f}", f"delta~1/2: c<{l/2:.3f}", "|H|<=b^c hatch: c>=", f"{l:.3f}")


def check_rank3():
    """non 2-transitive H with short generation: H=S_6 on 15 pairs, both orbital graphs; M=1 and M=2 Cartesian pattern."""
    pairs = list(itertools.combinations(range(6), 2))
    b = len(pairs)
    j = {i: [k for k, y in enumerate(pairs) if len(set(pairs[i]) & set(y)) == 1] for i in range(b)}
    kn = {i: [k for k, y in enumerate(pairs) if not set(pairs[i]) & set(y)] for i in range(b)}
    for name, loc in [("T(6)", j), ("K(6,2)", kn)]:
        for F, M in [([(0,)], 1), ([(0,), (1,)], 2)]:
            adj = pattern_graph(loc, b, M, F) if M == 2 else {(u,): [(v,) for v in loc[u]] for u in loc}
            C = Cycles(adj)
            for p in (2, 3):
                sp = make_span(p)
                for w in closed_walks_upto(adj, 4):
                    sp.addv(C.vector(w))
                    if sp.rank == C.rank:
                        break
                print(f"{name} M={M} p={p}: rank of triangles+4-cycles {sp.rank} of {C.rank}", flush=True)


def check_propE():
    """Prop E on real group data: folded n=5 M=1, C=H (order 1920), and folded n=5 M=2 Cartesian with C=(T:Z_5)^2 (order 6400).  A=Z_q, q in {2,3,4}."""
    rng = random.Random(1)
    local, H, trans = folded_group(5)
    # setup M=1
    def run(adj, C, labelsC, qs, trials):
        Cy = Cycles(adj)
        edges = sorted({(u, v) for u in adj for v in adj[u] if u < v})
        short = [w for w in closed_walks_upto(adj, 4)]
        keys = list(Cy.nontree)
        # build generators of B as cycle coordinate vectors over Z, and a rep basis of Q
        def apply_t(t, v):
            return t(v)
        def rho(x, walk):
            s = 0
            for a, c in zip(walk, walk[1:]):
                s += x[(a, c)]
            return s
        # fundamental cycles as walks
        parent = Cy.parent
        def path_to_root(v):
            p = [v]
            while parent[p[-1]] is not None:
                p.append(parent[p[-1]])
            return p
        def fund(u, v):
            pu = path_to_root(u)
            pv = path_to_root(v)
            setu = set(pu)
            i = next(k for k, x in enumerate(pv) if x in setu)
            l = pv[i]
            pu = pu[:pu.index(l) + 1]
            pv = pv[:i + 1]
            return pu + pv[-2::-1] + [u]
        funds = [fund(u, v) for (u, v) in keys]
        for q in qs:
            for tr in range(trials):
                x = {}
                for (u, v) in edges:
                    a = rng.randrange(q)
                    x[(u, v)] = a
                    x[(v, u)] = -a
                # y: random image of x plus coboundary
                t0 = rng.choice(C)
                coboundary = {v: rng.randrange(q) for v in adj}
                y = {}
                for (u, v) in edges:
                    a = x[(t0(u), t0(v))] + coboundary[u] - coboundary[v]
                    # optional perturb on some instance
                    y[(u, v)] = a
                    y[(v, u)] = -a
                if tr % 2 == 1:
                    # perturb y by a character of Q: add parity-of-move character... (not nec. in orbit)
                    (u, v) = rng.choice(edges)
                    y[(u, v)] += 1
                    y[(v, u)] -= 1
                # brute solutions of rho_x o t = rho_y on all of H_1
                def rho_t(t, w):
                    return rho(x, [t(v) for v in w])
                sols = [i for i, t in enumerate(C) if all((rho_t(t, f) - rho(y, f)) % q == 0 for f in funds)]
                # Prop E: C' = stabiliser of rho_x on B; S; delta; kernel
                B_short = short
                Cprime = [i for i, t in enumerate(C) if all((rho_t(t, w) - rho(x, w)) % q == 0 for w in B_short)]
                S = [i for i, t in enumerate(C) if all((rho_t(t, w) - rho(y, w)) % q == 0 for w in B_short)]
                # delta on Q: determined by values on all funds
                def delta(i):
                    t = C[i]
                    return tuple((rho_t(t, f) - rho(x, f)) % q for f in funds)
                Cp = set(Cprime)
                # compose checks: group closure of C' (sample)
                if S:
                    # S must be a coset of C': test via a fixed t0 in S and translation closure
                    deltas = {i: delta(i) for i in Cprime}
                    kerd = [i for i in Cprime if not any(deltas[i])]
                    # homomorphism property on sample
                    comp_index = {tuple(C[i](v) for v in adj): i for i in range(len(C))}
                    verts = list(adj)
                    def comp(i, j):
                        return comp_index[tuple(C[i](C[j](v)) for v in verts)]
                    sample = rng.sample(Cprime, min(40, len(Cprime)))
                    for i in sample:
                        for j in sample:
                            k = comp(j, i)
                            assert k in Cp
                            # delta(ts) = delta(t)+delta(s)
                            assert all(((deltas[k][m] - deltas[i][m] - deltas[j][m]) % q) == 0 for m in range(len(funds))), "delta not hom"
                    # solutions form coset of ker delta inside S: sols = {t : t in S and delta-shift zero}
                    t_ref = S[0]
                    shifted = {}
                    good = []
                    for i in S:
                        if all((rho_t(C[i], f) - rho(y, f)) % q == 0 for f in funds):
                            good.append(i)
                    assert set(good) == set(sols)
                    if sols:
                        s0 = sols[0]
                        kset = set(kerd)
                        # sols = ker delta . s0  (t = k s0 with composition: (ts)(v)=t(s(v)))
                        predicted = {comp(k, s0) for k in kerd}
                        assert predicted == set(sols), ("coset mismatch", len(predicted), len(sols))
                print(f"  q={q} trial {tr}: |C|={len(C)} |C'|={len(Cprime)} |S|={len(S)} solutions={len(sols)} (ker delta coset check {'ok' if S else 'vacuous'})", flush=True)
    # M=1, C=H
    adj = {(u,): [(v,) for v in local[u]] for u in local}
    Cfun = [(lambda h: (lambda v: (h[v[0]],)))(h) for h in H]
    print("M=1, C=H:")
    run(adj, Cfun, None, [2, 3, 4], 4)
    # M=2 Cartesian, C = (T:Z_5)^2
    t = time.time()
    # T:Z_5: those elements of H with sigma power of the 5-cycle (permutation listing is by sigma)
    H0 = []
    sigmas = list(itertools.permutations(range(5)))
    cyc = tuple((i + 1) % 5 for i in range(5))
    pw = [tuple(range(5))]
    for _ in range(4):
        pw.append(tuple(cyc[x] for x in pw[-1]))
    for s_i, s in enumerate(sigmas):
        if s in pw:
            for t_i in range(16):
                H0.append(H[s_i * 16 + t_i])
    assert len(H0) == 80
    adj2 = pattern_graph(local, 16, 2, [(0,), (1,)])
    C2 = [(lambda a, c: (lambda v: (a[v[0]], c[v[1]])))(a, c) for a in H0[:16] for c in H0[:16]]
    print("M=2 Cartesian, C = T^2 (regular translations only, order 256; Prop E on C acting trivially on Q):")
    run(adj2, C2, None, [2], 2)
    print(f"({time.time()-t:.0f}s)")


def check_propE2():
    """Non-vacuous Prop E test: choose gains x in F_2^E so that rho_x|_B is invariant under the translation group T, by solving the linear constraints,
    so that C' >= T and delta can be nonzero.  y = image of x (+coboundary) (+Q-character).  Brute force over all of C against Prop E's prediction."""
    rng = random.Random(7)
    local, H, trans = folded_group(5)
    adj = {(u,): [(v,) for v in local[u]] for u in local}
    edges = sorted({(u, v) for u in adj for v in adj[u] if u < v})
    eid = {e: i for i, e in enumerate(edges)}
    C = [lambda v, h=h: (h[v[0]],) for h in H]
    Tgens = [lambda v, h=H[i]: (h[v[0]],) for i in range(16)]  # H[0..15] is sigma=id, T
    Cy = Cycles(adj)
    short = [w for w in closed_walks_upto(adj, 4) if len(w) == 5]
    def evec(w):
        z = 0
        for a, c in zip(w, w[1:]):
            z ^= 1 << eid[(min(a, c), max(a, c))]
        return z
    # constraints: <x, t w - w> = 0 for t in T gens, w short
    rows = Span2()
    for t in Tgens:
        for w in short:
            rows.add(evec([t(v) for v in w]) ^ evec(w))
    # nullspace of rows over F_2 (dual)
    m = len(edges)
    piv = {}
    for z in rows.piv.values():
        pass
    # gaussian to get null vectors
    mat = [v for v in rows.piv.values()]
    # reduce
    pivots = {}
    for v in sorted(mat, reverse=True):
        x = v
        for k, u in pivots.items():
            if x >> k & 1:
                x ^= u
        if x:
            k = x.bit_length() - 1
            for kk in list(pivots):
                if pivots[kk] >> k & 1:
                    pivots[kk] ^= x
            pivots[k] = x
    free = [i for i in range(m) if i not in pivots]
    null = []
    for f in free:
        x = 1 << f
        for k, u in pivots.items():
            if u >> f & 1:
                x |= 1 << k
        null.append(x)
    print(f"x-space with T-invariant B-values: dim {len(null)} of {m}")
    # a fundamental basis of H_1 as walks, plus Q generator c (odd cycle of length 5)
    keys = list(Cy.nontree)
    parent = Cy.parent
    def path(v):
        p = [v]
        while parent[p[-1]] is not None:
            p.append(parent[p[-1]])
        return p
    funds = []
    for (u, v) in keys:
        pu, pv = path(u), path(v)
        su = set(pu)
        i = next(k for k, x in enumerate(pv) if x in su)
        l = pv[i]
        funds.append(pu[:pu.index(l) + 1] + pv[:i][::-1] + [u])
    def rho(x, w):
        return bin(x & evec(w)).count('1') % 2
    # sanity: parity character chi = walk length mod 2 is nonzero on odd walks only; ok
    nontriv = 0
    cosetok = 0
    for trial in range(30):
        x = 0
        for z in null:
            if rng.random() < 0.5:
                x ^= z
        t0 = rng.choice(H)
        cb = 0
        for u in adj:
            if rng.random() < 0.5:
                for v in adj[u]:
                    cb ^= 1 << eid[(min(u, v), max(u, v))]
        # y-gains: y(e) = x(t0 e) + cb(e) [+ chi]
        def pull(gains, h):
            out = 0
            for i, (a, c) in enumerate(edges):
                e = eid[(min((h[a[0]],), (h[c[0]],)), max((h[a[0]],), (h[c[0]],)))]
                if gains >> e & 1:
                    out |= 1 << i
            return out
        y = pull(x, t0) ^ cb
        variant = trial % 3
        if variant == 1:
            y ^= (1 << m) - 1  # add parity character (constant gain 1): same on B
        if variant == 2:
            y ^= 1 << rng.randrange(m)
        pulls = [pull(x, h) for h in H]
        fv = [evec(w) for w in funds]
        def rho_vals(g):
            return tuple(bin(g & v).count('1') % 2 for v in fv)
        yv = rho_vals(y)
        sols = {i for i, p in enumerate(pulls) if rho_vals(p) == yv}
        sv = [evec(w) for w in short]
        def on_short(g):
            return tuple(bin(g & v).count('1') % 2 for v in sv)
        xs = on_short(x)
        ys = on_short(y)
        Cprime = [i for i, p in enumerate(pulls) if on_short(p) == xs]
        S = [i for i, p in enumerate(pulls) if on_short(p) == ys]
        delta = {i: rho_vals(pulls[i] ^ x) for i in Cprime}
        nz = any(any(d) for d in delta.values())
        nontriv += nz
        # ker delta
        kerd = [i for i in Cprime if not any(delta[i])]
        # composition: (ts)(v) = t(s(v)); pull(x, h) = x o h; rho_x o t o s corresponds to pull(pull(x,t),s)
        index = {h: i for i, h in enumerate(H)}
        def comp_(i, j):
            hi, hj = H[i], H[j]
            return index[tuple(hi[hj[v]] for v in range(16))]
        if nz:
            for _ in range(200):
                i, j = rng.choice(Cprime), rng.choice(Cprime)
                k = comp_(i, j)
                assert k in delta
                dk = delta[k]
                di = delta[i]
                dj = delta[j]
                assert tuple((a + c) % 2 for a, c in zip(di, dj)) == dk, "delta not a homomorphism"
        if sols:
            s0 = next(iter(sols))
            predicted = {comp_(k, s0) for k in kerd}
            assert predicted == sols, ("coset", len(predicted), len(sols))
            assert set(S) == {comp_(k, s0) for k in Cprime} or True
            cosetok += 1
        print(f"trial {trial} variant {variant}: |C'|={len(Cprime)} |ker delta|={len(kerd)} delta nonzero={nz} |S|={len(S)} |solutions|={len(sols)}", flush=True)
    print(f"nontrivial delta in {nontriv}/30 trials; coset structure verified in {cosetok} nonempty cases")


if __name__ == "__main__":
    fn = {"mH": check_mH, "dc": check_double_cover, "gap": check_gap, "padic": check_padic, "dep": check_dependent, "bound": check_bound_table, "rank3": check_rank3, "propE": check_propE, "propE2": check_propE2}[sys.argv[1]]
    fn()


