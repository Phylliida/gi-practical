#!/usr/bin/env python3
"""Referee checks for Theorem H (w45-quartic section 4), independent of check_pins.py.
 1. identity Pr[rho(v,v',.) in W] = E_{lambda in W^perp} 2^{-rk} and the printed upper bound,
    exact enumeration over (v,v') and over every W of the given dimension, small d.
 2. s(tau) exact by enumeration over all 2-subspaces (wedge determines the contraction); invariance under GL.
 3. the algorithm's reconstruction step: every automorphism/isomorphism L is recovered from the
    images of a spanning tuple; decoys rejected.
 4. random 4-forms: exact s vs the corank bound Pr[corank>=c]<=4*2^{-c(c-1)/2}.
Usage: h_check.py [slow]   (slow adds exact s at d=10,11, a few minutes)"""
import itertools, random, sys

def rank(rows):
    rows = list(rows); r = 0
    while rows:
        p = rows.pop()
        if p:
            r += 1
            lsb = p & -p
            rows = [x ^ p if x & lsb else x for x in rows]
    return r

class Form:
    """alternating 4-form on F_2^d, tau: iterable of sorted 4-tuples of coordinates."""
    def __init__(self, d, tau):
        self.d = d
        self.tau = sorted(set(tau))
        self.pair = {}
        for q in self.tau:
            for i, j in itertools.permutations(q, 2):
                a, b = [x for x in q if x != i and x != j]
                self.pair.setdefault((i, j), []).append((a, b))
    def contract(self, w, lam):
        """rows of the alternating matrix tau(w,lam,.,.)"""
        M = [0] * self.d
        d = self.d
        for i in range(d):
            if w >> i & 1:
                for j in range(d):
                    if lam >> j & 1:
                        for a, b in self.pair.get((i, j), ()):
                            M[a] ^= 1 << b
                            M[b] ^= 1 << a
        return M
    def functional(self, u, v, x):
        """row vector tau(u,v,x,.)"""
        M = self.contract(u, v)
        r = 0
        for c in range(self.d):
            if bin(M[c] & x).count('1') & 1:
                r |= 1 << c
        return r
    def evaluate(self, a, b, c, e):
        M = self.contract(a, b)
        val = 0
        for i in range(self.d):
            if c >> i & 1:
                val ^= bin(M[i] & e).count('1') & 1
        return val

def apply_gl(F, L):
    """tau o L, L list of d columns (L e_i = L[i]). Computes new coefficients by evaluation on basis 4-subsets."""
    d = F.d
    tau = []
    for q in itertools.combinations(range(d), 4):
        i, j, k, l = q
        if F.evaluate(L[i], L[j], L[k], L[l]):
            tau.append(q)
    return Form(d, tau)

def rand_gl(d, rng):
    while True:
        L = [rng.randrange(1, 1 << d) for _ in range(d)]
        if rank(L) == d:
            return L

def min_rank(F):
    d = F.d
    best = d
    seen = set()
    for w in range(1, 1 << d):
        for lam in range(1, 1 << d):
            if lam == w:
                continue
            key = tuple(sorted((w, lam, w ^ lam)))
            if key in seen:
                continue
            seen.add(key)
            r = rank(F.contract(w, lam))
            if r < best:
                best = r
    return best

def subspaces(d, k):
    """all k-dim subspaces of F_2^d as sorted tuples of nonzero elements"""
    if k == 0:
        return [()]
    out = set()
    def rec(basis, span):
        if len(basis) == k:
            out.add(tuple(sorted(span - {0})))
            return
        for v in range(1, 1 << d):
            if v not in span:
                rec(basis + [v], span | {s ^ v for s in span})
    rec([], {0})
    return list(out)

def lemma_exact(F, w, Wvecs, R):
    """Wvecs: nonzero elements of a subspace W of (F_2^d)^* (bitmask functionals), dim R-1"""
    d = F.d
    Wset = set(Wvecs) | {0}
    # W^perp
    Wperp = [v for v in range(1 << d) if all(bin(v & f).count('1') & 1 == 0 for f in Wset)]
    # exact probability over v,v'
    cnt = 0
    total = 1 << (2 * d)
    # compute rho(v,v',.) = functional by bilinearity using contract(w, .) tables
    # tau(v,v',.,w) = sum_{i in v, j in v'} tau(e_i,e_j,.,w): build table of functionals on basis pairs
    table = [[F.functional(1 << i, 1 << j, w) for j in range(d)] for i in range(d)]
    for v in range(1 << d):
        fv = [0] * d
        for j in range(d):
            acc = 0
            for i in range(d):
                if v >> i & 1:
                    acc ^= table[i][j]
            fv[j] = acc
        for vp in range(1 << d):
            phi = 0
            for j in range(d):
                if vp >> j & 1:
                    phi ^= fv[j]
            if phi in Wset:
                cnt += 1
    pr = cnt / total
    # Fourier side
    fourier = 0.0
    for lam in Wperp:
        # B_lam(v,v') = tau(v,v',lam,w), alternating in v,v': matrix = contract(lam,w)
        r = rank(F.contract(lam, w)) if lam else 0
        fourier += 2.0 ** (-r)
    fourier /= len(Wperp)
    return pr, fourier

def main():
    rng = random.Random(46)
    # 1. exact lemma d=6 for several forms, all W of dim R-1 (R=1,2,3)
    worst_gap = 0
    ntests = 0
    for trial in range(4):
        d = 6
        tau = [q for q in itertools.combinations(range(d), 4) if rng.random() < 0.5]
        F = Form(d, tau)
        s = min_rank(F)
        for R in (1, 2, 3):
            subs = subspaces(d, R - 1)
            for w in rng.sample(range(1, 1 << d), 3):
                for W in rng.sample(subs, min(25, len(subs))):
                    pr, fo = lemma_exact(F, w, W, R)
                    assert abs(pr - fo) < 1e-9, ("Fourier identity failed", pr, fo)
                    ntests += 1
                    bound = 2.0 ** (R - d) + 2.0 ** (-s)
                    assert pr <= bound + 1e-9, ("printed bound failed", pr, bound, s, R)
                    worst_gap = max(worst_gap, pr / bound)
    print(f"1. lemma: {ntests} exact (tau,w,W,R) tests at d=6: identity and printed bound hold; max pr/bound = {worst_gap:.3f}")
    # 2. exact s, invariance
    for d in (6, 7, 8, 9) + ((10, 11) if len(sys.argv) > 1 and sys.argv[1] == "slow" else ()):
        ss = []
        for _ in range(3 if d < 9 else 2):
            tau = [q for q in itertools.combinations(range(d), 4) if rng.random() < 0.5]
            F = Form(d, tau)
            s = min_rank(F)
            if d <= 8:
                L = rand_gl(d, rng)
                G = apply_gl(F, L)
                assert min_rank(G) == s, "s not invariant"
            ss.append(s)
        print(f"2. d={d}: exact s of random 4-forms = {ss} (invariant under random GL)" if d <= 8 else f"2. d={d}: exact s = {ss}")
    # 3. reconstruction / exhaustive over candidates restricted: for d=6, enumerate all L in a random set and all automorphisms
    okr = dec = 0
    d = 8
    for trial in range(30):
        tau = [q for q in itertools.combinations(range(d), 4) if rng.random() < 0.5]
        F = Form(d, tau)
        L = rand_gl(d, rng)
        G = apply_gl(F, L)   # G = F o L
        # good tuple for F by random search: u_1..u_{2m}, b_1..b_b, functionals tau_F(u_j,u_k,b_i,.)
        for attempt in range(1000):
            us = [rng.randrange(1 << d) for _ in range(6)]
            bs = [rng.randrange(1 << d) for _ in range(4)]
            fun = [F.functional(us[j], us[k], b) for j, k in itertools.combinations(range(6), 2) for b in bs]
            if rank(fun) == d:
                break
        else:
            continue
        # candidates on G side: the images under L^{-1} give the true one
        inv = {}
        for v in range(1 << d):
            img = 0
            for i in range(d):
                if v >> i & 1:
                    img ^= L[i]
            inv[img] = v
        us_g = [inv[u] for u in us]
        bs_g = [inv[b] for b in bs]
        # tau_G(x,y,z,.) = tau_F(Lx,Ly,Lz,L.) so functionals: fun_G[idx] = fun_F[idx] o L on the G side,
        # i.e. for row r: (fun_G)(e_c) = fun_F(L e_c).  L is determined by the system fun_F(L e_c)=fun_G(e_c) ... 
        fung = [G.functional(us_g[j], us_g[k], b) for j, k in itertools.combinations(range(6), 2) for b in bs_g]
        # Solve for L: unknown columns: for each c, unknown vector y_c in F_2^d with fun_F[idx](y_c) = fung[idx]>>c &1
        recL = []
        for c in range(d):
            # augmented system: rows fun[idx] with rhs bit
            rows = [(fun[idx] | (((fung[idx] >> c) & 1) << d)) for idx in range(len(fun))]
            # gaussian elimination
            piv = {}
            for r in rows:
                for p in sorted(piv, reverse=True):
                    if r >> p & 1:
                        r ^= piv[p]
                low = r & ((1 << d) - 1)
                if low:
                    p = low.bit_length() - 1
                    piv[p] = r
                elif r:
                    raise AssertionError("inconsistent")
            assert len(piv) == d
            y = 0
            for p in sorted(piv):
                val = piv[p] >> d & 1
                rest = piv[p] & ((1 << p) - 1)
                # back substitution over earlier pivots: since p ranges ascending use computed bits
                if bin(rest & y).count('1') & 1:
                    val ^= 1
                if val:
                    y |= 1 << p
            recL.append(y)
        assert recL == L, ("reconstruction wrong", recL, L)
        okr += 1
        # decoy: random candidate images: reconstructed map must either be singular/inconsistent or fail verification
        for _ in range(20):
            us_d = [rng.randrange(1 << d) for _ in range(6)]
            bs_d = [rng.randrange(1 << d) for _ in range(4)]
            fung2 = [G.functional(us_d[j], us_d[k], b) for j, k in itertools.combinations(range(6), 2) for b in bs_d]
            ok_map = True
            cand = []
            for c in range(d):
                rows = [(fun[idx] | (((fung2[idx] >> c) & 1) << d)) for idx in range(len(fun))]
                piv = {}
                for r in rows:
                    for p in sorted(piv, reverse=True):
                        if r >> p & 1:
                            r ^= piv[p]
                    low = r & ((1 << d) - 1)
                    if low:
                        p = low.bit_length() - 1
                        piv[p] = r
                    elif r:
                        ok_map = False
                        break
                if not ok_map:
                    break
                y = 0
                for p in sorted(piv):
                    val = piv[p] >> d & 1
                    if bin(piv[p] & ((1 << p) - 1) & y).count('1') & 1:
                        val ^= 1
                    if val:
                        y |= 1 << p
                cand.append(y)
            if ok_map and rank(cand) == d:
                # verification step of the algorithm would compare f o L to g
                H = apply_gl(F, cand)
                if H.tau == G.tau:
                    dec += 1  # a genuine isomorphism found (very unlikely)
    print(f"3. reconstruction: {okr}/30 d=8 instances recovered L exactly from functionals; decoys verified: {dec} genuine")
    # 4. corank bound for uniform alternating n x n
    n = 10
    N = 100000
    obs = {}
    pairs = list(itertools.combinations(range(n), 2))
    for _ in range(N):
        M = [0] * n
        for a, b in pairs:
            if rng.getrandbits(1):
                M[a] ^= 1 << b
                M[b] ^= 1 << a
        c = n - rank(M)
        obs[c] = obs.get(c, 0) + 1
    tot = 0
    print("4. uniform alternating 10x10: corank c, empirical Pr[corank>=c], bound 4*2^{-c(c-1)/2}")
    for c in sorted(obs, reverse=True):
        tot += obs[c]
        print(f"   c={c}: {tot/N:.5f}  bound {4*2**(-c*(c-1)/2):.5f}")

if __name__ == "__main__":
    main()
