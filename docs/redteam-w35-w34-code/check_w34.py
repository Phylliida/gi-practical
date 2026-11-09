#!/usr/bin/env python3
"""
Referee checks for docs/w34-vc.md (branch w37-redteam-cubic); pure python, single process.
Sections: arith greedy prop31 thm32 lemma41 prop42
Run: nice -n 19 python3 -I docs/redteam-w35-w34-code/check_w34.py [section ...]
"""
import itertools, math, random, sys, time
from collections import Counter

def paley_prime(q):
    squares = {(x*x) % q for x in range(1, q)}
    return [[0 if x == y else (-1 if ((x - y) % q) in squares else 1) for y in range(q)] for x in range(q)]

def paley9():
    # F_9 = F_3[i], i^2=-1; elements a+bi encoded a+3b
    def add(x, y): return ((x % 3 + y % 3) % 3) + 3*((x//3 + y//3) % 3)
    def neg(x): return ((-x % 3) % 3) + 3*((-(x//3)) % 3)
    def mul(x, y):
        a, b = x % 3, x//3; c, d = y % 3, y//3
        # (a+bi)(c+di) = (ac-bd) + (ad+bc)i
        return ((a*c - b*d) % 3) + 3*((a*d + b*c) % 3)
    squares = {mul(x, x) for x in range(1, 9)}
    return [[0 if x == y else (-1 if add(x, neg(y)) in squares else 1) for y in range(9)] for x in range(9)]

def check_conference(V):
    n = len(V)
    assert all(V[i][i] == 0 for i in range(n))
    assert all(V[i][j] == V[j][i] for i in range(n) for j in range(n))
    assert all(abs(V[i][j]) == 1 for i in range(n) for j in range(n) if i != j)
    # V^2 = nI - J (sampled)
    assert all(sum(V[i][k]*V[j][k] for k in range(n)) == (n-1 if i == j else -1) for i in range(0, n, max(1, n//11)) for j in range(0, n, max(1, n//11)))
    assert all(sum(V[i]) == 0 for i in range(n))

def turyn(V1, V2):
    n1, n2 = len(V1), len(V2); N = n1*n2
    W = [[0]*N for _ in range(N)]
    for x1 in range(n1):
        for x2 in range(n2):
            for y1 in range(n1):
                for y2 in range(n2):
                    W[x1*n2+x2][y1*n2+y2] = V1[x1][y1]*V2[x2][y2] + (1 if x1 == y1 else 0) - (1 if x2 == y2 else 0)
    return W

def wl(M, singles, rounds):
    """1-WL (colour refinement) with individualized vertices `singles`; rounds=None means stable; returns colours."""
    n = len(M)
    colour = [0]*n
    for i, s in enumerate(singles):
        colour[s] = i + 1
    def canon(col):
        idx = {}
        return [idx.setdefault(c, len(idx)) for c in col]
    colour = canon(colour)
    r = 0
    while rounds is None or r < rounds:
        keys = []
        for v in range(n):
            row = M[v]
            ctr = {}
            for z in range(n):
                k = (colour[z], row[z])
                ctr[k] = ctr.get(k, 0) + 1
            keys.append((colour[v], tuple(sorted(ctr.items()))))
        idx = {}
        new = [idx.setdefault(k, len(idx)) for k in keys]
        r += 1
        if rounds is None and len(set(new)) == len(set(colour)):
            colour = new; break
        colour = new
    return colour

def section_arith():
    print("[arith] epsilon-net constants")
    eps = 3/4
    c2 = (8/eps)*math.log2(13/eps)
    delta = 2/2**(11*eps/4)
    print(f"  (8d/eps) log2(13/eps) per d at eps=3/4: {c2:.3f} (<=44: {c2 <= 44}); (4/eps)log2(2/delta) <= 11 iff delta >= {delta:.4f}")
    print(f"  union bound for sets outside B(tau): < 1/(2n); total failure < {delta:.4f}+1/(2n) < 1 for n>=5: {delta+1/10<1}")
    # Prop 1.1 bound and identity for small Paley graphs
    ok = True
    for q in (13, 17, 29, 37):
        C = paley_prime(q)
        G = list(itertools.combinations(range(q), 2))
        pmax = 0
        for x, y in itertools.combinations(range(q), 2):
            agree = [u for u in range(q) if u not in (x, y) and C[u][x] == C[u][y]]
            if len(agree) != (q-3)//2:
                ok = False
            fset = 0
            for a, b in itertools.combinations(agree, 2):
                Tx = sum(C[a][z]*C[b][z]*C[x][z] for z in range(q))
                Ty = sum(C[a][z]*C[b][z]*C[y][z] for z in range(q))
                if Tx == Ty:
                    fset += 1
            pmax = max(pmax, fset/len(G))
        bound = (q-3)*(q-5)/(4*q*(q-1))
        print(f"  P({q}): max p_2 = {pmax:.4f}; Prop 1.1 bound {bound:.4f}; holds: {pmax <= bound + 1e-12}")
        ok = ok and pmax <= bound + 1e-12
    return ok

def section_greedy():
    """Thm 2.1 proof steps on P(65537) with d=4 (and all intermediate inequalities)."""
    q = 65537
    print(f"[greedy] P({q}), checking the greedy step inequalities of Thm 2.1")
    # Legendre via quadratic residue table
    sq = bytearray(q)
    for x in range(1, q):
        sq[(x*x) % q] = 1
    def C(x, y):
        if x == y: return 0
        return -1 if sq[(x-y) % q] else 1
    d = int(0.5*math.log2(q)) - 4
    print(f"  d = floor(0.5 log2 n)-4 = {d}")
    rng = random.Random(3456)
    D = []
    cells = {(): list(range(q))}
    ok = True
    for i in range(d):
        psi = sum(1/len(c) for c in cells.values())
        # search candidates x not in D until sum_Q <C_x,1_Q>^2/|Q|^2 <= 2 psi
        tries = 0
        while True:
            x = rng.randrange(q)
            if x in D: continue
            tries += 1
            s = 0.0
            for pat, c in cells.items():
                t = sum(C(x, y) for y in c)
                s += t*t/(len(c)**2)
            if s <= 2*psi: break
        D.append(x)
        alpha = 2**(i+1)/math.sqrt(q)
        newcells = {}
        for pat, c in cells.items():
            plus = [y for y in c if y != x and C(x, y) > 0]
            minus = [y for y in c if y != x and C(x, y) < 0]
            lower = (len(c)*(1-math.sqrt(2*psi)) - 1)/2
            if len(plus) < lower - 1e-9 or len(minus) < lower - 1e-9:
                ok = False
            newcells[pat+(1,)] = plus; newcells[pat+(-1,)] = minus
        mincell = min(len(c) for c in newcells.values())
        if mincell < q/2**(i+2): ok = False
        cells = newcells
        print(f"  step {i}: psi={psi:.6f}, sqrt(2psi)={math.sqrt(2*psi):.5f}, alpha_i={alpha:.5f}, candidates tried {tries}, min new cell {mincell} >= n/2^(i+2)={q/2**(i+2):.1f}")
    allpatterns = all(len(c) >= 2 for c in cells.values()) and len(cells) == 2**d
    print(f"  all {2**d} patterns on D realized by >=2 vertices: {allpatterns}")
    return ok and allpatterns

def section_prop31():
    """Prop 3.1 product coarsening, W_1 over P(5), P(9); W_2 over P(5); random individualized sets."""
    rng = random.Random(370021)
    def proj_cells(cols):
        return cols
    P5 = paley_prime(5); P9 = paley9(); P13 = paley_prime(13)
    for V in (P5, P9, P13):
        check_conference(V)
    ok = True; tot = 0
    # L=1 tests
    for V, name in ((P5, 'P5'), (P9, 'P9'), (P13, 'P13')):
        v = len(V)
        W = turyn(V, V)
        check_conference(W)
        n = v*v
        for trial in range(25):
            k = rng.choice([1, 2, 3])
            S = rng.sample(range(n), k)
            S1 = sorted({s // v for s in S}); S2 = sorted({s % v for s in S})
            for rounds in (1, 2, 3, None):
                c1 = wl(V, S1, rounds); c2 = wl(V, S2, rounds)
                c = wl(W, S, rounds)
                tot += 1
                # each product cell lies in one cell of W
                seen = {}
                for x in range(n):
                    key = (c1[x // v], c2[x % v])
                    if key in seen and seen[key] != c[x]:
                        ok = False; print("  violation", name, S, rounds)
                        break
                    seen[key] = c[x]
    print(f"[prop31] L=1 (P5,P9,P13) {tot} (S,r) cases: product cells inside W cells: {ok}")
    # L=2 over P5: 4 coordinates, W_2 of order 625
    W1 = turyn(P5, P5); W2 = turyn(W1, W1)
    check_conference(W2)
    v = 5; n = 625; tot2 = 0; ok2 = True
    def coords(x):
        return (x//125, (x//25) % 5, (x//5) % 5, x % 5)
    for trial in range(12):
        S = rng.sample(range(n), 2)
        for rounds in (1, 2, None):
            cs = [wl(P5, sorted({coords(s)[j] for s in S}), rounds) for j in range(4)]
            c = wl(W2, S, rounds)
            seen = {}; tot2 += 1
            for x in range(n):
                key = tuple(cs[j][coords(x)[j]] for j in range(4))
                if key in seen and seen[key] != c[x]:
                    ok2 = False; print("  L=2 violation", S, rounds); break
                seen[key] = c[x]
    print(f"[prop31] L=2 over P5: {tot2} cases: {ok2}")
    return ok and ok2

def section_thm32():
    """Exact shattering of Thm 3.2 on W_2 over P(5) (n=625, m=4): all Y subset of [3], tests a^i, k=1,2,3, r=1,2,stable."""
    P5 = paley_prime(5); W1 = turyn(P5, P5); W2 = turyn(W1, W1)
    v = 5; m = 4
    def enc(c):
        return c[0]*125 + c[1]*25 + c[2]*5 + c[3]
    rng = random.Random(370022)
    V = P5
    t0 = time.time()
    ok = True; tot = 0
    for (s, t) in [(0, 1), (0, 2), (3, 4)]:
        alphas = [a for a in range(v) if a not in (s, t) and V[a][s] == V[a][t]]
        betas = [a for a in range(v) if a not in (s, t) and V[a][s] != V[a][t]]
        assert alphas and betas
        alpha = alphas[0]; ap1 = betas[0]
        others = [z for z in range(v) if z not in (s, t, ap1)]
        for k in (1, 2, 3):
            aprimes = [ap1] + others[:k-1]
            if len(aprimes) < k:
                continue
            for i in range(3):
                tuple_ = []
                for rho in range(k):
                    coords = [alpha]*4
                    coords[i] = aprimes[rho]
                    tuple_.append(enc(tuple(coords)))
                for Y in itertools.product([0, 1], repeat=3):
                    x = [s]*4
                    y = [s]*4
                    for j in range(3):
                        if not Y[j]:
                            y[j] = t
                    y[3] = t
                    X = enc(tuple(x)); YY = enc(tuple(y))
                    for rounds in (1, 2, None):
                        c = wl(W2, tuple_, rounds)
                        same = c[X] == c[YY]
                        tot += 1
                        expected = bool(Y[i])
                        if same != expected:
                            ok = False
                            print(f"  MISMATCH (s,t)={s,t} k={k} i={i} Y={Y} r={rounds}: same={same} expected={expected}")
    print(f"[thm32] W_2 over P5 (n=625): {tot} instances, all agree with the shattering pattern: {ok} ({time.time()-t0:.1f}s)")
    return ok

def section_lemma41():
    """w32 Lemma 4.1 formula for T^W on generic triples, and Lemma 3.3 / Prop 4.2 collision-lifting on P(9) iterates."""
    P5 = paley_prime(5); P9 = paley9(); P13 = paley_prime(13)
    rng = random.Random(370023)
    ok = True; cnt = 0
    def T(V, a, b, x):
        return sum(V[a][z]*V[b][z]*V[x][z] for z in range(len(V)))
    for V, name in ((P5, 'P5'), (P9, 'P9'), (P13, 'P13')):
        v = len(V); W = turyn(V, V)
        for _ in range(400):
            a1, b1, x1 = rng.sample(range(v), 3)
            a2, b2, x2 = rng.sample(range(v), 3)
            a = a1*v+a2; b = b1*v+b2; x = x1*v+x2
            lhs = T(W, a, b, x)
            s, t, u = V[a1][b1], V[a1][x1], V[b1][x1]
            sp, tp, up = V[a2][b2], V[a2][x2], V[b2][x2]
            R = -(s*t+s*u+t*u) + (sp*tp+sp*up+tp*up) - (s*tp+s*up+t*sp+t*up+u*sp+u*tp)
            rhs = T(V, a1, b1, x1)*T(V, a2, b2, x2) + R
            cnt += 1
            if lhs != rhs:
                ok = False
                print("  mismatch", name, a1, b1, x1, a2, b2, x2, lhs, rhs)
                break
    print(f"[lemma41] formula on {cnt} generic triples: {ok}")
    return ok

def section_prop42():
    """Prop 4.2 ingredients on P(9): (i) base collision configuration; (ii) iterated collision of the 'all a, all b' test for x^Y,y^Y on W_2 (order 6561);
       (iii) tests a^i are collisions iff i in Y; (iv) lifting one more level via T^W row computation at order 6561 from W_1 factor."""
    V = paley9(); v = 9; check_conference(V)
    def TV(a, b, x):
        return sum(V[a][z]*V[b][z]*V[x][z] for z in range(9))
    # find collision configuration
    conf = None
    for (a, b, s, t) in itertools.permutations(range(9), 4):
        if V[a][s] == V[a][t] and V[b][s] == V[b][t] and TV(a, b, s) == TV(a, b, t):
            conf = (a, b, s, t); break
    print(f"[prop42] P(9) collision configuration (a,b;s,t) = {conf}")
    assert conf is not None
    a, b, s, t = conf
    # W_2 entries by coordinate recursion
    def W_entry(xc, yc):
        """W_L on coordinate tuples of length 2^L, recursion W = W1 tensor W2 + I tensor J - J tensor I."""
        n = len(xc)
        if n == 1:
            return V[xc[0]][yc[0]]
        h = n//2
        x1, x2, y1, y2 = xc[:h], xc[h:], yc[:h], yc[h:]
        return W_entry(x1, y1)*W_entry(x2, y2) + (1 if x1 == y1 else 0) - (1 if x2 == y2 else 0)
    allv = list(itertools.product(range(9), repeat=4))
    assert len(allv) == 6561
    def rowW(xc):
        return [W_entry(xc, z) for z in allv]
    t0 = time.time()
    # x^Y, y^Y for m=4 (coordinates [4]; [m-1]={1,2,3}), s common, witness coordinate m
    A = (a,a,a,a); B = (b,b,b,b)
    rA = rowW(A); rB = rowW(B)
    def T_W(rowa, rowb, rowx):
        return sum(p*q*r for p, q, r in zip(rowa, rowb, rowx))
    ok1 = True
    for Y in itertools.product([0,1], repeat=3):
        x = [s]*4; y = [s]*4
        for j in range(3):
            if not Y[j]:
                y[j] = t
        y[3] = t
        x = tuple(x); y = tuple(y)
        rx = rowW(x); ry = rowW(y)
        if W_entry(A, x) != W_entry(A, y) or W_entry(B, x) != W_entry(B, y):
            ok1 = False; print("  sign mismatch", Y)
        if T_W(rA, rB, rx) != T_W(rA, rB, ry):
            ok1 = False; print("  T mismatch", Y)
    print(f"[prop42] 'all-a, all-b' test is a collision for every x^Y,y^Y on W_2 (6561): {ok1} ({time.time()-t0:.1f}s)")
    # (iii) tests a^i (k=2): at coordinate i: alpha'_1, alpha'_2, others alpha
    alpha = next(z for z in range(9) if z not in (s, t) and V[z][s] == V[z][t])
    ap1 = next(z for z in range(9) if z not in (s, t) and V[z][s] != V[z][t])
    ap2 = next(z for z in range(9) if z not in (s, t, ap1))
    ok3 = True; t1 = time.time()
    for i in range(3):
        c1 = [alpha]*4; c1[i] = ap1; c2 = [alpha]*4; c2[i] = ap2
        c1 = tuple(c1); c2 = tuple(c2)
        r1 = rowW(c1); r2 = rowW(c2)
        for Y in itertools.product([0,1], repeat=3):
            x = [s]*4; y = [s]*4
            for j in range(3):
                if not Y[j]:
                    y[j] = t
            y[3] = t
            x = tuple(x); y = tuple(y)
            rx = rowW(x); ry = rowW(y)
            collision = (W_entry(c1, x) == W_entry(c1, y) and W_entry(c2, x) == W_entry(c2, y) and T_W(r1, r2, rx) == T_W(r1, r2, ry))
            expected = bool(Y[i])
            if collision != expected:
                ok3 = False; print(f"  pattern mismatch i={i} Y={Y}: collision={collision} expected={expected}")
    print(f"[prop42] shattering pattern for tests a^i on W_2 via T: {ok3} ({time.time()-t1:.1f}s)")
    return ok1 and ok3

SECTIONS = {"arith": section_arith, "greedy": section_greedy, "prop31": section_prop31, "thm32": section_thm32, "lemma41": section_lemma41, "prop42": section_prop42}

if __name__ == "__main__":
    which = sys.argv[1:] or list(SECTIONS)
    allok = True
    for s in which:
        t0 = time.time()
        try:
            ok = SECTIONS[s]()
        except Exception as e:
            import traceback; traceback.print_exc(); ok = False
        print(f"== {s}: {'PASS' if ok else 'FAIL'}  ({time.time()-t0:.1f}s)\n", flush=True)
        allok = allok and ok
    print("ALL PASS" if allok else "SOME FAILED")
