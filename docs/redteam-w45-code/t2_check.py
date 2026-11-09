#!/usr/bin/env python3
"""Referee test of T2 (w45-quartic section 2.2), both directions, exact on small cases.
The solver tiso.c (built separately) decides 3-tensor isomorphism of S_T, S_T' over F_2 with no
structural assumption beyond the rank profile of all slices; ground truth for the tuple problem is brute force
over (pi in Aut_side(H)) x GL(n1) x GL(n2) x GL(n3).

Build: gcc -O2 -o tiso tiso.c  (keep the binary out of the repo).
Usage: t2_check.py <path-to-tiso-binary>"""
import itertools, random, subprocess, sys, time

def gl(n):
    out = []
    def rec(cols, span):
        if len(cols) == n:
            out.append(tuple(cols)); return
        for v in range(1, 1 << n):
            if v not in span:
                rec(cols + [v], span | {s ^ v for s in span})
    rec([], {0})
    return out

def side_auts(E, h):
    """brute force side-preserving automorphisms: (px,py) with (px[i],py[j]) in E iff (i,j) in E"""
    Es = set(E); res = []
    for px in itertools.permutations(range(h)):
        # derive py by matching neighbourhoods
        nbr_y = {y: frozenset(px[x] for x, yy in E if yy == y) for y in range(h)}
        cand_y = {y: [v for v in range(h) if frozenset(x for x, yy in E if yy == v) == nbr_y[y]] for y in range(h)}
        if any(not c for c in cand_y.values()):
            continue
        # distinct neighbourhood assumption in our graphs: exact product
        for py in itertools.product(*[cand_y[y] for y in range(h)]):
            if len(set(py)) == h and all((px[x], py[y]) in Es for x, y in E):
                res.append((px, py))
    return res

def theta157():
    """theta(1,5,7): X vertices 0..5, Y vertices 0..5, branch X0 - Y0 (edge), plus paths X0-..-Y0 of length 5 and 7."""
    # path of length 5: X0 - Y1 - X1 - Y2 - X2 - Y0
    E = [(0, 0)]
    E += [(0, 1), (1, 1), (1, 2), (2, 2), (2, 0)]
    # path of length 7: X0 - Y3 - X3 - Y4 - X4 - Y5 - X5 - Y0
    E += [(0, 3), (3, 3), (3, 4), (4, 4), (4, 5), (5, 5), (5, 0)]
    return E, 6

def cycle(h):
    return [(i, i) for i in range(h)] + [((i + 1) % h, i) for i in range(h)], h

def Hh(h):
    """the graph of w45 (zero-based indices)"""
    E, h = cycle(h)
    return E + [(0, 3), (1, 5)], h

def c4free(E, h):
    nx = {i: {y for x, y in E if x == i} for i in range(h)}
    return all(len(nx[a] & nx[b]) <= 1 for a, b in itertools.combinations(range(h), 2))

def connected(E, h):
    nx = {i: {y for x, y in E if x == i} for i in range(h)}
    ny = {i: {x for x, y in E if y == i} for i in range(h)}
    seen = {('x', 0)}; st = [('x', 0)]
    while st:
        s, v = st.pop()
        for w in (nx[v] if s == 'x' else ny[v]):
            t = ('y' if s == 'x' else 'x', w)
            if t not in seen:
                seen.add(t); st.append(t)
    return len(seen) == 2 * h

def build(E, h, n1, n2, n3, T):
    """S_T slices: returns nX,nY,nZ,slices (list of nZ lists of nX row ints).  T: list of h tensors, each an int
    with bit (a*n2*n3 + b*n3 + c) for T_i(a,b,c)."""
    m = max(n1, n2) + 1
    nX = h * m; nY = n2 + h * m; nZ = n3 + len(E)
    def xi(i, a):
        return i * m + a
    def yj(j, a):
        return n2 + j * m + a
    slices = []
    for c in range(n3):
        M = [0] * nX
        for i in range(h):
            for a in range(n1):
                for b in range(n2):
                    if T[i] >> (a * n2 * n3 + b * n3 + c) & 1:
                        M[xi(i, a)] |= 1 << b
        slices.append(M)
    for (i, j) in E:
        M = [0] * nX
        for a in range(m):
            M[xi(i, a)] |= 1 << yj(j, a)
        slices.append(M)
    return nX, nY, nZ, slices

def tensor_action(T, P, Q, R, n1, n2, n3):
    """T(a,b,c) -> new tensor (T o (P,Q,R))(a,b,c)=T(Pe_a,Qe_b,Re_c), P,Q,R lists of column ints"""
    out = 0
    for a in range(n1):
        for b in range(n2):
            for c in range(n3):
                v = 0
                for a2 in range(n1):
                    if P[a] >> a2 & 1:
                        for b2 in range(n2):
                            if Q[b] >> b2 & 1:
                                for c2 in range(n3):
                                    if R[c] >> c2 & 1:
                                        if T >> (a2 * n2 * n3 + b2 * n3 + c2) & 1:
                                            v ^= 1
                if v:
                    out |= 1 << (a * n2 * n3 + b * n3 + c)
    return out

def concise_tuple(T, n1, n2, n3):
    # factor 1 radical
    def rank_vectors(vecs):
        vecs = list(vecs); r = 0
        while vecs:
            p = vecs.pop()
            if p:
                r += 1
                lsb = p & -p
                vecs = [x ^ p if x & lsb else x for x in vecs]
        return r
    v1, v2, v3 = [], [], []
    for t in T:
        for a in range(n1):
            bits = 0
            for b in range(n2):
                for c in range(n3):
                    if t >> (a * n2 * n3 + b * n3 + c) & 1:
                        bits |= 1 << (b * n3 + c)
            v1.append(bits)
    # rows indexed by a across all t and (b,c): vector over a; easier: radical test directly
    def rad1():
        for x in range(1, 1 << n1):
            if all(all(all(sum(((t >> (a * n2 * n3 + b * n3 + c)) & 1) for a in range(n1) if x >> a & 1) & 1 == 0 for c in range(n3)) for b in range(n2)) for t in T):
                return True
        return False
    def rad2():
        for x in range(1, 1 << n2):
            if all(all(all(sum(((t >> (a * n2 * n3 + b * n3 + c)) & 1) for b in range(n2) if x >> b & 1) & 1 == 0 for c in range(n3)) for a in range(n1)) for t in T):
                return True
        return False
    def rad3():
        for x in range(1, 1 << n3):
            if all(all(all(sum(((t >> (a * n2 * n3 + b * n3 + c)) & 1) for c in range(n3) if x >> c & 1) & 1 == 0 for b in range(n2)) for a in range(n1)) for t in T):
                return True
        return False
    return not (rad1() or rad2() or rad3())

class Solver:
    def __init__(self, path):
        self.p = subprocess.Popen([path], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)
    def query(self, a, b):
        nX, nY, nZ, S = a
        nX2, nY2, nZ2, Sp = b
        assert (nX, nY, nZ) == (nX2, nY2, nZ2)
        lines = [f"Q {nX} {nY} {nZ}"]
        for tens in (S, Sp):
            for sl in tens:
                lines.append(" ".join(f"{v:x}" for v in sl))
        self.p.stdin.write("\n".join(lines) + "\n")
        self.p.stdin.flush()
        return self.p.stdout.readline().strip()
    def histogram(self, a):
        nX, nY, nZ, S = a
        lines = [f"H {nX} {nY} {nZ}"]
        for sl in S:
            lines.append(" ".join(f"{v:x}" for v in sl))
        self.p.stdin.write("\n".join(lines) + "\n")
        self.p.stdin.flush()
        return tuple(int(x) for x in self.p.stdout.readline().split())

def truth_equiv(T, Tp, auts, GLn1, GLn2, GLn3, n1, n2, n3):
    # image set of T under GL
    images = {tuple(tensor_action(t, P, Q, R, n1, n2, n3) for t in T) for P in GLn1 for Q in GLn2 for R in GLn3}
    h = len(T)
    for (px, _py) in auts:
        # T'_i = T_{pi(i)} o (P,B,R)  (see proof step 4): candidate tuple: Tp reindexed
        cand = tuple(Tp[px.index(i)] for i in range(h))
        if cand in images:
            return True
    return False

def run_family(name, E, h, n1, n2, n3, tuples, solver, pairs=None, auts=None):
    t0 = time.time()
    if auts is None:
        auts = side_auts(E, h)
    GLn1, GLn2, GLn3 = gl(n1), gl(n2), gl(n3)
    built = {T: build(E, h, n1, n2, n3, T) for T in tuples}
    if pairs is None:
        pairs = [(a, b) for a in tuples for b in tuples]
    agree = disagree = isoc = noniso = overflow = 0
    profile_only = 0
    maxleaves = 0
    bad = []
    for a, b in pairs:
        r = solver.query(built[a], built[b]).split()
        res = r[0]
        truth = truth_equiv(a, b, auts, GLn1, GLn2, GLn3, n1, n2, n3)
        if res == "OVERFLOW":
            overflow += 1
            continue
        if r[1] == "profile":
            profile_only += 1
        leaves = int(r[2].split('=')[1])
        maxleaves = max(maxleaves, leaves)
        tiso = res == "ISO"
        if tiso == truth:
            agree += 1
            if truth: isoc += 1
            else: noniso += 1
        else:
            disagree += 1
            bad.append((a, b, res, truth))
    print(f"{name}: pairs={len(pairs)} agree={agree} (iso={isoc}, noniso={noniso}, of which rank-profile only={profile_only}) DISAGREE={disagree} overflow={overflow} max leaves={maxleaves} t={time.time()-t0:.1f}s")
    for bad_item in bad[:5]:
        print("   DISAGREEMENT:", bad_item)
    return disagree == 0 and overflow == 0

def main():
    path = sys.argv[1]
    solver = Solver(path)
    rng = random.Random(4646)
    # positive/negative control of the solver on random small tensors
    def rand_tensor(nX, nY, nZ):
        return [[rng.getrandbits(nY) for _ in range(nX)] for _ in range(nZ)]
    def act(S, nX, nY, nZ):
        """S' with S'(x,y,z)=S(Px,Py,Pz) for random invertible P's; returns S' """
        def rand_inv(n):
            while True:
                M = [rng.randrange(1, 1 << n) for _ in range(n)]
                if rank2(M) == n:
                    return M
        P = rand_inv(nX); Q = rand_inv(nY); Pz = rand_inv(nZ)
        # M'(e_k) = P^T M(Pz e_k) Q: rows; Mz = sum_{bit in Pz[k]}  S[bit]
        out = []
        for k in range(nZ):
            Mz = [0] * nX
            for t in range(nZ):
                if Pz[k] >> t & 1:
                    for r in range(nX):
                        Mz[r] ^= S[t][r]
            # (P^T Mz Q)[i] row = sum_{r in column i of P} ...: P^T row i = column i of P
            Mp = [0] * nX
            for i in range(nX):
                row = 0
                for r in range(nX):
                    if P[i] >> r & 1:  # (P e_i)_r
                        row ^= Mz[r]
                # now apply Q on right: entry (i,c) = row . (Q e_c)
                row2 = 0
                for c in range(nY):
                    if bin(row & Q[c]).count('1') & 1:
                        row2 |= 1 << c
                Mp[i] = row2
            out.append(Mp)
        return out
    def rank2(M):
        M = list(M); r = 0
        while M:
            p = M.pop()
            if p:
                r += 1
                lsb = p & -p
                M = [x ^ p if x & lsb else x for x in M]
        return r
    print("control: random tensors with planted isomorphism, nX=nY=5, nZ=4")
    okiso = oknon = 0
    for t in range(30):
        S = rand_tensor(5, 5, 4)
        Sp = act(S, 5, 5, 4)
        r = solver.query((5, 5, 4, S), (5, 5, 4, Sp)).split()
        assert r[0] == "ISO", r
        okiso += 1
        Sq = [list(sl) for sl in Sp]
        Sq[0][0] ^= 1
        r2 = solver.query((5, 5, 4, S), (5, 5, 4, Sq)).split()
        if r2[0] == "NONISO":
            oknon += 1
    print(f"  planted iso found {okiso}/30; single-bit perturbations classified non-iso {oknon}/30 (some may be genuinely iso)")
    # graphs
    graphs = {"C6": cycle(3), "C8": cycle(4), "theta(1,5,7)": theta157()}
    for name, (E, h) in graphs.items():
        auts = side_auts(E, h)
        print(f"{name}: h={h} |E|={len(E)} C4-free={c4free(E,h)} connected={connected(E,h)} min-deg={min(min(sum(1 for e in E if e[0]==i) for i in range(h)), min(sum(1 for e in E if e[1]==j) for j in range(h)))} side-auts={len(auts)}")
    results = []
    # exhaustive (1,1,1) on C6, C8, theta
    for name, (E, h) in graphs.items():
        tups = [t for t in itertools.product(range(2), repeat=h) if any(t)]
        results.append(run_family(f"{name} (1,1,1) exhaustive", E, h, 1, 1, 1, tups, solver))
    # (1,1,2) on C6/C8 exhaustive; theta sampled
    for name, (E, h) in [("C6", cycle(3))]:
        tups = [t for t in itertools.product(range(4), repeat=h) if concise_tuple(t, 1, 1, 2)]
        results.append(run_family(f"{name} (1,1,2) exhaustive", E, h, 1, 1, 2, tups, solver))
    # (2,1,1) on C6: T_i in F_2^2
    for name, (E, h) in [("C6", cycle(3))]:
        tups = [t for t in itertools.product(range(4), repeat=h) if concise_tuple(t, 2, 1, 1)]
        results.append(run_family(f"{name} (2,1,1) exhaustive", E, h, 2, 1, 1, tups, solver))
    # (1,2,1)
    for name, (E, h) in [("C6", cycle(3))]:
        tups = [t for t in itertools.product(range(4), repeat=h) if concise_tuple(t, 1, 2, 1)]
        results.append(run_family(f"{name} (1,2,1) exhaustive", E, h, 1, 2, 1, tups, solver))
    # theta (1,1,2)/(2,2,1) sampled
    E, h = theta157()
    samp = set()
    while len(samp) < 120:
        t = tuple(rng.randrange(4) for _ in range(h))
        if concise_tuple(t, 1, 1, 2):
            samp.add(t)
    tups = sorted(samp)
    pairs = [(a, b) for a in tups for b in rng.sample(tups, 6)]
    results.append(run_family("theta (1,1,2) sampled", E, h, 1, 1, 2, tups, solver, pairs=pairs))
    samp = set()
    while len(samp) < 60:
        t = tuple(rng.randrange(16) for _ in range(h))
        if concise_tuple(t, 2, 2, 1):
            samp.add(t)
    tups = sorted(samp)
    pairs = [(a, b) for a in tups for b in rng.sample(tups, 4)]
    # add planted iso pairs: permuted under GL
    planted = []
    GL1, GL2 = gl(2), gl(2)
    for t in tups[:20]:
        P, Q = rng.choice(GL1), rng.choice(GL2)
        t2 = tuple(tensor_action(x, P, Q, (1,), 2, 2, 1) for x in t)
        if concise_tuple(t2, 2, 2, 1):
            planted.append((t, t2))
    allt = sorted(set(tups) | {b for _, b in planted})
    results.append(run_family("theta (2,2,1) sampled (m=3)", E, h, 2, 2, 1, allt, solver, pairs=pairs + planted))
    # doc's own graph H_9, 1x1x1: sample pairs including all Hamming distance 1 neighbours of a few vectors
    E9, h9 = Hh(9)
    auts9 = side_auts(E9, h9) if False else [(tuple(range(9)), tuple(range(9)))]
    print(f"H_9: h=9 |E|={len(E9)} C4-free={c4free(E9,9)} connected={connected(E9,9)} side-auts=1 (w45 check_graph)")
    base = [tuple(rng.randrange(2) for _ in range(9)) for _ in range(5)]
    base = [b for b in base if any(b)]
    pairs = []
    for b in base:
        pairs.append((b, b))
        for i in rng.sample(range(9), 3):
            c = list(b); c[i] ^= 1; c = tuple(c)
            if any(c):
                pairs.append((b, c))
    tups9 = sorted({x for p in pairs for x in p})
    results.append(run_family("H_9 (1,1,1) doc graph (sampled pairs)", E9, 9, 1, 1, 1, tups9, solver, pairs=pairs, auts=auts9))
    # ---- exhaustive by rank-profile classes (only same-profile pairs need the solver)
    def run_grouped(name, E, h, n1, n2, n3, tuples, solver, cap=4000):
        t0 = time.time()
        auts = side_auts(E, h)
        GLn1, GLn2, GLn3 = gl(n1), gl(n2), gl(n3)
        built = {T: build(E, h, n1, n2, n3, T) for T in tuples}
        groups = {}
        for T in tuples:
            groups.setdefault(solver.histogram(built[T]), []).append(T)
        pairs = []
        for g in groups.values():
            for i, a in enumerate(g):
                for b in g[i:]:
                    pairs.append((a, b))
        total = len(pairs)
        if total > cap:
            pairs = rng.sample(pairs, cap)
        print(f"  {name}: {len(tuples)} concise tuples, {len(groups)} rank-profile classes, {total} same-profile pairs" + (f" (sampling {cap})" if total > cap else " (all)"))
        return run_family(name, E, h, n1, n2, n3, tuples, solver, pairs=pairs, auts=auts)
    results2 = []
    E6, h6 = cycle(3)
    tups = [t for t in itertools.product(range(16), repeat=h6) if concise_tuple(t, 2, 2, 1)]
    results2.append(run_grouped("C6 (2,2,1) exhaustive", E6, h6, 2, 2, 1, tups, solver))
    E, h = theta157()
    tups = [t for t in itertools.product(range(4), repeat=h) if concise_tuple(t, 1, 1, 2)]
    results2.append(run_grouped("theta (1,1,2) exhaustive", E, h, 1, 1, 2, tups, solver))
    # ---- mutation controls: harness must be able to detect failures
    print("\nMutation controls (each should produce disagreements):")
    # (a) graph C4 (contains a 4-cycle), expected to break Step 3 and hence the theorem: h=2
    Ec4 = [(0,0),(1,0),(0,1),(1,1)]
    h2 = 2
    tups = [t for t in itertools.product(range(2), repeat=2) if any(t)]
    autsC4 = side_auts(Ec4, 2)
    print(f"  C4: side-auts={len(autsC4)}; S_T iso vs tuple truth (expected: possible false iso/non-iso)")
    run_family("C4 (mutation: has a 4-cycle), 1,1,1", Ec4, 2, 1, 1, 1, tups, solver, auts=autsC4)
    # (b) no padding: m=max(n1,n2) instead of +1
    def build_nopad(E, h, n1, n2, n3, T):
        m = max(n1, n2)
        nX = h * m; nY = n2 + h * m; nZ = n3 + len(E)
        xi = lambda i, a: i * m + a
        yj = lambda j, a: n2 + j * m + a
        slices = []
        for c in range(n3):
            M = [0] * nX
            for i in range(h):
                for a in range(n1):
                    for b in range(n2):
                        if T[i] >> (a * n2 * n3 + b * n3 + c) & 1:
                            M[xi(i, a)] |= 1 << b
            slices.append(M)
        for (i, j) in E:
            M = [0] * nX
            for a in range(m):
                M[xi(i, a)] |= 1 << yj(j, a)
            slices.append(M)
        return nX, nY, nZ, slices
    disagree = 0; n = 0
    E8, h8 = cycle(4)
    auts8 = side_auts(E8, h8)
    GL1 = [(1,)]
    tups8 = [t for t in itertools.product(range(2), repeat=4) if any(t)]
    for a in tups8:
        for b in tups8:
            r = solver.query(build_nopad(E8, h8, 1, 1, 1, a), build_nopad(E8, h8, 1, 1, 1, b)).split()
            truth = truth_equiv(a, b, auts8, GL1, GL1, GL1, 1, 1, 1)
            if r[0] != "OVERFLOW" and (r[0] == "ISO") != truth:
                disagree += 1
            n += 1
    print(f"  no padding (m=max(n1,n2)=1) on C8, 1,1,1: {disagree} disagreements of {n} pairs (expected > 0 if padding matters)")
    print("ALL OK" if all(results) and all(results2) else "SOME FAILED")

if __name__ == "__main__":
    main()
