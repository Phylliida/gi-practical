#!/usr/bin/env python
"""Small experiments for docs/w28-sigma.md (run under nice, one process, minutes at most).

  w28-sigma-check.py phase0 m "T"        status of the root certificate for T, stopping at Step 4
                                         (this is Phase 0 of the lazy variant, sec 5)
  w28-sigma-check.py rigid m r [seed]    PG(m-1,2) minus r random lines: Aut order, 1-WL, wrong-anchor test
  w28-sigma-check.py pasch m k [seed]    PG(m-1,2) with k disjoint Pasch switches: STS check, Aut, defect
                                         invariant, refinement from it
  w28-sigma-check.py count               memoization and chain counts (sec 3)
  w28-sigma-check.py twins m             line-pattern twin classes on PG(m-1,2) points

Needs pynauty for Aut (r2-hybrid venv).  The phase0 mode reuses the exact replay Root class of
docs/redteam-w18-latin-check.py.
"""
import sys, os, random, math, itertools, time, importlib.util, collections


def load_redteam():
    here = os.path.dirname(os.path.abspath(__file__))
    spec = importlib.util.spec_from_file_location("rt", os.path.join(here, "redteam-w18-latin-check.py"))
    rt = importlib.util.module_from_spec(spec)
    argv, sys.argv = sys.argv, ["x", "none"]
    try:
        spec.loader.exec_module(rt)
    finally:
        sys.argv = argv
    return rt


def phase0(m, T):
    """Stop at the first Step 4 (or Nonfull/Full): the lazy variant's Phase 0."""
    rt = load_redteam()
    R = rt.Root(m, T)
    n, k = R.n, R.k
    t0 = time.time()
    print(f"phase0 m={m} n={n} T={T}", flush=True)
    for it in range(40):
        gens, m1, e1, orbs, _ = R.auto()
        ok, ev = R.phi_ok(gens)
        wn = sum(sum(1 for y in range(n) if y != x and R.win[x][y]) for x in range(n))
        print(f" iter {it}: |W|={wn} phi even={ev}/{rt.alt_size(k)} t={time.time()-t0:.0f}s", flush=True)
        if not ok:
            print(" STATUS: NONFULL at iteration", it); return "NONFULL", it
        vreps = sorted({orbs[i] for i in range(n)})
        reps = []
        for a in vreps:
            g2, _, _, o2, _ = R.auto(indiv=[a])
            for b in sorted({o2[y] for y in range(n) if y != a}):
                if not R.win[a][b]:
                    reps.append((a, b))
        affected = []
        for (a, b) in reps:
            g2, _, _, _, _ = R.auto(indiv=[a, b])
            ok2, _ = R.phi_ok(g2)
            if not ok2:
                affected.append((a, b))
        print(f"   orbit reps {len(reps)}, affected {len(affected)}", flush=True)
        if not affected:
            U = [(x, y) for x in range(n) for y in range(n) if x != y and not R.win[x][y]]
            if not U:
                print(" STATUS: window exhausted (FULL)"); return "FULL", it
            # Step 3: K = pointwise stabilizer of U.  Fixing a pair (x,y) under the diagonal action fixes x and y.
            verts = sorted({x for x, y in U} | {y for x, y in U})
            g3, _, _, _, _ = R.auto(indiv=verts)
            ok3, ev3 = R.phi_ok(g3)
            status = "FULL at Step 3" if ok3 else "PENDING (Step 3 fails, Step 4 would run)"
            print(f" no affected positions, |U|={len(U)}, |verts(U)|={len(verts)}: phi(K) even={ev3}/{rt.alt_size(k)}")
            print(f" STATUS: {status} at iteration {it}")
            return ("FULL" if ok3 else "PENDING"), it
        S = set()
        for (a, b) in affected:
            st = [(a, b)]
            S.add((a, b))
            while st:
                nx = []
                for (x, y) in st:
                    for g in gens:
                        q = (g[x], g[y])
                        if q not in S:
                            S.add(q); nx.append(q)
                st = nx
        for (x, y) in S:
            R.win[x][y] = 1
    return "ITER", 40


# ---------------------------------------------------------------------------
def pg_lines(m):
    return [(a, b, a ^ b) for a in range(1, 2**m) for b in range(a+1, 2**m) if (a ^ b) > b]


def refine(pts, blocks, initial=None):
    """1-WL (colour refinement) on the incidence graph; pts: ids, blocks: list of tuples.
    Returns (point colour dict, block colour list, rounds)."""
    pc = {p: 0 for p in pts} if initial is None else dict(initial)
    inc = collections.defaultdict(list)
    for i, b in enumerate(blocks):
        for p in b:
            inc[p].append(i)
    bc = [0]*len(blocks)
    rounds = 0
    ncol = (len(set(pc.values())), len(set(bc)))
    while True:
        rounds += 1
        keyb = [tuple(sorted(pc[p] for p in b)) for b in blocks]
        rb = {k: i for i, k in enumerate(sorted(set(keyb)))}
        nb = [rb[k] for k in keyb]
        keyp = {p: (pc[p], tuple(sorted(nb[i] for i in inc[p]))) for p in pts}
        rp = {k: i for i, k in enumerate(sorted(set(keyp.values())))}
        np_ = {p: rp[keyp[p]] for p in pts}
        nc = (len(rp), len(rb))
        if nc == ncol:
            return np_, nb, rounds
        pc, bc, ncol = np_, nb, nc


def aut_order(pts, blocks):
    from pynauty import Graph, autgrp
    idx = {p: i for i, p in enumerate(pts)}
    n = len(pts) + len(blocks)
    adj = {i: [] for i in range(n)}
    for j, b in enumerate(blocks):
        for p in b:
            adj[idx[p]].append(len(pts) + j)
    cols = [set(range(len(pts))), set(range(len(pts), n))]
    g = Graph(n, directed=False, adjacency_dict=adj, vertex_coloring=cols)
    _, m1, e1, orbs, norb = autgrp(g)
    return m1, e1, norb


def rigid(m, r, seed=1):
    random.seed(seed)
    lines = pg_lines(m)
    pts = list(range(1, 2**m))
    R = set(random.sample(range(len(lines)), r))
    blocks = [l for i, l in enumerate(lines) if i not in R]
    print(f"PG({m-1},2) minus {r} random lines: {len(pts)} points, {len(blocks)} blocks, n={len(pts)+len(blocks)}")
    if m <= 8:
        t = time.time()
        m1, e1, norb = aut_order(pts, blocks)
        print(f"  |Aut| = {m1}e{e1}, orbits {norb}, ({time.time()-t:.1f}s)")
    pc, bc, rounds = refine(pts, blocks)
    print(f"  1-WL: {len(set(pc.values()))} point colours of {len(pts)}, {len(set(bc))} block colours of {len(blocks)}, rounds {rounds}")
    # wrong-anchor test: relabel by a random linear map tau (so y = tau(x)); anchor p in x, p' != tau(p) in y
    A = random_invertible(m)
    ap = lambda v: apply(A, v, m)
    blocksY = [tuple(sorted(ap(p) for p in b)) for b in blocks]
    # joint refinement on the disjoint union of x and y = tau(x): is every colour class one point of x and one of y?
    upts = [(0, p) for p in pts] + [(1, p) for p in pts]
    ublocks = [tuple((0, p) for p in b) for b in blocks] + [tuple((1, p) for p in b) for b in blocksY]
    pcu, bcu, rnds = refine(upts, ublocks)
    byc = collections.defaultdict(list)
    for v, c in pcu.items():
        byc[c].append(v)
    good = all(len(l) == 2 and {l[0][0], l[1][0]} == {0, 1} for l in byc.values())
    correct = all(pcu[(0, p)] == pcu[(1, ap(p))] for p in pts)
    print(f"  joint 1-WL on x + tau(x): {len(byc)} point classes, each one-from-each-side: {good}; matches tau: {correct}, rounds {rnds}")


def refine_with_anchor(pts, blocks, p):
    init = {q: 0 for q in pts}
    init[p] = 1
    pc, bc, _ = refine(pts, blocks, init)
    return (tuple(sorted(collections.Counter(pc.values()).items())), tuple(sorted(collections.Counter(bc).items())))


def random_invertible(m):
    while True:
        A = [random.getrandbits(m) for _ in range(m)]
        # rank check
        r = 0; rows = A[:]
        for c in range(m):
            piv = None
            for i in range(r, m):
                if rows[i] >> c & 1:
                    piv = i; break
            if piv is None:
                continue
            rows[r], rows[piv] = rows[piv], rows[r]
            for i in range(m):
                if i != r and rows[i] >> c & 1:
                    rows[i] ^= rows[r]
            r += 1
        if r == m:
            return A


def apply(A, v, m):
    x = 0
    for c in range(m):
        if v >> c & 1:
            x ^= A[c]
    return x


# ---------------------------------------------------------------------------
def pasch(m, k, seed=1):
    random.seed(seed)
    pts = list(range(1, 2**m))
    lines = set(tuple(sorted(l)) for l in pg_lines(m))
    used = set()
    switches = []
    tries = 0
    while len(switches) < k and tries < 100000:
        tries += 1
        a, b, d = random.sample(pts, 3)
        c = a ^ b; e = a ^ d; f = b ^ d
        six = {a, b, c, d, e, f}
        if len(six) != 6 or (a ^ b ^ d) == 0 or (six & used):
            continue
        if (a ^ b ^ d) in six:
            continue
        used |= six
        switches.append((a, b, c, d, e, f))
    blocks = set(lines)
    for (a, b, c, d, e, f) in switches:
        for l in [(a, b, c), (a, d, e), (b, d, f), (c, e, f)]:
            blocks.remove(tuple(sorted(l)))
        for l in [(a, b, d), (a, c, e), (b, c, f), (d, e, f)]:
            blocks.add(tuple(sorted(l)))
    blocks = sorted(blocks)
    # STS check
    pairs = collections.Counter()
    for b in blocks:
        for x, y in itertools.combinations(b, 2):
            pairs[(x, y)] += 1
    is_sts = len(pairs) == len(pts)*(len(pts)-1)//2 and set(pairs.values()) == {1}
    print(f"PG({m-1},2) with {len(switches)} disjoint Pasch switches: STS(v={len(pts)}): {is_sts}, blocks={len(blocks)}")
    third = {}
    for b in blocks:
        for x, y, z in itertools.permutations(b):
            third[(x, y)] = z
    if os.environ.get("W28_PASCH_AUT"):
        m1, e1, norb = aut_order(pts, blocks)
        print(f"  |Aut| = {m1}e{e1}, orbits {norb}", flush=True)
    pc0, _, rounds0 = refine(pts, blocks)
    print(f"  plain 1-WL: {len(set(pc0.values()))} point colours (STS is point-regular)")
    # defect invariant: for each point p, number of pairs (a,b) with {p,a,b} a triangle whose closure is not 7 points
    t0 = time.time()
    defect = {}
    for p in pts:
        cnt = 0
        for a in pts:
            if a == p:
                continue
            ca = third[(p, a)]
            for b in pts:
                if b <= a or b == p or b == ca:
                    continue
                cb = third[(p, b)]
                ab = third[(a, b)]
                # the triangle {p,a,b} closes to a Fano plane iff the three "opposite" points coincide
                z1 = third[(ca, b)] if ca != b else None
                z2 = third[(cb, a)] if cb != a else None
                z3 = third[(ab, p)] if ab != p else None
                if not (z1 == z2 == z3 and z1 is not None):
                    cnt += 1
        defect[p] = cnt
    vals = collections.Counter(defect.values())
    print(f"  defect invariant (non-Fano triangles through p): {len(vals)} values; profile {sorted(vals.items())[:8]}... t={time.time()-t0:.1f}s")
    pc, bc, rounds = refine(pts, blocks, defect)
    print(f"  1-WL from defect colours: {len(set(pc.values()))} point colours of {len(pts)}, {len(set(bc))} block colours of {len(blocks)}, rounds {rounds}")


# ---------------------------------------------------------------------------
def gauss(n, k):
    """Gaussian binomial [n choose k]_2."""
    if k < 0 or k > n:
        return 0
    num = den = 1
    for i in range(k):
        num *= 2**(n-i) - 1
        den *= 2**(i+1) - 1
    return num//den


def count():
    print("memoization: kappa, m, J, log2(tree product of (1/2)binom(q_j,kappa)), log2(#flags), log2(#subspaces at best level), m^2/4")
    for kappa, m in [(5, 60), (5, 100), (8, 100), (8, 200)]:
        c = 0  # ignore the cutoff here: this table compares counts only
        J = m//kappa - 2
        lt = lf = 0.0
        for j in range(J):
            r = m - j*kappa
            q = 2**r - 1
            lt += math.log2(math.comb(q, kappa)) - 1
            lf += math.log2(gauss(r, kappa))
        ls = max(math.log2(gauss(m, j*kappa)) for j in range(J+1))
        print(f"  kappa={kappa} m={m} J={J}: tree {lt:.0f}, flags {lf:.0f}, ratio {lt-lf:.0f} ({(lt-lf)/m:.1f} per m), subspaces(best level) {ls:.0f}, m^2/4={m*m/4:.0f}, m^2/2={m*m/2:.0f}")


def twins(m):
    pts = list(range(1, 2**m))
    # twin check on pair {x,y}: exists a line through x not containing y, whose swap image is not a line, or a linear dependency witness
    lines = set(tuple(sorted(l)) for l in pg_lines(m))
    ntw = 0
    for x, y in itertools.combinations(pts, 2):
        # find a line through x avoiding y
        found = False
        for a in pts:
            b = a ^ x
            if a == x or a == y or b == x or b == y or a >= b or b == 0:
                continue
            if tuple(sorted((y, a, b))) not in lines:
                found = True
                break
        if not found:
            ntw += 1
    print(f"m={m}: pairs of points with no line-witness separating them under transposition: {ntw}")


if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'phase0':
        phase0(int(sys.argv[2]), eval(sys.argv[3]))
    elif mode == 'rigid':
        rigid(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]) if len(sys.argv) > 4 else 1)
    elif mode == 'pasch':
        pasch(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]) if len(sys.argv) > 4 else 1)
    elif mode == 'count':
        count()
    elif mode == 'twins':
        twins(int(sys.argv[2]))
