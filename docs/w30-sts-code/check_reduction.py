"""Exact check of Theorem 2 (reduction from linear equivalence of colourings to STS isomorphism) for d=3,
and a sample for d=4. Run with an interpreter having pynauty."""
import itertools, random, sys
import sts
import pynauty

def nauty_cert(Q):
    n = len(Q)
    bl = sts.blocks_of(Q)
    v = n + len(bl)
    adj = {i: [] for i in range(v)}
    for j, b in enumerate(bl):
        for x in b:
            adj[x].append(n + j)
            adj[n + j].append(x)
    g = pynauty.Graph(number_of_vertices=v, directed=False, adjacency_dict=adj,
                      vertex_coloring=[set(range(n)), set(range(n, v))])
    return pynauty.certificate(g)

def gl_matrices(d):
    """All invertible d x d matrices over F_2 as tuples of column images (ints)."""
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

def apply(A, x):
    r = 0
    i = 0
    while x:
        if x & 1:
            r ^= A[i]
        x >>= 1
        i += 1
    return r

def main():
    rng = random.Random(7)
    # find a suitable F1
    while True:
        F1 = sts.patterned_factorization_k8(rng)
        nf, sp, T = sts.f1_acceptable(F1, 3)
        if nf and sp:
            break
    print("F1 found; T^1 chi2 dim", sts.char_space_dim(T), "PG(3,2) chi2 dim", sts.char_space_dim(sts.pg(4)))
    d = 3
    GL = gl_matrices(d)
    print("|GL(3,2)| =", len(GL))
    N = 1 << d
    # enumerate all colourings of F_2^3 \ 0 as bitmasks over c=1..7
    allchi = list(range(1, 1 << (N - 1)))  # exclude chi=0: handled separately (gives PG)
    # GL-orbit canonical
    def transform(chi, A):
        r = 0
        for c in range(1, N):
            if chi >> (c - 1) & 1:
                r |= 1 << (apply(A, c) - 1)
        return r
    orbit_id = {}
    orbits = []
    for chi in allchi:
        if chi in orbit_id:
            continue
        oid = len(orbits)
        orb = {transform(chi, A) for A in GL}
        for o in orb:
            orbit_id[o] = oid
        orbits.append(sorted(orb))
    print("colourings:", len(allchi), "GL-orbits:", len(orbits))
    def build(chi):
        return sts.x_fib(d, 3, lambda c: (chi >> (c - 1)) & 1, F1)
    certs = {}
    rep_cert = []
    for oid, orb in enumerate(orbits):
        Q = build(orb[0])
        assert sts.is_sts(Q)
        cert = nauty_cert(Q)
        rep_cert.append(cert)
        print("orbit", oid, "size", len(orb), flush=True)
    distinct = len(set(rep_cert))
    print("distinct certs over orbit representatives:", distinct, "(must equal #orbits)", len(orbits))
    # sample: random colourings' certificate must match its orbit representative
    for t in range(60):
        chi = rng.choice(allchi)
        Q = build(chi)
        c = nauty_cert(Q)
        assert c == rep_cert[orbit_id[chi]], "certificate mismatch"
    print("orbit-invariance sample OK (60 random colourings).")
    # chi=0 vs chi != 0: PG vs not
    Q0 = sts.x_fib(d, 3, lambda c: 0, F1)
    print("chi=0 gives PG(5,2)?", nauty_cert(Q0) == nauty_cert(sts.pg(6)))
    # also confirm a colouring with chi and chi' in the same orbit differ by the explicit forward isomorphism
    if len(sys.argv) < 2 or sys.argv[1] != "d4":
        return
    # d=4 sample
    d4 = 4
    # random: compare two random colourings at d=4 with same weight, using a brute-force orbit test on GL(4,2)
    GL4 = gl_matrices(4)
    print("|GL(4,2)| =", len(GL4))
    N4 = 1 << d4
    def transform4(chi, A):
        r = 0
        for c in range(1, N4):
            if chi >> (c - 1) & 1:
                r |= 1 << (apply(A, c) - 1)
        return r
    def build4(chi):
        return sts.x_fib(d4, 3, lambda c: (chi >> (c - 1)) & 1, F1)
    import time
    mism = 0
    for t in range(12):
        chi = rng.randrange(1, 1 << (N4 - 1))
        A = rng.choice(GL4)
        chi2 = transform4(chi, A)
        # equivalent: cert equal
        c1, c2 = nauty_cert(build4(chi)), nauty_cert(build4(chi2))
        assert c1 == c2, "equivalent colourings gave non-isomorphic STS"
        # a generically inequivalent colouring: flip one bit and verify non-equivalence by brute force GL
        chi3 = chi ^ (1 << rng.randrange(N4 - 1))
        same = any(transform4(chi3, B) == chi for B in GL4)
        c3 = nauty_cert(build4(chi3))
        assert (c3 == c1) == same, ("mismatch", same)
        mism += 1
    print("d=4: 12 equivalent pairs and 12 flipped pairs agree with brute force GL(4,2)")

if __name__ == "__main__":
    main()
