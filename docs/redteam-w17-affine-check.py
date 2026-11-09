#!/usr/bin/env python3
"""Referee checks for docs/w17-affine.md.  Run: nice python3 -I docs/redteam-w17-affine-check.py [fast|balance]

Sections:
  1  exact arithmetic for Theorems A, B and B' (Gaussian binomials, up to k=64)
  2  group structure: B is the full stabiliser of the direction flag; 2-group; contains translations
  3  an actual polynomial-time Luks recursion for Can_B, compared with brute-force lexmin over B
  4  Theorem A: canonical form and canonizer, exhaustive at k=3, sampled at k=4
  5  Theorem B: decision and the whole-coset generator claim, with the *polynomial* Can_B
     (exhaustive at k=3; k=4 against brute force; k=5,6 on planted and certified-negative pairs)
  6  three-block parabolic: the same proof with a better balance
  7  the oracle model of Prop. B': v_g(F) = v_f(h.F) for real Can_B labels
  8  Theorem C: exhaustive over AGL(4,2); pruned-exhaustive at K=6; direction of the stated Iso set
  9  Prop. D (pattern separation) on random functions
 10  Proposition G arithmetic: mu versus Sylow-row cost
"""
import itertools, math, random, sys, time
from fractions import Fraction
from sympy.combinatorics import Permutation, PermutationGroup

FAST = len(sys.argv) > 1 and sys.argv[1] == "fast"

# ---------------------------------------------------------------- arithmetic


def fact2(n):
    r = 1
    for i in range(1, n + 1):
        r *= (1 << i) - 1
    return r


def gauss(n, m):
    return fact2(n) // (fact2(m) * fact2(n - m))


def log2(x):
    if isinstance(x, Fraction):
        return log2(x.numerator) - log2(x.denominator)
    if x < 1 << 1000:
        return math.log2(x)
    s = x.bit_length() - 900
    return math.log2(x >> s) + s


def agl_order(k):
    r = 1 << k
    for i in range(k):
        r *= (1 << k) - (1 << i)
    return r


def composition_sizes(parts):
    """|G/H| and |B\\H| for the parabolic H of block sizes `parts`."""
    k = sum(parts)
    s1 = fact2(k)
    s2 = 1
    for p in parts:
        s1 //= fact2(p)
        s2 *= fact2(p)
    return s1, s2


def compositions(k, r):
    if r == 1:
        yield (k,)
        return
    for a in range(1, k - r + 2):
        for rest in compositions(k - a, r - 1):
            yield (a,) + rest


def section1():
    print("== 1. arithmetic")
    for k in range(2, 65):
        m = k // 2
        G, flags = agl_order(k), fact2(k)
        B = 1 << (k * (k - 1) // 2 + k)
        assert G == B * flags
        S1, S2 = gauss(k, m), fact2(m) * fact2(k - m)
        assert S1 * S2 == flags
        assert S1 == composition_sizes((m, k - m))[0] and S2 == composition_sizes((m, k - m))[1]
        assert Fraction(S1, 1 << (m * (k - m))) <= Fraction(347, 100)
        assert S2 ** 4 <= 1 << (k * k + 2 * k), k  # time exponent k^2/4 + k/2, also for odd k
        assert S1 ** 4 <= 347 ** 4 * (1 << (k * k)) // 100 ** 4  # space exponent k^2/4
        assert flags <= 1 << (k * (k + 1) // 2)
    print("  OK k=2..64: |G|=|B||flags|; |S1||S2|=|flags|; |S1|<=3.47*2^{m(k-m)};"
          " |S2|<=2^{k^2/4+k/2}, |S1|<=3.47*2^{k^2/4}")
    k = 40
    m = 20
    print(f"  k=40 constants: |S2|/2^(m^2+m) = {fact2(m)*fact2(k-m)/2**(m*m+m):.5f}"
          f"  (doc 0.083);  flags/2^(k(k+1)/2) = {fact2(k)/2**(k*(k+1)//2):.5f} (doc 0.289)")
    print("  best parabolic: k, max(|S1|,|S2|) for two blocks, for best <=4 blocks, sqrt(#flags), in log2")
    worst = 0.0
    for k in (6, 8, 12, 16, 20, 24, 32, 40):
        m = k // 2
        two = max(composition_sizes((m, k - m)))
        best, arg = None, None
        for r in (2, 3, 4):
            for c in compositions(k, r):
                v = max(composition_sizes(c))
                if best is None or v < best:
                    best, arg = v, c
        sq = log2(fact2(k)) / 2
        worst = max(worst, log2(best) - sq)
        print(f"   k={k:2d}: two-block {log2(two):8.2f}   best {log2(best):8.2f} {arg}"
              f"   sqrt(#flags) {sq:8.2f}   k^2/4+k/4 = {k*k/4+k/4:.1f}")
    print(f"  max excess of best-parabolic over sqrt(#flags) on these k: {worst:.2f} bits")


# ---------------------------------------------------------------- affine maps as permutations


def apply_cols(cols, x):
    r, i = 0, 0
    while x:
        if x & 1:
            r ^= cols[i]
        x >>= 1
        i += 1
    return r


def perm_of(cols, t, k):
    return tuple(apply_cols(cols, x) ^ t for x in range(1 << k))


def mul(a, b):  # a o b
    return tuple(a[y] for y in b)


def inv(a):
    r = [0] * len(a)
    for i, v in enumerate(a):
        r[v] = i
    return tuple(r)


def pull(f, a):  # f o a
    return tuple(f[y] for y in a)


def rank(vs):
    basis = {}
    for v in vs:
        while v:
            h = v.bit_length()
            if h in basis:
                v ^= basis[h]
            else:
                basis[h] = v
                break
    return len(basis)


def gl(k):
    for cols in itertools.product(range(1, 1 << k), repeat=k):
        if rank(cols) == k:
            yield cols


def span(vs):
    s = {0}
    for v in vs:
        s |= {x ^ v for x in s}
    return frozenset(s)


def random_gl(k, rng):
    while True:
        c = tuple(rng.randrange(1, 1 << k) for _ in range(k))
        if rank(c) == k:
            return c


def borel_gens(k):
    gens = [perm_of(tuple(1 << i for i in range(k)), 1 << j, k) for j in range(k)]
    for i in range(k):
        for j in range(i + 1, k):
            cols = [1 << a for a in range(k)]
            cols[j] ^= 1 << i
            gens.append(perm_of(tuple(cols), 0, k))
    return gens


# ---------------------------------------------------------------- polynomial-time Can_B


def reduce_gens(gens, n):
    """Filter a generating list (preserves the generated group)."""
    table = {}
    idn = tuple(range(n))
    out = []
    for g in gens:
        while g != idn:
            i = next(j for j in range(n) if g[j] != j)
            key = (i, g[i])
            if key in table:
                g = mul(inv(table[key]), g)
            else:
                table[key] = g
                out.append(g)
                break
    return out


COUNTER = {"calls": 0}


def canon_rec(x, rho, gens, lo, size, n):
    """min over k in <gens> of (x o rho o k) on [lo,lo+size); <gens> preserves the window.
    Returns the word, a new rho and generators of the minimiser subgroup (a coset rho<gens>)."""
    COUNTER["calls"] += 1
    if size == 1:
        return (x[rho[lo]],), rho, gens
    half = size // 2
    mid = lo + half
    swaps = [g for g in gens if g[lo] >= mid]
    if swaps:
        tau = swaps[0]
        tinv = inv(tau)
        k0 = []
        for g in gens:
            if g[lo] >= mid:
                k0 += [mul(g, tinv), mul(tau, g)]
            else:
                k0 += [g, mul(mul(tau, g), tinv)]
        cands = [rho, mul(rho, tau)]
    else:
        k0, cands = list(gens), [rho]
    k0 = reduce_gens(k0, n)
    best = None
    for r in cands:
        w0, r0, g0 = canon_rec(x, r, k0, lo, half, n)
        if best is not None and w0 > best[0][:half]:
            continue  # strictly worse on the left half
        w1, r1, g1 = canon_rec(x, r0, g0, mid, half, n)
        w = w0 + w1
        if best is None or w < best[0]:
            best = (w, r1, list(g1))
        elif w == best[0]:
            best[2].append(mul(inv(best[1]), r1))
    return best[0], best[1], reduce_gens(best[2], n)


def can_b(x, bgens):
    n = len(x)
    return canon_rec(tuple(x), tuple(range(n)), bgens, 0, n, n)


def group_order(gens, n):
    gens = [g for g in gens if g != tuple(range(n))]
    if not gens:
        return 1
    return int(PermutationGroup([Permutation(list(g)) for g in gens]).order())


def closure(gens, n):
    idn = tuple(range(n))
    seen = {idn}
    frontier = [idn]
    while frontier:
        nxt = []
        for a in frontier:
            for g in gens:
                c = mul(a, g)
                if c not in seen:
                    seen.add(c)
                    nxt.append(c)
        frontier = nxt
    return seen


def setup_enum(k):
    GL = list(gl(k))
    U = [c for c in GL if all((c[j] >> j) & 1 == 1 and (c[j] >> (j + 1)) == 0 for j in range(k))]
    B = [perm_of(c, t, k) for c in U for t in range(1 << k)]
    return GL, U, B


def section2():
    print("== 2. group structure of B")
    for k in (2, 3, 4):
        GL, U, B = setup_enum(k)
        ids = tuple(1 << i for i in range(k))
        flag = [span(ids[:i]) for i in range(1, k + 1)]
        stab = [c for c in GL if all(frozenset(apply_cols(c, x) for x in W) == W for W in flag)]
        assert sorted(stab) == sorted(U), k
        assert len(U) == 2 ** (k * (k - 1) // 2)
        assert len(set(B)) == 2 ** (k * (k + 1) // 2)
        # B = {x -> Ux+t}: closed, contains all translations
        bs = set(B)
        for a, b in itertools.islice(zip(B, reversed(B)), 2000):
            assert mul(a, b) in bs
        for t in range(1 << k):
            assert perm_of(ids, t, k) in bs
        gens = borel_gens(k)
        assert closure(gens, 1 << k) == bs
        # every element has 2-power order
        assert all(_order(p) in (1, 2, 4, 8, 16) for p in B)
        # the affine stabiliser of the *linear* flag (subspaces through 0) would be U only:
        pinned = [p for p in B if p[0] == 0]
        assert len(pinned) == len(U)
        print(f"  k={k}: linear stabiliser of the flag is exactly U; B=U.T has order 2^{k*(k+1)//2}, is a 2-group,"
              f" contains T, generated by {len(gens)} elements")


def _order(p):
    idn = tuple(range(len(p)))
    q, o = p, 1
    while q != idn:
        q = mul(q, p)
        o += 1
    return o


def section3(rng):
    print("== 3. polynomial Luks recursion for Can_B vs brute-force lexmin over B")
    for k in (2, 3, 4):
        GL, U, B = setup_enum(k)
        gens = borel_gens(k)
        n = 1 << k
        tests = [tuple(rng.randrange(3) for _ in range(n)) for _ in range(300 if k < 4 else 40)]
        tests += [(0,) * n, tuple(int(bin(x).count("1") == 1) for x in range(n))]
        if k == 4:
            tests.append(tuple(((x & 1) & (x >> 1)) ^ ((x >> 2) & (x >> 3) & 1) for x in range(n)))
        for x in tests:
            w, rho, ag = can_b(x, gens)
            brute = sorted(B, key=lambda b: pull(x, b))
            best = pull(x, brute[0])
            assert w == best, (k, x)
            minset = {b for b in B if pull(x, b) == best}
            assert rho in minset and pull(x, rho) == w
            assert all(pull(w, a) == w for a in ag)
            assert group_order(ag, n) == len(minset), (k, x)
        print(f"  k={k}: recursion returns the true lexmin over B and the exact coset of minimisers ({len(tests)} strings)")
    for k in (5, 6) if FAST else (5, 6, 7):
        n = 1 << k
        gens = borel_gens(k)
        x = tuple(rng.randrange(2) for _ in range(n))
        COUNTER["calls"] = 0
        t = time.time()
        can_b(x, gens)
        c1 = COUNTER["calls"]
        COUNTER["calls"] = 0
        t2 = time.time()
        can_b((0,) * n, gens)
        print(f"  k={k} (N={n}): recursion calls random {c1} ({t2-t:.3f}s), constant {COUNTER['calls']}"
              f" ({time.time()-t2:.3f}s); N^2={n*n}")


# ---------------------------------------------------------------- coset representatives


def flag_reps_enum(k):
    """One matrix per complete flag of F_2^k: s, with s(F_0) = that flag."""
    d = {}
    for c in gl(k):
        key = tuple(span(c[:i]) for i in range(1, k + 1))
        d.setdefault(key, c)
    return list(d.values())


def reps_two_block(k, m):
    """S1: reps of G/H (m-subspaces); S2: reps of B\\H (pairs of flags); all linear."""
    if m == 0:
        s1 = [tuple(1 << i for i in range(k))]
    else:
        d = {}
        for vs in itertools.combinations(range(1, 1 << k), m):
            if rank(vs) == m:
                d.setdefault(span(vs), vs)
        s1 = []
        for vs in d.values():
            cols = list(vs)
            for i in range(k):
                if rank(cols + [1 << i]) == len(cols) + 1:
                    cols.append(1 << i)
            s1.append(tuple(cols))
    fa = flag_reps_enum(m) if m else [()]
    fb = flag_reps_enum(k - m)
    s2 = []
    for a in fa:
        for b in fb:
            cols = list(a) + [v << m for v in b]  # this is t^{-1}: maps F_0 to the chosen flag
            s2.append(inv(perm_of(tuple(cols), 0, k)))
    return [perm_of(s, 0, k) for s in s1], s2


def decide(f, g, S1, S2, bgens):
    """Theorem B decision: returns one witness h (permutation) or None."""
    table = {}
    for s in S1:
        w, rho, _ = can_b(pull(f, s), bgens)
        table.setdefault(w, (s, rho))
    for t in S2:
        w, rho2, _ = can_b(pull(g, inv(t)), bgens)
        if w in table:
            s, rho = table[w]
            b = mul(rho, inv(rho2))
            return mul(mul(s, b), t)
    return None


def aut_gens(f, S1, S2, bgens):
    """The generating set of the proof of Theorem B, run on (f,f)."""
    gens, buckets = [], {}
    for s in S1:
        w, rho, ag = can_b(pull(f, s), bgens)
        buckets.setdefault(w, {"S": [], "T": []})["S"].append((s, rho))
        # ag generates Aut_B(w), w = (f o s) o rho; so rho ag rho^-1 generates Aut_B(f o s)
        c = mul(s, rho)
        cinv = inv(c)
        gens += [mul(mul(c, b), cinv) for b in ag]
    for t in S2:
        w, rho, _ = can_b(pull(f, inv(t)), bgens)
        if w in buckets:
            buckets[w]["T"].append((t, rho))
    for v in buckets.values():
        if not v["T"]:
            continue
        s0, r0 = v["S"][0]
        t0, rt0 = v["T"][0]
        for s, r in v["S"]:
            gens.append(mul(mul(s, mul(r, inv(rt0))), t0))
        for t, rt in v["T"]:
            gens.append(mul(mul(s0, mul(r0, inv(rt))), t))
    return gens


def section4(rng):
    print("== 4. Theorem A: Can(f) = min over flags of Can_B(f o s)")
    for k in (3, 4):
        n = 1 << k
        bgens = borel_gens(k)
        reps = [perm_of(c, 0, k) for c in flag_reps_enum(k)]
        assert len(reps) == fact2(k)

        def can_g(f):
            bestw, bests = None, None
            for s in reps:
                w, rho, _ = can_b(pull(f, s), bgens)
                if bestw is None or w < bestw:
                    bestw, bests = w, mul(s, rho)
            return bestw, bests

        if k == 3:
            fs = list(itertools.product((0, 1), repeat=n))
            canon = {}
            for f in fs:
                w, c = can_g(f)
                assert pull(f, c) == w
                canon[f] = w
            G = [perm_of(c, t, k) for c in gl(k) for t in range(n)]
            for f in fs:
                for a in G:
                    assert canon[pull(f, a)] == canon[f]
            nclasses = len(set(canon.values()))
            # classes = orbits on the 256 functions
            orbits = set(frozenset(pull(f, a) for a in G) for f in fs)
            assert nclasses == len(orbits)
            print(f"  k=3: exhaustive on all 256 functions: invariant under all 1344 maps, Can(f) in orbit of f,"
                  f" {nclasses} classes = {len(orbits)} orbits")
        else:
            for _ in range(10 if FAST else 40):
                f = tuple(rng.randrange(2) for _ in range(n))
                w, c = can_g(f)
                assert pull(f, c) == w
                h = perm_of(random_gl(k, rng), rng.randrange(n), k)
                assert can_g(pull(f, h))[0] == w
            print("  k=4: invariance and in-orbit on sampled random functions with random maps")


def section5(rng):
    print("== 5. Theorem B with polynomial Can_B")
    # k=3: all pairs of functions
    k, n = 3, 8
    bgens = borel_gens(k)
    S1, S2 = reps_two_block(k, k // 2)
    assert len(S1) == gauss(3, 1) and len(S2) == fact2(1) * fact2(2)
    G = [perm_of(c, t, k) for c in gl(k) for t in range(n)]
    # factorisation
    seen = set()
    B = closure(bgens, n)
    for s in S1:
        for b in B:
            for t in S2:
                seen.add(mul(mul(s, b), t))
    assert len(seen) == len(G) == len(S1) * len(B) * len(S2)
    fs = list(itertools.product((0, 1), repeat=n))
    left = {f: {can_b(pull(f, s), bgens)[0] for s in S1} for f in fs}
    right = {f: {can_b(pull(f, inv(t)), bgens)[0] for t in S2} for f in fs}
    orbit = {f: frozenset(pull(f, a) for a in G) for f in fs}
    bad = 0
    for f in fs:
        for g in fs:
            if bool(left[f] & right[g]) != (g in orbit[f]):
                bad += 1
    assert bad == 0
    print("  k=3: unique factorisation s.b.t by exhaustion; collision = isomorphism on all 65536 pairs")
    for f in fs:
        gens = aut_gens(f, S1, S2, bgens)
        assert all(pull(f, a) == f for a in gens)
        brute = sum(1 for a in G if pull(f, a) == f)
        assert group_order(gens, n) == brute, f
    print("  k=3: whole-coset generators give exactly Aut(f) for all 256 functions")
    # Iso(f,g) = Aut(f) h
    for _ in range(200):
        f = rng.choice(fs)
        h0 = rng.choice(G)
        g = pull(f, h0)
        h = decide(f, g, S1, S2, bgens)
        assert h is not None and pull(f, h) == g
        iso = {a for a in G if pull(f, a) == g}
        aut = {a for a in G if pull(f, a) == f}
        assert {mul(a, h) for a in aut} == iso
    print("  k=3: Iso(f,g) = Aut(f) h on 200 planted pairs (right coset, as the doc writes)")

    # k=4, brute-force truth
    k, n = 4, 16
    bgens = borel_gens(k)
    S1, S2 = reps_two_block(k, 2)
    assert (len(S1), len(S2)) == (35, 9)
    G = [perm_of(c, t, k) for c in gl(k) for t in range(n)]
    structured = {
        "constant": (0,) * n,
        "point": tuple(int(x == 0) for x in range(n)),
        "hyperplane": tuple(x & 1 for x in range(n)),
        "bent x1x2+x3x4": tuple((x & (x >> 1) & 1) ^ ((x >> 2) & (x >> 3) & 1) for x in range(n)),
        "x1x2x3": tuple(int((x & 7) == 7) for x in range(n)),
        "3 colours": tuple((x & 1) + ((x >> 1) & 1) for x in range(n)),
    }
    for name, f in structured.items():
        gens = aut_gens(f, S1, S2, bgens)
        assert all(pull(f, a) == f for a in gens)
        brute = sum(1 for a in G if pull(f, a) == f)
        got = group_order(gens, n)
        assert got == brute, (name, got, brute)
        print(f"  k=4 {name}: |Aut| = {got} (brute force agrees)")
    rounds = 8 if FAST else 30
    for _ in range(rounds):
        f = tuple(rng.randrange(2) for _ in range(n))
        if rng.random() < 0.5:
            g = pull(f, rng.choice(G))
        else:
            g = list(f)
            i, j = rng.randrange(n), rng.randrange(n)
            g[i], g[j] = g[j], g[i]  # same weight, usually a different class
            g = tuple(g)
        truth = any(pull(f, a) == g for a in G)
        h = decide(f, g, S1, S2, bgens)
        assert (h is not None) == truth
        if h is not None:
            assert pull(f, h) == g
    print(f"  k=4: decision agrees with brute force over AGL(4,2) on {rounds} pairs (near-miss negatives included)")

    # k=5,6: no brute force; planted positives and certified negatives
    for k in (5,) if FAST else (5, 6):
        n = 1 << k
        bgens = borel_gens(k)
        S1, S2 = reps_two_block(k, k // 2)
        assert len(S1) == gauss(k, k // 2) and len(S2) == fact2(k // 2) * fact2(k - k // 2)
        t0 = time.time()
        pos = neg = 0
        for _ in range(1 if k == 6 else 12):
            f = tuple(rng.randrange(2) for _ in range(n))
            h0 = perm_of(random_gl(k, rng), rng.randrange(n), k)
            g = pull(f, h0)
            h = decide(f, g, S1, S2, bgens)
            assert h is not None and pull(f, h) == g
            pos += 1
            # certified negative: same weight, different multiset of |Walsh coefficients|
            while True:
                g2 = list(f)
                i, j = rng.randrange(n), rng.randrange(n)
                g2[i], g2[j] = g2[j], g2[i]
                g2 = tuple(g2)
                if sorted(map(abs, walsh(g2, k))) != sorted(map(abs, walsh(f, k))):  # |W| is the affine invariant
                    break
            assert decide(f, g2, S1, S2, bgens) is None
            neg += 1
        print(f"  k={k}: |S1|={len(S1)} |S2|={len(S2)}: {pos} planted isomorphic and {neg} Walsh-certified"
              f" non-isomorphic pairs decided correctly ({time.time()-t0:.1f}s)")
    # k=5 structured, orders known in closed form
    k, n = 5, 32
    bgens = borel_gens(k)
    S1, S2 = reps_two_block(k, 2)
    for name, f, expected in [
        ("constant", (0,) * n, agl_order(5)),
        ("point", tuple(int(x == 0) for x in range(n)), agl_order(5) // 32),
        ("hyperplane", tuple(x & 1 for x in range(n)), agl_order(5) // 62),
    ]:
        gens = aut_gens(f, S1, S2, bgens)
        assert all(pull(f, a) == f for a in gens)
        got = group_order(gens, n)
        assert got == expected, (name, got, expected)
        print(f"  k=5 {name}: |Aut| = {got} (closed form agrees)")


def walsh(f, k):
    n = 1 << k
    return tuple(sum((-1) ** (f[x] ^ (bin(x & a).count("1") & 1)) for x in range(n)) for a in range(n))


def section6(rng):
    print("== 6. three-block parabolic (2,1,1) at k=4: same proof, different H")
    k, n = 4, 16
    bgens = borel_gens(k)
    GL = list(gl(k))
    ids = tuple(1 << i for i in range(k))
    H0 = [c for c in GL if span(c[:2]) == span(ids[:2]) and span(c[:3]) == span(ids[:3])]
    d1 = {}
    for c in GL:
        d1.setdefault((span(c[:2]), span(c[:3])), c)
    d2 = {}
    for c in H0:
        ci = inv(perm_of(c, 0, k))
        cols = tuple(ci[1 << i] for i in range(k))
        d2.setdefault(tuple(span(cols[:i]) for i in range(1, k + 1)), c)
    S1 = [perm_of(c, 0, k) for c in d1.values()]
    S2 = [perm_of(c, 0, k) for c in d2.values()]
    assert (len(S1), len(S2)) == composition_sizes((2, 1, 1))
    G = [perm_of(c, t, k) for c in GL for t in range(n)]
    for _ in range(6 if FAST else 20):
        f = tuple(rng.randrange(2) for _ in range(n))
        g = pull(f, rng.choice(G)) if rng.random() < 0.5 else tuple(rng.randrange(2) for _ in range(n))
        truth = any(pull(f, a) == g for a in G)
        h = decide(f, g, S1, S2, bgens)
        assert (h is not None) == truth
    print(f"  |S1|={len(S1)} |S2|={len(S2)}; decision agrees with brute force")


def section7(rng):
    print("== 7. Prop. B' model fidelity: real labels satisfy v_g(F) = v_f(h.F)")
    for k in (3, 4):
        n = 1 << k
        bgens = borel_gens(k)
        reps = {}
        for c in flag_reps_enum(k):
            reps[tuple(span(c[:i]) for i in range(1, k + 1))] = perm_of(c, 0, k)

        def label(f, F):
            return can_b(pull(f, reps[F]), bgens)[0]

        for _ in range(30):
            f = tuple(rng.randrange(2) for _ in range(n))
            L, t = random_gl(k, rng), rng.randrange(n)
            h = perm_of(L, t, k)
            g = pull(f, h)
            F = rng.choice(list(reps))
            hF = tuple(frozenset(apply_cols(L, x) for x in W) for W in F)
            assert label(g, F) == label(f, hF)
        print(f"  k={k}: identity holds; only the linear part of h moves flags (translations are in B)")


# ---------------------------------------------------------------- Theorem C


def t_eval(T, xs, d, k):
    r = 0
    for idx in itertools.product(range(k), repeat=d):
        if T[idx] and all((xs[j] >> idx[j]) & 1 for j in range(d)):
            r ^= 1
    return r


def split(x, d, k):
    return [(x >> (k * i)) & ((1 << k) - 1) for i in range(d)]


def classes(d, k):
    """T-independent part of c_T: 0 star, 1+mask partial, 1+2^d full."""
    out = []
    for x in range(1 << (d * k)):
        mask = sum(1 << i for i, v in enumerate(split(x, d, k)) if v)
        out.append(0 if mask == 0 else (1 + mask if mask != (1 << d) - 1 else 1 + (1 << d)))
    return tuple(out)


def c_table(T, d, k):
    cl = classes(d, k)
    return tuple(c if c != 1 + (1 << d) else c + t_eval(T, split(x, d, k), d, k) for x, c in enumerate(cl))


def direct_sum(As, d, k):
    cols = []
    for i, A in enumerate(As):
        cols += [v << (k * i) for v in A]
    return tuple(cols)


def t_act(T, As, d, k):
    """T o (A_1,...,A_d) as a coefficient table."""
    out = {}
    for idx in itertools.product(range(k), repeat=d):
        out[idx] = t_eval(T, [As[j][idx[j]] for j in range(d)], d, k)
    return out


def all_T(d, k):
    idxs = list(itertools.product(range(k), repeat=d))
    for bits in itertools.product((0, 1), repeat=len(idxs)):
        yield dict(zip(idxs, bits))


def section8(rng):
    print("== 8. Theorem C")
    d, k, K = 2, 2, 4
    n = 1 << K
    cl = classes(d, k)
    AGL = [(c, t) for c in gl(K) for t in range(n)]
    perms = [perm_of(c, t, K) for c, t in AGL]
    pinned = [p for p in perms if pull(cl, p) == cl]
    GLk = list(gl(k))
    tuples = list(itertools.product(GLk, repeat=d))
    sums = {perm_of(direct_sum(As, d, k), 0, K): As for As in tuples}
    assert set(pinned) == set(sums) and len(pinned) == len(tuples)
    print(f"  (d,k)=(2,2): of all {len(perms)} maps of AGL(4,2), exactly the {len(pinned)} direct sums preserve the pinned classes")
    Ts = list(all_T(d, k))
    tables = [c_table(T, d, k) for T in Ts]
    action = {}
    for i, T in enumerate(Ts):
        for As in tuples:
            action[(i, As)] = t_act(T, As, d, k)
    mismatches = doc_diff = 0
    example = None
    for i, T in enumerate(Ts):
        for j, Tp in enumerate(Ts):
            iso = {p for p in pinned if pull(tables[i], p) == tables[j]}
            expect = {perm_of(direct_sum(As, d, k), 0, K) for As in tuples if action[(i, As)] == Tp}
            if iso != expect:
                mismatches += 1
            doc = {perm_of(direct_sum(As, d, k), 0, K) for As in tuples if action[(j, As)] == T}
            if iso != doc:
                doc_diff += 1
                if example is None:
                    example = (i, j)
    assert mismatches == 0
    print(f"  (d,k)=(2,2): for all 256 pairs (T,T'): {{A: c_T o A = c_T'}} = {{(A_1,A_2): T o (A_1,A_2) = T'}}")
    print(f"  direction: the set as printed in the doc (T' o A = T) differs from Iso(c_T,c_T') on {doc_diff} of 256 pairs"
          f" (it is the inverse set); first example T#{example[0]}, T'#{example[1]}")
    for _ in range(10):
        i, j = rng.randrange(16), rng.randrange(16)
        full = {p for p in perms if pull(tables[i], p) == tables[j]}
        expect = {perm_of(direct_sum(As, d, k), 0, K) for As in tuples if action[(i, As)] == Ts[j]}
        assert full == expect
    print("  (d,k)=(2,2): direct scan of all of AGL(4,2) (no pinning shortcut) agrees on 10 random pairs")

    for d, k, rounds in ((2, 3, 3), (3, 2, 6)):
        K = d * k
        n = 1 << K
        cl = classes(d, k)
        # necessary condition only: 0 -> 0, e_i -> a point of the same class.  Everything else is checked.
        basis = [1 << i for i in range(K)]
        byclass = {}
        for x in range(n):
            byclass.setdefault(cl[x], []).append(x)
        choices = [byclass[cl[e]] for e in basis]
        GLk = list(gl(k))
        tuples = list(itertools.product(GLk, repeat=d))
        for _ in range(rounds):
            idxs = list(itertools.product(range(k), repeat=d))
            T = {i: rng.randrange(2) for i in idxs}
            if rng.random() < 0.7:
                A0 = tuple(rng.choice(GLk) for _ in range(d))
                Tp = t_act(T, A0, d, k)
            else:
                Tp = {i: rng.randrange(2) for i in idxs}
            ct, ctp = c_table(T, d, k), c_table(Tp, d, k)
            found = set()
            for cols in itertools.product(*choices):
                if rank(cols) != K:
                    continue
                ok = True
                for x in range(n):
                    if ct[apply_cols(cols, x)] != ctp[x]:
                        ok = False
                        break
                if ok:
                    found.add(cols)
            expect = {direct_sum(As, d, k) for As in tuples if t_act(T, As, d, k) == Tp}
            assert found == expect, (d, k)
        print(f"  (d,k)=({d},{k}), K={K}: pruned-exhaustive linear search equals the explicit tensor stabiliser coset"
              f" on {rounds} instances ({len(tuples)} tuples)")


def section9(rng):
    print("== 9. Prop. D: pattern separation")
    for k in (8, 10, 12, 14):
        n = 1 << k
        tdoc = math.ceil(math.log2(k)) + 3
        res = []
        for _ in range(5):
            g = [rng.randrange(2) for _ in range(n)]
            for t in range(1, k + 1):
                U = range(1 << t)
                pats = {tuple(g[x ^ w] for w in U) for x in range(n)}
                if len(pats) == n:
                    res.append(t)
                    break
            else:
                res.append(None)
        pats = None
        bound = Fraction(1 << (2 * k), 1) / (1 << (1 << tdoc)) + Fraction(1 << (k + tdoc), 1) / (1 << (1 << (tdoc - 1)))
        print(f"  k={k}: doc's t={tdoc}; smallest separating t over 5 random g: {res}; union bound {float(bound):.2e}")


def section10():
    print("== 10. Prop. G arithmetic for AGL(r,2) on d=2^r points (children of size n/d)")
    print("   r   mu=log|P|/r   log|P|_2'/r   Sylow row: (log|P|_2' + 2r)/r   ratio to mu")
    for r in (4, 6, 12, 24, 48, 96):
        lp = log2(agl_order(r))
        lo = log2(fact2(r))
        mu = lp / r
        mu2 = (lo + 2 * r) / r
        print(f"  {r:3d}   {mu:9.2f}   {lo/r:10.2f}   {mu2:12.2f}   {mu2/mu:18.3f}")


def balance_table():
    """Report section 2.4: worst excess of the best parabolic over sqrt(#flags), k=4..64."""
    for R in (2, 3, 4):
        w, wk = 0.0, None
        for k in range(4, 65):
            best = min(max(composition_sizes(c)) for r in range(2, R + 1) for c in compositions(k, r))
            e = log2(best) - log2(fact2(k)) / 2
            if e > w:
                w, wk = e, k
        print(f"  blocks <= {R}: worst excess over sqrt(#flags), k=4..64: {w:.2f} bits at k={wk}")


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "balance":
        balance_table()
        return
    rng = random.Random(20261108)
    t0 = time.time()
    section1()
    section2()
    section3(rng)
    section4(rng)
    section5(rng)
    section6(rng)
    section7(rng)
    section8(rng)
    section9(rng)
    section10()
    print(f"ALL CHECKS PASSED in {time.time()-t0:.1f}s")


if __name__ == "__main__":
    main()
