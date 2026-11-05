#!/usr/bin/env python3
"""Referee checks for docs/w10-blackbox.md (red-team: docs/redteam-w10-blackbox.md).

Standard library only. About 40 s at `nice 19` (part 2 uses exact rationals).

Part 1: Theorem X's recurrence, unrolled with the true arities t_j = max(9, 3 + log2 m_{j-1}),
        the candidate factor (t + log m) log m, and the brute-force base case m <= 20 t.
        Compared with t log^3 m + log^5 m. Also the regime profile min{max(3, 5 - x), 2x}, and
        where it beats the previously signed profile min{max(3, 6 - x), 2x}: exactly 5/3 < x < 3.
Part 2: closed-form proof of the Lemma O3 hypergeometric bound (red-team section 5.3).
        For K < k/4 marked points and s < k/10 draws, and every 1 <= j <= min(K, s):
        either N_{j-1}/N_j > 1/5 (case A: K s <= 3.25 j k) or N_{j+1}/N_j > 1.45 (case B).
        Hence P(X = j) < 5/6. Checked with exact rationals on a grid up to k = 600.
Part 3: Proposition 1.3's instance (PSL(2,q), PGL(2,q) on the projective line, q prime).
        (a) PSL(2,q) is 2-transitive, so a single invariant binary structure is trivial;
        (b) after one point, PSL's stabilizer has rank 3 on the remaining q points, so the
            k-member family {Y_x} of its orbital structures is permuted by PSL(2,q) and every
            member is non-trivial (the "poly(k)-size family" remark in w10 section 1.3 is false);
        (c) PGL(2,q) is sharply 3-transitive, so after individualizing 3 points the colouring of
            injective t-tuples by PGL-orbits (which the case-(v) colours refine) separates all
            points: this instance needs only k^3 branches, not k^{Theta(t)}.
"""
import math
from fractions import Fraction
from itertools import permutations


# ---------------------------------------------------------------- part 1
def unrolled(m, t):
    """log2 X(m,t) with all O-constants set to 1."""
    total = 0.0
    while m > 20 * t:
        lm = math.log2(m)
        total += t * lm ** 3 + (t + lm) * lm  # GNS run on m^t points, and the candidates
        t = max(9, 3 + lm)
        m = 0.75 * m
    total += 20 * t * math.log2(20 * t)  # brute force (20t)!
    return total


def part1():
    worst = 0.0
    for L in (12, 16, 24, 32, 48, 64, 96, 128, 192, 256):
        d = 2.0 ** L
        t = max(9, 3 + L)
        for frac in (1.0, 0.5, 0.25):
            m = d ** frac
            if m <= 20 * t:
                continue
            v = unrolled(m, t)
            lm = math.log2(m)
            r = v / (t * lm ** 3 + lm ** 5)
            worst = max(worst, r)
        print(f"  L={L:4d}: log X(d,t)/(t L^3 + L^5) = {unrolled(d, t) / (t * L ** 3 + L ** 5):.3f}")
    assert worst < 1.0, worst
    # regime profile
    xs = [1 + i / 10000 for i in range(0, 30001)]
    prof = [min(max(3.0, 5 - x), 2 * x) for x in xs]
    mx = max(prof)
    arg = xs[prof.index(mx)]
    assert abs(mx - 10 / 3) < 1e-3 and abs(arg - 5 / 3) < 1e-3
    for x, p in zip(xs, prof):
        if x <= 1.5 or x >= 2:
            assert p <= 3 + 1e-12
        # gain over the statement signed in redteam-w8-gnsexp.md section 8 (black box 2^O(L^6))
        old = min(max(3.0, 6 - x), 2 * x)
        if 5 / 3 + 1e-9 < x < 3 - 1e-9:
            assert p < old - 1e-12, x
        else:
            assert abs(p - old) < 1e-12, x
    print(f"  worst ratio {worst:.3f} < 1; profile max {mx:.4f} at x = {arg:.4f}")
    print("  part 1 ok")


# ---------------------------------------------------------------- part 2
def part2():
    cnt = {"A": 0, "B": 0}
    worst = Fraction(0)
    ks = list(range(20, 201)) + list(range(210, 601, 10))
    for k in ks:
        for K in range(1, (k - 1) // 4 + 1):  # K < k/4
            if 4 * K >= k:
                continue
            for s in range(1, (k - 1) // 10 + 1):  # s < k/10
                if 10 * s >= k:
                    continue
                for j in range(1, min(K, s) + 1):
                    down = Fraction(j * (k - K - s + j), (K - j + 1) * (s - j + 1))  # N_{j-1}/N_j
                    if 4 * K * s <= 13 * j * k:  # K s <= 3.25 j k
                        cnt["A"] += 1
                        assert down > Fraction(1, 5), (k, K, s, j)
                        pj_bound = 1 / (1 + down)
                    else:
                        cnt["B"] += 1
                        assert j < min(K, s), (k, K, s, j)
                        up = Fraction((K - j) * (s - j), (j + 1) * (k - K - s + j + 1))  # N_{j+1}/N_j
                        assert up > Fraction(145, 100), (k, K, s, j, up)
                        pj_bound = 1 / (1 + up)
                    assert pj_bound < Fraction(5, 6)
                    worst = max(worst, pj_bound)
    # exact maxima, for comparison with the bound
    exact = 0.0
    for k in range(20, 401, 20):
        for K in range(1, (k - 1) // 4 + 1):
            for s in range(1, (k - 1) // 10 + 1):
                tot = math.comb(k, s)
                exact = max(exact, max(math.comb(K, j) * math.comb(k - K, s - j) / tot
                                       for j in range(1, min(K, s) + 1)))
    print(f"  case A {cnt['A']}, case B {cnt['B']}; bound max {float(worst):.4f} < 5/6; "
          f"exact max_j>=1 P(X=j) seen {exact:.4f}")
    print("  part 2 ok")


# ---------------------------------------------------------------- part 3
def proj_line(q):
    return list(range(q)) + ["inf"]


def mobius(a, b, c, d, q):
    def f(x):
        if x == "inf":
            return "inf" if c % q == 0 else (a * pow(c, q - 2, q)) % q
        den = (c * x + d) % q
        if den == 0:
            return "inf"
        return ((a * x + b) * pow(den, q - 2, q)) % q
    return f


def group(q, special):
    pts = proj_line(q)
    idx = {p: i for i, p in enumerate(pts)}
    squares = {(x * x) % q for x in range(1, q)}
    elems = set()
    for a in range(q):
        for b in range(q):
            for c in range(q):
                for d in range(q):
                    det = (a * d - b * c) % q
                    if det == 0:
                        continue
                    if special and det not in squares:
                        continue
                    f = mobius(a, b, c, d, q)
                    elems.add(tuple(idx[f(p)] for p in pts))
    return pts, elems


def orbits_on_pairs(elems, points):
    pairs = {(x, y) for x in points for y in points if x != y}
    orbs = []
    while pairs:
        p = pairs.pop()
        orb = {p}
        for g in elems:
            orb.add((g[p[0]], g[p[1]]))
        pairs -= orb
        orbs.append(orb)
    return orbs


def part3():
    for q in (7, 11, 13):
        k = q + 1
        pts, psl = group(q, True)
        _, pgl = group(q, False)
        assert len(pgl) == k * q * (q - 1) and len(psl) == len(pgl) // 2
        allp = list(range(k))
        # (a) PSL 2-transitive: one orbital off the diagonal
        assert len(orbits_on_pairs(psl, allp)) == 1
        # (b) stabilizer of the point inf (index q) in PSL: rank 3 on the other q points
        inf = k - 1
        st = [g for g in psl if g[inf] == inf]
        rest = list(range(q))
        orbs = orbits_on_pairs(st, rest)
        assert len(orbs) == 2, len(orbs)  # 2 off-diagonal orbitals = rank 3: non-trivial binary structure
        # the family {Y_x}: Y_x = orbitals of PSL_x on P^1 - {x}; PSL permutes it (Y_x^g = Y_{x^g})
        # and every member is non-trivial; check one conjugate explicitly
        g0 = next(g for g in psl if g[inf] != inf)
        x = g0[inf]
        stx = [g for g in psl if g[x] == x]
        orbs_x = orbits_on_pairs(stx, [p for p in allp if p != x])
        img = sorted(sorted((g0[a], g0[b]) for (a, b) in o) for o in orbs)
        assert img == sorted(sorted(o) for o in orbs_x)
        # (c) PGL sharply 3-transitive: the stabilizer of 3 points is trivial
        for trip in [(0, 1, inf), (0, 2, 5), (1, 3, 4)]:
            fix = [g for g in pgl if all(g[p] == p for p in trip)]
            assert len(fix) == 1
        # PGL_inf is 2-transitive on F_q; PGL_{inf,0} has q - 2 > 1 orbitals on F_q^*
        stg = [g for g in pgl if g[inf] == inf]
        assert len(orbits_on_pairs(stg, rest)) == 1
        st2 = [g for g in stg if g[0] == 0]
        assert len(orbits_on_pairs(st2, list(range(1, q)))) == q - 2
        print(f"  q={q:2d}, k={k}: PSL 2-transitive; PSL_inf rank 3; PGL sharply 3-transitive; "
              f"PGL_inf,0 has {q - 2} orbitals")
    # (c') with t >= 4 the PGL-orbit colour of (p1,p2,p3,u,v5..vt) determines u: verify for q = 7, t = 4
    q, t = 7, 4
    pts, pgl = group(q, False)
    k = q + 1
    orbit_id = {}
    nid = 0
    for tup in permutations(range(k), t):
        if tup in orbit_id:
            continue
        for g in pgl:
            orbit_id[tuple(g[a] for a in tup)] = nid
        nid += 1
    p = (0, 1, 2)
    colours = {u: orbit_id[p + (u,)] for u in range(3, k)}  # PGL-orbit of (p1, p2, p3, u)
    assert len(set(colours.values())) == k - 3
    print(f"  q=7, t=4: after individualizing 3 points the {k - 3} other points get distinct colours")
    print("  part 3 ok")


if __name__ == "__main__":
    print("part 1: Theorem X recurrence"); part1()
    print("part 2: Lemma O3 hypergeometric bound, closed form"); part2()
    print("part 3: Proposition 1.3 instance"); part3()
    print("all checks passed")
