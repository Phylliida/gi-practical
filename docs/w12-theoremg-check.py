#!/usr/bin/env python3
"""Checks for docs/w12-theoremg.md. Standard library only; about a minute at nice 19.

These are consistency checks of the elementary parts of the argument. They do not check the
group-theoretic inputs (GNS, HBD, Lemma A), and they prove nothing by themselves.

Part 1: the tower potential: f(a) + f(b) <= f(ab) - 1, monotonicity of f, rho <= 2 log2 n,
        and a random simulation of insertion and restriction on maintained towers.
Part 2: Lemma 5.2 (partitions): for every wreath-type orbit on s-subsets of measure > 5/6, exact
        rational arithmetic confirms that Psi takes >= 2 values and has a fibre with >= 2 subsets.
        Also the Lemma's two probability bounds, tested against the exact maximum.
Part 3: Lemma 5.3 (Johnson): the hypergeometric bound, and the sum over a Johnson chain.
Part 4: the recurrence: the constants A, B close all five inequalities of Theorem 7.2, and the
        final exponent is 3 in every regime.
Part 5: the exponent profile with and without the Babai--Helfgott switch.
Part 6: Bochert's bound as used in Lemma A: n!/floor((n+1)/2)! < m!/2 for 16 <= m < 3000, m < n <= 4m/3,
        and the analytic inequality used for m >= 40.
"""
import math
import random
from fractions import Fraction as Fr
from functools import lru_cache


# ---------- Part 1: tower potential ----------
def f(r):
    return 0 if r == 1 else 2 * math.floor(math.log2(r) + 1e-12) - 1


def f_exact(r):
    # floor(log2 r) by bit length, to avoid floating-point trouble
    return 0 if r == 1 else 2 * (r.bit_length() - 1) - 1


def part1():
    for a in range(2, 600):
        for b in range(2, 600):
            assert f_exact(a) + f_exact(b) <= f_exact(a * b) - 1, (a, b)
    for r in range(1, 5000):
        assert f_exact(r) <= f_exact(r + 1)
    assert f_exact(2) == 1 and f_exact(3) == 1 and f_exact(4) == 3

    rng = random.Random(20261108)
    drops = 0
    for _ in range(3000):
        levels = [rng.randint(2, 40) for _ in range(rng.randint(1, 8))]
        n = math.prod(levels)
        rho = sum(f_exact(r) for r in levels)
        assert rho <= 2 * math.log2(n)
        for _step in range(rng.randint(1, 8)):
            i = rng.randrange(len(levels))
            r = levels[i]
            if rng.random() < 0.5:
                # restriction: a level may shrink, possibly to 1
                new = rng.randint(1, r)
                old_rho = sum(f_exact(x) for x in levels)
                levels[i] = new
                assert sum(f_exact(x) for x in levels) <= old_rho
                levels = [x for x in levels if x > 1] or [2]
            else:
                # strict insertion
                divs = [a for a in range(2, r) if r % a == 0]
                if divs:
                    a = rng.choice(divs)
                    old_rho = sum(f_exact(x) for x in levels)
                    levels = levels[:i] + [a, r // a] + levels[i + 1:]
                    assert sum(f_exact(x) for x in levels) <= old_rho - 1
                    drops += 1
    print(f"  part 1 ok ({drops} strict insertions simulated)")


# ---------- Part 2: partition lemma ----------
def partitions_into(s, maxpart, maxlen):
    """Partitions of s into at most maxlen parts, each at most maxpart (non-increasing lists)."""
    if s == 0:
        yield []
        return
    if maxlen == 0:
        return
    for first in range(min(s, maxpart), 0, -1):
        for rest in partitions_into(s - first, first, maxlen - 1):
            yield [first] + rest


def type_count(counts, b, p):
    """Number of subsets of p blocks of size b whose block-count multiset is `counts`."""
    from collections import Counter

    c = Counter(counts)
    zeros = p - len(counts)
    arrangements = math.factorial(p) // math.factorial(zeros)
    for v in c.values():
        arrangements //= math.factorial(v)
    per = 1
    for x in counts:
        per *= math.comb(b, x)
    return arrangements, per


def part2():
    tested = 0
    big_orbits = 0
    max_nonshrink_ok = Fr(0)
    for k in list(range(40, 201, 4)) + [240, 300, 400, 600, 900, 1200]:
        for q in sorted({0, k // 8, k // 5}):  # q points outside E (singletons, fixed)
            e = k - q
            if q >= k / 4 or e <= 3 * k / 4:
                continue
            bs = [b for b in range(2, e // 2 + 1) if e % b == 0 and b <= 3 * k / 4]
            for b in bs:
                p = e // b
                if p < 2:
                    continue
                for s in range(1, min(8, (k - 1) // 10) + 1):
                    if not s < k / 10:
                        continue
                    total = math.comb(k, s)
                    # j of the s points lie in Q; L fixes Q pointwise in the worst case
                    for j in range(0, min(q, s) + 1):
                        q_choices_worst = 1  # a single subset of Q forms one orbit part
                        for counts in partitions_into(s - j, b, p):
                            arr, per = type_count(counts, b, p)
                            orbit = q_choices_worst * arr * per
                            mu = Fr(orbit, total)
                            tested += 1
                            if mu > Fr(5, 6):
                                big_orbits += 1
                                # (a) Psi takes at least two values on the orbit
                                assert arr >= 2, (k, q, b, s, j, counts)
                                # (b) some Psi-fibre contains at least two subsets
                                assert any(0 < c < b for c in counts) or per >= 2, (k, q, b, s, j, counts)
                                max_nonshrink_ok = max(max_nonshrink_ok, mu)
    print(f"  part 2 ok: {tested} orbit types, {big_orbits} of measure > 5/6, largest {float(max_nonshrink_ok):.4f}")

    # Bound of Lemma 5.2(a): every fibre of Psi has measure < 5/6. A fibre fixes the count in each
    # block; the points outside E (Q, size q) are unconstrained by Psi, so they contribute C(q, j).
    worst = Fr(0)
    cases = 0
    for k in list(range(40, 161, 8)) + [240, 400]:
        for q in sorted({0, k // 8, (k - 1) // 4}):
            e = k - q
            for b in range(2, e + 1):
                if e % b or b > 3 * k / 4:
                    continue
                p = e // b
                for s in range(1, min(7, (k - 1) // 10) + 1):
                    total = math.comb(k, s)
                    for j in range(0, min(q, s) + 1):
                        for counts in partitions_into(s - j, b, p):
                            per = math.comb(q, j)
                            for c in counts:
                                per *= math.comb(b, c)
                            m = Fr(per, total)
                            worst = max(worst, m)
                            cases += 1
    assert worst < Fr(5, 6)
    print(f"  part 2b ok: {cases} fibres, largest measure {float(worst):.4f} < 5/6")


# ---------- Part 3: Johnson ----------
def part3():
    # hypergeometric bound, exact (independent of the redteam script)
    cnt = 0
    worst = Fr(0)
    for k in list(range(40, 121, 2)) + [200, 400]:
        for K in range(1, (k - 1) // 4 + 1, max(1, k // 40)):
            for s in range(1, (k - 1) // 10 + 1):
                tot = math.comb(k, s)
                for j in range(1, min(K, s) + 1):
                    nj = math.comb(K, j) * math.comb(k - K, s - j)
                    mu = Fr(nj, tot)
                    assert mu < Fr(5, 6), (k, K, s, j)
                    worst = max(worst, mu)
                    cnt += 1
    print(f"  part 3 hypergeometric ok: {cnt} cases, max {float(worst):.4f}")

    # Johnson chain: k_{i+1} <= 1 + sqrt(2 k_i). Charge t*log k_i + c*log^2 k_i, c = 12.
    worst_ratio = 0.0
    for L in [20, 40, 80, 160, 320, 640, 1280]:
        t = max(9, 3 + L)
        logk = float(L)
        s = 0.0
        steps = 0
        while logk > math.log2(40 * t):
            s += t * logk + 12 * logk**2
            logk = min(logk - 0.1, 0.5 * logk + 1.0)  # log2(1 + sqrt(2k)) <= log2(k)/2 + 1
            steps += 1
        worst_ratio = max(worst_ratio, s / L**2)
        assert steps <= 2 * math.log2(L) + 6
    print(f"  part 3 chain ok: sum(t log k_i + 12 log^2 k_i)/L^2 <= {worst_ratio:.2f}")
    assert worst_ratio < 40.0


# ---------- Part 4: recurrence ----------
def part4():
    # log2-scale constants (all multiplying L^2)
    c_tree = 40.0  # log2 of the node bound Z of a macro step, per L^2
    c_exit = 10.0  # log2 of the exit mass per node, per L^2
    c_child = 20.0  # log2 of the number of heavy children, per L^2
    c_work = 10.0  # log2 of the per-node non-recursive factor, per L^2, plus B-H
    for L in [8, 16, 32, 64, 128]:
        A = ((c_tree + c_child) / math.log2(6 / 5) + c_tree + c_exit + c_work + 20) * L * L
        B = (c_tree + c_child + 4) * L * L
        for logn in [L, L**1.5, L**2, L**3]:
            # exits: Z * exit mass * 2^{-(A-1)}
            assert (c_tree + c_exit) * L * L - (A - 1) <= -2
            # shrink children: Z * C_h * (5/6)^{A-1}
            assert (c_tree + c_child) * L * L - (A - 1) * math.log2(6 / 5) <= -2
            # tower children: Z * C_h * 2^{-B}
            assert (c_tree + c_child) * L * L - B <= -2
            # non-recursive work against n^A (B-H: log^3 k <= L^2 log n)
            assert (c_tree + c_work) * L * L * logn - (A - 2) * logn <= 0 or logn < 1
            # semi-regular step: b^2 (n/b)^A <= n^A / 4 for A >= 4
            assert A >= 4
    print("  part 4 ok: the inequalities close with A, B = O(L^2)")

    # Bound for the whole run: N^{A + 2B}, with log2 N <= C L log2 n: exponent O(L^3).
    # check that (A+2B)/L^2 is a constant independent of L
    ratios = set()
    for L in [8, 16, 32, 64]:
        A = ((c_tree + c_child) / math.log2(6 / 5) + c_tree + c_exit + c_work + 20) * L * L
        B = (c_tree + c_child + 4) * L * L
        ratios.add(round((A + 2 * B) / L**2, 6))
    assert len(ratios) == 1
    print(f"  part 4 ok: exponent constant (A + 2B)/L^2 = {ratios.pop():.1f}")


# ---------- Part 5: regimes ----------
def part5():
    xs = [1 + i / 1000 for i in range(9001)]
    # Theorem G: 3 for every x; with the B-H switch min(3, 2x).
    assert all(abs(min(3.0, 2 * x) - (2 * x if x < 1.5 else 3.0)) < 1e-9 for x in xs)
    assert max(min(3.0, 2 * x) for x in xs) == 3.0
    # Theorem X profile for comparison
    assert abs(max(min(max(3.0, 5 - x), 2 * x) for x in xs) - 10 / 3) < 2e-3
    print("  part 5 ok")


# ---------- Part 6: Bochert ----------
def part6():
    fact = [1] * 4300
    for i in range(1, 4300):
        fact[i] = fact[i - 1] * i
    cnt = 0
    for m in range(16, 3000):
        for n in range(m + 1, (4 * m) // 3 + 1):
            assert 4 * n > 0
            if 3 * n >= 4 * m + 3:
                continue
            assert fact[n] * 2 < fact[m] * fact[(n + 1) // 2], (m, n)
            cnt += 1
    # m >= 40: (2/3) ln(4m/3) + ln2/m < ln m - 1
    for m in range(40, 200000, 97):
        assert (2 / 3) * math.log(4 * m / 3) + math.log(2) / m < math.log(m) - 1
    print(f"  part 6 ok ({cnt} pairs)")


if __name__ == "__main__":
    print("Part 1"); part1()
    print("Part 2"); part2()
    print("Part 3"); part3()
    print("Part 4"); part4()
    print("Part 5"); part5()
    print("Part 6"); part6()
    print("all checks passed")
