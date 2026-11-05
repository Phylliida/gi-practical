#!/usr/bin/env python3
"""Checks for docs/w10-blackbox.md. Standard library only; runs in well under a second.

Part 1: exponent profiles  min{max(3, a - x), 2x}  (B-H switch) and  min{max(3, a - x), x}  (HJ switch),
        where the black box costs 2^{O(L^a)} and log n = L^x.
Part 2: the unrolled recursion of Theorem X:  sum_j (5 + log m_j) log^3 m_j  with m_j = (3/4)^j m,
        compared with log^5 m.
Part 3: Lemma O1 (pattern bound): for colourings of [k] with classes <= 3k/4 and s <= k/10, every
        colour-count pattern of a uniform s-subset has probability <= max_class/(k-s+1) <= 5/6.
Part 4: Lemma O3 (hypergeometric): population k, |O| <= k/4 marked, s <= k/10 draws:
        max_{j>=1} P(X = j) <= 5/6.
Part 5: Johnson parameter: C(r,2) <= m  =>  r <= 1 + sqrt(2m) <= 3m/4 for m >= 8.
"""
import itertools
import math
import random


def part1():
    xs = [1 + i / 1000 for i in range(0, 9001)]

    def prof(a, sw):
        return max(min(max(3.0, a - x), sw(x)) for x in xs)

    bh = lambda x: 2 * x
    hj = lambda x: x
    res = {a: (prof(a, bh), prof(a, hj)) for a in (6, 5, 4.5, 4)}
    for a, (p_bh, p_hj) in res.items():
        print(f"  black box 2^O(L^{a}): worst exponent with B-H switch {p_bh:.4f}, with HJ switch {p_hj:.4f}")
    assert abs(res[6][0] - 4) < 1e-9
    assert abs(res[5][0] - 10 / 3) < 2e-3
    assert abs(res[4.5][0] - 3) < 1e-9 and abs(res[4][0] - 3) < 1e-9
    assert all(abs(v[1] - 3) < 1e-9 for v in res.values())
    # argmax for a = 5 is x = 5/3
    best = max(xs, key=lambda x: min(max(3.0, 5 - x), 2 * x))
    assert abs(best - 5 / 3) < 2e-3
    # a = 5: exponent 3 exactly for x >= 2 and x <= 1.5
    for x in xs:
        v = min(max(3.0, 5 - x), 2 * x)
        if x >= 2 or x <= 1.5:
            assert v <= 3 + 1e-12
    print("  part 1 ok")


def part2():
    c = math.log2(4 / 3)
    for L in (10, 20, 40, 80, 160):
        tot, j = 0.0, 0
        while True:
            lm = L - j * c
            if lm <= 6:
                break
            tot += (5 + L) * lm ** 3 if j > 0 else (4 + L) * lm ** 3
            j += 1
        ratio = tot / L ** 5
        print(f"  L={L:4d}: sum/L^5 = {ratio:.3f}")
        assert ratio < 1 / (4 * c) + 2.0
    print("  part 2 ok")


def pattern_max(sizes, s):
    k = sum(sizes)
    tot = math.comb(k, s)
    best = 0.0
    # enumerate count vectors (s_1..s_q) with 0 <= s_j <= sizes_j, sum = s
    def rec(i, left, prod):
        nonlocal best
        if i == len(sizes) - 1:
            if left <= sizes[i]:
                best = max(best, prod * math.comb(sizes[i], left) / tot)
            return
        for a in range(0, min(left, sizes[i]) + 1):
            rec(i + 1, left - a, prod * math.comb(sizes[i], a))
    rec(0, s, 1)
    return best


def part3():
    rng = random.Random(20261105)
    worst = 0.0
    for k in (40, 60, 90, 120):
        for _ in range(60):
            q = rng.randint(2, 5)
            # random class sizes with max <= 3k/4
            while True:
                cuts = sorted(rng.sample(range(1, k), q - 1))
                sizes = [b - a for a, b in zip([0] + cuts, cuts + [k])]
                if max(sizes) <= 3 * k / 4:
                    break
            for s in range(1, k // 10 + 1):
                p = pattern_max(sizes, s)
                bound = max(sizes) / (k - s + 1)
                assert p <= bound + 1e-12, (k, sizes, s, p, bound)
                assert bound <= 5 / 6 + 1e-12
                worst = max(worst, p)
    print(f"  part 3 ok (worst pattern probability seen {worst:.3f} <= 5/6)")


def part4():
    worst = 0.0
    for k in range(20, 301, 10):
        for K in range(1, k // 4 + 1):
            for s in range(1, k // 10 + 1):
                tot = math.comb(k, s)
                m = max(math.comb(K, j) * math.comb(k - K, s - j) / tot for j in range(1, min(K, s) + 1))
                worst = max(worst, m)
                assert m <= 5 / 6, (k, K, s, m)
    print(f"  part 4 ok (max over j>=1 of P(X=j) seen {worst:.3f} <= 5/6)")


def part5():
    for m in range(8, 100000):
        r = 1
        while math.comb(r + 1, 2) <= m:
            r += 1
        assert r <= 1 + math.sqrt(2 * m) + 1e-9 and 1 + math.sqrt(2 * m) <= 3 * m / 4
    print("  part 5 ok")


if __name__ == "__main__":
    print("part 1: exponent profiles"); part1()
    print("part 2: unrolled recursion of Theorem X"); part2()
    print("part 3: Lemma O1 pattern bound"); part3()
    print("part 4: Lemma O3 hypergeometric bound"); part4()
    print("part 5: Johnson parameter"); part5()
    print("all checks passed")
