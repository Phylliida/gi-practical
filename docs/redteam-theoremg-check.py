#!/usr/bin/env python3
"""Referee checks for docs/redteam-theoremg.md. Standard library only; a few seconds at nice 19.

Arithmetic only. Nothing here tests a group-theoretic input.

Part 1: HBD Prop. bicoup, worst path: product of options and number of points read, from the
        recursion as written (each expensive round costs |V2|^d * |C2| and shrinks V2 by 2/3).
Part 2: what happens if a contracted V2-element is individualized through a representative point.
Part 3: macro-step size: worst path by dynamic programming over k, light and Johnson steps mixed.
Part 4: Theorem 7.2's inequalities, with the G2 exit inside the macro tree included.
Part 5: regimes, with and without the unrefereed exp(O(log^2 n)) switch.
"""
import math
from functools import lru_cache
from fractions import Fraction as Fr


# ---------- Part 1 ----------
def bicoup_worst(logm):
    """Worst path. Sizes in log2. Returns (log2 product of options, points read)."""
    base = 1.5 * math.log2(6 * logm)          # |V2| <= (6 log m)^{3/2}
    logv = logm
    total, points = 0.0, 0
    # Thm coupjohn: one point x
    total += logm
    points += 1
    rounds = 0
    while logv > base:
        d = 6 * math.ceil(logm / logv)
        # Design Lemma tuple (at most d points of V2), then one point y of C2
        total += d * logv + logv
        points += d + 1
        logv += math.log2(2 / 3)
        rounds += 1
    # base case: all of V2 individualized, |V2|! options
    v = 2 ** min(base, 60)
    total += v * base
    points += int(v)
    return total, points, rounds


def part1():
    worst_ratio, worst_pts = 0, 0
    for logm in list(range(40, 400, 7)) + [2 ** j for j in range(9, 16)]:
        tot, pts, rounds = bicoup_worst(logm)
        worst_ratio = max(worst_ratio, tot / logm ** 2)
        worst_pts = max(worst_pts, pts / logm ** 1.5)
        assert rounds <= 1.71 * logm + 1
    print(f"  part 1: max log2(options)/log^2 m = {worst_ratio:.1f}; max points/log^1.5 m = {worst_pts:.1f}")
    assert worst_ratio < 45 and worst_pts < 50


# ---------- Part 2 ----------
def part2():
    # One round on a contracted V2 of size v, the underlying C2 having c >> v points.
    logm, logc = 1000.0, 999.0
    for logv in (15.0, 30.0, 100.0):
        d = 6 * math.ceil(logm / logv)
        as_block = d * logv
        as_point = d * logc
        print(f"  part 2: log v = {logv:5.0f}: block read {as_block/logm:8.1f} log m bits, "
              f"representative point read {as_point/logm:8.1f} log m bits")
        assert as_block <= 12.1 * logm and as_point > 5 * as_block
    print("  part 2: the literal 'one point of Gamma' reading does not keep m^{O(1)} per round")


# ---------- Part 3 ----------
def part3():
    cH = 40
    worst = 0
    for L in [10, 12, 14, 16, 18]:
        d = 2 ** L
        t = 3 + L
        tau0 = 40 * t

        @lru_cache(maxsize=None)
        def best(k):
            if k <= tau0:
                return 0.0
            lk = math.log2(k)
            light = math.log2(2 * d) + 6 * lk + best(int(3 * k / 4))
            john = math.log2(d) + t * lk + cH * lk * lk + best(int(1 + math.sqrt(2 * k)))
            return max(light, john)

        import sys
        sys.setrecursionlimit(100000)
        val = best(d)
        worst = max(worst, val / L ** 2)
        print(f"  part 3: L = {L}: log2 Z / L^2 = {val / L**2:.2f}")
    assert worst < 60


# ---------- Part 4 ----------
def part4():
    for L in [4, 8, 16, 64, 256, 4096]:
        z, h, e = 60, 60, 60                  # Z, C_h and exit factors, as 2^{c L^2}
        A = 5 * (z + h + e + 12) * L ** 2 + 8    # log2(6/5) > 0.26 forces the factor 4-5
        B = (z + h + 4) * L ** 2
        LL = L ** 2
        # exits, including G2 inside the tree: b <= d cosets, pieces <= n/2
        assert z * LL + e * LL + L - (A - 1) <= -2
        # type S
        assert (z + h) * LL - (A - 1) * math.log2(6 / 5) <= -2
        # type T: large orbit, small orbits
        assert (z + h) * LL - B <= -2
        assert (z + h) * LL - (A - 1) * math.log2(6) <= -2
        # root G2
        assert A >= 4
    # Final exponent: (A + 2B) * O(L) log n
    print("  part 4: all inequalities close with A, B = O(L^2); no extra log d")


# ---------- Part 5 ----------
def part5():
    gained, sub = [], True
    for i in range(1, 8001):
        x = Fr(i, 1000)
        if x < 1:
            continue
        with_G = min(Fr(3), 2 * x)
        without_G = min(max(Fr(3), 5 - x), 2 * x)
        assert with_G <= without_G
        if with_G < without_G:
            gained.append(x)
        # HJ switch, Theorem C alone: exponent min(max(3, 6 - x), x)
        hj_C = min(max(Fr(3), 6 - x), x)
        if hj_C != min(Fr(3), x):
            sub = False
    print(f"  part 5: exponent strictly improved for x in ({float(min(gained)):.3f}, {float(max(gained)):.3f})")
    assert min(gained) > Fr(3, 2) and min(gained) <= Fr(3, 2) + Fr(1, 1000)
    assert max(gained) < 2 and max(gained) >= 2 - Fr(1, 1000)
    assert min(Fr(3), 2 * Fr(3, 2)) == min(max(Fr(3), 5 - Fr(3, 2)), 2 * Fr(3, 2))
    assert sub
    print("  part 5: at x = 3/2 both give 3; with the exp(O(log^2 n)) switch, Theorem C alone gives min(3, x)")


for name, fn in [("Part 1", part1), ("Part 2", part2), ("Part 3", part3), ("Part 4", part4), ("Part 5", part5)]:
    print(name)
    fn()
print("all checks passed")
