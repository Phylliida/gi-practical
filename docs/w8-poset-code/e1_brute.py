"""w8 E1: the poset DP against brute force over all of S_b^{(P)} (tiny cases)."""
import itertools, random, sys, time
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from w8lib import *
from gi.perm import mul

rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
TR = int(sys.argv[2]) if len(sys.argv) > 2 else 4

def all_posets(h):
    """all posets on [h] up to nothing (labelled, naturally ordered: j<i only if j<i as ints)"""
    pairs = [(j, i) for i in range(h) for j in range(i)]
    seen = set()
    for bits in itertools.product([0, 1], repeat=len(pairs)):
        rel = [p for p, bt in zip(pairs, bits) if bt]
        pred = closure(h, rel)
        key = tuple(frozenset(p) for p in pred)
        if key in seen:
            continue
        seen.add(key)
        yield pred

cases = []
for pred in all_posets(3):
    cases.append((2, pred))
for pred in all_posets(2):
    cases.append((3, pred))
for pred in all_posets(4):
    if gwp_order(2, pred) <= 2 ** 14:
        cases.append((2, pred))
for pred in all_posets(3):
    if gwp_order(3, pred) <= 7776:
        cases.append((3, pred))

tot = ok = 0
t0 = time.time()
for b, pred in cases:
    h = len(pred)
    order = gwp_order(b, pred)
    if order > 70000:
        continue
    elems = list(all_gwp_elements(b, h, pred))
    assert len(elems) == order
    pts = list(itertools.product(range(b), repeat=h))
    for trial in range(TR):
        ncol = rng.choice([1, 2, 2, 3])
        if trial % 4 == 3:      # structured: a function of a sum of two coordinates
            i, j = rng.sample(range(h), 2) if h >= 2 else (0, 0)
            xs = {z: (z[i] + z[j]) % b for z in pts}
        else:
            xs = {z: rng.randrange(ncol) for z in pts}
        g0 = rng.choice(elems)
        if rng.random() < 0.6:
            ys = {g0[z]: xs[z] for z in pts}
        else:
            ys = {z: xs[rng.choice(pts)] for z in pts}
        S = PosetSI(b, pred)
        x = S.to_lam_string(xs); y = S.to_lam_string(ys)
        A, r = S.solve(x, y)
        bf_aut = sum(1 for g in elems if all(xs[g[z]] == xs[z] for z in pts))
        bf_iso = [g for g in elems if all(ys[g[z]] == xs[z] for z in pts)]
        good = A.order() == bf_aut and ((r is None) == (len(bf_iso) == 0))
        if r is not None:
            gc = S.perm_to_coords(r)
            good &= in_gwp(b, h, pred, gc) and all(ys[gc[z]] == xs[z] for z in pts)
        for gen in A.gens:
            gc = S.perm_to_coords(gen)
            good &= in_gwp(b, h, pred, gc) and all(xs[gc[z]] == xs[z] for z in pts)
        tot += 1; ok += good
        if not good:
            print("MISMATCH", b, [sorted(p) for p in pred], A.order(), bf_aut, r is None, len(bf_iso))
print(f"E1 brute force: {ok}/{tot} agree ({len(cases)} posets), {time.time()-t0:.1f}s")
