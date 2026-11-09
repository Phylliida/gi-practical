#!/usr/bin/env python3
"""Exhaustive T2 families by rank-profile class (see redteam-w45-quartic.md section 4.2).
Usage: t2_full.py <path-to-tiso-binary>  (about 30 minutes, one process)"""
import os, sys, itertools, random, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import t2_check as T
s = T.Solver(sys.argv[1])
rng = random.Random(7)
def grouped(name, E, h, n1, n2, n3, tuples, auts=None):
    t0 = time.time()
    auts = T.side_auts(E, h) if auts is None else auts
    built = {x: T.build(E, h, n1, n2, n3, x) for x in tuples}
    groups = {}
    for x in tuples:
        groups.setdefault(s.histogram(built[x]), []).append(x)
    pairs = [(a, b) for g in groups.values() for i, a in enumerate(g) for b in g[i:]]
    print(f"{name}: {len(tuples)} tuples, {len(groups)} profile classes, {len(pairs)} same-profile pairs (all solved) t_build={time.time()-t0:.0f}s", flush=True)
    return T.run_family(name, E, h, n1, n2, n3, tuples, s, pairs=pairs, auts=auts)
E9, h9 = T.Hh(9)
tups = [t for t in itertools.product(range(2), repeat=9) if any(t)]
r1 = grouped("H_9 (1,1,1) exhaustive over all 511 concise tuples", E9, 9, 1, 1, 1, tups, auts=[(tuple(range(9)), tuple(range(9)))])
E, h = T.theta157()
tups = [t for t in itertools.product(range(4), repeat=h) if T.concise_tuple(t, 1, 1, 2)]
r2 = grouped("theta(1,5,7) (1,1,2) exhaustive", E, h, 1, 1, 2, tups)
E, h = T.cycle(3)
tups = [t for t in itertools.product(range(16), repeat=h) if T.concise_tuple(t, 2, 2, 1)]
r3 = grouped("C6 (2,2,1) exhaustive", E, h, 2, 2, 1, tups)
print("ALL OK" if r1 and r2 and r3 else "SOME FAILED", flush=True)
