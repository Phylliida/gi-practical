"""Exact 1-WL depth on algebraic families; see report. Shared definitions in depth_families_lib.py."""
import sys, itertools, random, time
sys.path.insert(0, '.')
from rt_common import *
from depth_families_lib import *

def paley_all(qmax):
    res = {}
    for q in range(5, qmax + 1, 4):
        pe = factor_pp(q)
        if not pe: continue
        p, e = pe
        F = Field(q); A = paley_adj(q, F); assert conf(A)
        sq = F.squares(); ns = next(x for x in range(2, q) if x not in sq)
        ones = (0, 1); onex = (0, ns)
        dis = [is_discrete(A, S) for S in (ones, onex)]
        if e == 1:
            res[q] = 2 if all(dis) else ('?', dis)
        else:
            ok3 = None
            if any(dis):
                res[q] = ('2?!', dis); continue
            for x in range(2, q):
                if is_discrete(A, (0, 1, x)): ok3 = x; break
            res[q] = 3 if ok3 else ('no triple', dis)
    return res

def main():
    t0 = time.time()
    what = sys.argv[1]
    if what == 'paley':
        qmax = int(sys.argv[2])
        r = paley_all(qmax)
        bad = {q: v for q, v in r.items() if not ((v == 2 and factor_pp(q)[1] == 1) or (v == 3 and factor_pp(q)[1] > 1))}
        print(f'Paley q<={qmax}: {len(r)} prime powers = 1 mod 4; deviations from "2 for prime, 3 for non-prime": {bad}; {time.time()-t0:.0f}s', flush=True)
    if what == 'families':
        rng = random.Random(9)
        lst = []
        for q in (9, 49, 81, 121, 361): lst.append((f'peisert{q}', peisert(q)))
        for q, cnt in ((5, 2), (7, 2), (9, 2), (11, 2), (13, 2)):
            for i in range(cnt):
                L = rng.sample(range(q + 1), (q + 1) // 2)
                lst.append((f'lines{q}#{i}', lines_graph(q, L)))
        for name, A in lst:
            assert conf(A), name
            n = len(A)
            order, orb, _ = aut_info(A)
            # exhaustive over pairs through vertex 0 (vertex transitive by translations)
            disc2 = [v for v in range(1, n) if is_discrete(A, (0, v))]
            if disc2:
                res = 2
            else:
                res = None
                for tup in itertools.combinations(range(1, n), 2):
                    if is_discrete(A, (0,) + tup): res = 3; wit = tup; break
                res = res or '>3'
            print(f'{name}: n={n}, |Aut|={order:.0f}, #discrete pairs through 0: {len(disc2)}/{n-1}, exact MIN={res} [{time.time()-t0:.0f}s]', flush=True)
main()
