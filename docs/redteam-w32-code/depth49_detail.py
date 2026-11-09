"""Which descendants at n=49 have depth 3? Aut order, pair stabilizers, orbit counts."""
import sys, itertools, collections
sys.path.insert(0, '.')
from rt_common import *
from depth_families_lib import *
from depth_spence_lib import min_depth

base = parse_rows(SPENCE + '/conf2graph.50', 49)
P49 = paley_adj(49)
print('Aut(P49) =', aut_info(P49)[0], flush=True)
for i, A in enumerate(base):
    d3 = []
    ds = list(descendants(A))
    for j, D in enumerate(ds):
        k, S = min_depth(D, 4)
        if k == 3: d3.append(j)
    if d3:
        print(f'two-graph #{i}: {len(d3)} of 50 labellings have MIN=3: {d3[:60]}', flush=True)
        for j in d3[:6]:
            D = ds[j]; ord_, orb_, _ = aut_info(D)
            print(f'  descendant {j}: |Aut| = {ord_}, orbits = {orb_}', flush=True)
            # classify all pairs: number of pairs, how many with trivial stabilizer, 1-WL cells vs orbits
            n = 49; triv = 0; mism = 0; tot = 0; ex = None
            for x, y in itertools.combinations(range(n), 2):
                g, orb, _ = aut_info(D, fixed=(x, y))
                cells = stable_cells(D, (x, y))
                tot += 1
                if g == 1: triv += 1
                if cells != orb:
                    mism += 1
                    if ex is None: ex = ((x, y), cells, orb, g)
            print(f'     all {tot} pairs: trivial pair stabilizers {triv}; pairs with #1-WL cells != #stabilizer orbits {mism}; example {ex}', flush=True)
