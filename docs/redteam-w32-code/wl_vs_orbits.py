"""S7 claim: for algebraic families the 1-WL partition after individualizing a pair equals the orbit
partition of the pair stabilizer.  Tested here on all pairs through vertex 0 (the families are vertex
transitive), on sizes beyond the memo's (Paley <= 100, Peisert <= 121, lines <= 81, Turyn <= 81)."""
import sys, time
sys.path.insert(0, '.')
from rt_common import *
from depth_families_lib import *

def test(name, A, verts=None):
    n = len(A); bad = []; t0 = time.time(); tot = 0; trivial = 0
    verts = verts if verts is not None else range(1, n)
    for v in verts:
        cells = stable_cells(A, (0, v))
        g, orb, _ = aut_info(A, fixed=(0, v))
        tot += 1
        if g == 1: trivial += 1
        if cells != orb:
            bad.append((v, cells, orb, g))
    print(f'{name}: n={n}, pairs (0,v) tested {tot}, trivial stabilizer {trivial}, #1-WL cells != #orbits on {len(bad)} pairs; ex {bad[:5]} [{time.time()-t0:.0f}s]', flush=True)

def main():
    P5 = seidel(paley_adj(5)); P9 = seidel(paley_adj(9)); P13 = seidel(paley_adj(13))
    skew11 = paley_tournament_V(11)
    fam = [('P(121)', paley_adj(121)), ('P(125)', paley_adj(125)), ('P(169)', paley_adj(169)),
           ('Peisert 121', peisert(121)), ('Peisert 361', peisert(361)),
           ('W(P9,P9)', adj_of_C(turyn(P9, P9))), ('W(P13,P13)', adj_of_C(turyn(P13, P13))),
           ('W(skew11,skew11)', adj_of_C(turyn(skew11, skew11))),
           ('W2(P5)', adj_of_C(turyn(turyn(P5, P5), turyn(P5, P5))))]
    for name, A in fam:
        if len(A) > 200:
            test(name, A, verts=list(range(1, len(A), 7)))
        else:
            test(name, A)
main()
