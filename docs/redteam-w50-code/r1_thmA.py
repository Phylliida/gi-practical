"""Theorem A at homology and pi_1 level, exhaustive over pattern families.
For C = prod N_j with N_j 2-transitive, the C-orbit of (u,v) is determined by the set of coordinates where they differ, so
EVERY C-invariant graph is Gamma_F(K_b) for a family F of nonempty subsets of [M].  So the enumeration over F below is
exhaustive for all 2-transitive local groups at the given (b,M), unlike a random sample of H-orbital unions."""
import itertools, sys, time
sys.path.insert(0, '.')
from rtlib import *


def all_F(M):
    subs = [c for r in range(1, M + 1) for c in itertools.combinations(range(M), r)]
    seen = set()
    for r in range(1, len(subs) + 1):
        for F in itertools.combinations(subs, r):
            cf = min(tuple(sorted(tuple(sorted(p[j] for j in I)) for I in F)) for p in itertools.permutations(range(M)))
            if cf in seen:
                continue
            seen.add(cf)
            yield cf


def homology(bs_Ms, primes=(2, 3, 5)):
    tot = bad = 0
    hist = defaultdict(int)
    for b, M in bs_Ms:
        for F in all_F(M):
            adj = pattern_graph(complete(b), b, M, F)
            for p in primes:
                k, tbl = least_k(adj, b, M, p, kmax=min(b, 5))
                hist[(b, M, p, k)] += 1
                tot += 1
                if k not in (3,) and Cycles(adj).rank > 0:
                    print("non-3:", b, M, F, p, k, tbl, flush=True)
                    bad += 1
    print("homology pairs", tot, "non-3", bad)
    for key in sorted(hist):
        print("b,M,p,k", key, hist[key])


def pi1(b, M, k=3):
    """eliminate generators of pi_1 using relators from all k-box fundamental cycles"""
    ok = fail = 0
    for F in all_F(M):
        adj = pattern_graph(complete(b), b, M, F)
        C = Cycles(adj)
        rels = []
        for box in itertools.product(itertools.combinations(range(b), k), repeat=M):
            for cyc in box_cycles(adj, box):
                w = C.word(cyc)
                if w:
                    rels.append(w)
        try:
            alive, left = tietze_simplify(rels, C.rank)
        except RuntimeError as e:
            print("blow-up", b, M, F)
            fail += 1
            continue
        if not alive and not left:
            ok += 1
        else:
            fail += 1
            print("not collapsed", b, M, F, len(alive), len(left), flush=True)
    print(f"pi1 b={b} M={M} k={k}: {ok} collapsed to trivial group, {fail} not")


if __name__ == "__main__":
    if sys.argv[1] == "hom":
        homology(eval(sys.argv[2]))
    else:
        pi1(int(sys.argv[2]), int(sys.argv[3]))
