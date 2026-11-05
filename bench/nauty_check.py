"""Cross-check graph_iso against nauty (pynauty) on graphs outside the benchmark
families, including sizes beyond the xl tier. For each graph X: a random
relabeling Y (isomorphic) and, for CFI graphs, the twisted graph (not
isomorphic). Checks the decision, the returned isomorphism, that every
generator is an automorphism, and |<gens>| (sympy) against nauty's |Aut|.

    .venv/bin/python bench/nauty_check.py              # needs pynauty, see reference.py
    .venv/bin/python bench/nauty_check.py --only "rook12;PG(2,11)" --timeout 300
"""
import argparse
import os
import random
import signal
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.setrecursionlimit(100000)

import networkx as nx
import pynauty
from sympy.combinatorics import Permutation, PermutationGroup

from bench.families import adj, shuffled, cfi, projective_plane, paley, rook
from gi import graph_iso, Solver


class Timeout(Exception):
    pass


def _alarm(signum, frame):
    raise Timeout()


def nauty_graph(A):
    n = len(A)
    return pynauty.Graph(n, adjacency_dict={i: [j for j in range(n) if A[i][j] and j != i]
                                            for i in range(n)})


def graphs():
    """(name, X, twisted X or None), lazily."""
    for seed in (20, 21):
        base = nx.random_regular_graph(3, 20, seed=seed)
        yield f"CFI(3reg20,s{seed})", lambda b=base: cfi(b), lambda b=base: cfi(b, True)
    for nm, base in (("CFI(K33)", nx.complete_bipartite_graph(3, 3)),
                     ("CFI(Petersen)", nx.petersen_graph()), ("CFI(Q3)", nx.hypercube_graph(3))):
        yield nm, lambda b=base: cfi(b), lambda b=base: cfi(b, True)
    yield "rook12", lambda: rook(12), None
    yield "Paley149", lambda: paley(149), None
    yield "PG(2,11)", lambda: projective_plane(11), None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", default="")
    ap.add_argument("--timeout", type=float, default=300)
    args = ap.parse_args()
    only = set(filter(None, args.only.split(";")))
    signal.signal(signal.SIGALRM, _alarm)
    rng = random.Random(7)
    bad = 0
    for name, fx, ftw in graphs():
        if only and name not in only:
            continue
        A = adj(fx())
        pairs = [(name, shuffled(A, rng))]
        if ftw is not None:
            pairs.append((name + "-twist", shuffled(adj(ftw()), rng)))
        _, s1, s2, _, _ = pynauty.autgrp(nauty_graph(A))
        aut = s1 * 10 ** s2
        cert = pynauty.certificate(nauty_graph(A))
        n = len(A)
        for label, B in pairs:
            iso = cert == pynauty.certificate(nauty_graph(B))
            t0 = time.time()
            signal.setitimer(signal.ITIMER_REAL, args.timeout)
            try:
                r = graph_iso(A, B, solver=Solver(certificates=False))
                signal.setitimer(signal.ITIMER_REAL, 0)
            except Timeout:
                print(f"{label:24s} n={n:4d} timeout", flush=True)
                continue
            dt = time.time() - t0
            ok = (r is not None) == iso
            if ok and r is not None:
                sigma, gens = r
                ok = all(B[sigma[i]][sigma[j]] == A[i][j] for i in range(n) for j in range(n))
                ok = ok and all(A[g[i]][g[j]] == A[i][j]
                                for g in gens for i in range(n) for j in range(n))
                order = PermutationGroup([Permutation(list(g)) for g in gens]).order() if gens else 1
                ok = ok and abs(order - aut) <= 1e-9 * aut
            bad += not ok
            print(f"{label:24s} n={n:4d} iso={iso!s:5s} {dt:8.2f}s {'ok' if ok else 'WRONG'}"
                  f"  |Aut|={aut:.6g}", flush=True)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
