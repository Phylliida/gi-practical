"""Correctness-checked benchmark.

    python3 bench/run.py --tiers tiny,small --timeout 60 --label baseline

Every answer is verified: the isomorphism is checked edge by edge, every
returned generator is checked to be an automorphism, and the order of the
generated group (computed with sympy, independently of gi) is compared with
the known order of Aut(X) (or with networkx's count on small graphs).
A run counts as solved only if it is correct and within the time limit.
"""
import argparse
import json
import math
import os
import signal
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.setrecursionlimit(100000)

import networkx as nx
from sympy.combinatorics import Permutation, PermutationGroup

from bench.families import instances
from gi import graph_iso, Solver, Unsupported


class Timeout(Exception):
    pass


def _alarm(signum, frame):
    raise Timeout()


def group_order(n, gens):
    if not gens:
        return 1
    return PermutationGroup([Permutation(list(g)) for g in gens]).order()


def nx_aut_count(A, limit=200000):
    n = len(A)
    G = nx.Graph()
    G.add_nodes_from(range(n))
    G.add_edges_from((i, j) for i in range(n) for j in range(i + 1, n) if A[i][j])
    c = 0
    for _ in nx.algorithms.isomorphism.GraphMatcher(G, G).isomorphisms_iter():
        c += 1
        if c > limit:
            return None
    return c


def check(X, Y, res, expect_iso, expect_aut):
    n = len(X)
    if (res is not None) != expect_iso:
        return False, "wrong iso decision"
    if res is None:
        return True, ""
    sigma, gens = res
    if sorted(sigma) != list(range(n)) or any(
            Y[sigma[i]][sigma[j]] != X[i][j] for i in range(n) for j in range(n)):
        return False, "returned map is not an isomorphism"
    for g in gens:
        if any(X[g[i]][g[j]] != X[i][j] for i in range(n) for j in range(n)):
            return False, "a generator is not an automorphism"
    order = group_order(n, gens)
    want = expect_aut if expect_aut is not None else (nx_aut_count(X) if n <= 16 else None)
    if want is not None and order != want:
        return False, f"|<gens>| = {order}, expected {want}"
    return True, f"|Aut|={order}"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tiers", default="tiny,small")
    ap.add_argument("--only", default="", help="comma-separated instance names")
    ap.add_argument("--timeout", type=float, default=60)
    ap.add_argument("--label", default="run")
    ap.add_argument("--solver-args", default="{}", help="JSON kwargs for Solver")
    ap.add_argument("--graph-args", default="{}",
                    help='JSON kwargs for graph_iso (front end), e.g. {"ir": 0}')
    args = ap.parse_args()
    tiers = set(args.tiers.split(","))
    only = set(filter(None, args.only.split(",")))
    kwargs = json.loads(args.solver_args)
    gkwargs = json.loads(args.graph_args)
    signal.signal(signal.SIGALRM, _alarm)
    rows = []
    for name, tier, X, Y, expect_iso, expect_aut in instances():
        if tier not in tiers or (only and name not in only):
            continue
        S = Solver(**kwargs)
        t0 = time.time()
        status, note = "ok", ""
        signal.setitimer(signal.ITIMER_REAL, args.timeout)
        try:
            res = graph_iso(X, Y, solver=S, **gkwargs)
            signal.setitimer(signal.ITIMER_REAL, 0)
            ok, note = check(X, Y, res, expect_iso, expect_aut)
            status = "ok" if ok else "WRONG"
        except Timeout:
            status = "timeout"
        except Unsupported as e:
            signal.setitimer(signal.ITIMER_REAL, 0)
            status, note = "unsupported", str(e)
        except RecursionError:
            signal.setitimer(signal.ITIMER_REAL, 0)
            status = "recursion"
        dt = time.time() - t0
        rows.append(dict(name=name, tier=tier, n=len(X), status=status, time=round(dt, 3),
                         note=note, stats=dict(S.stats)))
        print(f"{name:22s} {tier:7s} n={len(X):3d} {status:11s} {dt:8.2f}s  {note}", flush=True)
    solved = [r for r in rows if r["status"] == "ok"]
    wrong = [r for r in rows if r["status"] == "WRONG"]
    print(f"\n{args.label}: solved {len(solved)}/{len(rows)}, wrong {len(wrong)}, "
          f"time on solved {sum(r['time'] for r in solved):.1f}s")
    os.makedirs(os.path.join(os.path.dirname(__file__), "results"), exist_ok=True)
    with open(os.path.join(os.path.dirname(__file__), "results", f"{args.label}.json"), "w") as f:
        json.dump(dict(label=args.label, solver_args=kwargs, graph_args=gkwargs, timeout=args.timeout,
                       rows=rows), f, indent=1)
    sys.exit(1 if wrong else 0)


if __name__ == "__main__":
    main()
