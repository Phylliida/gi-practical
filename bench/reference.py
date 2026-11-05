"""Reference timings on the benchmark instances: networkx VF2 (decision only)
and, when it can be imported, pynauty (nauty's canonical labeling).

    python3 bench/reference.py --tiers large --timeout 180 --label ref-large
    python3 bench/reference.py --tiers xl --timeout 300 --compare r2-hybrid-xl

VF2 only answers "isomorphic or not" (nx.is_isomorphic); it computes no
automorphism group, so it does strictly less than graph_iso. pynauty answers
by comparing certificates (canonical forms) and also reports |Aut| from
autgrp, which is checked against the known order. Every decision is checked
against the instance's known answer. With --compare LABEL the table also shows
the times of bench/results/LABEL.json (a bench/run.py result).

pynauty is not a dependency of the project. To try it without touching the
global environment:

    python3 -m venv .venv && .venv/bin/pip install pynauty networkx sympy
    .venv/bin/python bench/reference.py ...
"""
import argparse
import json
import os
import signal
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

import networkx as nx

from bench.families import instances

try:
    import pynauty
except ImportError:                     # optional
    pynauty = None


class Timeout(Exception):
    pass


def _alarm(signum, frame):
    raise Timeout()


def to_nx(A):
    n = len(A)
    G = nx.Graph()
    G.add_nodes_from(range(n))
    G.add_edges_from((i, j) for i in range(n) for j in range(i + 1, n) if A[i][j])
    return G


def to_nauty(A):
    n = len(A)
    adj = {i: [j for j in range(n) if A[i][j] and j != i] for i in range(n)}
    return pynauty.Graph(n, directed=False, adjacency_dict=adj)


def timed(f, timeout):
    """(status, seconds, value) of f() under a wall-clock limit."""
    t0 = time.time()
    signal.setitimer(signal.ITIMER_REAL, timeout)
    try:
        v = f()
        signal.setitimer(signal.ITIMER_REAL, 0)
        return "ok", time.time() - t0, v
    except Timeout:
        return "timeout", time.time() - t0, None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tiers", default="large")
    ap.add_argument("--only", default="")
    ap.add_argument("--timeout", type=float, default=180)
    ap.add_argument("--label", default="")
    ap.add_argument("--compare", default="", help="label of a bench/run.py result to show")
    ap.add_argument("--no-vf2", action="store_true")
    args = ap.parse_args()
    tiers = set(args.tiers.split(","))
    only = set(filter(None, args.only.split(",")))
    signal.signal(signal.SIGALRM, _alarm)
    ours = {}
    if args.compare:
        path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results",
                            args.compare + ".json")
        ours = {r["name"]: r for r in json.load(open(path))["rows"]}
    print(f"pynauty: {'version ' + pynauty.__version__ if pynauty else 'not available'}")
    hdr = f"{'instance':26s} {'n':>4s} {'iso':>5s}  {'VF2':>12s}  {'pynauty':>12s}"
    if ours:
        hdr += f"  {args.compare:>14s}"
    print(hdr)
    rows = []
    for name, tier, X, Y, expect_iso, expect_aut in instances(tiers=tiers):
        if tier not in tiers or (only and name not in only):
            continue
        row = dict(name=name, tier=tier, n=len(X), expect_iso=expect_iso)
        cells = []
        if not args.no_vf2:
            G, H = to_nx(X), to_nx(Y)
            st, dt, v = timed(lambda: nx.is_isomorphic(G, H), args.timeout)
            if st == "ok" and v != expect_iso:
                st = "WRONG"
            row["vf2"] = dict(status=st, time=round(dt, 3))
            cells.append(f"{dt:8.2f}s" if st == "ok" else st)
        else:
            cells.append("-")
        if pynauty is not None:
            G, H = to_nauty(X), to_nauty(Y)

            def nauty():
                same = pynauty.certificate(G) == pynauty.certificate(H)
                _, size1, size2, _, _ = pynauty.autgrp(G)
                return same, size1 * 10 ** size2     # |Aut| = grpsize1 * 10^grpsize2

            st, dt, v = timed(nauty, args.timeout)
            note = ""
            if st == "ok":
                same, aut = v
                bad_aut = expect_aut is not None and abs(aut - expect_aut) > 1e-9 * expect_aut
                if same != expect_iso or bad_aut:
                    st, note = "WRONG", f"iso={same} |Aut|={aut:.6g}"
            row["pynauty"] = dict(status=st, time=round(dt, 4), note=note)
            cells.append(f"{dt:8.3f}s" if st == "ok" else st)
        else:
            cells.append("n/a")
        line = f"{name:26s} {len(X):4d} {str(expect_iso):>5s}  {cells[0]:>12s}  {cells[1]:>12s}"
        if ours:
            r = ours.get(name)
            line += f"  {(f'{r['time']:8.2f}s' if r['status'] == 'ok' else r['status']) if r else '-':>14s}"
        print(line, flush=True)
        rows.append(row)
    if args.label:
        os.makedirs(os.path.join(os.path.dirname(__file__), "results"), exist_ok=True)
        with open(os.path.join(os.path.dirname(__file__), "results", f"{args.label}.json"), "w") as f:
            json.dump(dict(label=args.label, timeout=args.timeout,
                           pynauty=getattr(pynauty, "__version__", None), rows=rows), f, indent=1)
    sys.exit(1 if any(r.get(k, {}).get("status") == "WRONG" for r in rows
                      for k in ("vf2", "pynauty")) else 0)


if __name__ == "__main__":
    main()
