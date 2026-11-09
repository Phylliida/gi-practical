"""Paired before/after timings of two checkouts of the solver.

    python3 bench/paired.py run --before PATH --label NAME --tiers xl --modes full,ir0 --rounds 3
    python3 bench/paired.py table --label NAME [--per-instance]

Each workload (tier, mode) runs in a fresh process per checkout, with the two
checkouts alternating (before, after, then after, before, ...). A cell is the
minimum over the rounds of solver time alone, per instance. The output
(sigma, generators) and the solver's stats must be identical between the two
checkouts and across the rounds, and a mismatch is reported; the keys in
NEW_STATS are ignored in that comparison. bench/run.py remains the correctness
check, including the group order of the generators.
"""
import argparse
import hashlib
import json
import os
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RESULTS = os.path.join(ROOT, "bench", "results")
NEW_STATS = {"stage_memo_mismatch"}     # stats the "before" code does not have


def digest(x):
    return hashlib.sha256(repr(x).encode()).hexdigest()[:16]


def worker(root, tier, mode):
    sys.path.insert(0, root)
    sys.setrecursionlimit(100000)
    from bench.families import instances
    from gi import graph_iso, Solver
    kw = {} if mode == "full" else {"ir": 0}
    rows = {}
    for name, t, X, Y, _, _ in instances(tiers={tier}):
        if t != tier:
            continue
        S = Solver(certificates=False)
        t0 = time.perf_counter()
        r = graph_iso(X, Y, solver=S, **kw)
        dt = time.perf_counter() - t0
        stats = {k: v for k, v in sorted(S.stats.items()) if k not in NEW_STATS}
        rows[name] = dict(t=dt, d=digest(r), s=digest(stats), i=digest((X, Y)))
    print(json.dumps(rows))


def run_one(root, tier, mode, timeout):
    env = dict(os.environ)
    p = subprocess.run([sys.executable, os.path.abspath(__file__), "worker", root, tier, mode],
                       env=env, check=True, capture_output=True, text=True, timeout=timeout,
                       cwd=root)
    return json.loads(p.stdout.strip().splitlines()[-1])


def cmd_run(args):
    before, after = os.path.abspath(args.before), os.path.abspath(args.after)
    out = {}
    for tier in args.tiers.split(","):
        for mode in args.modes.split(","):
            res = {"before": [], "after": []}
            for r in range(args.rounds):
                order = ("before", "after") if r % 2 == 0 else ("after", "before")
                for side in order:
                    res[side].append(run_one(before if side == "before" else after, tier, mode,
                                             args.timeout))
            cells = {}
            for name in res["after"][0]:
                b, a = [x[name] for x in res["before"]], [x[name] for x in res["after"]]
                same = len({(x["d"], x["s"], x["i"]) for x in b + a}) == 1
                cells[name] = dict(before=min(x["t"] for x in b), after=min(x["t"] for x in a),
                                   same=same)
                if not same:
                    print(f"MISMATCH {tier} {mode} {name}", file=sys.stderr, flush=True)
            out[f"{tier}:{mode}"] = cells
            print(f"{tier}:{mode} {sum(c['before'] for c in cells.values()):.3f} -> "
                  f"{sum(c['after'] for c in cells.values()):.3f}", flush=True)
    os.makedirs(RESULTS, exist_ok=True)
    with open(os.path.join(RESULTS, f"paired-{args.label}.json"), "w") as f:
        json.dump(out, f, indent=0)


def cmd_table(args):
    with open(os.path.join(RESULTS, f"paired-{args.label}.json")) as f:
        data = json.load(f)
    print("| workload | before (s) | after (s) | speedup | identical |")
    print("|---|---|---|---|---|")
    for w, rows in data.items():
        b = sum(r["before"] for r in rows.values())
        a = sum(r["after"] for r in rows.values())
        same = all(r["same"] for r in rows.values())
        print(f"| {w} | {b:.3f} | {a:.3f} | {b / a if a else 0:.2f} | {'yes' if same else 'NO'} |")
    if args.per_instance:
        for w, rows in data.items():
            print(f"\n{w}")
            for name, r in rows.items():
                print(f"  {name:28s} {r['before']:9.4f} {r['after']:9.4f}  "
                      f"{r['before'] / r['after'] if r['after'] else 0:6.2f}x")


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    w = sub.add_parser("worker")
    w.add_argument("root")
    w.add_argument("tier")
    w.add_argument("mode")
    r = sub.add_parser("run")
    r.add_argument("--before", required=True, help="checkout of the old code")
    r.add_argument("--after", default=ROOT)
    r.add_argument("--label", required=True)
    r.add_argument("--tiers", default="tiny,small,medium,hard,large,xl")
    r.add_argument("--modes", default="full,ir0")
    r.add_argument("--rounds", type=int, default=3)
    r.add_argument("--timeout", type=float, default=590)
    t = sub.add_parser("table")
    t.add_argument("--label", required=True)
    t.add_argument("--per-instance", action="store_true")
    args = ap.parse_args()
    if args.cmd == "worker":
        worker(args.root, args.tier, args.mode)
    elif args.cmd == "run":
        cmd_run(args)
    else:
        cmd_table(args)


if __name__ == "__main__":
    main()
