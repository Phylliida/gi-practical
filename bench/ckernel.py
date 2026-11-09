"""Paired timings of the compiled kernel: the same code with it off and on.

    python3 bench/ckernel.py run --label NAME [--rounds 2]    # alternates off, on
    python3 bench/ckernel.py table --label NAME

Each workload runs in a fresh process per mode, off and on alternating, and a
cell is the minimum over the rounds of solver time alone (bench/run.py's times
include its sympy verification). Outputs are compared too: the sigma and
generators, or the labelling and generators, must be identical in both modes,
and a mismatch is reported. bench/run.py, bench/irhard.py and bench/canon.py
remain the correctness checks; run them in both modes.
"""
import argparse
import hashlib
import json
import os
import random
import subprocess
import sys
import time

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
sys.path.insert(0, ROOT)
sys.setrecursionlimit(100000)
RESULTS = os.path.join(ROOT, "bench", "results")

TIERS = ("tiny", "small", "medium", "hard", "large", "xl")
SPARSE = [("ns", "ns", (16, 32, 64, 112, 144), "biso"), ("ns", "ns", (16, 32, 64, 112, 144), "canon"),
          ("cfix", "cfix", (20, 40, 80, 160, 320), "biso"), ("cfix", "cfix", (20, 40, 80, 160, 320), "canon"),
          ("reg3", "reg3", (500, 1000, 2000, 4000), "biso"), ("reg3", "reg3", (500, 1000, 2000, 4000), "canon"),
          ("cube", "cube", (6, 8, 9, 10, 11), "biso"), ("cube", "cube", (6, 8, 9, 10, 11), "canon")]


def digest(x):
    return hashlib.sha256(repr(x).encode()).hexdigest()[:16]


def worker(which):
    from gi import graph_iso, Solver
    from gi.bounded import bounded_iso_lists
    from gi.canon import canonical_labeling_lists
    from gi.kernel import active
    rows = {}

    def timed(key, f):
        t0 = time.perf_counter()
        r = f()
        rows[key] = dict(t=time.perf_counter() - t0, d=digest(r))

    if which.startswith("tier:"):
        from bench.families import instances
        _, tier, ir = which.split(":")
        kw = {} if ir == "full" else {"ir": 0}
        for name, t, X, Y, _, _ in instances(tiers={tier}):
            if t == tier:
                timed(name, lambda: graph_iso(X, Y, solver=Solver(certificates=False), **kw))
    else:
        from bench import canon as bc
        _, fam, sizes, mode = which.split(":")
        for s in sizes.split(","):
            for I in bc.FAMILIES[fam](int(s), random.Random(0)):
                X, Y = I["X"], I["Y"]
                if mode == "biso":
                    timed(I["name"], lambda: bounded_iso_lists(
                        X, Y, solver=Solver(cameron_no_enum=True, certificates=False)))
                else:
                    timed(I["name"], lambda: (canonical_labeling_lists(X),
                                              canonical_labeling_lists(Y)))
    print(json.dumps(dict(active=active(), rows=rows)))


def workloads(ir0):
    w = [f"tier:{t}:full" for t in TIERS]
    if ir0:
        w += ["tier:large:ir0"]
    for _, fam, sizes, mode in SPARSE:
        w.append("sparse:" + fam + ":" + ",".join(map(str, sizes)) + ":" + mode)
    return w


def cmd_run(args):
    out = {}
    for w in (args.only.split(";") if args.only else workloads(args.ir0)):
        res = {}
        for r in range(args.rounds):
            # off and on alternate; the second round reverses the order
            order = ("off", "on") if r % 2 == 0 else ("on", "off")
            for mode in order:
                env = dict(os.environ)
                env.pop("GI_NO_CKERNEL", None)
                if mode == "off":
                    env["GI_NO_CKERNEL"] = "1"
                p = subprocess.run([sys.executable, __file__, "worker", w], env=env, check=True,
                                   capture_output=True, text=True, timeout=args.timeout)
                d = json.loads(p.stdout.strip().splitlines()[-1])
                if d["active"] != (mode == "on"):
                    raise RuntimeError(f"{w}: mode {mode}, but active={d['active']}")
                res.setdefault(mode, []).append(d["rows"])
        for name in res["on"][0]:
            off = [x[name] for x in res["off"]]
            on = [x[name] for x in res["on"]]
            same = len({x["d"] for x in off + on}) == 1
            cell = dict(off=min(x["t"] for x in off), on=min(x["t"] for x in on), same=same)
            out.setdefault(w, {})[name] = cell
            if not same:
                print(f"MISMATCH {w} {name}", file=sys.stderr)
        print(w, "done", flush=True)
    os.makedirs(RESULTS, exist_ok=True)
    with open(os.path.join(RESULTS, f"ckernel-{args.label}.json"), "w") as f:
        json.dump(out, f, indent=0)


def cmd_table(args):
    with open(os.path.join(RESULTS, f"ckernel-{args.label}.json")) as f:
        data = json.load(f)
    print("| workload | off (s) | on (s) | speedup | identical |")
    print("|---|---|---|---|---|")
    for w, rows in data.items():
        off = sum(r["off"] for r in rows.values())
        on = sum(r["on"] for r in rows.values())
        all_same = all(r["same"] for r in rows.values())
        print(f"| {w} | {off:.3f} | {on:.3f} | {off / on:.2f} | {'yes' if all_same else 'NO'} |")
    if args.per_instance:
        for w, rows in data.items():
            print(f"\n{w}")
            for name, r in rows.items():
                print(f"  {name:28s} {r['off']:9.4f} {r['on']:9.4f}  {r['off'] / r['on']:6.2f}x")


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    w = sub.add_parser("worker")
    w.add_argument("which")
    r = sub.add_parser("run")
    r.add_argument("--label", required=True)
    r.add_argument("--rounds", type=int, default=2)
    r.add_argument("--timeout", type=float, default=590)
    r.add_argument("--only", default="", help='workloads separated by ";"')
    r.add_argument("--ir0", action="store_true", help="also the large tier with ir=0")
    t = sub.add_parser("table")
    t.add_argument("--label", required=True)
    t.add_argument("--per-instance", action="store_true")
    args = ap.parse_args()
    if args.cmd == "worker":
        worker(args.which)
    elif args.cmd == "run":
        cmd_run(args)
    else:
        cmd_table(args)


if __name__ == "__main__":
    main()
