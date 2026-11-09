"""Paired before/after timings of the canonical and bounded paths: the code of two
source trees run on the same instances, alternating, in fresh processes.

    python3 bench/w23.py run --base DIR --label NAME [--rounds 3] [--no-ck]
    python3 bench/w23.py table --label NAME

DIR is a checkout of the "before" commit with its kernel built (the kernel of this
tree must be built too). Each round runs every family once in each tree, the order of
the trees alternating between rounds, one process at a time; a cell is the minimum over
the rounds. canon = both canonical labelings of a pair (X, relabelled or twisted Y);
biso = bounded_iso_lists(X, Y), the isomorphism test with Aut(X). Digests of the
canonical form, the labelling, the generators and the bounded_iso result are compared
between the trees and between rounds; bench/canon.py and bench/run.py remain the
correctness checks. Results go to bench/results/w23-LABEL.json.
"""
import argparse
import hashlib
import json
import os
import random
import subprocess
import sys
import time

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
RESULTS = os.path.join(ROOT, "bench", "results")
SPEC = [("cube", (6, 8, 9, 10, 11, 12)), ("cfix", (20, 40, 80, 160, 320)), ("mzgen", (25, 50, 100, 150)),
        ("reg3", (200, 1000, 4000)), ("reg4", (1000, 4000)), ("ns", (16, 32, 64, 112, 160, 256)),
        ("nsr", (32, 64)), ("nst", (16, 32, 64))]

WORKER = r"""
import hashlib, json, random, sys, time
root = sys.argv[1]
sys.path.insert(0, root)
sys.setrecursionlimit(100000)
from bench import canon as bc
from gi.canon import canonical_labeling_lists, _form_of
from gi.bounded import bounded_iso_lists
from gi.kernel import active


def d(x):
    return hashlib.sha256(repr(x).encode()).hexdigest()[:12]


rows = []
for fam, sizes in json.loads(sys.argv[2]):
    for size in sizes:
        for I in bc.FAMILIES[fam](size, random.Random(7919 * size)):
            X, Y = I["X"], I["Y"]
            t0 = time.perf_counter()
            lx, gx = canonical_labeling_lists(X)
            ly, _ = canonical_labeling_lists(Y)
            t1 = time.perf_counter()
            r = bounded_iso_lists(X, Y)
            t2 = time.perf_counter()
            fx, fy = _form_of(X, lx, None), _form_of(Y, ly, None)
            rows.append(dict(name=I["name"], n=len(X), canon=t1 - t0, biso=t2 - t1, same=fx == fy,
                             form=d((fx, fy)), lab=d((lx, ly)), gens=d(gx), iso=d(r), active=active()))
print(json.dumps(rows))
"""


def run_tree(tree, spec, no_ck):
    env = dict(os.environ)
    env.pop("GI_NO_CKERNEL", None)
    if no_ck:
        env["GI_NO_CKERNEL"] = "1"
    p = subprocess.run(["nice", "-n", "19", sys.executable, "-c", WORKER, tree, json.dumps(spec)],
                       env=env, capture_output=True, text=True, check=True)
    return json.loads(p.stdout.strip().splitlines()[-1])


def cmd_run(args):
    spec = SPEC
    if args.only:
        spec = [(f, s) for f, s in SPEC if f in args.only.split(",")]
    best = {}
    meta = {}
    for rnd in range(args.rounds):
        order = [("base", args.base), ("new", ROOT)]
        if rnd % 2:
            order.reverse()
        for which, tree in order:
            for row in run_tree(tree, spec, args.no_ck):
                k = (row["name"], which)
                b = best.setdefault(k, dict(row))
                b["canon"] = min(b["canon"], row["canon"])
                b["biso"] = min(b["biso"], row["biso"])
                for f in ("form", "lab", "gens", "iso"):
                    if row[f] != b[f]:
                        raise SystemExit(f"nondeterministic output: {k} {f}")
                meta[row["name"]] = row["n"]
        print(f"round {rnd + 1}/{args.rounds} done", flush=True)
    rows = []
    for name, n in meta.items():
        b, a = best[(name, "base")], best[(name, "new")]
        rows.append(dict(name=name, n=n, canon_before=round(b["canon"], 4), canon_after=round(a["canon"], 4),
                         biso_before=round(b["biso"], 4), biso_after=round(a["biso"], 4),
                         same_form=b["form"] == a["form"], same_lab=b["lab"] == a["lab"],
                         same_gens=b["gens"] == a["gens"], same_iso=b["iso"] == a["iso"],
                         decision=a["same"], active_before=b["active"], active_after=a["active"]))
    path = os.path.join(RESULTS, f"w23-{args.label}.json")
    with open(path, "w") as fh:
        json.dump(dict(label=args.label, rounds=args.rounds, no_ck=args.no_ck, rows=rows), fh, indent=1)
    print(path)


def cmd_table(args):
    rows = json.load(open(os.path.join(RESULTS, f"w23-{args.label}.json")))["rows"]
    print("| instance | n | canon before | canon after | ratio | biso before | biso after | ratio | form | lab | gens | iso |")
    print("|---|---|---|---|---|---|---|---|---|---|---|---|")
    for r in rows:
        f = lambda k: "=" if r[k] else "DIFF"
        print(f"| {r['name']} | {r['n']} | {r['canon_before']:.3f} | {r['canon_after']:.3f} | "
              f"{r['canon_before'] / r['canon_after']:.1f} | {r['biso_before']:.3f} | {r['biso_after']:.3f} | "
              f"{r['biso_before'] / r['biso_after']:.1f} | {f('same_form')} | {f('same_lab')} | {f('same_gens')} | {f('same_iso')} |")


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run")
    r.add_argument("--base", required=True)
    r.add_argument("--label", required=True)
    r.add_argument("--rounds", type=int, default=3)
    r.add_argument("--only", default="")
    r.add_argument("--no-ck", action="store_true")
    t = sub.add_parser("table")
    t.add_argument("--label", required=True)
    args = ap.parse_args()
    {"run": cmd_run, "table": cmd_table}[args.cmd](args)


if __name__ == "__main__":
    main()
