"""Canonical labeling benchmarks: gi.canon (canonical Luks reduction, pure
Python) against nauty's canonical labeling, on bounded-degree families.

    PY=../r2-hybrid/.venv/bin/python          # pynauty, networkx, sympy
    nice $PY bench/canon.py run --family ns --sizes 16,32,64 --modes canon,pyn,dnd,dns,dnt \\
        --timeout 600 --label ns
    $PY bench/canon.py table --label ns

Modes (each computes the canonical forms of both graphs of a pair X, Y and
compares them; times are for the two canonical forms, construction and I/O
excluded):
  canon  gi.canon.canonical_labeling_lists on X and on Y (in process, wall
         time); its decision is form(X) == form(Y);
  biso   for reference: gi.bounded.bounded_iso_lists(X, Y), the isomorphism
         test with Aut(X) (no canonical forms), in process ("iso" is an alias);
  pyn    pynauty 2.8.8.1 certificate(X), certificate(Y) (dense nauty, default
         options), in a subprocess so that the timeout can stop it;
  dnd, dns, dnt  dreadnaut (nauty 2.9.1): dense nauty (Ad), sparse nauty (As),
         Traces (At) with canonical labeling on ("c"), X then Y; the time is
         the sum of the two reported cpu times (as bench/irhard.py).
Per graph times are kept as well (t_x, t_y).

Families: ns, nsr, nst, cfix (from bench/irhard.py, where the answers are
known: Neuen-Schweitzer's lemma, CFI); reg3, reg4 [n] (random connected
d-regular graph: a relabeled copy, and a second random graph whose answer
comes from gi.bounded.bounded_iso_lists and nauty); cube [d] (hypercube Q_d
and a relabeled copy, |Aut| = 2^d d!).

Checks (every run of canon): lab is a bijection and relabels X onto the
form; every generator is an automorphism; |<gens>| (gi.group.PermGroup) equals
the known |Aut| (lemma, hypercube formula, or nauty's grpsize where nauty
finished, else the order of gi.bounded's group); the decision equals
the known answer. A wrong answer is reported as WRONG. Results go to
bench/results/canon-LABEL.json.
"""
import argparse
import hashlib
import json
import math
import os
import random
import re
import signal
import subprocess
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.setrecursionlimit(100000)

import networkx as nx

from gi.canon import canonical_labeling_lists, _form_of
from gi.bounded import bounded_iso_lists
from gi.group import PermGroup
from bench import irhard, adversary

RESULTS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")


class Timeout(Exception):
    pass


def _alarm(signum, frame):
    raise Timeout()


def lists_of(G):
    nodes = sorted(G.nodes(), key=repr)
    idx = {v: i for i, v in enumerate(nodes)}
    nb = [[] for _ in nodes]
    for u, v in G.edges():
        nb[idx[u]].append(idx[v])
        nb[idx[v]].append(idx[u])
    return nb


def connected_regular(d, n, seed):
    while True:
        G = nx.random_regular_graph(d, n, seed=seed)
        if nx.is_connected(G):
            return G
        seed += 1


def fam_reg(d):
    def f(n, rng):
        X = lists_of(connected_regular(d, n, 7 * n + d))
        Z = lists_of(connected_regular(d, n, 7 * n + d + 100000))
        return [dict(name=f"{d}reg{n}", X=X, Y=irhard.relabeled(X, rng), claim=True, aut=None,
                     cert="relabel"),
                dict(name=f"{d}reg{n}-other", X=X, Y=irhard.relabeled(Z, rng), claim=None, aut=None,
                     cert="bounded_iso")]
    return f


def fam_cube(d, rng):
    X = lists_of(nx.hypercube_graph(d))
    return [dict(name=f"Q{d}", X=X, Y=irhard.relabeled(X, rng), claim=True,
                 aut=2 ** d * math.factorial(d), cert="formula")]


FAMILIES = dict(ns=irhard.fam_ns, nsr=irhard.fam_nsr, nst=irhard.fam_nst, cfix=irhard.fam_cfix,
                reg3=fam_reg(3), reg4=fam_reg(4), cube=fam_cube, mzgen=irhard.fam_mzgen,
                **adversary.FAMILIES)           # (docs/w40-solvable.md)


# -- the modes -------------------------------------------------------------------------------
def run_canon(I, timeout):
    signal.signal(signal.SIGALRM, _alarm)
    out = {}
    signal.setitimer(signal.ITIMER_REAL, timeout)
    try:
        res = []
        for G in (I["X"], I["Y"]):
            t0 = time.perf_counter()
            lab, gens = canonical_labeling_lists(G)
            res.append((time.perf_counter() - t0, lab, gens))
        signal.setitimer(signal.ITIMER_REAL, 0)
    except Timeout:
        return dict(status="timeout", time=timeout)
    (tx, lx, gx), (ty, ly, _) = res
    I["_order"] = None
    fx, fy = _form_of(I["X"], lx, None), _form_of(I["Y"], ly, None)
    out = dict(status="ok", time=round(tx + ty, 3), t_x=round(tx, 3), t_y=round(ty, 3),
               same=fx == fy, ngens=len(gx))
    err = check_canon(I, lx, gx, fx)
    if err:
        out.update(status="WRONG", note=err)
    out["aut_order"] = I["_order"]
    return out


def check_canon(I, lab, gens, form):
    X = I["X"]
    n = len(X)
    if sorted(lab) != list(range(n)):
        return "not a bijection"
    E = set((u, v) for u in range(n) for v in X[u])
    if form[2] != tuple(sorted(min(lab[u], lab[v]) * n + max(lab[u], lab[v])
                               for u, v in E if u < v)):
        return "form is not X relabeled"
    for g in gens:
        if any((g[u], g[v]) not in E for u, v in E):
            return "a generator is not an automorphism"
    I["_order"] = PermGroup(n, gens).order() if gens else 1
    return ""


PYN_CHILD = r"""
import sys, json, time, hashlib, pynauty
d = json.load(sys.stdin)
out = []
for nb in d:
    g = pynauty.Graph(len(nb), adjacency_dict={i: nb[i] for i in range(len(nb))})
    t = time.perf_counter()
    c = pynauty.certificate(g)
    out.append([time.perf_counter() - t, hashlib.sha1(c).hexdigest()])
print(json.dumps(out))
"""


def run_pyn(I, timeout):
    try:
        p = subprocess.run(["nice", "-n", "19", sys.executable, "-c", PYN_CHILD],
                           input=json.dumps([I["X"], I["Y"]]), capture_output=True, text=True,
                           timeout=timeout)
    except subprocess.TimeoutExpired:
        return dict(status="timeout", time=timeout)
    if p.returncode != 0:
        return dict(status="error", time=0, note=p.stderr[-300:])
    (tx, cx), (ty, cy) = json.loads(p.stdout)
    return dict(status="ok", time=round(tx + ty, 3), t_x=round(tx, 3), t_y=round(ty, 3),
                same=cx == cy)


def run_dreadnaut(I, alg, timeout):
    script = [f"$=0 {alg} -a -m c", irhard._dre_graph(I["X"]), "x @", irhard._dre_graph(I["Y"]),
              "x #", "q"]
    try:
        p = subprocess.run(["nice", "-n", "19", irhard.DREADNAUT], input="\n".join(script) + "\n",
                           capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return dict(status="timeout", time=timeout)
    out = p.stdout
    cpu = [float(c) for c in re.findall(r"cpu time = ([0-9.]+)", out)]
    grp = re.findall(r"grpsize=([0-9.e+]+)", out)
    if len(cpu) < 2 or ("are identical" not in out and "are different" not in out):
        return dict(status="error", time=0, note=out[-300:])
    return dict(status="ok", time=round(sum(cpu), 3), t_x=cpu[0], t_y=cpu[1],
                same="are identical" in out, aut=float(grp[0]) if grp else None)


def run_iso(I, timeout):
    """gi.bounded.bounded_iso_lists(X, Y) (isomorphism and Aut(X), no
    canonical form), for reference."""
    signal.signal(signal.SIGALRM, _alarm)
    signal.setitimer(signal.ITIMER_REAL, timeout)
    try:
        t0 = time.perf_counter()
        res = bounded_iso_lists(I["X"], I["Y"])
        dt = time.perf_counter() - t0
        signal.setitimer(signal.ITIMER_REAL, 0)
    except Timeout:
        return dict(status="timeout", time=timeout)
    return dict(status="ok", time=round(dt, 3), same=res is not None)


def run_mode(I, mode, timeout):
    if mode == "canon":
        return run_canon(I, timeout)
    if mode == "biso":
        return run_iso(I, timeout)
    if mode == "pyn":
        return run_pyn(I, timeout)
    return run_dreadnaut(I, {"dnd": "Ad", "dns": "As", "dnt": "At"}[mode], timeout)


# -- commands ---------------------------------------------------------------------------------
MODES = ("canon", "biso", "pyn", "dnd", "dns", "dnt")


def cmd_run(args):
    modes = ["biso" if m == "iso" else m for m in args.modes.split(",")]   # (alias)
    path = os.path.join(RESULTS, f"canon-{args.label}.json")
    rows = json.load(open(path))["rows"] if os.path.exists(path) and args.append else []
    dead = set()
    bad = 0
    for size in [int(s) for s in args.sizes.split(",")]:
        rng = random.Random(7919 * size + args.seed)
        insts = FAMILIES[args.family](size, rng)
        for I in insts:
            if args.only and not re.search(args.only, I["name"]):
                continue
            n = len(I["X"])
            kind = I["name"].split("-")[-1] if "-" in I["name"] else "iso"
            row = dict(name=I["name"], family=args.family, size=size, n=n, seed=args.seed,
                       maxdeg=max(map(len, I["X"])), edges=sum(map(len, I["X"])) // 2,
                       cert=I["cert"])
            expect, aut = I["claim"], I["aut"]
            for mode in sorted(modes, key=lambda m: m in ("canon", "biso")):   # nauty first
                if (mode, kind) in dead:
                    row[mode] = dict(status="skipped", time=args.timeout)
                    continue
                r = row[mode] = run_mode(I, mode, args.timeout)
                if r["status"] == "timeout" and not args.no_skip:
                    dead.add((mode, kind))
                if mode not in ("canon", "biso") and r["status"] == "ok":
                    if expect is None:
                        expect = r["same"]
                    elif r["same"] != expect:
                        r["status"] = "WRONG"
                    if aut is None and r.get("aut") and r["same"]:
                        aut = r["aut"]
            if expect is None:                  # no nauty answer: gi.bounded decides
                expect = bounded_iso_lists(I["X"], I["Y"]) is not None
                row["cert"] = "bounded_iso"
            c = row.get("biso")
            if c and c["status"] == "ok" and c["same"] != expect:
                c["status"], c["note"] = "WRONG", "wrong decision"
            c = row.get("canon")
            if c and c["status"] == "ok":
                if c["same"] != expect:
                    c["status"], c["note"] = "WRONG", "wrong decision"
                if aut is None:
                    res = bounded_iso_lists(I["X"], I["X"])
                    aut = PermGroup(n, res[1]).order() if res[1] else 1
                if abs(c["aut_order"] - aut) > 1e-9 * aut:
                    c["status"], c["note"] = "WRONG", f"|<gens>| = {c['aut_order']}, |Aut| = {aut}"
                c["aut_order"] = str(c["aut_order"])
            row["iso"], row["aut"] = expect, (None if aut is None else float(aut))
            bad += sum(row[m]["status"] == "WRONG" for m in modes)
            cells = "  ".join(f"{m}={row[m]['time']}" + ("" if row[m]["status"] == "ok"
                                                         else f"({row[m]['status']})")
                              for m in modes)
            print(f"{I['name']:16s} n={n:5d} iso={expect!s:5s} {cells}", flush=True)
            rows.append(row)
            os.makedirs(RESULTS, exist_ok=True)
            with open(path, "w") as fh:
                json.dump(dict(label=args.label, timeout=args.timeout, rows=rows), fh, indent=1)
    sys.exit(1 if bad else 0)


def load(labels):
    """The rows of the given labels; rows of the same instance (name, seed)
    from several labels are merged (later labels add modes)."""
    rows, at = [], {}
    for lab in labels.split(","):
        for r in json.load(open(os.path.join(RESULTS, f"canon-{lab}.json")))["rows"]:
            k = (r["name"], r["seed"])
            if k in at:
                at[k].update({m: r[m] for m in MODES if m in r})
            else:
                at[k] = r
                rows.append(r)
    return rows


def cmd_table(args):
    rows = load(args.label)
    modes = [m for m in MODES if any(m in r for r in rows)]

    def cell(r, m):
        v = r.get(m)
        if not isinstance(v, dict):
            return "-"
        if v["status"] in ("timeout", "skipped"):
            return f">{v['time']:.0f}"
        return f"{v['time']:.3g}" if v["status"] == "ok" else v["status"]

    print("| instance | n | iso | " + " | ".join(modes) + " | canon per graph |")
    print("|---|---|---|" + "---|" * len(modes) + "---|")
    for r in rows:
        c = r.get("canon", {})
        per = f"{c['t_x']:.3g} / {c['t_y']:.3g}" if c.get("status") == "ok" else "-"
        print(f"| {r['name']} | {r['n']} | {r['iso']} | " + " | ".join(cell(r, m) for m in modes)
              + f" | {per} |")


def cmd_fit(args):
    """t ~ n^c fits (least squares of log t on log n) per mode and kind."""
    rows = load(args.label)
    for kind in (True, False):
        for m in MODES:
            pts = sorted({r["n"]: r[m]["time"] for r in rows if r["iso"] == kind and m in r
                          and r[m]["status"] == "ok" and r[m]["time"] >= args.floor}.items())
            if len(pts) < 3:
                continue
            xs = [math.log(n) for n, _ in pts]
            ys = [math.log(t) for _, t in pts]
            mx, my = sum(xs) / len(xs), sum(ys) / len(ys)
            b = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs)
            ss = sum((y - my - b * (x - mx)) ** 2 for x, y in zip(xs, ys))
            st = sum((y - my) ** 2 for y in ys) or 1e-300
            print(f"iso={kind!s:5s} {m:6s} n={pts[0][0]}..{pts[-1][0]} ({len(pts)} pts): "
                  f"t ~ n^{b:.2f} (R2 {1 - ss / st:.3f})")


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run")
    r.add_argument("--family", required=True, choices=sorted(FAMILIES))
    r.add_argument("--sizes", required=True)
    r.add_argument("--modes", default="canon,pyn,dnd,dns,dnt")
    r.add_argument("--timeout", type=float, default=600)
    r.add_argument("--label", required=True)
    r.add_argument("--only", default="")
    r.add_argument("--seed", type=int, default=0)
    r.add_argument("--append", action="store_true")
    r.add_argument("--no-skip", action="store_true")
    t = sub.add_parser("table")
    t.add_argument("--label", required=True)
    f = sub.add_parser("fit")
    f.add_argument("--label", required=True)
    f.add_argument("--floor", type=float, default=0.05)
    args = ap.parse_args()
    {"run": cmd_run, "table": cmd_table, "fit": cmd_fit}[args.cmd](args)


if __name__ == "__main__":
    main()
