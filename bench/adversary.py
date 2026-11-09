"""Adversarial families for canonical labeling at bounded degree, built in w40
(docs/w40-solvable.md Sec. 2): inputs on which the old search canonizers
(perm_canon, ir_canon) of gi.canon are exponential, and the guaranteed path is
polynomial. Families (in bench/canon.py as well; every instance has a known
answer, checked by bench/canon.py):

  cfi3   [b]  CFI over Z_3 on a random cubic base with b vertices (degree 4):
              the layer groups are abelian but not 2-groups. iso: two twists
              summing to 0 mod 3; twist: one twist (total nonzero: not
              isomorphic to the untwisted graph, see cfi3 below).
  tm     [k]  a perfect binary tree of depth k with a tail on its root and a
              random perfect matching on its leaves (degree 3).
  tb3, tb4 [k]  the same with branching 3 and 4 (degree 4, 5).
  cfit   [b]  CFI over Z_2 on a random cubic base, plus a hub carrying a twin
              triple, which makes the layer group non-elementary-abelian from
              the hub on (degree 4); iso and twist pairs as CFI.
  nst3   [k]  a shrunken multipede (bench/irhard.py) with the same hub.

    python3 bench/adversary.py paired --base DIR --family tm --sizes 3,4,5,6 --timeout 60 --label NAME

runs the two source trees alternately on the same instances (a fresh process per
instance and tree, one at a time, under `nice`); a timeout is reported as such.
Results go to bench/results/adversary-NAME.json.
"""
import argparse
import hashlib
import itertools
import json
import os
import random
import re
import subprocess
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.setrecursionlimit(100000)

from bench import irhard

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
RESULTS = os.path.join(ROOT, "bench", "results")


def relabeled(nbr, rng):
    return irhard.relabeled(nbr, rng)


def add_triple(nbr, v=0):
    """nbr with a hub attached to vertex v, the hub carrying three leaves (a
    twin triple: a Sym(3) direct factor of the group, so every later layer group
    of gi.canon is non-elementary-abelian)."""
    n = len(nbr)
    out = [list(r) for r in nbr]
    out[v].append(n)
    out.append([v, n + 1, n + 2, n + 3])
    out.extend([[n], [n], [n]])
    return out


def cfi3(b, E, twist):
    """CFI over Z_3 on the cubic base (b vertices, edge list E): outer vertices
    (v, e, a) for a in Z_3, one inner vertex per (a_e)_{e at v} with sum 0
    adjacent to the (v, e, a_e), and (u, e, a) ~ (v, e, -a + t_e) for an edge
    e = {u, v} (t = twist.get(e, 0)). Degree 4 (inner: 3; outer: 3 + 1).

    Isomorphism class: a coordinate shift g(v, e) with sum 0 at every v changes
    t_e by g(u, e) + g(v, e), so sum_e t_e is unchanged, and any twist
    difference of total 0 is such a shift when the base is connected; a global
    negation of the coordinates maps t to -t. So with total 0 the graph is
    isomorphic to the untwisted one; with total +-1 it is not."""
    inc = [[] for _ in range(b)]
    for ei, (u, v) in enumerate(E):
        inc[u].append(ei)
        inc[v].append(ei)
    nbr, outer = [], {}
    for v in range(b):
        for ei in inc[v]:
            for c in range(3):
                outer[(v, ei, c)] = len(nbr)
                nbr.append([])
    for v in range(b):
        for bits in itertools.product(range(3), repeat=len(inc[v])):
            if sum(bits) % 3:
                continue
            m = len(nbr)
            nbr.append([outer[(v, ei, c)] for ei, c in zip(inc[v], bits)])
            for o in nbr[m]:
                nbr[o].append(m)
    for ei, (u, v) in enumerate(E):
        t = twist.get(ei, 0)
        for c in range(3):
            p, q = outer[(u, ei, c)], outer[(v, ei, (-c + t) % 3)]
            nbr[p].append(q)
            nbr[q].append(p)
    return nbr


def tree_matching(b, k, rng):
    """The perfect b-ary tree of depth k with a tail of length 3 on its root, and
    a random perfect matching on the leaves (one leaf is left out if their number
    is odd)."""
    nbr = [[]]
    level = [0]
    for _ in range(k):
        nxt = []
        for p in level:
            for _ in range(b):
                v = len(nbr)
                nbr.append([p])
                nbr[p].append(v)
                nxt.append(v)
        level = nxt
    leaves = level[:]
    rng.shuffle(leaves)
    for i in range(0, len(leaves) - 1, 2):
        u, v = leaves[i], leaves[i + 1]
        nbr[u].append(v)
        nbr[v].append(u)
    n = len(nbr)
    nbr[0].append(n)
    nbr.append([0, n + 1])
    nbr.append([n, n + 2])
    nbr.append([n + 1])
    return nbr


def fam_cfi3(b, rng):
    E = irhard.random_cubic(b, rng)
    X = cfi3(b, E, {})
    i, j = rng.sample(range(len(E)), 2)
    return [dict(name=f"cfi3-{b}", X=X, Y=relabeled(cfi3(b, E, {i: 1, j: 2}), rng), claim=True, aut=None,
                 cert="cfi3 twist sum"),
            dict(name=f"cfi3-{b}-twist", X=X, Y=relabeled(cfi3(b, E, {i: 1}), rng), claim=False, aut=None,
                 cert="cfi3 twist sum")]


def _fam_tree(b):
    def f(k, rng):
        X = tree_matching(b, k, rng)
        Z = tree_matching(b, k, rng)
        return [dict(name=f"tb{b}-{k}", X=X, Y=relabeled(X, rng), claim=True, aut=None, cert="relabel"),
                dict(name=f"tb{b}-{k}-other", X=X, Y=relabeled(Z, rng), claim=None, aut=None, cert="nauty")]
    return f


def fam_cfit(b, rng):
    E = irhard.random_cubic(b, rng)
    X = add_triple(irhard.cfi_lists(b, E, set()))
    i, j = rng.sample(range(len(E)), 2)
    return [dict(name=f"cfit-{b}", X=X, Y=relabeled(add_triple(irhard.cfi_lists(b, E, {i, j})), rng), claim=True,
                 aut=None, cert="cfi"),
            dict(name=f"cfit-{b}-twist", X=X, Y=relabeled(add_triple(irhard.cfi_lists(b, E, {i})), rng), claim=False,
                 aut=None, cert="cfi")]


def fam_nst3(k, rng):
    I = irhard.fam_ns(k, rng)[0]
    X = add_triple(I["X"])
    return [dict(name=f"nst3-{k}", X=X, Y=relabeled(X, rng), claim=True, aut=None, cert="relabel")]


FAMILIES = dict(cfi3=fam_cfi3, tm=_fam_tree(2), tb3=_fam_tree(3), tb4=_fam_tree(4), cfit=fam_cfit, nst3=fam_nst3)


WORKER = r"""
import hashlib, json, sys, time
sys.path.insert(0, sys.argv[1])
sys.setrecursionlimit(100000)
from collections import Counter
from gi.canon import canonical_labeling_lists, _form_of
d = json.load(sys.stdin)
st = Counter()
t0 = time.perf_counter()
lx, gx = canonical_labeling_lists(d["X"], stats=st)
ly, _ = canonical_labeling_lists(d["Y"], stats=st)
t = time.perf_counter() - t0
fx, fy = _form_of(d["X"], lx, None), _form_of(d["Y"], ly, None)
keep = {k: v for k, v in st.items() if k.startswith("canon_")}
print(json.dumps(dict(time=t, same=fx == fy, ngens=len(gx), stats=keep,
                      form=hashlib.sha256(repr((fx, fy)).encode()).hexdigest()[:12])))
"""


def run_tree(tree, I, timeout):
    t0 = time.perf_counter()
    try:
        p = subprocess.run(["nice", "-n", "19", sys.executable, "-c", WORKER, tree], capture_output=True, text=True,
                           input=json.dumps(dict(X=I["X"], Y=I["Y"])), timeout=timeout)
    except subprocess.TimeoutExpired:
        return dict(status="timeout", time=timeout)
    if p.returncode != 0:
        return dict(status="error", time=time.perf_counter() - t0, note=p.stderr[-400:])
    out = json.loads(p.stdout.strip().splitlines()[-1])
    out["status"] = "ok"
    return out


def cmd_paired(args):
    fam = FAMILIES[args.family]
    rows = []
    for size in [int(s) for s in args.sizes.split(",")]:
        rng = random.Random(7919 * size + args.seed)
        for I in fam(size, rng):
            if args.only and not re.search(args.only, I["name"]):
                continue
            row = dict(name=I["name"], family=args.family, size=size, n=len(I["X"]), maxdeg=max(map(len, I["X"])),
                       claim=I["claim"], cert=I["cert"])
            best = {}
            for rnd in range(args.rounds):
                order = [("before", args.base), ("after", ROOT)]
                if rnd % 2:
                    order.reverse()
                for which, tree in order:
                    if which in best and best[which]["status"] == "timeout":
                        continue
                    r = run_tree(tree, I, args.timeout)
                    if which not in best or (r["status"] == "ok" and r["time"] < best[which]["time"]):
                        best[which] = r
            row.update(best)
            claim = I["claim"]
            for which in ("before", "after"):
                if best[which]["status"] == "ok" and claim is not None and best[which]["same"] != claim:
                    best[which]["status"] = "WRONG"
            print(f"{I['name']:16s} n={row['n']:5d} deg {row['maxdeg']}  "
                  f"before {best['before']['status']:8s} {best['before']['time']:8.3f}s  "
                  f"after {best['after']['status']:8s} {best['after']['time']:8.3f}s", flush=True)
            rows.append(row)
            os.makedirs(RESULTS, exist_ok=True)
            with open(os.path.join(RESULTS, f"adversary-{args.label}.json"), "w") as fh:
                json.dump(dict(label=args.label, timeout=args.timeout, rows=rows), fh, indent=1)


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("paired")
    p.add_argument("--base", required=True)
    p.add_argument("--family", required=True, choices=sorted(FAMILIES))
    p.add_argument("--sizes", required=True)
    p.add_argument("--timeout", type=float, default=60)
    p.add_argument("--label", required=True)
    p.add_argument("--only", default="")
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--rounds", type=int, default=1)
    args = ap.parse_args()
    {"paired": cmd_paired}[args.cmd](args)


if __name__ == "__main__":
    main()
