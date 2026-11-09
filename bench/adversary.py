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
  mpi    [k]  the multipede of bench/irhard.py hung under a balanced tree whose
              siblings are told apart by pendant paths: every foot pair and the
              4 middles of every row are twins of a tree leaf, with the same hub
              (degree 9). Built to put the multipede in one phase-2 layer, but
              gi.canon picks its root edge elsewhere and the layers split it: what
              this family actually attacks is perm_canon (iso and twist pairs
              follow the multipede lemma). ir_canon's own exponential growth is
              measured by "irdirect" below, on the multipede as a colored graph.

    python3 bench/adversary.py paired --base DIR --family tm --sizes 3,4,5,6 --timeout 60 --label NAME

runs the two source trees alternately on the same instances (a fresh process per
instance and tree, one at a time, under `nice`); a timeout is reported as such.
Results go to bench/results/adversary-NAME.json.

    python3 bench/adversary.py handoff [--budget 50000] [--copies 8]

shows that a node budget handing off from perm_canon to the Luks canonizer is not
canonical: relabelled copies of one graph (tb4, depth 2) get different forms.

    python3 bench/adversary.py irdirect --sizes 4,8,16,32,64 --timeout 90

counts the search nodes of ir_canon called directly on rigid multipedes colored by
foot pair and by row.
"""
import argparse
import inspect
import itertools
import json
import os
import random
import re
import signal
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


def multipede_under_tree(rows, nw, rhs):
    """The multipede R(B, rhs) (bench/irhard.py) hung under a balanced binary
    tree: each foot pair and each row's four middles are the children of a tree
    leaf, siblings of the tree differ by pendant paths, and the root carries
    a tail of length 6; the hub with a twin triple is added by the caller.
    All feet and middles have the same distance from the root."""
    nbr = [[] for _ in range(2 * nw)]
    blocks = [[2 * w, 2 * w + 1] for w in range(nw)]
    for r, ws in zip(rhs, rows):
        mids = []
        for bits in itertools.product((0, 1), repeat=len(ws)):
            if sum(bits) % 2 != r:
                continue
            m = len(nbr)
            nbr.append([2 * w + b for w, b in zip(ws, bits)])
            for f in nbr[m]:
                nbr[f].append(m)
            mids.append(m)
        blocks.append(mids)
    level = []
    D = 1
    while (1 << D) < len(blocks):
        D += 1
    for i in range(1 << D):
        v = len(nbr)
        nbr.append([])
        if i < len(blocks):
            for b in blocks[i]:
                nbr[v].append(b)
                nbr[b].append(v)
        level.append(v)
    while len(level) > 1:
        nxt = []
        for i in range(0, len(level), 2):
            v = len(nbr)
            nbr.append([])
            for j, c in enumerate(level[i:i + 2]):
                nbr[v].append(c)
                nbr[c].append(v)
                prev = c
                for _ in range(1 + j):
                    u = len(nbr)
                    nbr.append([prev])
                    nbr[prev].append(u)
                    prev = u
            nxt.append(v)
        level = nxt
    root = level[0]
    prev = root
    for _ in range(6):
        u = len(nbr)
        nbr.append([prev])
        nbr[prev].append(u)
        prev = u
    return nbr, root


def fam_mpi(k, rng):
    while True:
        rows, nw = irhard.ns_base(k, rng)
        if not irhard.check_ns_lemma(rows, nw):
            break
    nv = len(rows)
    cs, cols = irhard.col_space(rows, nw)
    x = [rng.randrange(2) for _ in range(nw)]
    r_iso = [sum(x[w] for w in r) % 2 for r in rows]
    cand = [v for v in range(nv) if irhard._reduce(cs, 1 << v)]
    g = lambda rhs: add_triple(*multipede_under_tree(rows, nw, rhs))
    X = g([0] * nv)
    out = [dict(name=f"mpi{k}", X=X, Y=relabeled(g(r_iso), rng), claim=True, aut=None, cert="lemma")]
    if cand:
        v = rng.choice(cand)
        out.append(dict(name=f"mpi{k}-twist", X=X, Y=relabeled(g([int(i == v) for i in range(nv)]), rng), claim=False,
                        aut=None, cert="lemma"))
    return out


FAMILIES = dict(cfi3=fam_cfi3, tm=_fam_tree(2), tb3=_fam_tree(3), tb4=_fam_tree(4), cfit=fam_cfit, nst3=fam_nst3, mpi=fam_mpi)


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


def _patched(fn, old, new, **extra):
    """fn recompiled with old replaced by new in its source, in its module's
    namespace plus extra (for counting and limiting its search nodes)."""
    src = inspect.getsource(fn)
    if old not in src:
        raise SystemExit("the source of %s changed" % fn.__name__)
    ns = dict(vars(sys.modules[fn.__module__]))
    ns.update(extra)
    exec(src.replace(old, new, 1), ns)
    return ns[fn.__name__]


def cmd_handoff(args):
    import gi.canon as C
    from gi.group import PermGroup

    class Over(Exception):
        pass

    budget = [0]
    search = _patched(C.perm_canon, "nodes[0] += 1", "nodes[0] += 1\n        if nodes[0] > BUDGET[0]:\n            raise Over()",
                      BUDGET=budget, Over=Over)
    luks = C.luks_canon_group
    tally = [0, 0]

    def hybrid(P, x, stats=None, limit=None):
        try:
            F, lam, gens = search(P, x, None)
        except Over:
            tally[1] += 1
            return luks(P, x, stats, limit)
        tally[0] += 1
        return F, lam, (PermGroup(P.n, gens) if gens else PermGroup(P.n))

    C.luks_canon_group = hybrid
    rng = random.Random(3)
    X = tree_matching(4, 2, rng)
    copies = [X] + [relabeled(X, rng) for _ in range(args.copies - 1)]
    for B in (0, args.budget, 10 ** 9):
        budget[0] = B
        tally[:] = [0, 0]
        forms = [C.canonical_form_lists(g) for g in copies]
        print(f"budget {B:>10d}: {tally[0]} searches finished, {tally[1]} handed off, "
              f"{len(set(forms))} distinct forms among {args.copies} relabelled copies")


def cmd_irdirect(args):
    import gi.canon as C
    nodes = [0]

    class Stop(Exception):
        pass

    def stop(*a):
        raise Stop()

    search = _patched(C.ir_canon, "nodes = [0]", "nodes = NODES", NODES=nodes)
    signal.signal(signal.SIGALRM, stop)
    for k in [int(s) for s in args.sizes.split(",")]:
        rng = random.Random(k)
        while True:
            rows, nw = irhard.ns_base(k, rng)
            if not irhard.check_ns_lemma(rows, nw):
                break
        g = irhard.multipede(rows, nw, [0] * len(rows))
        col = [w // 2 for w in range(2 * nw)]
        for r in range(len(rows)):
            col += [nw + r] * 4
        nodes[0] = 0
        t0 = time.perf_counter()
        signal.setitimer(signal.ITIMER_REAL, args.timeout)
        try:
            search([list(r) for r in g], col)
            status = "ok"
        except Stop:
            status = "timeout"
        signal.setitimer(signal.ITIMER_REAL, 0)
        print(f"multipede {k:3d} n={len(g):5d}  {status:8s} {time.perf_counter() - t0:8.2f}s  ir_canon nodes {nodes[0]}", flush=True)


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
    h = sub.add_parser("handoff")
    h.add_argument("--budget", type=int, default=50000)
    h.add_argument("--copies", type=int, default=8)
    d = sub.add_parser("irdirect")
    d.add_argument("--sizes", required=True)
    d.add_argument("--timeout", type=float, default=90)
    args = ap.parse_args()
    {"paired": cmd_paired, "handoff": cmd_handoff, "irdirect": cmd_irdirect}[args.cmd](args)


if __name__ == "__main__":
    main()
