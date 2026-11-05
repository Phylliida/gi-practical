"""Bounded-degree families: Luks's reduction (gi/bounded.py, "new") against the
default pipeline (graph_iso, "default") and nauty (pynauty, "nauty").

    PY=../r2-hybrid/.venv/bin/python             # has pynauty, networkx, sympy
    nice $PY bench/bounded.py run --family cfi3 --sizes 4,6,8 --modes new,default,nauty \\
        --timeout 300 --label cfi3
    $PY bench/bounded.py table --label cfi3

Families (size parameter in brackets):
  cfi3 [b]      CFI over a random connected 3-regular base on b vertices (degree 3,
                n = 10 b), the pair (X, relabeled X) and the twisted pair;
  cfi4 [b]      the same over a 4-regular base (degree 5, n = 16 b);
  reg3 ... reg7 [n] random connected d-regular graph, relabeled copy, and a second
                random graph;
  cube [d]      hypercube Q_d (degree d, n = 2^d), relabeled copy;
  jgad [k]      k hubs with Johnson J(5,2) gadgets (degree 7), see jgad(); run it
                with the modes newh, newh0 to see (M) act;
  multipede [nv] rigid colored 3-XOR multipede on nv variables (feet of degree 4,
                gadget vertices of degree 3), isomorphic and non-isomorphic
                right-hand sides (builders copied from r3-hardness/bench/hardness.py).

Every answer is checked: the decision against nauty's certificates (and the
construction's claim), the isomorphism, each generator, and |<gens>| (sympy)
against nauty's |Aut(X)|. Modes: "new" = bounded_iso with
Solver(cameron_no_enum=True, certificates=False); "new0" = the same without
(M); "newh", "newh0" = the same with root="degree" (the root edge between
two vertices of maximum degree sum); "default" = graph_iso(X, Y, solver=Solver(certificates=False)).
Results go to bench/results/bounded-LABEL.json.
"""
import argparse
import itertools
import json
import math
import os
import random
import signal
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.setrecursionlimit(100000)

import networkx as nx

from bench.families import adj, relabel, cfi
from gi import graph_iso, Solver
from gi.bounded import bounded_iso

try:
    import pynauty
except ImportError:                     # optional
    pynauty = None


class Timeout(Exception):
    pass


def _alarm(signum, frame):
    raise Timeout()


def shuffled_colored(A, colors, rng):
    n = len(A)
    s = list(range(n))
    rng.shuffle(s)
    B = relabel(A, s)
    if colors is None:
        return B, None
    cB = [None] * n
    for i in range(n):
        cB[s[i]] = colors[i]
    return B, cB


def inst(name, A, A2, claim, rng, cx=None, cx2=None):
    B, cB = shuffled_colored(A2, cx2, rng)
    return dict(name=name, X=A, Y=B, claim=claim, cx=cx, cy=cB)


def connected_regular(d, b, seed):
    while True:
        G = nx.random_regular_graph(d, b, seed=seed)
        if nx.is_connected(G):
            return G
        seed += 1


def fam_cfi3(b, rng):
    base = connected_regular(3, b, 2000 + b)
    A = adj(cfi(base))
    return [inst(f"CFI(3reg{b})", A, A, True, rng),
            inst(f"CFI(3reg{b})-twist", A, adj(cfi(base, True)), False, rng)]


def fam_cfi4(b, rng):
    base = connected_regular(4, b, 1000 + b)
    A = adj(cfi(base))
    return [inst(f"CFI(4reg{b})", A, A, True, rng),
            inst(f"CFI(4reg{b})-twist", A, adj(cfi(base, True)), False, rng)]


def fam_reg(d):
    def f(n, rng):
        A = adj(connected_regular(d, n, 7 * n + d))
        C = adj(connected_regular(d, n, 7 * n + d + 100000))
        return [inst(f"{d}reg{n}", A, A, True, rng), inst(f"{d}reg{n}-other", A, C, None, rng)]
    return f


def fam_cube(d, rng):
    A = adj(nx.hypercube_graph(d))
    return [inst(f"Q{d}", A, A, True, rng)]


# --- multipedes (from r3-hardness/bench/hardness.py) --------------------------------
def rank_mod(rows, p):
    rows = [list(r) for r in rows]
    rk, col = 0, 0
    ncol = len(rows[0]) if rows else 0
    while rk < len(rows) and col < ncol:
        piv = next((i for i in range(rk, len(rows)) if rows[i][col] % p), None)
        if piv is None:
            col += 1
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        iv = pow(rows[rk][col], p - 2, p)
        rows[rk] = [c * iv % p for c in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][col] % p:
                f = rows[i][col]
                rows[i] = [(a - f * b) % p for a, b in zip(rows[i], rows[rk])]
        rk += 1
        col += 1
    return rk


def xor_system(nv, deg, rng, arity=3, tries=2000):
    """Random arity-XOR system: deg nv / arity equations, each variable in deg
    of them, no two sharing arity - 1 variables, full column rank over F_2
    (so the multipede is rigid)."""
    m = deg * nv // arity
    for _ in range(tries):
        pool = [v for v in range(nv) for _ in range(deg)]
        eqs, sub, ok = [], set(), True
        for _ in range(m):
            for _attempt in range(400):
                t = rng.sample(range(len(pool)), arity)
                vs = [pool[i] for i in t]
                if len(set(vs)) == arity and not any(
                        frozenset(q) in sub for q in itertools.combinations(vs, arity - 1)):
                    break
            else:
                ok = False
                break
            for i in sorted(t, reverse=True):
                pool.pop(i)
            eqs.append(tuple(sorted(vs)))
            sub.update(frozenset(q) for q in itertools.combinations(vs, arity - 1))
        if not ok:
            continue
        cols = [[1 if v in e else 0 for e in eqs] for v in range(nv)]
        if rank_mod(cols, 2) == nv:
            return eqs
    raise RuntimeError("no full-rank XOR system found")


def multipede(nv, eqs, rhs):
    """Colored graph of an XOR system: variable v has feet (v, 0), (v, 1); an
    equation with right-hand side r has one vertex per assignment of its
    variables with sum r, adjacent to the matching feet. Colors: one per
    variable and one per equation. Color-preserving isomorphisms between the
    systems (A, r), (A, r') are the flips S with A S = r + r'."""
    n = 2 * nv + sum(2 ** (len(e) - 1) for e in eqs)
    A = [[0] * n for _ in range(n)]
    colors = [v for v in range(nv) for _ in (0, 1)]
    k = 2 * nv
    for ei, (e, r) in enumerate(zip(eqs, rhs)):
        for bits in itertools.product((0, 1), repeat=len(e) - 1):
            bits = bits + ((r + sum(bits)) % 2,)
            for var, bit in zip(e, bits):
                A[k][2 * var + bit] = A[2 * var + bit][k] = 1
            colors.append(nv + ei)
            k += 1
    return A, colors


def fam_multipede(nv, rng):
    eqs = xor_system(nv, 4, rng)
    m = len(eqs)
    r = [rng.randrange(2) for _ in range(m)]
    s = [rng.randrange(2) for _ in range(nv)]
    r_iso = [(r[i] + sum(s[v] for v in e)) % 2 for i, e in enumerate(eqs)]
    cols = [[1 if v in e else 0 for e in eqs] for v in range(nv)]
    while True:
        e = [rng.randrange(2) for _ in range(m)]
        if rank_mod(cols + [e], 2) > rank_mod(cols, 2):
            break
    r_non = [(a + b) % 2 for a, b in zip(r, e)]
    A, c = multipede(nv, eqs, r)
    B1, c1 = multipede(nv, eqs, r_iso)
    B2, c2 = multipede(nv, eqs, r_non)
    return [inst(f"multipede{nv}", A, B1, True, rng, c, c1),
            inst(f"multipede{nv}-non", A, B2, False, rng, c, c2)]


def jgad(k, rng, twist=False):
    """k hubs on a cycle; each hub has 5 children and one grandchild per pair
    of children (the 2-sets of 5); the 10 grandchildren of consecutive hubs
    are joined by a random perfect matching (degree 7 at the hubs). From an
    edge between hubs, the up-sets of the grandchildren are the 2-sets of a
    twin class of 5: Sym(5) on 10 points, a Johnson action of order 120,
    which the default dispatcher enumerates (order <= enum_limit) and (M)
    does not. twist: one matching is changed by a transposition."""
    G = nx.Graph()
    pairs = list(itertools.combinations(range(5), 2))
    for i in range(k):
        G.add_edge(("h", i), ("h", (i + 1) % k))
        for a in range(5):
            G.add_edge(("h", i), ("c", i, a))
        for p in pairs:
            for a in p:
                G.add_edge(("c", i, a), ("g", i, p))
    for i in range(k):
        perm = list(range(10))
        rng.shuffle(perm)
        if twist and i == 0:
            perm[0], perm[1] = perm[1], perm[0]
        for j, p in enumerate(pairs):
            G.add_edge(("g", i, p), ("g", (i + 1) % k, pairs[perm[j]]))
    return adj(G)


def fam_jgad(k, rng):
    seed = rng.randrange(10 ** 9)
    A = jgad(k, random.Random(seed))
    B = jgad(k, random.Random(seed), twist=True)
    return [inst(f"jgad{k}", A, A, True, rng), inst(f"jgad{k}-twist", A, B, None, rng)]


FAMILIES = {"cfi3": fam_cfi3, "cfi4": fam_cfi4, "reg3": fam_reg(3), "reg4": fam_reg(4),
            "reg5": fam_reg(5), "reg6": fam_reg(6), "reg7": fam_reg(7), "cube": fam_cube,
            "multipede": fam_multipede, "jgad": fam_jgad}


# --- checking ------------------------------------------------------------------------
def group_order(gens):
    from sympy.combinatorics import Permutation, PermutationGroup
    if not gens:
        return 1
    return PermutationGroup([Permutation(list(g)) for g in gens]).order()


def nauty_graph(A, colors):
    n = len(A)
    kw = {}
    if colors is not None:
        kw["vertex_coloring"] = [set(i for i in range(n) if colors[i] == c)
                                 for c in sorted(set(colors))]
    return pynauty.Graph(n, adjacency_dict={i: [j for j in range(n) if A[i][j]] for i in range(n)},
                         **kw)


def nauty_answer(I):
    t0 = time.perf_counter()
    GX, GY = nauty_graph(I["X"], I["cx"]), nauty_graph(I["Y"], I["cy"])
    same = pynauty.certificate(GX) == pynauty.certificate(GY)
    _, s1, s2, _, _ = pynauty.autgrp(GX)
    return same, s1 * 10 ** s2, time.perf_counter() - t0


def check(I, res):
    X, Y, cx, cy = I["X"], I["Y"], I["cx"], I["cy"]
    n = len(X)
    if (res is not None) != I["expect"]:
        return "wrong decision"
    if res is None:
        return ""
    sigma, gens = res
    if sorted(sigma) != list(range(n)) or any(
            Y[sigma[i]][sigma[j]] != X[i][j] for i in range(n) for j in range(n)):
        return "not an isomorphism"
    if cx is not None and any(cy[sigma[i]] != cx[i] for i in range(n)):
        return "colors not preserved"
    for g in gens:
        if any(X[g[i]][g[j]] != X[i][j] for i in range(n) for j in range(n)):
            return "a generator is not an automorphism"
        if cx is not None and any(cx[g[i]] != cx[i] for i in range(n)):
            return "a generator moves colors"
    if I["aut"] is not None:
        o = group_order(gens)
        if abs(o - I["aut"]) > 1e-9 * I["aut"]:
            return f"|<gens>| = {o}, nauty {I['aut']:.6g}"
    return ""


KEEP = ("luks_runs", "luks_steps", "luks_aut_tests", "luks_iso_tests", "luks_phase1_max_degree",
        "luks_phase2_max_degree", "luks_phase2_max_log2_order", "luks_group_max_log2_order",
        "luks_twin_max", "alt_section_max", "enum_quotient",
        "enum_quotient_max_order", "enum_quotient_max_degree", "cameron_skip_enum",
        "cameron_small_johnson", "cameron_small_giant", "cameron_small_abstract",
        "cameron_small_product", "dispatch_cameron_small", "giant_step", "branch", "enumerate", "enum_cosets",
        "product_refine", "young_ind", "solve", "cont")


def run_mode(I, mode, timeout):
    if mode == "nauty":
        same, aut, dt = nauty_answer(I)
        return dict(status="ok", time=round(dt, 4))
    if mode.startswith("new"):
        S = Solver(cameron_no_enum=not mode.endswith("0"), certificates=False)
        root = "degree" if mode.startswith("newh") else "class"

        def f():
            return bounded_iso(I["X"], I["Y"], solver=S, vcolors_x=I["cx"], vcolors_y=I["cy"],
                               root=root)
    else:
        S = Solver(certificates=False)

        def f():
            return graph_iso(I["X"], I["Y"], solver=S, vcolors_x=I["cx"], vcolors_y=I["cy"])
    t0 = time.perf_counter()
    signal.setitimer(signal.ITIMER_REAL, timeout)
    try:
        res = f()
        signal.setitimer(signal.ITIMER_REAL, 0)
    except Timeout:
        return dict(status="timeout", time=round(time.perf_counter() - t0, 2))
    dt = time.perf_counter() - t0
    err = check(I, res)
    return dict(status="WRONG" if err else "ok", time=round(dt, 3), note=err,
                stats={k: S.stats[k] for k in KEEP if S.stats[k]})


def cmd_run(args):
    signal.signal(signal.SIGALRM, _alarm)
    modes = args.modes.split(",")
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results",
                        f"bounded-{args.label}.json")
    rows = json.load(open(path))["rows"] if os.path.exists(path) and args.append else []
    bad = 0
    for size in [int(s) for s in args.sizes.split(",")]:
        rng = random.Random(1000 + size)
        for I in FAMILIES[args.family](size, rng):
            if args.only and I["name"] not in args.only.split(";"):
                continue
            I["n"] = len(I["X"])
            same, aut, _ = nauty_answer(I)
            if I["claim"] is not None and I["claim"] != same:
                raise AssertionError(f"{I['name']}: claim {I['claim']}, nauty {same}")
            I["expect"], I["aut"] = same, aut
            row = dict(name=I["name"], family=args.family, size=size, n=I["n"], iso=same,
                       aut=aut, maxdeg=max(map(sum, I["X"])))
            for mode in modes:
                row[mode] = run_mode(I, mode, args.timeout)
                bad += row[mode]["status"] == "WRONG"
            cells = "  ".join(f"{m}={row[m]['time']}s" + ("" if row[m]["status"] == "ok"
                                                          else f"({row[m]['status']})")
                              for m in modes)
            st = row.get("new", row.get("newh", {})).get("stats", {})
            print(f"{I['name']:24s} n={I['n']:4d} iso={same!s:5s} {cells}  "
                  f"deg1={st.get('luks_phase1_max_degree', '-')} deg2={st.get('luks_phase2_max_degree', '-')} "
                  f"log2|G_r|={st.get('luks_group_max_log2_order', '-')} twin={st.get('luks_twin_max', '-')} "
                  f"alt={st.get('alt_section_max', 0)} enumq={st.get('enum_quotient_max_order', 0)}",
                  flush=True)
            rows.append(row)
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w") as fh:
                json.dump(dict(label=args.label, timeout=args.timeout, rows=rows), fh, indent=1)
    sys.exit(1 if bad else 0)


def cmd_table(args):
    rows = []
    for lab in args.label.split(","):
        path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results",
                            f"bounded-{lab}.json")
        rows += json.load(open(path))["rows"]
    modes = [m for m in ("new", "new0", "newh", "newh0", "default", "nauty")
             if any(m in r for r in rows)]

    def cell(r, m):
        v = r.get(m)
        if v is None:
            return "-"
        return f"{v['time']:.3g}" if v["status"] == "ok" else v["status"]

    print("| instance | n | iso | " + " | ".join(modes)
          + " | deg1 | deg2 | log2 max G_r | max twin | max alt | max enum |")
    print("|---|---|---|" + "---|" * len(modes) + "---|---|---|---|---|---|")
    for r in rows:
        st = r.get("new", r.get("newh", {})).get("stats", {})
        print(f"| {r['name']} | {r['n']} | {r['iso']} | " + " | ".join(cell(r, m) for m in modes)
              + f" | {st.get('luks_phase1_max_degree', '-')} | {st.get('luks_phase2_max_degree', 0)}"
              f" | {st.get('luks_group_max_log2_order', 0)} | {st.get('luks_twin_max', '-')}"
              f" | {st.get('alt_section_max', 0)} | {st.get('enum_quotient_max_order', 0)} |")


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run")
    r.add_argument("--family", required=True, choices=sorted(FAMILIES))
    r.add_argument("--sizes", required=True)
    r.add_argument("--modes", default="new,default,nauty")
    r.add_argument("--timeout", type=float, default=300)
    r.add_argument("--label", required=True)
    r.add_argument("--only", default="")
    r.add_argument("--append", action="store_true")
    t = sub.add_parser("table")
    t.add_argument("--label", required=True)
    args = ap.parse_args()
    {"run": cmd_run, "table": cmd_table}[args.cmd](args)


if __name__ == "__main__":
    main()
