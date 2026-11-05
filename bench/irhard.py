"""Bounded-degree families that are hard for individualization-refinement (IR)
solvers, with answers known by construction, measured against nauty and Traces.

    PY=../r2-hybrid/.venv/bin/python          # networkx, sympy (pynauty optional)
    nice $PY bench/irhard.py run --family ns --sizes 4,8,12 --modes new,dnd,dns,dnt \\
        --timeout 300 --label ns
    $PY bench/irhard.py table --label ns
    $PY bench/irhard.py fit --label ns
    nice $PY bench/irhard.py audit --size 112          # one ns size end to end (see docs)
    nice $PY bench/irhard.py nodes --sizes 16,32,48 --algs As,At,Ad --timeout 200

Families (size parameter k in brackets). All multipede families start from
Neuen and Schweitzer's rigid base construction (ESA 2017, "Benchmark graphs
for practical graph isomorphism", arXiv:1705.03686, Sec. 2-3):

  G_k        the 2k-cycle with its k diagonals (3-regular, 2k vertices, 3k edges);
  B(G_k, s)  bipartite, V = V(G_k) x {0, 1}, W = E(G_k), (v, 0) ~ e iff v in e,
             (v, 1) ~ e iff v in s(e) for a random permutation s of E(G_k);
  R(B, r)    the multipede graph: feet a(w), b(w) for w in W; for v in V with
             N(v) = (w1, w2, w3) and parity r_v, middle vertices m_i for the
             i in {0,1}^3 with |i| = r_v (mod 2), m_i ~ (i_j ? b : a)(w_j).
             r = 0 is NS's R(B). Uncolored.

  ns  [k]   R(B(G_k, s), r): 22k vertices, degree 8 (feet) and 3 (middles). NS's
            "z2" family. Pairs: R(B, 0) against a relabeled R(B, A x) (random
            x: isomorphic), and against a relabeled R(B, e_v) with e_v outside
            the column space of A (not isomorphic).
  nsr [k]   R(B*, r) with B* = B restricted to 3k rows of V that form a basis of
            F_2^W ("linear algebra reduction", NS Sec. 3.1; their "r2"): 18k
            vertices, feet of degree 2..8. A is square and invertible, so every
            parity vector gives an isomorphic graph; only isomorphic pairs.
  nss [k]   R*(B, r): every foot is bypassed (its neighbours are made a clique,
            the foot removed; NS Sec. 3.2, their "s2"): 16k vertices, degree <= 21.
  nst [k]   R*(B*, r), NS's "shrunken multipedes" ("t2"): 12k vertices.
  cfix [b]  CFI graphs over a random cubic graph on b vertices (an expander
            w.h.p.), n = 10b: two twisted edges (isomorphic: twists move along
            paths and cancel in pairs) and one twisted edge (not isomorphic,
            Cai-Fuerer-Immerman), both relabeled.

How the answers are known.
  * Lemma (NS17, Lemma 2.3, extended to isomorphisms). Let B = (V, W, E) be
    bipartite with (1) |N(v)| = 3 for v in V, (2) A = A_B of full column rank
    |W| over F_2 ("odd"), (3) B rigid, (4) no w1 != w2 in W with N^2(w1) =
    N^2(w2). Then R(B, r) is rigid for every r, and R(B, r) ~= R(B, r') iff
    r + r' is in the column space of A. Proof: feet have even degree, middles
    degree 3, so an isomorphism psi maps feet to feet; N^2(a(w)) = N^2(b(w)) =
    F(N^2_B(w)) (the two middles of a gadget at a(w) meet both feet of the other
    two variables), so by (4) psi maps foot pairs to foot pairs, and so
    gadgets to gadgets; the induced map is an automorphism of B, the identity
    by (3). With x_w = 1 iff psi swaps a(w) and b(w), the CFI gadget lemma
    (a gadget of parity r_v maps onto one of parity r'_v while swapping the
    pairs X iff |X| = r_v + r'_v mod 2) gives A x = r + r'; conversely such an
    x defines an isomorphism. Rigidity is the case r = r'.
    Conditions (1), (2), (4) are checked here directly (rank by Gaussian
    elimination), (3) by our exact solver on B (7k vertices, max degree 4)
    *and* by dreadnaut when it is installed. So for ns and nsr both answers and
    |Aut| = 1 are known by construction at every size.
  * nss, nst: the isomorphic pairs are isomorphic by construction (the flip
    psi of the lemma maps feet to feet, hence bypassed graphs onto bypassed
    graphs). |Aut| is taken from nauty when it finishes (else not checked).
  * cfix: Cai, Fuerer, Immerman (Combinatorica 1992), Lemma 6.2 and its
    converse for connected bases. |Aut| from nauty when it finishes.

Modes: "new" = gi.bounded.bounded_iso_lists with Solver(cameron_no_enum=True,
certificates=False); "default" = graph_iso(X, Y, Solver(certificates=False));
"dnd", "dns", "dnt" = dreadnaut (nauty 2.9.1) dense nauty, sparse nauty and
Traces: canonical forms of X and Y, compared (the standard IR isomorphism
test, as in NS17). For dreadnaut the time is the sum of the two reported
cpu times (process wall time in `wall`). Every answer is checked: the
decision, the isomorphism, every generator, and |<gens>| (sympy) when |Aut| is
known. Results go to bench/results/irhard-LABEL.json.
"""
import argparse
import itertools
import json
import math
import os
import random
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.setrecursionlimit(100000)

from gi import graph_iso, Solver
try:
    from gi.bounded import bounded_iso_lists
except ImportError:                     # an older gi (for before/after timings)
    from gi.bounded import bounded_iso

    def bounded_iso_lists(nx, ny, solver=None, **kw):
        n = len(nx)
        mats = []
        for nb in (nx, ny):
            A = [[0] * n for _ in range(n)]
            for u in range(n):
                for v in nb[u]:
                    A[u][v] = 1
            mats.append(A)
        return bounded_iso(mats[0], mats[1], solver=solver, **kw)

DREADNAUT = os.environ.get("DREADNAUT") or shutil.which("dreadnaut") or next(
    (p for p in ("/nix/store/4kd2j9xhcgz2p6msmflmr81pqms9cy05-nauty-2.9.1/bin/dreadnaut",)
     if os.path.exists(p)), None)


class Timeout(Exception):
    pass


def _alarm(signum, frame):
    raise Timeout()


# --- F_2 linear algebra (vectors are int bitmasks) -------------------------------
def _reduce(basis, v):
    """Reduce v by an echelon basis {pivot bit: vector}."""
    while v:
        p = v.bit_length() - 1
        b = basis.get(p)
        if b is None:
            return v
        v ^= b
    return 0


def echelon(vectors):
    basis = {}
    for v in vectors:
        v = _reduce(basis, v)
        if v:
            basis[v.bit_length() - 1] = v
    return basis


# --- the NS17 base construction ----------------------------------------------------
def cycle_diag(k):
    """G_k: the 2k-cycle with diagonals {i, i + k}."""
    m = 2 * k
    E = [(i, (i + 1) % m) for i in range(m)] + [(i, i + k) for i in range(k)]
    return [tuple(sorted(e)) for e in E]


def ns_base(k, rng):
    """Rows N(v) (triples of W-indices) of B(G_k, s), V = V(G_k) x {0,1} in the
    order (0,0), (1,0), ..., (0,1), ..."""
    E = cycle_diag(k)
    s = list(range(len(E)))
    rng.shuffle(s)
    rows = [[] for _ in range(4 * k)]
    for ei, (u, v) in enumerate(E):
        rows[u].append(ei)
        rows[v].append(ei)
        u1, v1 = E[s[ei]]
        rows[2 * k + u1].append(ei)
        rows[2 * k + v1].append(ei)
    return [tuple(r) for r in rows], len(E)


def basis_rows(rows, nw, rng):
    """A subset of the rows forming a basis of F_2^W (greedy in random order),
    in their original order; None if the rows do not span."""
    order = list(range(len(rows)))
    rng.shuffle(order)
    basis, keep = {}, []
    for i in order:
        v = _reduce(basis, sum(1 << w for w in rows[i]))
        if v:
            basis[v.bit_length() - 1] = v
            keep.append(i)
    if len(keep) != nw:
        return None
    return [rows[i] for i in sorted(keep)]


def col_space(rows, nw):
    """Echelon basis of the column space of A (columns as bitmasks over V)."""
    cols = [0] * nw
    for v, r in enumerate(rows):
        for w in r:
            cols[w] |= 1 << v
    return echelon(cols), cols


def multipede(rows, nw, rhs):
    """R(B, r) as neighbour lists: feet a(w) = 2w, b(w) = 2w + 1, then 4
    middles per row."""
    nbr = [[] for _ in range(2 * nw)]
    for r, ws in zip(rhs, rows):
        for bits in itertools.product((0, 1), repeat=len(ws)):
            if sum(bits) % 2 != r:
                continue
            m = len(nbr)
            nbr.append([2 * w + b for w, b in zip(ws, bits)])
            for f in nbr[m]:
                nbr[f].append(m)
    return nbr


def bypass(nbr, nfeet):
    """Remove vertices 0..nfeet-1, making the neighbourhood of each a clique."""
    n = len(nbr)
    S = [set() for _ in range(n - nfeet)]
    for f in range(nfeet):
        nb = [u - nfeet for u in nbr[f]]
        for a in nb:
            S[a].update(nb)
    for i, s in enumerate(S):
        s.discard(i)
    return [sorted(s) for s in S]


def base_graph(rows, nw):
    """B as neighbour lists: W = 0..nw-1, then V."""
    nbr = [[] for _ in range(nw)] + [list(r) for r in rows]
    for v, r in enumerate(rows):
        for w in r:
            nbr[w].append(nw + v)
    return nbr


def check_ns_lemma(rows, nw):
    """Conditions (1), (2), (4) of the lemma (the module docstring) and (3)
    by the exact solver; returns a string naming any failed condition."""
    if any(len(set(r)) != 3 for r in rows):
        return "(1) a row without 3 distinct neighbours"
    if len(echelon([sum(1 << w for w in r) for r in rows])) != nw:
        return "(2) A has rank < |W|"
    adjw = [set() for _ in range(nw)]
    for r in rows:
        for w in r:
            adjw[w].update(r)
    seen = {}
    for w in range(nw):
        key = frozenset(adjw[w] - {w})
        if key in seen:
            return f"(4) N^2({seen[key]}) = N^2({w})"
        seen[key] = w
    Bn = base_graph(rows, nw)
    res = bounded_iso_lists(Bn, Bn, solver=Solver(cameron_no_enum=True, certificates=False))
    if res is None or res[1]:
        return "(3) B is not rigid (solver)"
    if DREADNAUT:
        out = dreadnaut_run(Bn, None, "Ad", 120)
        if out.get("aut") != 1:
            return f"(3) B is not rigid (dreadnaut: {out})"
    return ""


def relabeled(nbr, rng):
    n = len(nbr)
    s = list(range(n))
    rng.shuffle(s)
    out = [None] * n
    for i in range(n):
        out[s[i]] = sorted(s[j] for j in nbr[i])
    return out


def ns_instances(k, rng, reduce_rows=False, shrink=False, tag="ns"):
    for attempt in range(50):
        rows, nw = ns_base(k, rng)
        if reduce_rows:
            rows = basis_rows(rows, nw, rng)
            if rows is None:
                continue
        bad = check_ns_lemma(rows, nw)
        if not bad:
            break
    else:
        raise RuntimeError(f"no base satisfying the lemma for k={k}: {bad}")
    cs, cols = col_space(rows, nw)
    nv = len(rows)
    zero = [0] * nv

    def graph(rhs):
        g = multipede(rows, nw, rhs)
        return bypass(g, 2 * nw) if shrink else g

    X = graph(zero)
    x = [rng.randrange(2) for _ in range(nw)]
    r_iso = [sum(x[w] for w in r) % 2 for r in rows]
    aut = None if shrink else 1
    cert = "lemma" if not shrink else "flip"
    out = [dict(name=f"{tag}{k}", X=X, Y=relabeled(graph(r_iso), rng), claim=True, aut=aut,
                cert=cert)]
    if not reduce_rows:
        cand = [v for v in range(nv) if _reduce(cs, 1 << v)]
        if cand:
            v = rng.choice(cand)
            r_non = [int(i == v) for i in range(nv)]
            out.append(dict(name=f"{tag}{k}-twist", X=X, Y=relabeled(graph(r_non), rng),
                            claim=None if shrink else False, aut=aut,
                            cert="lemma" if not shrink else "nauty"))
    return out


def fam_ns(k, rng):
    return ns_instances(k, rng, tag="ns")


def fam_nsr(k, rng):
    return ns_instances(k, rng, reduce_rows=True, tag="nsr")


def fam_nss(k, rng):
    return ns_instances(k, rng, shrink=True, tag="nss")


def fam_nst(k, rng):
    return ns_instances(k, rng, reduce_rows=True, shrink=True, tag="nst")


# --- CFI over random cubic graphs ---------------------------------------------------
def random_cubic(b, rng):
    """A uniform-ish random connected simple cubic graph (configuration model
    with rejection)."""
    while True:
        pts = [v for v in range(b) for _ in range(3)]
        rng.shuffle(pts)
        E = set()
        ok = True
        for i in range(0, len(pts), 2):
            u, v = pts[i], pts[i + 1]
            if u == v or (min(u, v), max(u, v)) in E:
                ok = False
                break
            E.add((min(u, v), max(u, v)))
        if not ok:
            continue
        adj = [[] for _ in range(b)]
        for u, v in E:
            adj[u].append(v)
            adj[v].append(u)
        seen, q = {0}, [0]
        for u in q:
            for w in adj[u]:
                if w not in seen:
                    seen.add(w)
                    q.append(w)
        if len(seen) == b:
            return sorted(E)


def cfi_lists(b, E, twists):
    """CFI graph over the base (b vertices, edge list E): for each vertex v with
    incident edges e_1..e_d, outer vertices (v, e, 0/1) and middles m_S
    (S even subsets of the incident edges) adjacent to (v, e, [e in S]); for
    each edge e = {u, v}, (u, e, c) ~ (v, e, c + [e twisted])."""
    inc = [[] for _ in range(b)]
    for ei, (u, v) in enumerate(E):
        inc[u].append(ei)
        inc[v].append(ei)
    nbr = []
    outer = {}
    for v in range(b):
        for ei in inc[v]:
            for c in (0, 1):
                outer[(v, ei, c)] = len(nbr)
                nbr.append([])
    for v in range(b):
        d = len(inc[v])
        for bits in itertools.product((0, 1), repeat=d):
            if sum(bits) % 2:
                continue
            m = len(nbr)
            nbr.append([outer[(v, ei, c)] for ei, c in zip(inc[v], bits)])
            for o in nbr[m]:
                nbr[o].append(m)
    for ei, (u, v) in enumerate(E):
        t = 1 if ei in twists else 0
        for c in (0, 1):
            p, q = outer[(u, ei, c)], outer[(v, ei, c ^ t)]
            nbr[p].append(q)
            nbr[q].append(p)
    return nbr


def fam_cfix(b, rng):
    E = random_cubic(b, rng)
    X = cfi_lists(b, E, set())
    t2 = set(rng.sample(range(len(E)), 2))
    t1 = {rng.randrange(len(E))}
    return [dict(name=f"CFIx{b}", X=X, Y=relabeled(cfi_lists(b, E, t2), rng), claim=True,
                 aut=None, cert="cfi"),
            dict(name=f"CFIx{b}-twist", X=X, Y=relabeled(cfi_lists(b, E, t1), rng),
                 claim=False, aut=None, cert="cfi")]


# --- Miyazaki graphs (bliss benchmark files) -----------------------------------------
MZ_DIR = os.environ.get("MZ_DIR", "/tmp/claude-1000/-home-bepis-math/"
                        "117a2777-2472-4276-845a-e0dfeb712755/scratchpad/w1-scale-src")


def read_dimacs(path):
    """Neighbour lists of a DIMACS 'p edge' file (vertices 1..n)."""
    nbr = None
    with open(path) as fh:
        for line in fh:
            t = line.split()
            if not t:
                continue
            if t[0] == "p":
                nbr = [[] for _ in range(int(t[2]))]
            elif t[0] == "e":
                u, v = int(t[1]) - 1, int(t[2]) - 1
                if u != v and v not in nbr[u]:
                    nbr[u].append(v)
                    nbr[v].append(u)
    return [sorted(r) for r in nbr]


def twist_pair(nbr, a, b, c, d):
    """Replace the edges a-c, b-d by a-d, b-c (a CFI twist of one base edge)."""
    out = [list(r) for r in nbr]
    for u, v in ((a, c), (b, d)):
        assert v in out[u], "the edge to twist is missing"
        out[u].remove(v)
        out[v].remove(u)
    for u, v in ((a, d), (b, c)):
        out[u].append(v)
        out[v].append(u)
    return [sorted(r) for r in out]


def mz_family(sub):
    """Miyazaki graphs from the bliss benchmark set (users.aalto.fi/~tjunttil/
    bliss/benchmarks/, files unpacked under MZ_DIR/bliss-<sub>/x/<sub>/):
    the relabeled graph (isomorphic), and the graph with the first
    inter-gadget edge pair (vertices 5,6 to 15,16) twisted (answer and |Aut|
    from nauty; Traces solves these instantly)."""
    def f(k, rng):
        X = read_dimacs(os.path.join(MZ_DIR, f"bliss-{sub}", "x", sub, f"{sub}-{k}"))
        out = [dict(name=f"{sub}-{k}", X=X, Y=relabeled(X, rng), claim=True, aut=None,
                    cert="relabel")]
        try:
            T = twist_pair(X, 4, 5, 14, 15)
            out.append(dict(name=f"{sub}-{k}-twist", X=X, Y=relabeled(T, rng), claim=None,
                            aut=None, cert="nauty"))
        except AssertionError:
            pass
        return out
    return f


def miyazaki_edges(k):
    """Edges (1-based) of Miyazaki's graph mz-k as in the bliss benchmark set:
    2k blocks of 10 vertices, each an odd CFI (Fuerer) gadget with outer
    pairs (1,2), (3,4), (5,6) and middles 7..10; blocks 2i-1, 2i joined by
    the pair (5,6) (a single base edge), blocks 2i, 2i+1 by the pairs (1,2)
    and (3,4) (a double base edge), and the pairs (1,2), (3,4) of the first
    and last block joined to each other (a loop). For k <= 50 this is
    exactly the edge set of the bliss file mz-k (checked by tests/test_irhard.py
    when the files are present)."""
    nb = 2 * k
    gad = [(1, 8), (1, 9), (2, 7), (2, 10), (3, 8), (3, 10), (4, 7), (4, 9), (5, 9), (5, 10),
           (6, 7), (6, 8)]
    E = []
    for i in range(nb):
        o = 10 * i
        E += [(o + a, o + b) for a, b in gad]
    o = 10 * (nb - 1)
    E += [(1, 3), (2, 4), (o + 1, o + 3), (o + 2, o + 4)]
    for i in range(0, nb, 2):
        o = 10 * i
        E += [(o + 5, o + 15), (o + 6, o + 16)]
    for i in range(1, nb - 1, 2):
        o = 10 * i
        E += [(o + a, o + 10 + a) for a in (1, 2, 3, 4)]
    return E


def fam_mzgen(k, rng):
    """Generated Miyazaki graphs (any k): relabeled copy (isomorphic) and the
    first single base edge twisted (answer from nauty)."""
    nbr = [[] for _ in range(20 * k)]
    for u, v in miyazaki_edges(k):
        nbr[u - 1].append(v - 1)
        nbr[v - 1].append(u - 1)
    X = [sorted(r) for r in nbr]
    return [dict(name=f"mz{k}", X=X, Y=relabeled(X, rng), claim=True, aut=None, cert="relabel"),
            dict(name=f"mz{k}-twist", X=X, Y=relabeled(twist_pair(X, 4, 5, 14, 15), rng),
                 claim=None, aut=None, cert="nauty")]


FAMILIES = {"ns": fam_ns, "nsr": fam_nsr, "nss": fam_nss, "nst": fam_nst, "cfix": fam_cfix,
            "mz": mz_family("mz"), "mzaug": mz_family("mz-aug"), "mzaug2": mz_family("mz-aug2"),
            "mzgen": fam_mzgen}


# --- dreadnaut -------------------------------------------------------------------------
def _dre_graph(nbr):
    lines = [f"n={len(nbr)} g"]
    for i, r in enumerate(nbr):
        lines.append(" ".join(str(j) for j in r if j > i) + ";")
    lines[-1] = lines[-1][:-1] + "."
    return "\n".join(lines)


def dreadnaut_run(X, Y, alg, timeout):
    """Canonical forms of X (and Y) with dreadnaut in mode alg ("Ad", "As",
    "At"); returns dict(status, time = sum of cpu times, wall, same, aut)."""
    script = [f"$=0 {alg} -a -m c", _dre_graph(X), "x @"]
    if Y is not None:
        script += [_dre_graph(Y), "x #"]
    script.append("q")
    t0 = time.perf_counter()
    try:
        p = subprocess.run(["nice", "-n", "19", DREADNAUT], input="\n".join(script) + "\n",
                           capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return dict(status="timeout", time=round(time.perf_counter() - t0, 2))
    wall = time.perf_counter() - t0
    out = p.stdout
    cpu = [float(c) for c in re.findall(r"cpu time = ([0-9.]+)", out)]
    grp = re.findall(r"grpsize=([0-9.e+]+)", out)
    if not cpu or (Y is not None and len(cpu) < 2):
        return dict(status="error", time=round(wall, 3), note=(out + p.stderr)[-300:])
    res = dict(status="ok", time=round(sum(cpu), 3), wall=round(wall, 3),
               aut=float(grp[0]) if grp else None)
    if Y is not None:
        if "are identical" in out:
            res["same"] = True
        elif "are different" in out:
            res["same"] = False
        else:
            res.update(status="error", note=out[-300:])
    return res


# --- checking ---------------------------------------------------------------------------
def group_order(gens, n):
    from sympy.combinatorics import Permutation, PermutationGroup
    if not gens:
        return 1
    return PermutationGroup([Permutation(list(g), size=n) for g in gens]).order()


def check(I, res):
    X, Y = I["X"], I["Y"]
    n = len(X)
    if I["expect"] is not None and (res is not None) != I["expect"]:
        return "wrong decision"
    if res is None:
        return ""
    sigma, gens = res
    if sorted(sigma) != list(range(n)):
        return "not a bijection"
    EY = set((u, v) for u in range(n) for v in Y[u])
    if sum(map(len, X)) != len(EY) or any((sigma[u], sigma[v]) not in EY
                                          for u in range(n) for v in X[u]):
        return "not an isomorphism"
    EX = set((u, v) for u in range(n) for v in X[u])
    for g in gens:
        if any((g[u], g[v]) not in EX for u in range(n) for v in X[u]):
            return "a generator is not an automorphism"
    if I["aut"] is not None:
        o = group_order(gens, n)
        if abs(o - I["aut"]) > 1e-9 * I["aut"]:
            return f"|<gens>| = {o}, expected {I['aut']:.6g}"
    return ""


KEEP = ("luks_runs", "luks_steps", "luks_ea_layers", "luks_ea_fallback", "luks_layers_max", "luks_aut_tests", "luks_iso_tests", "luks_phase1_max_degree",
        "luks_phase2_max_degree", "luks_phase2_max_log2_order", "luks_group_max_log2_order",
        "luks_twin_max", "enum_quotient_max_order", "giant_step", "branch", "enumerate", "solve",
        "cont")


def run_mode(I, mode, timeout):
    if mode in ("dnd", "dns", "dnt"):
        out = dreadnaut_run(I["X"], I["Y"], {"dnd": "Ad", "dns": "As", "dnt": "At"}[mode], timeout)
        if out["status"] == "ok" and I["expect"] is not None and out["same"] != I["expect"]:
            out["status"] = "WRONG"
        return out
    if mode == "new":
        S = Solver(cameron_no_enum=True, certificates=False)

        def f():
            return bounded_iso_lists(I["X"], I["Y"], solver=S)
    elif mode == "default":
        S = Solver(certificates=False)
        n = len(I["X"])

        def dense(nb):
            A = [[0] * n for _ in range(n)]
            for u in range(n):
                for v in nb[u]:
                    A[u][v] = 1
            return A

        def f():
            return graph_iso(dense(I["X"]), dense(I["Y"]), solver=S)
    else:
        raise ValueError(mode)
    t0 = time.perf_counter()
    signal.setitimer(signal.ITIMER_REAL, timeout)
    try:
        res = f()
        signal.setitimer(signal.ITIMER_REAL, 0)
    except Timeout:
        return dict(status="timeout", time=round(time.perf_counter() - t0, 2))
    dt = time.perf_counter() - t0
    err = check(I, res)
    out = dict(status="WRONG" if err else "ok", time=round(dt, 3), note=err, iso=res is not None,
               stats={k: S.stats[k] for k in KEEP if S.stats[k]})
    if not err and I["expect"] is None and res is None:
        out["note"] = "non-isomorphism unverified"
    return out


def cmd_run(args):
    signal.signal(signal.SIGALRM, _alarm)
    modes = args.modes.split(",")
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results",
                        f"irhard-{args.label}.json")
    rows = json.load(open(path))["rows"] if os.path.exists(path) and args.append else []
    bad = 0
    dead = set()                                # (mode, kind) that timed out at a smaller size
    for size in [int(s) for s in args.sizes.split(",")]:
        rng = random.Random(7919 * size + args.seed)
        t0 = time.perf_counter()
        insts = FAMILIES[args.family](size, rng)
        tgen = time.perf_counter() - t0
        for I in insts:
            if args.only and not re.search(args.only, I["name"]):
                continue
            n = len(I["X"])
            I["expect"] = I["claim"]
            row = dict(name=I["name"], family=args.family, size=size, n=n, seed=args.seed,
                       maxdeg=max(map(len, I["X"])), edges=sum(map(len, I["X"])) // 2,
                       cert=I["cert"], gen_time=round(tgen, 2))
            # nauty first, so that its answer and |Aut| check ours where the
            # construction does not give them
            kind = I["name"].split("-")[-1] if "-" in I["name"] else "iso"
            for mode in sorted(modes, key=lambda m: not m.startswith("dn")):
                if (mode, kind) in dead:
                    row[mode] = dict(status="skipped", time=args.timeout)
                    continue
                r = row[mode] = run_mode(I, mode, args.timeout)
                if r["status"] == "timeout" and not args.no_skip:
                    dead.add((mode, kind))
                if mode.startswith("dn") and r["status"] == "ok":
                    if I["expect"] is None:        # the answer comes from nauty
                        I["expect"] = r["same"]
                    if I["aut"] is None and r.get("aut") is not None and I["expect"]:
                        I["aut"] = r["aut"]
            for mode in modes:                     # our decisions against a late nauty answer
                r = row[mode]
                if not mode.startswith("dn") and r["status"] == "ok" and I["expect"] is not None \
                        and r["iso"] != I["expect"]:
                    r["status"], r["note"] = "WRONG", "wrong decision (nauty)"
            row["iso"], row["aut"] = I["expect"], I["aut"]
            bad += sum(row[m]["status"] == "WRONG" for m in modes)
            cells = "  ".join(f"{m}={row[m]['time']}s" + ("" if row[m]["status"] == "ok"
                                                          else f"({row[m]['status']})")
                              for m in modes)
            st = row.get("new", {}).get("stats", {})
            print(f"{I['name']:16s} n={n:5d} iso={I['expect']!s:5s} {cells}  "
                  f"log2|G_r|={st.get('luks_group_max_log2_order', '-')} "
                  f"twin={st.get('luks_twin_max', '-')}", flush=True)
            rows.append(row)
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w") as fh:
                json.dump(dict(label=args.label, timeout=args.timeout, rows=rows), fh, indent=1)
    sys.exit(1 if bad else 0)


MODES = ("new", "default", "dnd", "dns", "dnt")


def load(labels):
    rows = []
    for lab in labels.split(","):
        path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results",
                            f"irhard-{lab}.json")
        rows += json.load(open(path))["rows"]
    return rows


def cmd_table(args):
    rows = load(args.label)
    modes = [m for m in MODES if any(m in r for r in rows)]

    def cell(r, m):
        v = r.get(m)
        if v is None:
            return "-"
        if v["status"] in ("timeout", "skipped"):
            return f">{v['time']:.0f}"
        return f"{v['time']:.3g}" if v["status"] == "ok" else v["status"]

    print("| instance | n | iso | " + " | ".join(modes) + " | log2 max G_r |")
    print("|---|---|---|" + "---|" * len(modes) + "---|")
    for r in rows:
        st = r.get("new", {}).get("stats", {})
        print(f"| {r['name']} | {r['n']} | {r['iso']} | " + " | ".join(cell(r, m) for m in modes)
              + f" | {st.get('luks_group_max_log2_order', '-')} |")


def cmd_fit(args):
    """Least squares of log t against log n (t ~ n^c) and against n
    (t ~ 2^(c n)) per mode and kind (iso / non-iso), over finished runs with
    t >= floor, and the crossover n where the fitted curves of `new` and each
    other mode meet."""
    rows = [r for r in load(args.label) if r["n"] >= args.min_n]

    def fit(xs, ys):
        mx, my = sum(xs) / len(xs), sum(ys) / len(ys)
        sxx = sum((x - mx) ** 2 for x in xs)
        b = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sxx
        a = my - b * mx
        ss = sum((y - a - b * x) ** 2 for x, y in zip(xs, ys))
        st = sum((y - my) ** 2 for y in ys) or 1e-300
        return a, b, 1 - ss / st

    for kind in (True, False):
        fits = {}
        for m in MODES:
            pts = sorted({r["n"]: r[m]["time"] for r in rows if r["iso"] == kind and m in r
                          and r[m]["status"] == "ok" and r[m]["time"] >= args.floor}.items())
            if len(pts) < 3:
                continue
            ln = [math.log(n) for n, _ in pts]
            lt = [math.log(t) for _, t in pts]
            ap, bp, rp = fit(ln, lt)
            ae, be, re_ = fit([n for n, _ in pts], lt)
            fits[m] = (ap, bp, ae, be)
            print(f"iso={kind!s:5s} {m:8s} n={pts[0][0]}..{pts[-1][0]} ({len(pts)} pts): "
                  f"t ~ n^{bp:.2f} (R2 {rp:.3f});  t ~ 2^({be / math.log(2) * 1000:.2f} n/1000)"
                  f" (R2 {re_:.3f})")
        if "new" in fits:
            ap, bp, _, _ = fits["new"]
            for m, (ap2, bp2, ae2, be2) in fits.items():
                if m == "new":
                    continue
                # the smallest n >= 50 beyond which the fitted curve of `new` stays
                # below m's, for m's polynomial and its exponential fit
                def cross(f):
                    last = None
                    for n in range(50, 20001):
                        if ap + bp * math.log(n) < f(n):
                            if last is None:
                                last = n
                        else:
                            last = None
                    return last
                xp = cross(lambda n: ap2 + bp2 * math.log(n))
                xe = cross(lambda n: ae2 + be2 * n)
                print(f"   new below {m} for all n >= {xp} (polynomial fits), "
                      f">= {xe} (new polynomial vs {m} exponential); None = not below n=20000")


def cmd_audit(args):
    """End-to-end audit of the ns instances of one size (as `run --seed S`
    builds them): the lemma's conditions, our answer verified, and the
    dreadnaut input read back by dreadnaut ('t') with the same edge set."""
    from collections import Counter
    k = args.size
    insts = FAMILIES["ns"](k, random.Random(7919 * k + args.seed))
    rng2 = random.Random(7919 * k + args.seed)
    for _ in range(50):                 # the same base as ns_instances drew
        rows, nw = ns_base(k, rng2)
        bad = check_ns_lemma(rows, nw)
        if not bad:
            break
    print(f"base B: |V|={len(rows)} |W|={nw} rank(A)={len(echelon([sum(1 << w for w in r) for r in rows]))};"
          f" lemma conditions (1)-(4): {'all hold' if not bad else bad}")
    assert multipede(rows, nw, [0] * len(rows)) == insts[0]["X"]
    for I in insts:
        X, Y = I["X"], I["Y"]
        n, E = len(X), sum(map(len, X)) // 2
        print(f"{I['name']}: n={n} edges={E} degrees={dict(Counter(map(len, X)))} "
              f"answer by the lemma: {'isomorphic' if I['claim'] else 'not isomorphic'}, |Aut|=1")
        S = Solver(cameron_no_enum=True, certificates=False)
        t0 = time.perf_counter()
        res = bounded_iso_lists(X, Y, solver=S)
        dt = time.perf_counter() - t0
        I["expect"] = I["claim"]
        err = check(I, res)
        print(f"  ours: {dt:.3f}s, {'isomorphic' if res else 'not isomorphic'}; check: "
              f"{err or 'decision, sigma on every edge, generators and |<gens>| = 1 verified'}"
              + (f" ({len(res[1])} generators)" if res else ""))
        p = subprocess.run(["nice", "-n", "19", DREADNAUT], input=f"$=0 l=0\n{_dre_graph(X)}\nt\nq\n",
                           capture_output=True, text=True, timeout=120)
        got, cur = set(), None
        for line in p.stdout.splitlines():
            m = re.match(r"\s*(\d+)\s*:(.*)", line)
            if m:
                cur, rest = int(m.group(1)), m.group(2)
            elif cur is not None:
                rest = line
            else:
                continue
            got.update((cur, int(t)) for t in rest.replace(";", " ").split())
        want = {(u, v) for u in range(n) for v in X[u]}
        print(f"  dreadnaut reads the graph we pass it: edge set identical = {got == want}")


def cmd_nodes(args):
    """dreadnaut on X of ns_k (seed 0) per mode: cpu time, search-tree nodes,
    depth (maxlev) and grpsize, one JSON line each; a mode is dropped after
    its first timeout."""
    dead = set()
    for k in [int(x) for x in args.sizes.split(",")]:
        X = FAMILIES[args.family](k, random.Random(7919 * k + args.seed))[0]["X"]
        for alg in args.algs.split(","):
            if alg in dead:
                continue
            script = f"$=0 {alg} -a -m c\n{_dre_graph(X)}\nx\nq\n"
            try:
                p = subprocess.run(["nice", "-n", "19", DREADNAUT], input=script,
                                   capture_output=True, text=True, timeout=args.timeout)
            except subprocess.TimeoutExpired:
                print(json.dumps(dict(k=k, n=len(X), alg=alg, status="timeout",
                                      limit=args.timeout)), flush=True)
                dead.add(alg)
                continue
            o = p.stdout

            def g(pat):
                m = re.search(pat, o)
                return m.group(1) if m else None
            print(json.dumps(dict(k=k, n=len(X), alg=alg, status="ok",
                                  cpu=float(g(r"cpu time = ([0-9.]+)")),
                                  nodes=int(g(r"(\d+) nodes?")), maxlev=g(r"maxlev=(\d+)"),
                                  grpsize=g(r"grpsize=([0-9.e+]+)"))), flush=True)


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run")
    r.add_argument("--family", required=True, choices=sorted(FAMILIES))
    r.add_argument("--sizes", required=True)
    r.add_argument("--modes", default="new,dnd,dns,dnt")
    r.add_argument("--timeout", type=float, default=300)
    r.add_argument("--label", required=True)
    r.add_argument("--only", default="")
    r.add_argument("--seed", type=int, default=0)
    r.add_argument("--append", action="store_true")
    r.add_argument("--no-skip", action="store_true",
                   help="keep running a mode at larger sizes after it timed out")
    t = sub.add_parser("table")
    t.add_argument("--label", required=True)
    f = sub.add_parser("fit")
    f.add_argument("--label", required=True)
    f.add_argument("--min-n", type=int, default=0)
    f.add_argument("--floor", type=float, default=0.01)
    a = sub.add_parser("audit")
    a.add_argument("--size", type=int, required=True)
    a.add_argument("--seed", type=int, default=0)
    nd = sub.add_parser("nodes")
    nd.add_argument("--family", default="ns", choices=sorted(FAMILIES))
    nd.add_argument("--sizes", required=True)
    nd.add_argument("--algs", default="As,At,Ad")
    nd.add_argument("--timeout", type=float, default=200)
    nd.add_argument("--seed", type=int, default=0)
    args = ap.parse_args()
    {"run": cmd_run, "table": cmd_table, "fit": cmd_fit, "audit": cmd_audit,
     "nodes": cmd_nodes}[args.cmd](args)


if __name__ == "__main__":
    main()
