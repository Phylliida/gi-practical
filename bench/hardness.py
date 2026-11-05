"""Hardness families: parametrized instances whose size grows, with exactly
known answers, for measuring how the recursion's cost grows.

    PY=../r2-hybrid/.venv/bin/python            # has pynauty, networkx, sympy
    nice $PY bench/hardness.py list
    nice $PY bench/hardness.py run --family cfi4 --sizes 6,8,10 --modes full,ir0,nauty \\
        --timeout 300 --label cfi4
    $PY bench/hardness.py fit --label cfi4 --metric time

Every family builder returns instances (name, X, Y, claim, vertex colors).
claim is True for a random relabeling (isomorphic by construction), False
when a theorem cited in the builder gives non-isomorphism, and None when
pynauty decides. When pynauty can be imported, every claim is checked against
nauty and |Aut(X)| is taken from nauty; a disagreement aborts the run. Every
answer of graph_iso is verified: the decision, the isomorphism (edges and
vertex colors), each generator being an automorphism, and |<gens>| (sympy)
against |Aut(X)|.

Modes: "full" = graph_iso(X, Y, Solver(certificates=False)) with the default
front end (ir=3 plus budgeted levels up to log2 n); "ir0" = the same with
ir=0 (no graph-level individualization: the paper's recursion does the work);
"nauty" = pynauty certificates of both graphs plus autgrp.

The recorded stats are solver.stats plus, from TracingSolver:
  label_depth   deepest nesting of label individualization (branch_labels)
  try_young / try_giant   branch attempts (refinements) of the Young-label
                step and of the GiantStep individualization
  ir_depth      deepest graph-level individualization level
"""
import argparse
import cProfile
import io
import itertools
import json
import math
import os
import pstats
import random
import signal
import sys
import time
from collections import Counter

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.setrecursionlimit(100000)

import networkx as nx

from bench.families import adj, relabel, cfi, paley, latin_square_graph, cayley_table
import gi.graph as gigraph
from gi import graph_iso, Solver, Unsupported

try:
    import pynauty
except ImportError:                     # optional
    pynauty = None


# ---------------------------------------------------------------------------
# helpers

def shuffled_colored(A, colors, rng):
    """A random relabeling of (A, colors): (B, colors of B)."""
    n = len(A)
    s = list(range(n))
    rng.shuffle(s)
    B = relabel(A, s)
    cB = [None] * n
    for i in range(n):
        cB[s[i]] = colors[i] if colors is not None else 0
    return B, (cB if colors is not None else None)


def inst(name, X, Y, claim, cx=None, cy=None, note=""):
    return dict(name=name, X=X, Y=Y, claim=claim, cx=cx, cy=cy, note=note)


def iso_pair(name, A, rng, colors=None, note="random relabeling"):
    B, cB = shuffled_colored(A, colors, rng)
    return inst(name, A, B, True, colors, cB, note)


def noniso_pair(name, A, A2, rng, claim, colors=None, colors2=None, note=""):
    B, cB = shuffled_colored(A2, colors2, rng)
    return inst(name, A, B, claim, colors, cB, note)


def from_edges(n, edges):
    A = [[0] * n for _ in range(n)]
    for u, v in edges:
        if u != v:
            A[u][v] = A[v][u] = 1
    return A


# --- linear algebra over F_p -----------------------------------------------

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


def normalize(v, p):
    """The projective representative of v (first nonzero entry 1), or None."""
    for c in v:
        if c % p:
            iv = pow(c, p - 2, p)
            return tuple(x * iv % p for x in v)
    return None


def proj_points(dim, p):
    return sorted({normalize(v, p) for v in itertools.product(range(p), repeat=dim)} - {None})


def proj_lines(points, p):
    """Lines of the projective space: each as a sorted tuple of point indices."""
    idx = {pt: i for i, pt in enumerate(points)}
    lines = set()
    for i, a in enumerate(points):
        for b in points[i + 1:]:
            L = {idx[normalize(tuple((s * x + t * y) % p for x, y in zip(a, b)), p)]
                 for s in range(p) for t in range(p) if s or t}
            lines.add(tuple(sorted(L)))
    return sorted(lines)


# ---------------------------------------------------------------------------
# families. Each builder(size, rng) returns a list of instances.

def fam_cfi4(b, rng):
    """CFI over a random connected 4-regular graph on b vertices (n = 16 b).
    The middle classes have 8 vertices (>= young_min and ir_min).
    Non-isomorphism of the twisted pair: CFI theorem (connected base)."""
    seed = 1000 + b
    while True:
        base = nx.random_regular_graph(4, b, seed=seed)
        if nx.is_connected(base):
            break
        seed += 1
    A = adj(cfi(base))
    return [iso_pair(f"CFI(4reg{b})", A, rng),
            noniso_pair(f"CFI(4reg{b})-twist", A, adj(cfi(base, True)), rng, False,
                        note="CFI theorem")]


def fam_cfi3(b, rng):
    """CFI over a random connected 3-regular graph on b vertices (n = 10 b)."""
    seed = 2000 + b
    while True:
        base = nx.random_regular_graph(3, b, seed=seed)
        if nx.is_connected(base):
            break
        seed += 1
    A = adj(cfi(base))
    return [iso_pair(f"CFI(3reg{b})", A, rng),
            noniso_pair(f"CFI(3reg{b})-twist", A, adj(cfi(base, True)), rng, False,
                        note="CFI theorem")]


def fam_cfik(m, rng):
    """CFI over the complete graph K_m (treewidth m-1; n = m (2^(m-2) + 2(m-1)))."""
    base = nx.complete_graph(m)
    A = adj(cfi(base))
    return [iso_pair(f"CFI(K{m})", A, rng),
            noniso_pair(f"CFI(K{m})-twist", A, adj(cfi(base, True)), rng, False,
                        note="CFI theorem")]


def fam_cfigrid(k, rng):
    """CFI over the 3 x k grid (n = 36 k - 28)."""
    base = nx.convert_node_labels_to_integers(nx.grid_2d_graph(3, k))
    A = adj(cfi(base))
    return [iso_pair(f"CFI(grid3x{k})", A, rng),
            noniso_pair(f"CFI(grid3x{k})-twist", A, adj(cfi(base, True)), rng, False,
                        note="CFI theorem")]


def xor_system(nv, deg, rng, arity=3, tries=2000, m=None):
    """A random arity-XOR system: m = deg nv / arity equations (sets of
    `arity` variables), each variable in `deg` equations (or, when m is
    given, the arity m slots spread as evenly as possible), no two
    equations sharing more than arity - 2 variables (for arity 3 a linear
    hypergraph: otherwise 2-WL derives two-variable relations and solves
    small systems), and a matrix of full column rank over F_2 (so the
    multipede below is rigid; for even arity Aut has order 2, the flip of
    all variables)."""
    if m is None:
        m = deg * nv // arity
    for _ in range(tries):
        pool = [v for v in range(nv) for _ in range(deg)] if deg else \
            [v % nv for v in range(arity * m)]
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
        # even arity: the all-ones flip always solves A S = 0 (rank <= nv - 1)
        if rank_mod(cols, 2) == nv - (arity % 2 == 0):
            return eqs
    raise RuntimeError("no full-rank XOR system found")


def multipede(nv, eqs, rhs):
    """Colored graph of an XOR system (a multipede, Gurevich-Shelah; the
    constraint gadgets are CFI gadgets): variable v has two feet (v, 0),
    (v, 1); an equation e = (i, j, ...) with right-hand side r has one vertex
    per assignment with sum r, adjacent to the matching feet. Colors: one
    color per variable (its feet) and per equation (its gadget, 2^(|e|-1)
    vertices). Color-preserving isomorphisms between the systems (A, r) and
    (A, r') are exactly the flips S of variables with A S = r + r' (each foot
    pair is fixed or swapped, a gadget vertex is determined by its feet)."""
    n = 2 * nv + sum(2 ** (len(e) - 1) for e in eqs)
    edges, colors = [], [v for v in range(nv) for _ in (0, 1)]
    k = 2 * nv
    for ei, (e, r) in enumerate(zip(eqs, rhs)):
        for bits in itertools.product((0, 1), repeat=len(e) - 1):
            bits = bits + ((r + sum(bits)) % 2,)
            for var, bit in zip(e, bits):
                edges.append((k, 2 * var + bit))
            colors.append(nv + ei)
            k += 1
    return from_edges(n, edges), colors


def multipede_pair(nv, deg, arity, rng, tag, m=None):
    eqs = xor_system(nv, deg, rng, arity, m=m)
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
    return [noniso_pair(f"{tag}{nv}", A, B1, rng, True, c, c1, "r + A s"),
            noniso_pair(f"{tag}{nv}-non", A, B2, rng, False, c, c2, "r + e, e not in col(A)")]


def fam_multipede(nv, rng):
    """Rigid colored 3-XOR multipede on nv variables, each in 4 equations
    (n = 2 nv + 4 m, m = 4 nv / 3; classes of size 2 and 4). Iso:
    right-hand side r + A s. Non-iso: r + e with e outside the column space
    of A (rank test). Aut is trivial (A has full column rank). In the spirit
    of Neuen-Schweitzer's IR lower bound (multipedes over expanders)."""
    return multipede_pair(nv, 4, 3, rng, "multipede")


def fam_multipede4(nv, rng):
    """4-XOR multipede (Aut = the global flip, order 2): m = nv + max(2, nv / 8) equations, variables in
    4 or 5 of them; gadget classes of 8 vertices (>= young_min and ir_min, so
    both individualization heuristics can fire on them); n = 2 nv + 8 m."""
    return multipede_pair(nv, 0, 4, rng, "multipede4-", m=nv + max(2, nv // 8))


# --- groups and Latin squares ------------------------------------------------

def metacyclic(m, s, r, t):
    """<a, b | a^m, b^s = a^t, b a b^-1 = a^r>: elements a^i b^j."""
    elems = [(i, j) for i in range(m) for j in range(s)]

    def op(u, v):
        (i, j), (k, l) = u, v
        e = (i + k * pow(r, j, m)) % m
        jl = j + l
        if jl >= s:
            e, jl = (e + t) % m, jl - s
        return (e, jl)
    return elems, op


def direct(g1, g2):
    (e1, o1), (e2, o2) = g1, g2
    return [(a, b) for a in e1 for b in e2], lambda u, v: (o1(u[0], v[0]), o2(u[1], v[1]))


def cyclic(k):
    return list(range(k)), lambda a, b: (a + b) % k


def group_table(elems, op):
    t = cayley_table(elems, op)
    k = len(t)
    # sanity: a Latin square with an identity and associativity
    assert all(sorted(row) == list(range(k)) for row in t)
    assert all(t[t[a][b]][c] == t[a][t[b][c]] for a in range(k) for b in range(k) for c in range(k))
    return t


def groups_of_order(k):
    """Some groups of order k (name -> (elems, op)), pairwise non-isomorphic."""
    G = {f"Z{k}": cyclic(k)}
    if k % 2 == 0 and k >= 6:
        G[f"D{k // 2}"] = metacyclic(k // 2, 2, -1 % (k // 2), 0)
    if k == 8:
        G.update({"Z2xZ4": direct(cyclic(2), cyclic(4)), "Z2^3": direct(cyclic(2), direct(cyclic(2), cyclic(2))),
                  "Q8": metacyclic(4, 2, 3, 2)})
    if k == 9:
        G["Z3^2"] = direct(cyclic(3), cyclic(3))
    if k == 12:
        G["Z2xZ6"] = direct(cyclic(2), cyclic(6))
        G["Dic3"] = metacyclic(3, 4, 2, 0)
    if k == 16:
        G.update({
            "Z4^2": direct(cyclic(4), cyclic(4)),
            "Z2xZ8": direct(cyclic(2), cyclic(8)),
            "Q16": metacyclic(8, 2, 7, 4),
            "SD16": metacyclic(8, 2, 3, 0),
            "M16": metacyclic(8, 2, 5, 0),
            "Z4:Z4": metacyclic(4, 4, 3, 0),
            "Z2xQ8": direct(cyclic(2), metacyclic(4, 2, 3, 2)),
            "Z2xD4": direct(cyclic(2), metacyclic(4, 2, 3, 0)),
            "Z2^4": direct(direct(cyclic(2), cyclic(2)), direct(cyclic(2), cyclic(2))),
        })
    return G


def fam_latin_group(k, rng):
    """Latin-square graphs (n = k^2) of Cayley tables of groups of order k.
    Iso: random relabeling. Non-iso pairs: different groups of order k >= 5;
    graph isomorphism of Latin square graphs is main-class equivalence for
    order >= 5 (Bruck 1963), and the main class of a group table determines
    the group (all conjugates of a group table are isotopic to it, and
    isotopic groups are isomorphic, Albert 1943)."""
    G = groups_of_order(k)
    names = list(G)
    tabs = {nm: latin_square_graph(group_table(*G[nm])) for nm in names}
    out = []
    for nm in names:
        out.append(iso_pair(f"Latin({nm})", adj(tabs[nm]), rng))
    for a, b in zip(names, names[1:]):
        out.append(noniso_pair(f"Latin({a})-vs-({b})", adj(tabs[a]), adj(tabs[b]), rng,
                               False if k >= 5 else None, note="Bruck + Albert"))
    return out


def cycle_switch(L, r1, r2, c):
    k = len(L)
    pos1 = {L[r1][j]: j for j in range(k)}
    cols, j = [], c
    while True:
        cols.append(j)
        j = pos1[L[r2][j]]
        if j == c:
            break
    for j in cols:
        L[r1][j], L[r2][j] = L[r2][j], L[r1][j]


def random_latin(k, rng, steps=None):
    """A random-ish Latin square: the cyclic square scrambled by many random
    cycle switches on rows, columns and (via a conjugate) symbols."""
    L = [[(i + j) % k for j in range(k)] for i in range(k)]
    for _ in range(steps or 20 * k * k):
        r1, r2 = rng.sample(range(k), 2)
        cycle_switch(L, r1, r2, rng.randrange(k))
        w = rng.randrange(3)
        if w == 1:                                      # transpose
            L = [list(r) for r in zip(*L)]
        elif w == 2:                                    # (row, symbol, column) conjugate
            M = [[0] * k for _ in range(k)]
            for i in range(k):
                for j in range(k):
                    M[i][L[i][j]] = j
            L = M
    assert all(sorted(r) == list(range(k)) for r in L)
    assert all(sorted(c) == list(range(k)) for c in zip(*L))
    return L


def fam_latin_random(k, rng):
    """Latin-square graphs of random Latin squares of order k (n = k^2):
    an iso pair and a pair of two random squares (decided by nauty)."""
    L1, L2 = random_latin(k, rng), random_latin(k, rng)
    A1, A2 = adj(latin_square_graph(L1)), adj(latin_square_graph(L2))
    return [iso_pair(f"LatinRand{k}", A1, rng),
            noniso_pair(f"LatinRand{k}-pair", A1, A2, rng, None, note="nauty decides")]


# --- class 2, exponent p: alternating bilinear maps -------------------------

def random_alt_map(a, c, p, rng):
    """c random alternating a x a matrices over F_p, linearly independent,
    with trivial common radical (so the group is class 2 with center = W)."""
    while True:
        Bs = []
        for _ in range(c):
            B = [[0] * a for _ in range(a)]
            for i in range(a):
                for j in range(i + 1, a):
                    B[i][j] = rng.randrange(p)
                    B[j][i] = (-B[i][j]) % p
            Bs.append(B)
        flat = [[B[i][j] for i in range(a) for j in range(i + 1, a)] for B in Bs]
        if rank_mod(flat, p) < c:
            continue
        stacked = [row for B in Bs for row in B]       # radical = common kernel
        if rank_mod(stacked, p) == a:
            return Bs


def bilinear_graph(a, c, p, Bs):
    """Faithful projective encoding of an alternating bilinear map
    b: F_p^a x F_p^a -> F_p^c (p in {2, 3} for c = 2; any prime for c = 3):
    vertices are the points and lines of PG(a-1, p), the points (and, for
    c = 3, lines) of PG(c-1, p), and a zero vertex; a V-line spanned by u, v
    is joined to the point <b(u, v)> of PG(W), or to zero. For a >= 3 and
    trivial radical, color-preserving isomorphism of these graphs is exactly
    pseudo-isometry of the maps (fundamental theorem of projective geometry
    on both sides; a map that is a scalar multiple of b on every pair is a
    global scalar multiple when the radical is trivial), i.e. isomorphism of
    the class-2 exponent-p groups for odd p (Baer)."""
    assert c == 3 or (c == 2 and p in (2, 3))
    VP = proj_points(a, p)
    VL = proj_lines(VP, p)
    WP = proj_points(c, p)
    WL = proj_lines(WP, p) if c >= 3 else []
    widx = {w: i for i, w in enumerate(WP)}
    nVP, nVL, nWP, nWL = len(VP), len(VL), len(WP), len(WL)
    n = nVP + nVL + nWP + nWL + 1
    zero = n - 1
    edges = []
    for li, L in enumerate(VL):
        lv = nVP + li
        for pt in L:
            edges.append((lv, pt))
        u, v = VP[L[0]], VP[L[1]]
        w = tuple(sum(u[i] * B[i][j] * v[j] for i in range(a) for j in range(a)) % p for B in Bs)
        wn = normalize(w, p)
        edges.append((lv, zero if wn is None else nVP + nVL + widx[wn]))
    for li, L in enumerate(WL):
        for pt in L:
            edges.append((nVP + nVL + nWP + li, nVP + nVL + pt))
    colors = [0] * nVP + [1] * nVL + [2] * nWP + [3] * nWL + [4]
    return from_edges(n, edges), colors


def fam_bilinear(size, rng):
    """Sun's hard class (p-groups of class 2 and exponent p), encoded by the
    alternating bilinear map. size = (p, a, c) as "p,a,c" -> n ~ p^(2a-4).
    Iso: random relabeling. Non-iso: a second random map, decided by nauty."""
    p, a, c = size
    B1, B2 = random_alt_map(a, c, p, rng), random_alt_map(a, c, p, rng)
    A1, c1 = bilinear_graph(a, c, p, B1)
    A2, c2 = bilinear_graph(a, c, p, B2)
    nm = f"Bil(p{p},a{a},c{c})"
    return [iso_pair(nm, A1, rng, c1),
            noniso_pair(nm + "-pair", A1, A2, rng, None, c1, c2, "nauty decides")]


# --- designs and strongly regular graphs -------------------------------------

def random_sts(v, rng):
    """A random Steiner triple system on v points (Stinson's hill climbing)."""
    assert v % 6 in (1, 3)
    b = v * (v - 1) // 6
    third = {}                                  # frozenset pair -> third point
    blocks = set()
    live = {x: set(range(v)) - {x} for x in range(v)}   # uncovered partners
    while len(blocks) < b:
        x = rng.choice([x for x in range(v) if live[x]])
        y, z = rng.sample(sorted(live[x]), 2)
        w = third.get(frozenset((y, z)))
        if w is not None:
            old = tuple(sorted((w, y, z)))
            blocks.discard(old)
            for p, q in ((w, y), (w, z), (y, z)):
                del third[frozenset((p, q))]
            live[w].update((y, z))
            live[y].add(w)
            live[z].add(w)
        blk = tuple(sorted((x, y, z)))
        blocks.add(blk)
        for p, q, r in ((x, y, z), (x, z, y), (y, z, x)):
            third[frozenset((p, q))] = r
        live[x] -= {y, z}
        live[y].discard(x)
        live[z].discard(x)
        if w is None:
            live[y].discard(z)
            live[z].discard(y)
    return sorted(blocks)


def fam_sts(v, rng):
    """Point-block incidence graphs of random Steiner triple systems on v
    points (n = v + v(v-1)/6); points and blocks colored apart."""
    out = []
    S1, S2 = random_sts(v, rng), random_sts(v, rng)

    def graph(S):
        n = v + len(S)
        return from_edges(n, [(v + i, x) for i, B in enumerate(S) for x in B]), [0] * v + [1] * len(S)
    A1, c1 = graph(S1)
    A2, c2 = graph(S2)
    out.append(iso_pair(f"STS{v}", A1, rng, c1))
    out.append(noniso_pair(f"STS{v}-pair", A1, A2, rng, None, c1, c2, "nauty decides"))
    return out


def fam_gq(q, rng):
    """Collinearity graphs of the generalized quadrangles W(q) (symplectic) and
    Q(4, q) (parabolic), q prime: both SRG((q+1)(q^2+1), q(q+1), q-1, q+1);
    for odd q they are non-isomorphic (W(q) is not self-dual for odd q,
    Payne-Thas 3.2.1; the collinearity graph determines the GQ)."""
    P = proj_points(4, q)
    W = from_edges(len(P), [(i, j) for i in range(len(P)) for j in range(i + 1, len(P))
                            if (P[i][0] * P[j][1] - P[i][1] * P[j][0]
                                + P[i][2] * P[j][3] - P[i][3] * P[j][2]) % q == 0])
    out = [iso_pair(f"W({q})", W, rng)]
    if q % 2:
        Qp = [x for x in proj_points(5, q) if (x[0] ** 2 + x[1] * x[2] + x[3] * x[4]) % q == 0]

        def form(x, y):
            return (2 * x[0] * y[0] + x[1] * y[2] + x[2] * y[1] + x[3] * y[4] + x[4] * y[3]) % q
        Q = from_edges(len(Qp), [(i, j) for i in range(len(Qp)) for j in range(i + 1, len(Qp))
                                 if form(Qp[i], Qp[j]) == 0])
        assert len(Qp) == len(P)
        out.append(noniso_pair(f"W({q})-vs-Q(4,{q})", W, Q, rng, False, note="Payne-Thas"))
    return out


def fam_symplectic(m, rng):
    """Symplectic graph Sp(2m, 2): nonzero vectors of F_2^(2m), adjacent when
    the symplectic form is 1 (the non-commuting graph of an extraspecial
    2-group modulo its center). n = 4^m - 1."""
    V = [v for v in itertools.product((0, 1), repeat=2 * m) if any(v)]

    def form(x, y):
        return sum(x[2 * i] * y[2 * i + 1] + x[2 * i + 1] * y[2 * i] for i in range(m)) % 2
    A = from_edges(len(V), [(i, j) for i in range(len(V)) for j in range(i + 1, len(V))
                            if form(V[i], V[j])])
    return [iso_pair(f"Sp({2 * m},2)", A, rng)]


def sylvester(k):
    H = [[1]]
    for _ in range(k):
        H = [r + r for r in H] + [r + [-c for c in r] for r in H]
    return H


def paley_hadamard(q):
    """Paley I Hadamard matrix of order q + 1, q prime, q = 3 mod 4."""
    sq = {(i * i) % q for i in range(1, q)}

    def chi(a):
        a %= q
        return 0 if a == 0 else (1 if a in sq else -1)
    Q = [[chi(j - i) for j in range(q)] for i in range(q)]
    S = [[0] + [1] * q] + [[-1] + Q[i] for i in range(q)]
    return [[S[i][j] + (1 if i == j else 0) for j in range(q + 1)] for i in range(q + 1)]


def hadamard_graph(H):
    """Vertices r_i^s, c_j^t (s, t = +-1); r_i^s ~ c_j^t iff H_ij s t = 1.
    n = 4 m. Isomorphic iff the matrices are Hadamard equivalent."""
    m = len(H)
    assert all(sum(H[i][k] * H[j][k] for k in range(m)) == (m if i == j else 0)
               for i in range(m) for j in range(m))
    edges = []
    for i in range(m):
        for j in range(m):
            for s in (0, 1):
                for t in (0, 1):
                    if H[i][j] * (1 - 2 * s) * (1 - 2 * t) == 1:
                        edges.append((2 * i + s, 2 * m + 2 * j + t))
    return from_edges(4 * m, edges)


def fam_hadamard(m, rng):
    """Hadamard graphs (n = 4 m) of Sylvester (m = 2^k) and Paley I (m = q + 1)
    matrices; the pair at m = 2^k = q + 1 is decided by nauty."""
    out = []
    Hs = {}
    if m & (m - 1) == 0:
        Hs["Syl"] = sylvester(m.bit_length() - 1)
    q = m - 1
    if q % 4 == 3 and all(q % d for d in range(2, int(q ** 0.5) + 1)):
        Hs["PaleyI"] = paley_hadamard(q)
    graphs = {k: hadamard_graph(H) for k, H in Hs.items()}
    for k, A in graphs.items():
        out.append(iso_pair(f"Had{k}{m}", A, rng))
    if len(graphs) == 2:
        out.append(noniso_pair(f"HadSyl{m}-vs-PaleyI", graphs["Syl"], graphs["PaleyI"], rng, None,
                               note="nauty decides"))
    return out


class GF:
    """GF(p^k) by tables; elements 0..q-1 (base-p digits = coefficients)."""
    POLY = {4: (2, (1, 1)), 8: (2, (1, 1, 0)), 9: (3, (1, 0)), 25: (5, (2, 0)),
            16: (2, (1, 1, 0, 0))}      # x^k = -(c0 + c1 x + ...): q -> (p, low coefficients of
                                        # a monic irreducible polynomial)

    def __init__(self, q):
        if all(q % d for d in range(2, q)):
            p, k, low = q, 1, None
        else:
            p, low = self.POLY[q]
            k = len(low)
        self.q, self.p = q, p

        def vec(a):
            return [(a // p ** i) % p for i in range(k)]

        def num(v):
            return sum(c * p ** i for i, c in enumerate(v))

        def pmul(u, v):
            r = [0] * (2 * k - 1)
            for i, a in enumerate(u):
                for j, b in enumerate(v):
                    r[i + j] = (r[i + j] + a * b) % p
            for d in range(2 * k - 2, k - 1, -1):      # reduce x^d = x^(d-k) x^k
                c, r[d] = r[d], 0
                for i, l in enumerate(low):
                    r[d - k + i] = (r[d - k + i] - c * l) % p
            return r[:k]
        self.add = [[num([(a + b) % p for a, b in zip(vec(x), vec(y))]) for y in range(q)]
                    for x in range(q)]
        self.mul = [[num(pmul(vec(x), vec(y))) for y in range(q)] for x in range(q)]
        assert all(sorted(self.mul[x][1:]) == list(range(1, q)) for x in range(1, q)), "not a field"


def plane_graph(q, mul, add, colored=False):
    """Incidence graph of the projective completion of the affine plane with
    lines y = x o m + b and x = c, where (x, m) -> x o m is a (right)
    quasifield multiplication; checked: two points are on exactly one line."""
    pts = [("a", x, y) for x in range(q) for y in range(q)] + [("s", m) for m in range(q)] + [("inf",)]
    pidx = {pt: i for i, pt in enumerate(pts)}
    lines = []
    for m in range(q):
        for b in range(q):
            lines.append([pidx[("a", x, add[mul(x, m)][b])] for x in range(q)] + [pidx[("s", m)]])
    for c in range(q):
        lines.append([pidx[("a", c, y)] for y in range(q)] + [pidx[("inf",)]])
    lines.append([pidx[("s", m)] for m in range(q)] + [pidx[("inf",)]])
    N = len(pts)
    assert len(lines) == N == q * q + q + 1
    cnt = Counter()
    for L in lines:
        assert len(set(L)) == q + 1
        for a, b in itertools.combinations(sorted(L), 2):
            cnt[a, b] += 1
    assert len(cnt) == N * (N - 1) // 2 and set(cnt.values()) == {1}, "not a projective plane"
    A = from_edges(2 * N, [(i, N + li) for li, L in enumerate(lines) for i in L])
    return A, ([0] * N + [1] * N if colored else None)


def fam_plane(q, rng):
    """Projective planes of order q (n = 2 (q^2 + q + 1)): the Desarguesian
    PG(2, q) (iso pair), and for q = 9 the Hall plane (the nearfield plane:
    x o m = x m for m a square, x^3 m otherwise), which is not Desarguesian;
    the pair PG(2,9) vs Hall(9) is decided by nauty, as is the
    points/lines-colored pair Hall(9) vs its dual."""
    F = GF(q)
    A, _ = plane_graph(q, lambda x, m: F.mul[x][m], F.add)
    out = [iso_pair(f"PG(2,{q})", A, rng)]
    if q == 9:
        sq = {F.mul[a][a] for a in range(1, q)}
        cube = [F.mul[F.mul[x][x]][x] for x in range(q)]

        def near(x, m):
            return F.mul[x][m] if (m == 0 or m in sq) else F.mul[cube[x]][m]
        H, _ = plane_graph(q, near, F.add)
        out.append(iso_pair("Hall(9)", H, rng))
        out.append(noniso_pair("PG(2,9)-vs-Hall(9)", A, H, rng, None, note="nauty decides"))
        Hc, cc = plane_graph(q, near, F.add, colored=True)
        N = q * q + q + 1
        dual = [[Hc[(i + N) % (2 * N)][(j + N) % (2 * N)] for j in range(2 * N)] for i in range(2 * N)]
        out.append(noniso_pair("Hall(9)-vs-dual(colored)", Hc, dual, rng, None, cc, cc,
                               "nauty decides"))
    return out


def fam_paley(q, rng):
    """Paley graphs, q prime = 1 mod 4."""
    return [iso_pair(f"Paley{q}", adj(paley(q)), rng)]


def fam_cayley2(d, rng):
    """Random Cayley graphs of Z_2^d (n = 2^d) with |S| about n/4: an iso pair
    and a pair of two random connection sets of equal size (nauty decides)."""
    n = 2 ** d
    k = n // 4

    def graph(S):
        return from_edges(n, [(u, u ^ s) for u in range(n) for s in S])
    S1 = rng.sample(range(1, n), k)
    S2 = rng.sample(range(1, n), k)
    A1, A2 = graph(S1), graph(S2)
    return [iso_pair(f"Cay(Z2^{d})", A1, rng),
            noniso_pair(f"Cay(Z2^{d})-pair", A1, A2, rng, None, note="nauty decides")]


FAMILIES = {
    "cfi4": (fam_cfi4, "6,8,10,12,14,16,18", "CFI over random 4-regular base, n = 16b"),
    "cfi3": (fam_cfi3, "10,14,18,22,26", "CFI over random 3-regular base, n = 10b"),
    "cfik": (fam_cfik, "4,5,6,7", "CFI over K_m"),
    "cfigrid": (fam_cfigrid, "3,4,5,6,7,8", "CFI over 3 x k grids, n = 36k - 28"),
    "multipede": (fam_multipede, "12,18,24,30,36", "rigid 3-XOR multipedes, n ~ 7.3 nv"),
    "multipede4": (fam_multipede4, "12,16,20,24", "4-XOR multipedes, n = 2 nv + 8 m"),
    "latin_group": (fam_latin_group, "5,7,8,9,11,12,13,16", "Latin square graphs of groups, n = k^2"),
    "latin_random": (fam_latin_random, "6,8,10,12,14,16", "Latin square graphs of random squares"),
    "bilinear": (fam_bilinear, "3:3:2,2:4:2,2:4:3,3:4:2,2:5:2", "class-2 exp-p: alternating maps"),
    "sts": (fam_sts, "13,15,19,21,25,27,31,33,37", "random Steiner triple systems (incidence)"),
    "gq": (fam_gq, "2,3,5", "GQ W(q) vs Q(4,q) collinearity graphs"),
    "symplectic": (fam_symplectic, "2,3,4", "symplectic graphs Sp(2m,2)"),
    "hadamard": (fam_hadamard, "8,12,16,20,24,32,44,48,60,68,72", "Hadamard graphs, n = 4m"),
    "plane": (fam_plane, "2,3,4,5,7,8,9", "projective planes; Hall(9) vs PG(2,9)"),
    "paley": (fam_paley, "29,61,101,149,197,257", "Paley graphs"),
    "cayley2": (fam_cayley2, "5,6,7,8", "random Cayley graphs of Z_2^d"),
}


def parse_size(s):
    return tuple(int(t) for t in s.split(":")) if ":" in s else int(s)


# ---------------------------------------------------------------------------
# measurement

class TracingSolver(Solver):
    """Solver with extra counters (the algorithm is unchanged)."""

    def __init__(self, **kw):
        super().__init__(**kw)
        self._ctx = []
        self._ldepth = 0

    def _in(self, tag, f, *a):
        self._ctx.append(tag)
        try:
            return f(*a)
        finally:
            self._ctx.pop()

    def young_step(self, G, x, y, known=None):
        return self._in("young", super().young_step, G, x, y, known)

    def individualize(self, *a):
        return self._in("giant", super().individualize, *a)

    def branch_labels(self, G, phi, sym, Cx, Cy, refined, x, y, known, seeds=()):
        tag = self._ctx[-1] if self._ctx else "other"
        st = self.stats

        def counted(l, g, z):
            st["try_" + tag] += 1
            return refined(l, g, z)
        self._ldepth += 1
        st["label_depth"] = max(st["label_depth"], self._ldepth)
        st[f"bl_calls_d{self._ldepth}"] += 1
        try:
            return super().branch_labels(G, phi, sym, Cx, Cy, counted, x, y, known, seeds)
        finally:
            self._ldepth -= 1


class Timeout(Exception):
    pass


def _alarm(signum, frame):
    raise Timeout()


def group_order(gens):
    from sympy.combinatorics import Permutation, PermutationGroup
    if not gens:
        return 1
    return PermutationGroup([Permutation(list(g)) for g in gens]).order()


def check(I, res, aut):
    X, Y, cx, cy = I["X"], I["Y"], I["cx"], I["cy"]
    n = len(X)
    if (res is not None) != I["expect"]:
        return False, "wrong iso decision"
    if res is None:
        return True, ""
    sigma, gens = res
    if sorted(sigma) != list(range(n)) or any(
            Y[sigma[i]][sigma[j]] != X[i][j] for i in range(n) for j in range(n)):
        return False, "returned map is not an isomorphism"
    if cx is not None and any(cy[sigma[i]] != cx[i] for i in range(n)):
        return False, "returned map does not preserve colors"
    for g in gens:
        if any(X[g[i]][g[j]] != X[i][j] for i in range(n) for j in range(n)):
            return False, "a generator is not an automorphism"
        if cx is not None and any(cx[g[i]] != cx[i] for i in range(n)):
            return False, "a generator does not preserve colors"
    if aut is not None:
        order = group_order(gens)
        if order != aut:
            return False, f"|<gens>| = {order}, expected {aut}"
        return True, f"|Aut|={order}"
    return True, ""


def nauty_graph(A, colors):
    n = len(A)
    kw = {}
    if colors is not None:
        vals = sorted(set(colors))
        kw["vertex_coloring"] = [set(i for i in range(n) if colors[i] == c) for c in vals]
    return pynauty.Graph(n, adjacency_dict={i: [j for j in range(n) if A[i][j] and j != i]
                                            for i in range(n)}, **kw)


def nauty_answer(I):
    """(iso, |Aut(X)|, seconds) by nauty."""
    t0 = time.perf_counter()
    GX, GY = nauty_graph(I["X"], I["cx"]), nauty_graph(I["Y"], I["cy"])
    same = pynauty.certificate(GX) == pynauty.certificate(GY)
    _, s1, s2, _, _ = pynauty.autgrp(GX)
    dt = time.perf_counter() - t0
    aut = round(s1 * 10 ** s2)
    if s2 > 12:                         # float precision: do not check exactly
        aut = None
    return same, aut, dt


def prepare(I):
    """Fix the expected answer (claim, checked by nauty when available)."""
    I["n"] = len(I["X"])
    if pynauty is not None:
        same, aut, dt = nauty_answer(I)
        if I["claim"] is not None and I["claim"] != same:
            raise AssertionError(f"{I['name']}: claim {I['claim']} but nauty says {same}")
        I["expect"], I["aut"], I["nauty_time"] = same, aut, dt
    else:
        if I["claim"] is None:
            I["expect"] = None
        else:
            I["expect"] = I["claim"]
        I["aut"], I["nauty_time"] = None, None
    return I


def run_ours(I, mode, timeout, profile=False, solver_args=None, graph_pick="small"):
    S = TracingSolver(certificates=False, **(solver_args or {}))
    gk = dict(vcolors_x=I["cx"], vcolors_y=I["cy"])
    if mode == "ir0":
        gk["ir"] = 0
    ir_depth = [0]
    orig = gigraph.individualize

    def ind(solver, n, x, y, method, factors, fixed, C, pol, depth, need_all, known=None):
        if graph_pick == "large":
            # individualize in the largest non-uniform Sym factor instead of the
            # smallest (exact: any Sym factor of G gives an exhaustive split)
            cand = [P for P, g in factors if g is None and len(P) >= pol.ir_min
                    and not gigraph.sym_clean(x, y, P, P)]
            if cand:
                C = max(cand, key=lambda P: (len(P), -P[0]))
        ir_depth[0] = max(ir_depth[0], depth)
        solver.stats[f"ir_ind_d{depth}"] += 1
        return orig(solver, n, x, y, method, factors, fixed, C, pol, depth, need_all, known)
    gigraph.individualize = ind
    prof = cProfile.Profile() if profile else None
    t0 = time.perf_counter()
    status, note, res = "ok", "", None
    signal.setitimer(signal.ITIMER_REAL, timeout)
    try:
        if prof:
            prof.enable()
        res = graph_iso(I["X"], I["Y"], solver=S, **gk)
        if prof:
            prof.disable()
        signal.setitimer(signal.ITIMER_REAL, 0)
    except Timeout:
        status = "timeout"
    except Unsupported as e:
        signal.setitimer(signal.ITIMER_REAL, 0)
        status, note = "unsupported", str(e)
    except RecursionError:
        signal.setitimer(signal.ITIMER_REAL, 0)
        status = "recursion"
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        gigraph.individualize = orig
        if prof:
            prof.disable()
    dt = time.perf_counter() - t0
    if status == "ok":
        if I["expect"] is None:
            note = "unchecked (no nauty)"
        else:
            ok, note = check(I, res, I["aut"])
            status = "ok" if ok else "WRONG"
    st = dict(S.stats)
    st["ir_depth"] = ir_depth[0]
    out = dict(status=status, time=round(dt, 3), note=note, stats=st)
    if prof:
        s = io.StringIO()
        pstats.Stats(prof, stream=s).sort_stats("cumulative").print_stats(40)
        out["profile"] = s.getvalue()
    return out


KEYS = ("branch", "try_young", "try_giant", "ir_branch", "label_depth", "ir_depth",
        "giant_step", "young_ind", "young_split", "enum_cosets", "product_cosets",
        "scheme_johnson", "scheme_hamming", "pruned", "ir_pruned", "stage", "cont")


def short_stats(st):
    return " ".join(f"{k}={st[k]}" for k in KEYS if st.get(k))


def cmd_run(args):
    fam, default_sizes, _ = FAMILIES[args.family]
    sizes = [parse_size(s) for s in (args.sizes or default_sizes).split(",")]
    modes = args.modes.split(",")
    only = set(filter(None, args.only.split(",")))
    signal.signal(signal.SIGALRM, _alarm)
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results", "hardness",
                        f"{args.label}.json")
    os.makedirs(os.path.dirname(path), exist_ok=True)
    rows = json.load(open(path))["rows"] if (args.append and os.path.exists(path)) else []
    dead = set()            # (mode, name-stem) that timed out: skip larger sizes
    solver_args = json.loads(args.solver_args)
    for size in sizes:
        rng = random.Random(f"{args.family}:{size}:{args.seed}")
        t0 = time.perf_counter()
        insts = fam(size, rng)
        tb = time.perf_counter() - t0
        for I in insts:
            if only and I["name"] not in only:
                continue
            prepare(I)
            kind = "iso" if I["expect"] else "non"
            print(f"# {I['name']} n={I['n']} expect={I['expect']} |Aut|={I['aut']} "
                  f"(built {tb:.1f}s)", flush=True)
            for mode in modes:
                row = dict(family=args.family, size=size, name=I["name"], n=I["n"], kind=kind,
                           mode=mode, aut=I["aut"])
                if mode == "nauty":
                    if I["nauty_time"] is None:
                        continue
                    row.update(status="ok", time=round(I["nauty_time"], 5), stats={})
                elif (mode, kind) in dead:
                    row.update(status="skipped", time=None, stats={})
                else:
                    row.update(run_ours(I, mode, args.timeout, args.profile, solver_args,
                                        args.graph_pick))
                    if row["status"] == "timeout":
                        dead.add((mode, kind))
                print(f"  {mode:5s} {row['status']:8s} "
                      f"{(row['time'] if row['time'] is not None else float('nan')):9.3f}s  "
                      f"{row.get('note', '')}  {short_stats(row['stats'])}", flush=True)
                if "profile" in row:
                    print(row.pop("profile"))
                rows.append(row)
                with open(path, "w") as f:
                    json.dump(dict(label=args.label, rows=rows), f, indent=1)
    wrong = [r for r in rows if r["status"] == "WRONG"]
    print(f"\n{args.label}: {len(rows)} rows, wrong {len(wrong)}")
    sys.exit(1 if wrong else 0)


# ---------------------------------------------------------------------------
# growth fits

def lstsq(xs, ys):
    """y = a + b x; returns (a, b, rss)."""
    k = len(xs)
    mx, my = sum(xs) / k, sum(ys) / k
    sxx = sum((x - mx) ** 2 for x in xs)
    b = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sxx if sxx else 0.0
    a = my - b * mx
    rss = sum((y - a - b * x) ** 2 for x, y in zip(xs, ys))
    return a, b, rss


MODELS = {
    "poly   y = A n^c": lambda n: math.log(n),
    "quasi  y = A n^(c log2 n)": lambda n: math.log(n) * math.log2(n),
    "exp    y = A 2^(c n)": lambda n: n * math.log(2),
    "subexp y = A 2^(c sqrt n)": lambda n: math.sqrt(n) * math.log(2),
}


def fit(ns, ys):
    """For each model: (c, rss of log y, leave-last-out relative error of the
    largest point, in factors). Returns a list of dicts."""
    out = []
    ly = [math.log(y) for y in ys]
    for name, f in MODELS.items():
        xs = [f(n) for n in ns]
        a, c, rss = lstsq(xs, ly)
        tss = sum((v - sum(ly) / len(ly)) ** 2 for v in ly)
        r2 = 1 - rss / tss if tss else 1.0
        if len(ns) >= 4:
            a2, c2, _ = lstsq(xs[:-1], ly[:-1])
            pred = a2 + c2 * xs[-1]
            loo = math.exp(abs(ly[-1] - pred))
        else:
            loo = None
        out.append(dict(model=name, c=c, r2=r2, rss=rss, last_factor=loo))
    return out


def local_exponents(ns, ys):
    """d log y / d log n between consecutive points."""
    return [(ns[i + 1], math.log(ys[i + 1] / ys[i]) / math.log(ns[i + 1] / ns[i]))
            for i in range(len(ns) - 1) if ys[i] > 0 and ns[i + 1] != ns[i]]


def cmd_fit(args):
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results", "hardness",
                        f"{args.label}.json")
    import re
    rows = load_rows(args.label.split(","))
    groups = {}
    for r in rows:
        if r["status"] != "ok" or (args.filter and not re.search(args.filter, r["name"])):
            continue
        v = (r["time"] if args.metric == "time" else branches(r["stats"])
             if args.metric == "branches" else r["stats"].get(args.metric, 0))
        if v is None:
            continue
        stem = r["name"].split("-")[0] if args.by == "kind" else r["name"]
        key = (r["mode"], r["kind"]) if args.by == "kind" else (r["mode"], r["name"])
        groups.setdefault(key, []).append((r["n"], max(v, args.floor)))
    for key in sorted(groups):
        pts = sorted(groups[key])
        # one value per n (max over instances of that kind and size)
        agg = {}
        for n, v in pts:
            agg[n] = max(agg.get(n, 0), v)
        ns, ys = list(agg), [agg[n] for n in agg]
        print(f"\n== {args.label} {key} metric={args.metric}: " +
              ", ".join(f"n={n}: {y:.4g}" for n, y in zip(ns, ys)))
        if len(ns) < 3:
            print("   (fewer than 3 sizes: no fit)")
            continue
        print("   local exponents d log y / d log n: " +
              ", ".join(f"{n}: {e:.2f}" for n, e in local_exponents(ns, ys)))
        for f in fit(ns, ys):
            lf = f"{f['last_factor']:.2f}x" if f["last_factor"] else "-"
            print(f"   {f['model']:28s} c={f['c']:.4f}  R2={f['r2']:.4f}  "
                  f"rss={f['rss']:.4f}  leave-last-out error {lf}")


def load_rows(labels):
    rows = []
    for lab in labels:
        path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results", "hardness",
                            f"{lab}.json")
        rows += json.load(open(path))["rows"]
    return rows


def branches(st):
    """All branch attempts: graph-level individualization branches plus label
    branches (refinements tried) of the Young step and the GiantStep."""
    return st.get("ir_branch", 0) + st.get("try_young", 0) + st.get("try_giant", 0)


def cmd_table(args):
    """Markdown table: one line per instance, columns per mode."""
    rows = load_rows(args.labels.split(","))
    by = {}
    order = []
    for r in rows:
        k = r["name"]
        if k not in by:
            order.append(k)
            by[k] = {"n": r["n"], "kind": r["kind"]}
        by[k][r["mode"]] = r            # later rows (re-runs) win
    modes = args.modes.split(",")
    hdr = "| instance | n | " + " | ".join(
        f"{m} s | {m} br (depth)" if m != "nauty" else "nauty s" for m in modes) + " |"
    print(hdr)
    print("|" + "---|" * (2 + sum(1 if m == "nauty" else 2 for m in modes)))
    for k in order:
        e = by[k]
        cells = [k + ("" if e["kind"] == "iso" else " (non-iso)"), str(e["n"])]
        for m in modes:
            r = e.get(m)
            if r is None:
                cells += ["-"] if m == "nauty" else ["-", "-"]
                continue
            if m == "nauty":
                cells.append(f"{r['time']:.3g}")
                continue
            st = r["stats"]
            t = f"{r['time']:.3g}" if r["status"] == "ok" else (
                f">{r['time']:.0f}" if r["status"] == "timeout" else r["status"])
            d = max(st.get("label_depth", 0), 0) + st.get("ir_depth", 0)
            cells += [t, f"{branches(st)} ({st.get('ir_depth', 0)}+{st.get('label_depth', 0)})"
                      if r["status"] in ("ok", "timeout") else "-"]
        print("| " + " | ".join(cells) + " |")


def cmd_list(args):
    for k, (_, sizes, d) in FAMILIES.items():
        print(f"{k:14s} sizes {sizes:36s} {d}")


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run")
    r.add_argument("--family", required=True)
    r.add_argument("--sizes", default="")
    r.add_argument("--modes", default="full,ir0,nauty")
    r.add_argument("--only", default="")
    r.add_argument("--timeout", type=float, default=300)
    r.add_argument("--label", default="")
    r.add_argument("--seed", type=int, default=0)
    r.add_argument("--append", action="store_true")
    r.add_argument("--profile", action="store_true")
    r.add_argument("--solver-args", default="{}")
    r.add_argument("--graph-pick", default="small", choices=("small", "large"),
                   help="graph-level individualization target: smallest (default, as in "
                        "gi.graph) or largest non-uniform Sym factor (prototype)")
    f = sub.add_parser("fit")
    f.add_argument("--label", required=True)
    f.add_argument("--metric", default="time")
    f.add_argument("--by", default="kind", choices=("kind", "name"))
    f.add_argument("--floor", type=float, default=1e-3)
    f.add_argument("--filter", default="", help="regex on instance names")
    t = sub.add_parser("table")
    t.add_argument("--labels", required=True)
    t.add_argument("--modes", default="full,ir0,nauty")
    sub.add_parser("list")
    args = ap.parse_args()
    if args.cmd == "run":
        args.label = args.label or args.family
        cmd_run(args)
    elif args.cmd == "fit":
        cmd_fit(args)
    elif args.cmd == "table":
        cmd_table(args)
    else:
        cmd_list(args)


if __name__ == "__main__":
    main()
