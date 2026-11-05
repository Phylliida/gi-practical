"""Check of the [GAP-1] input against GNS Lemma 7.2 (arXiv:1802.04659v3, L2087, L2126).

G = (S_m wr S_2) x C_q on Omega = [m]^2 x [q] (product action on [m]^2, C_q regular),
B_1 = cells {(a,b)} x [q], C' = rows {a} x [m] x [q], phi = row projection,
x(a,b,c) = [a in U], H = phi^-1(Sym(U) x Sym(U^c)) in G' = S_m x S_m x C_q.
Prints, for small m: primitivity of G on cells, kernel of phi, orbits of H, every block
system of H' = H|Omega' on the cells of Omega', and the image of H'_(C') on each maximal one.
Then the smallest m at which all numeric hypotheses of GNS Lemma 7.2 hold (log = log2).
Run: nice python3 -I docs/redteam-gns-lemma72-check.py
"""
import math
import sys
from itertools import combinations

from sympy.combinatorics import Permutation, PermutationGroup


def build(m, q, U):
    n = m * m * q
    idx = lambda a, b, c: (a * m + b) * q + c

    def perm(f):
        img = [0] * n
        for a in range(m):
            for b in range(m):
                for c in range(q):
                    img[idx(a, b, c)] = idx(*f(a, b, c))
        return Permutation(img)

    def sym_gens(S):  # generators of Sym(S) as maps on [m]
        S = sorted(S)
        if len(S) < 2:
            return []
        t = {S[0]: S[1], S[1]: S[0]}
        cyc = {S[i]: S[(i + 1) % len(S)] for i in range(len(S))}
        return [lambda v, t=t: t.get(v, v), lambda v, cyc=cyc: cyc.get(v, v)]

    row = [perm(lambda a, b, c, s=s: (s(a), b, c)) for s in sym_gens(range(m))]
    col = [perm(lambda a, b, c, s=s: (a, s(b), c)) for s in sym_gens(range(m))]
    swap = perm(lambda a, b, c: (b, a, c))
    cq = perm(lambda a, b, c: (a, b, (c + 1) % q))
    Uc = [a for a in range(m) if a not in U]
    rowU = [perm(lambda a, b, c, s=s: (s(a), b, c)) for s in sym_gens(U) + sym_gens(Uc)]
    return n, idx, row, col, swap, cq, rowU, Uc


def induced(gens, classes, npts):
    """Induced action of permutations on a list of disjoint point sets."""
    where = {}
    for i, C in enumerate(classes):
        for p in C:
            where[p] = i
    out = []
    for g in gens:
        img = [where[g(next(iter(C)))] for C in classes]
        out.append(Permutation(img))
    return PermutationGroup(out) if out else PermutationGroup([Permutation(len(classes) - 1)])


def minimal_block(N, gens, seeds):
    """Atkinson: finest invariant partition in which all seeds lie in one class."""
    parent = list(range(N))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    queue = []
    s0 = seeds[0]
    for s in seeds[1:]:
        a, b = find(s0), find(s)
        if a != b:
            parent[max(a, b)] = min(a, b)
            queue.append((s0, s))
    while queue:
        u, v = queue.pop()
        for g in gens:
            a, b = find(g(u)), find(g(v))
            if a != b:
                parent[max(a, b)] = min(a, b)
                queue.append((g(u), g(v)))
    lab = [find(x) for x in range(N)]
    classes = {}
    for x in range(N):
        classes.setdefault(lab[x], []).append(x)
    return frozenset(frozenset(c) for c in classes.values())


def all_block_systems(N, gens):
    """All block systems of a transitive group (lattice closure of minimal blocks at 0)."""
    systems = {minimal_block(N, gens, [0, b]) for b in range(1, N)}
    changed = True
    while changed:
        changed = False
        for P, Q in combinations(list(systems), 2):
            bp = next(c for c in P if 0 in c)
            bq = next(c for c in Q if 0 in c)
            R = minimal_block(N, gens, sorted(bp | bq))
            if R not in systems:
                systems.add(R)
                changed = True
    return systems


def check(m, q):
    k_U = max(1, round(0.3 * m))
    U = list(range(k_U))
    n, idx, row, col, swap, cq, rowU, Uc = build(m, q, U)
    G = PermutationGroup(row + col + [swap, cq])
    Gp = PermutationGroup(row + col + [cq])
    cells = [frozenset(idx(a, b, c) for c in range(q)) for a in range(m) for b in range(m)]
    rows = [frozenset(idx(a, b, c) for b in range(m) for c in range(q)) for a in range(m)]
    P = induced(G.generators, cells, n)
    print(f"m={m} q={q} |U|={len(U)} n={n}")
    print(f"  |G| = {G.order()} = 2(m!)^2 q: {G.order() == 2 * math.factorial(m)**2 * q}")
    print(f"  G^B1 on {len(cells)} cells: transitive={P.is_transitive()} primitive={P.is_primitive()}")
    # phi = action of G' on rows; its kernel is G'_(C')
    phiG = induced(Gp.generators, rows, n)
    kerphi = PermutationGroup(col + [cq])
    print(f"  |phi(G')| = {phiG.order()} = m!; |ker phi| = |G'|/|phi(G')| = "
          f"{Gp.order() // phiG.order()} = |<columns, C_q>| = {kerphi.order()}")
    H = PermutationGroup(rowU + col + [cq])
    xval = lambda p: 1 if (p // q) // m in U else 0
    assert all(xval(g(p)) == xval(p) for g in H.generators for p in range(n)), "H <= Aut(x)"
    orbs = sorted((len(o) for o in H.orbits()), reverse=True)
    print(f"  H <= Aut_G'(x); |G':H| = {Gp.order() // H.order()} = binom(m,|U|) = "
          f"{math.comb(m, len(U))}; H-orbit sizes {orbs}  (n/2 = {n / 2})")
    # H' = H restricted to Omega' = U^c x [m] x [q]; work on its cells
    cells2 = [frozenset(idx(a, b, c) for c in range(q)) for a in Uc for b in range(m)]
    Hc = induced(H.generators, cells2, n)
    N = len(cells2)
    hg = [lambda v, g=g: g(v) for g in Hc.generators]
    systems = all_block_systems(N, hg)
    nontriv = [S for S in systems if 1 < len(S) < N]
    maximal = [S for S in nontriv
               if not any(T != S and all(any(c <= d for d in T) for c in S) for T in nontriv)]
    print(f"  H' on {N} cells of Omega': transitive={Hc.is_transitive()}, "
          f"{len(nontriv)} nontrivial block systems, sizes {sorted(len(S) for S in nontriv)}")
    # rows / columns of Omega' as partitions of the cell set
    cell_rc = [(a, b) for a in Uc for b in range(m)]
    rowsP = frozenset(frozenset(i for i, (a, b) in enumerate(cell_rc) if a == a0) for a0 in Uc)
    colsP = frozenset(frozenset(i for i, (a, b) in enumerate(cell_rc) if b == b0) for b0 in range(m))
    # H_(C') = elements of H fixing every row: <columns, C_q> (equality by order)
    fixrows = PermutationGroup(col + [cq])
    Hrows = induced(H.generators, rows, n)
    assert all(fixrows.generators[i](p) // (m * q) == p // (m * q)
               for i in range(len(fixrows.generators)) for p in range(n))
    fixrows_order = fixrows.order()
    assert fixrows_order == H.order() // Hrows.order()
    Kc = induced(fixrows.generators, cells2, n)          # H'_(C') acting on the cells of Omega'
    for S in maximal:
        name = "ROWS (= C'[Omega'])" if S == rowsP else "COLUMNS" if S == colsP else "other"
        D = induced(Hc.generators, list(S), N)
        K = induced(Kc.generators, list(S), N)
        print(f"   maximal system {name}: {len(S)} blocks, P' order {D.order()}, "
              f"primitive={D.is_primitive()}, giant={D.order() >= math.factorial(len(S)) // 2}; "
              f"|image of H'_(C') on it| = {K.order()}")
    print(f"  |H'_(C')| = {fixrows_order} = m! q: {fixrows_order == math.factorial(m) * q}")


def threshold():
    lg = math.log2
    for m in range(5, 2000):
        d = m * m
        t = max(9, 3 + lg(d))
        u = round(0.3 * m)
        ok = (m > 10 * t                                                   # k = m > 10t
              and 1 + 2 * lg(math.factorial(m)) >= lg(d) * (1 + lg(d))      # |P| >= d^{1+log d}
              and lg(math.factorial(m)) >= lg(d) * (1 + lg(d))              # |P'| = m! (columns)
              and m >= 24 and u >= t and m - u < 0.75 * m and u >= m / 4)   # aggregation case
        if ok:
            kprime_fix = m - u
            print(f"smallest m with all numeric hypotheses: m = {m} (d = {d}, t = {t:.2f}, "
                  f"10t = {10 * t:.1f}); GNS bound k - k/(3 log k) = {m - m / (3 * lg(m)):.1f}; "
                  f"columns choice: k' = {m}; rows choice (fix): k' = {kprime_fix}")
            return


if __name__ == "__main__":
    for m in [int(a) for a in sys.argv[1:]] or [5, 6, 7, 8]:
        check(m, 2)
    threshold()
