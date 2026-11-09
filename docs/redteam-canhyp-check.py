"""Toy check of paper/canon.tex section 10.9 (CanHyp), Lemmas W, F2^set, B, E4, SIMP, and the
virtual-size bookkeeping.  Standard library only.  Run under `nice python3 -I` (about a minute).

What it covers:
  A. CanHyp-lite on sets of P-strings under tiny groups: Steps 0, 1, 2, 3(a) with Chain, Luks,
     Lemma B, Lemma W, F2^set and E4 implemented as written.  Giant steps 3(b)/4 are out of reach of
     tiny groups (they need k > 10t >= 90); see part C for the local-certificates loop.
     Checked: (C1), (C2), left-coset shape, and strict decrease of the measure (s, |G|) at every call.
     Mutants: right-multiplied cosets, no linking graph, input-dependent orbit choice in Chain and
     Lemma B, one branch only in Luks, omitted pi in E4, no complete occupancy at the root.
  B. Lemma SIMP (S2), (S3), (S4 total) and the false (S4 second half), and the fix (S4').
     The worst case of (IV) is simulated numerically.  Mutant: no Step 3 (fails the estimate).
  C. Toy CanLC loop (H = S_5, t = 3, Omega of 10 points): ECM property, invariants, (LC3),
     strict decrease of the corrected potential; mutant: renormalization seeded from raw data.
  D. Explicit counterexample to Neu20 Thm 4.17(G) / (S4) second half.
  E. The A_k parity construction of Prop. opt1.

Right actions: x^(gh) = (x^g)^h; compose(g, h) applies g first.
"""
import itertools
import random
import sys
import zlib

BOT = 9  # the padding letter


def ident(n):
    return tuple(range(n))


def compose(g, h):
    return tuple(h[g[i]] for i in range(len(g)))


def inverse(g):
    inv = [0] * len(g)
    for i, gi in enumerate(g):
        inv[gi] = i
    return tuple(inv)


def closure(gens, n):
    idn = ident(n)
    seen = {idn}
    frontier = [idn]
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = compose(x, g)
                if y not in seen:
                    seen.add(y)
                    new.append(y)
        frontier = new
    return frozenset(seen)


def orbits(G, D):
    seen, orbs = set(), []
    for a in sorted(D):
        if a not in seen:
            o = frozenset(g[a] for g in G)
            seen |= o
            orbs.append(tuple(sorted(o)))
    orbs.sort(key=lambda o: (len(o), o[0]))
    return orbs


# -- P-strings: a string is (P, x), P a sorted tuple, x a tuple of values aligned with P.


def act_s(s, g):
    P, x = s
    vals = {g[a]: v for a, v in zip(P, x)}
    Q = tuple(sorted(vals))
    return (Q, tuple(vals[a] for a in Q))


def act(Z, g):
    return frozenset(act_s(s, g) for s in Z)


def restrict(Z, U):
    U = set(U)
    out = set()
    for P, x in Z:
        Q = tuple(a for a in P if a in U)
        if Q:
            out.add((Q, tuple(v for a, v in zip(P, x) if a in U)))
    return frozenset(out)


def key(Z):
    return tuple(sorted(Z))


def m_of(Z, P):
    return sum(1 for (Q, _) in Z if Q == P)


def vsize(Z, partition, f=1):
    return sum(len(P) * m_of(Z, P) ** (f + 1) for P in partition)


def shat(Z, partition, W, f=1):
    """the corrected out-of-window potential: sum |P \\ W| m_Z(P)^(f+1)"""
    W = set(W)
    return sum(sum(1 for a in P if a not in W) * m_of(Z, P) ** (f + 1) for P in partition)


def restrict_part(partition, U):
    U = set(U)
    out = []
    for P in partition:
        Q = tuple(a for a in P if a in U)
        if Q:
            out.append(Q)
    return out


def complete(Z, partition):
    return all(m_of(Z, P) >= 1 for P in partition)


def restrict_group(G, V):
    """the restriction of G to V, extended by the identity"""
    n = len(next(iter(G)))
    V = set(V)
    return frozenset(tuple(g[i] if i in V else i for i in range(n)) for g in G)


def stab_set(G, U):
    U = set(U)
    return frozenset(g for g in G if {g[a] for a in U} == U)


def act_block(P, g):
    return tuple(sorted(g[a] for a in P))


class Stats:
    def __init__(self):
        self.measure_fail = 0
        self.calls = 0


def lemma_W(R2, U, V, F, FV, y):
    """Lemma W (with brute-force Theorem A/Cor D on the linking graph).  Returns (F_W, E, R3)."""
    Ws = set(U) | set(V)
    verts = sorted(F) + sorted(FV)
    idx = {v: i for i, v in enumerate(verts)}

    def theta(h):
        return tuple(idx[act_s(v, h)] for v in verts)

    def link(Z):
        Uset, Vset = set(U), set(V)
        edges = set()
        for P, x in Z:
            PU = tuple(a for a in P if a in Uset)
            PV = tuple(a for a in P if a in Vset)
            if PU and PV:
                s1 = (PU, tuple(v for a, v in zip(P, x) if a in Uset))
                s2 = (PV, tuple(v for a, v in zip(P, x) if a in Vset))
                i, j = idx[s1], idx[s2]
                edges.add((min(i, j), max(i, j)))
        return frozenset(edges)

    def act_edges(E, th):
        return frozenset((min(th[i], th[j]), max(th[i], th[j])) for i, j in E)

    graph = link(y)
    thetas = {h: theta(h) for h in R2}
    best = None
    for h in R2:
        k = tuple(sorted(act_edges(graph, thetas[h])))
        if best is None or k < best:
            best = k
    E = frozenset(h for h in R2 if tuple(sorted(act_edges(graph, thetas[h]))) == best)
    sigma = min(E)
    R3 = frozenset(compose(inverse(sigma), e) for e in E)
    # F_W decoded from the canonical graph: strings of F, FV on one-side blocks, unions over edges
    out = set()
    cover = set()
    for i, j in best:
        (Q1, z1), (Q2, z2) = verts[i], verts[j]
        cover |= {verts[i], verts[j]}
        vals = dict(zip(Q1, z1))
        vals.update(zip(Q2, z2))
        Q = tuple(sorted(vals))
        out.add((Q, tuple(vals[a] for a in Q)))
    Uset, Vset = set(U), set(V)
    block_of = {}
    for (Q, _z) in list(F) + list(FV):
        block_of[Q] = None
    for (Q, z) in list(F) + list(FV):
        # a vertex on a block meeting both sides lies on at least one edge of y, hence of the canonical graph
        if (Q, z) not in cover:
            out.add((Q, z))
    return frozenset(out), E, R3


def canhyp_chain(A, Z, dom, part, seq, stats, mutant):
    """Chain(A, Z)"""
    n = len(next(iter(A)))
    R = A
    pi = ident(n)
    U = ()
    F = frozenset()
    while set(U) != set(dom):
        rest = [a for a in dom if a not in set(U)]
        orbs = orbits(R, rest)
        if mutant == "input_orbit":
            z = act(Z, pi)
            V = min(orbs, key=lambda O: sorted(x for _, x in restrict(z, O)))   # compares values only
        else:
            V = orbs[0]
        w = act(Z, pi)
        RV = restrict_group(R, V)
        partV = restrict_part(part, V)
        seqV = [restrict_part(lv, V) for lv in seq]
        dedup = []
        for lv in seqV:
            if not dedup or lv != dedup[-1]:
                dedup.append(lv)
        FV, LamV = canhyp(tuple(V), RV, partV, dedup, restrict(w, V), stats, (vsize(Z, part), len(A)), mutant)
        Lam_lift = frozenset(r for r in R if tuple(r[i] if i in set(V) else i for i in range(n)) in LamV)
        lam = min(Lam_lift)
        y = act(w, lam)
        R2 = frozenset(r for r in R if act(FV, r) == FV)
        if mutant == "no_link":
            F_plus = frozenset(F | FV)
            sigma, R3 = ident(n), R2
        else:
            F_plus, E, R3 = lemma_W(R2, U, V, F, FV, y)
            sigma = next(iter(E))
            assert restrict(act(y, sigma), set(U) | set(V)) == F_plus, "Lemma W: decoding mismatch"
            assert E == frozenset(compose(sigma, r) for r in R3), "Lemma W: not a left coset"
        if mutant == "right":
            pi = compose(sigma, compose(lam, pi))
        else:
            pi = compose(pi, compose(lam, sigma))
        R = R3
        U = tuple(sorted(set(U) | set(V)))
        F = F_plus
    return F, frozenset(compose(pi, r) for r in R)


def lemma_B(A, part, Z, mutant):
    """Lemma B: returns (pi, R) with Z^pi balanced on every R-orbit"""
    n = len(next(iter(A)))
    pi = ident(n)
    R = A
    dom = sorted({a for P in part for a in P})
    while True:
        z = act(Z, pi)
        unb = []
        for O in orbits(R, dom):
            blocks = restrict_part(part, O)
            zO = restrict(z, O)
            if len({m_of(zO, Q) for Q in blocks}) > 1:
                unb.append(O)
        if not unb:
            return pi, R
        if mutant == "balance_input":
            O = min(unb, key=lambda O: tuple(m_of(restrict(z, O), Q) for Q in restrict_part(part, O)))   # position-dependent
        else:
            O = unb[0]
        blocks = restrict_part(part, O)
        zO = restrict(z, O)
        mu = {Q: m_of(zO, Q) for Q in blocks}
        B = {r: tuple(mu[act_block(Q, inverse(r))] for Q in blocks) for r in R}  # mu^r(Q^r) = mu(Q)
        best = min(B.values())
        E = frozenset(r for r in R if B[r] == best)
        sigma = next(iter(sorted(E)))
        R2 = frozenset(compose(inverse(sigma), e) for e in E)
        assert len(R2) < len(R), "Lemma B: right group did not shrink"
        pi = compose(pi, sigma)
        R = R2


def luks(A, D_, Z, dom, part, seq, stats, mutant):
    pi, B = lemma_B(A, part, Z, mutant)
    y = act(Z, pi)
    if len(orbits(B, dom)) > 1:
        F, Lam = canhyp_chain(B, y, dom, part, seq, stats, mutant)
    else:
        kernel = frozenset(g for g in B if all(act_block(Q, g) == Q for Q in D_))
        reps = []
        seen = set()
        for g in sorted(B):
            if g not in seen:
                reps.append(g)
                seen |= {compose(g, k) for k in kernel}
        results = []
        if mutant == "first_coset":
            reps = reps[:1]
        for rho in reps:
            Fr, Lr = canhyp_chain(kernel, act(y, rho), dom, part, seq, stats, mutant)
            results.append((key(Fr), Fr, frozenset(compose(rho, l) for l in Lr)))
        m = min(r[0] for r in results)
        F = next(r[1] for r in results if r[0] == m)
        Lam = frozenset().union(*[r[2] for r in results if r[0] == m])
    if mutant == "omit_pi":
        return F, Lam
    return F, frozenset(compose(pi, l) for l in Lam)


def is_invariant(partition, G):
    S = set(partition)
    return all(act_block(Q, g) in S for Q in partition for g in G)


def coarsenings(partition, G):
    """all G-invariant strict coarsenings of partition (brute force), with at least two classes"""
    k = len(partition)
    if k > 8:
        return []
    out = []
    labels = [0] * k

    def rec(i, maxl):
        if i == k:
            if maxl >= 2 and maxl < k:
                classes = [[] for _ in range(maxl)]
                for j, l in enumerate(labels):
                    classes[l] += partition[j]
                cand = [tuple(sorted(c)) for c in classes]
                if is_invariant(cand, G):
                    out.append(sorted(cand))
            return
        for l in range(maxl + 1):
            labels[i] = l
            rec(i + 1, max(maxl, l + 1))

    rec(0, 0)
    return out


def canhyp(dom, G, part, seq, X, stats, parent, mutant):
    stats.calls += 1
    mu = (vsize(X, part), len(G))
    if parent is not None and not mu < parent:
        stats.measure_fail += 1
    if len(dom) == 1:
        return X, G
    if len(orbits(G, dom)) > 1:
        return canhyp_chain(G, X, dom, part, seq, stats, mutant)
    B1 = seq[1]
    # the action on B1 is semi-regular iff nontrivial elements fix no block
    induced = {}
    for g in G:
        induced[tuple(act_block(Q, g) for Q in B1)] = g
    semireg = all(all(a != b for a, b in zip(x, B1)) or x == tuple(B1) for x in induced)
    if semireg:
        return luks(G, B1, X, dom, part, seq, stats, mutant)
    # Step 3: maximal block system above B1 on which G is primitive (brute force, P1)
    coarse = coarsenings(B1, G)
    if coarse:
        # primitive quotient: a block system with no invariant coarsening between it and {Omega}
        best = None
        for c in coarse:
            if not coarsenings(c, G):
                if best is None or (len(c), c) < (len(best), best):
                    best = c
        D_ = best if best else B1
    else:
        D_ = B1
    return luks(G, D_, X, dom, part, seq, stats, mutant)


# -- instances -------------------------------------------------------------------------------

GROUPS = []


def _make_groups():
    # (name, n, generators, sequence of invariant partitions from top to discrete)
    def disc(n):
        return [(i,) for i in range(n)]

    def top(n):
        return [tuple(range(n))]

    wr23 = closure([(1, 0, 2, 3, 4, 5), (2, 3, 4, 5, 0, 1), (2, 3, 0, 1, 4, 5)], 6)   # S2 wr S3 (order 48)
    wr32 = closure([(1, 2, 0, 3, 4, 5), (1, 0, 2, 3, 4, 5), (3, 4, 5, 0, 1, 2)], 6)   # S3 wr S2 (order 72)
    c6 = closure([(1, 2, 3, 4, 5, 0)], 6)
    d6 = closure([(1, 2, 3, 4, 5, 0), (0, 5, 4, 3, 2, 1)], 6)
    int33 = closure([(1, 2, 0, 3, 4, 5), (1, 0, 2, 3, 4, 5), (0, 1, 2, 4, 5, 3)], 6)  # S3 x C3, intransitive
    s4 = closure([(1, 2, 3, 0), (1, 0, 2, 3)], 4)
    a4x = closure([(1, 2, 0, 3, 4, 5), (1, 0, 3, 2, 4, 5), (0, 1, 2, 3, 5, 4)], 6)    # A4 x S2, intransitive
    GROUPS.extend([
        ("S2wrS3", 6, wr23, [top(6), [(0, 1), (2, 3), (4, 5)], disc(6)]),
        ("S3wrS2", 6, wr32, [top(6), [(0, 1, 2), (3, 4, 5)], disc(6)]),
        ("C6", 6, c6, [top(6), [(0, 2, 4), (1, 3, 5)], disc(6)]),
        ("D6", 6, d6, [top(6), [(0, 3), (1, 4), (2, 5)], disc(6)]),
        ("S3xC3", 6, int33, [top(6), [(0, 1, 2), (3, 4, 5)], disc(6)]),
        ("S4", 4, s4, [top(4), disc(4)]),
        ("A4xS2", 6, a4x, [top(6), [(0, 1, 2, 3), (4, 5)], disc(6)]),
    ])


def rand_instance(rng):
    name, n, G, seq = rng.choice(GROUPS)
    part = rng.choice(seq)
    X = set()
    for P in part:
        m = rng.randint(1, 3)
        for _ in range(m):
            X.add((P, tuple(rng.randint(0, 1) for _ in P)))
    return n, G, seq, part, frozenset(X)


def run_canhyp(n, G, seq, part, X, mutant):
    stats = Stats()
    F, L = canhyp(tuple(range(n)), G, part, seq, X, stats, None, mutant)
    return F, L, stats


def part_A(rng, trials=110):
    print("A. CanHyp-lite (Steps 0,1,2,3(a); Chain, Luks, Lemmas B, W, F2^set, E4)")
    print("   mutant          (C1)bad (C2)bad coset-bad measure-bad   calls")
    ok = True
    expected_fail = {"none": False, "right": True, "no_link": True, "input_orbit": True,
                     "balance_input": False, "first_coset": True, "omit_pi": True, "no_occupancy": True}
    for mutant in ["none", "right", "no_link", "input_orbit", "balance_input", "first_coset", "omit_pi", "no_occupancy"]:
        c1 = c2 = cs = ms = calls = 0
        loc = random.Random(zlib.crc32(mutant.encode()) ^ 20261108)
        for _ in range(trials if mutant == "none" else trials // 3):
            n, G, seq, part, X = rand_instance(loc)
            if mutant == "no_occupancy":
                if len(part) >= 2:
                    # drop every string of one block (the root instance is no longer completely occupied)
                    victim = part[0]
                    X = frozenset(s for s in X if s[0] != victim) or X
                else:
                    continue
            base = "none" if mutant == "no_occupancy" else mutant
            try:
                F, L, stats = run_canhyp(n, G, seq, part, X, base)
            except (AssertionError, KeyError):   # a mutant broke an internal invariant: detected
                if mutant == "none":
                    raise
                c1 += 1
                continue
            calls += stats.calls
            ms += stats.measure_fail
            exact = frozenset(g for g in G if act(X, g) == F)
            if mutant != "no_occupancy":
                if L != exact or not L:
                    c1 += 1
                c = next(iter(L)) if L else None
                if L and c is not None:
                    Rr = frozenset(compose(inverse(c), l) for l in L)
                    if len(Rr) != len(L) or not all(compose(a, b) in Rr for a in list(Rr)[:6] for b in list(Rr)[:6]):
                        cs += 1
                sample = sorted(G)
                loc.shuffle(sample)
                for g in sample[:12]:
                    try:
                        Fg, Lg, _ = run_canhyp(n, G, seq, part, act(X, g), base)
                    except (AssertionError, KeyError):
                        c2 += 1
                        break
                    if key(Fg) != key(F) or Lg != frozenset(compose(inverse(g), l) for l in L):
                        c2 += 1
                        break
        fail = (c1 + c2 + cs + ms) > 0
        print(f"   {mutant:15s} {c1:6d} {c2:7d} {cs:9d} {ms:10d} {calls:8d}  -> {'FAILS' if fail else 'passes'}"
              f" (expected {'fail' if expected_fail[mutant] else 'pass'})")
        ok &= (fail == expected_fail[mutant])
    return ok


# -- SIMP --------------------------------------------------------------------------------------


def simp_copy(A, part, Wset, F):
    """Step 1 of Lemma SIMP.  Returns Omega' as a list of (alpha, z), an index, the partition P',
    W', and psi'(g) as a tuple on indices; z is the window string (a canonical tuple) of the copy."""
    F_by_block = {}
    for Q, z in F:
        F_by_block.setdefault(Q, []).append((Q, z))
    pts, new_blocks = [], []
    for P in part:
        Q = tuple(a for a in P if a in Wset)
        zs = sorted(F_by_block.get(Q, [])) if Q else [("", ())]
        for z in zs:
            new_blocks.append((P, z))
            pts += [(a, z) for a in P]
    index = {p: i for i, p in enumerate(pts)}
    P2 = [tuple(sorted(index[(a, z)] for a in P)) for (P, z) in new_blocks]
    W2 = tuple(sorted(i for (a, z), i in index.items() if a in Wset))

    def psi1(g):
        def imz(z):
            if z == ("", ()):
                return z
            return act_s(z, g)
        return tuple(index[(g[a], imz(z))] for (a, z) in pts)

    psi = {g: psi1(g) for g in A}
    return pts, index, P2, W2, psi


def simp_object(Z, pts, index, Wset):
    """Z -> Z' of Step 1"""
    out = set()
    for P, x in Z:
        Q = tuple(a for a in P if a in Wset)
        if Q:
            z = (Q, tuple(v for a, v in zip(P, x) if a in Wset))
        else:
            z = ("", ())
        Pp = tuple(sorted(index[(a, z)] for a in P))
        vals = {index[(a, z)]: v for a, v in zip(P, x)}
        out.add((Pp, tuple(vals[i] for i in Pp)))
    return frozenset(out)


def is_simple(F):
    seen = set()
    for Q, _ in F:
        if Q in seen:
            return False
        seen.add(Q)
    return True


def part_D():
    print("D. Counterexample to Neu20 Thm 4.17(G) / the second half of (S4)")
    ok = True
    n = 4
    A = frozenset([ident(n)])
    part = [(0, 1), (2, 3)]
    Wset = {0, 2}
    Z = frozenset([((0, 1), (0, 0)), ((0, 1), (1, 0)), ((2, 3), (0, 0))])
    F = restrict(Z, Wset)
    pts, index, P2, W2, psi = simp_copy(A, part, Wset, F)
    Zp = simp_object(Z, pts, index, Wset)
    out = [i for i in range(len(pts)) if i not in set(W2)]
    before = vsize(restrict(Z, [1, 3]), restrict_part(part, [1, 3]))
    after = vsize(restrict(Zp, out), restrict_part(P2, out))
    hat_before = shat(Z, part, Wset)
    hat_after = shat(Zp, P2, W2)
    print(f"   virtual size of Z[Omega-W] = {before}; of Z'[Omega'-W'] = {after}  (the claim was after <= before)")
    print(f"   the corrected potential: {hat_before} -> {hat_after}")
    ok &= after > before and hat_after <= hat_before
    return ok


def part_B(rng, trials=120):
    print("B. Lemma SIMP (Step 1 and Step 3; Step 4 simulated at the worst case of (IV))")
    groups = GROUPS
    viol_total = viol_hat = viol_second = viol_nobal = 0
    bad_inj = bad_equiv = bad_simple = bad_occ = 0
    n_nonsimple = 0
    for t in range(trials):
        if t % 2 == 0:
            # the generic case
            name, n, G, seq = rng.choice(groups)
            part = rng.choice(seq)
            orbs = orbits(G, range(n))
            # W: a union of G-orbits; Z with Z[W] = F and G[W] <= Aut(F)
            W = tuple(sorted(a for O in orbs if rng.random() < 0.5 for a in O))
            Wset = set(W)
            X = set()
            for P in part:
                for _ in range(rng.randint(1, 3)):
                    X.add((P, tuple(rng.randint(0, 1) for _ in P)))
        else:
            # targeted: S3 x S3 on {0,1,2} + {3,4,5}, one block, window the first orbit; the window
            # strings are permuted transitively and the out-of-window parts collide
            n = 6
            G = closure([(1, 2, 0, 3, 4, 5), (1, 0, 2, 3, 4, 5), (0, 1, 2, 4, 5, 3), (0, 1, 2, 4, 3, 5)], 6)
            part = [tuple(range(6))]
            W = (0, 1, 2)
            Wset = set(W)
            X = set()
            wins = [(1, 0, 0), (0, 1, 0), (0, 0, 1)]
            outs = [(0, 0, 0), (1, 1, 1), (1, 0, 0)]
            for wv in wins:
                for ov in rng.sample(outs, rng.randint(1, 2)):
                    X.add((part[0], wv + ov))
            if rng.random() < 0.4:
                X.add((part[0], wins[0] + outs[2]))
        Z0 = frozenset(X)
        # choose A to be the stabiliser of F := Z0[W], so that A[W] <= Aut(F) holds
        F = restrict(Z0, Wset)
        A = frozenset(g for g in G if act(F, g) == F)
        if is_simple(F):
            continue
        n_nonsimple += 1
        pts, index, P2, W2, psi = simp_copy(A, part, Wset, F)
        Zp = simp_object(Z0, pts, index, Wset)
        n2 = len(pts)
        # (S3) injectivity and equivariance of Step 1 on the orbit
        for g in list(A)[:30]:
            Zg = act(Z0, g)
            if simp_object(Zg, pts, index, Wset) != act(Zp, psi[g]):
                bad_equiv += 1
                break
        # Step 3: canonical string x(Z') under psi(A)[P'], then A''' = its stabilizer
        Wp = set(W2)
        def xstr(Y):
            Yout = restrict(Y, [i for i in range(n2) if i not in Wp])
            res = {}
            for Q in P2:
                Qout = tuple(a for a in Q if a not in Wp)
                res[Q] = (m_of(Y, Q), m_of(Yout, Qout) if Qout else 0)
            return res

        def action_string(g2, val):
            return tuple(val[act_block(Q, g2)] for Q in P2)

        x0 = xstr(Zp)
        best = min(action_string(psi[g], x0) for g in A)
        coset = [g for g in A if action_string(psi[g], x0) == best]
        pi = coset[0]
        Appp = frozenset(psi[compose(inverse(pi), c)] for c in coset)
        Zpp = simp_object(act(Z0, pi), pts, index, Wset)
        # sanity: Z'' = Z'^{psi(pi)}
        if Zpp != act(Zp, psi[pi]):
            bad_equiv += 1
        if not complete(Zpp, P2):
            bad_occ += 1
        if restrict(Zpp, W2) != restrict(Zp, W2) or not is_simple(restrict(Zpp, W2)):
            bad_simple += 1
        # (S4), total: with |f'^{-1}(P')| = |A_{P'}|^f (worst case of (IV)), f = 1
        for grp_name, Gr in (("A'''", Appp), ("psi(A) [mutant: no Step 3]", frozenset(psi.values()))):
            # orbit of P' under the stabilizer of its base block B_P in the group
            base = {}
            for Q in P2:
                a = Q[0]
                alpha = pts[a][0]
                P = next(p for p in part if alpha in p)
                base[Q] = P
            orbit_of = {}
            for Q in P2:
                P = base[Q]
                Hp = [h for h in Gr if base[act_block(Q, h)] == P]  # elements of the group fixing B_P on this copy
                orb = {act_block(Q, h) for h in Hp}
                orbit_of[Q] = orb
            total = sum(len(Q) * m_of(Zpp, Q) ** 2 * len(orbit_of[Q]) for Q in P2)
            hat = sum(sum(1 for a in Q if a not in Wp) * m_of(Zpp, Q) ** 2 * len(orbit_of[Q]) for Q in P2)
            if grp_name.startswith("A"):
                if total > vsize(Z0, part):
                    viol_total += 1
                if hat > shat(Z0, part, Wset):
                    viol_hat += 1
                out = [i for i in range(n2) if i not in Wp]
                Y = restrict(Zpp, out)
                Yp = restrict_part(P2, out)
                outs = [a for a in range(n) if a not in Wset]
                if outs and sum(len(Q) * m_of(Y, Q) ** 2 for Q in Yp) > vsize(restrict(act(Z0, pi), outs), restrict_part(part, outs)):
                    viol_second += 1
            else:
                if total > vsize(Z0, part):
                    viol_nobal += 1
    print(f"   non-simple windows tested: {n_nonsimple}")
    print(f"   (S3) equivariance failures {bad_equiv}; occupancy failures {bad_occ}; simplicity failures {bad_simple}")
    print(f"   (S4), total virtual size failures {viol_total}; corrected potential failures {viol_hat}")
    print(f"   (S4), second half (claim of the paper and of Neu20 (G)): failures {viol_second}")
    print(f"   mutant without Step 3 violates the total estimate on {viol_nobal} instances")
    return bad_equiv == bad_occ == bad_simple == viol_total == viol_hat == 0 and viol_second > 0 and viol_nobal > 0


# -- toy CanLC ---------------------------------------------------------------------------------


K = 5
T0 = (0, 1, 2)
N_LC = 10  # Omega = [5] x {0,1}, H = S_5 acting diagonally: point i+5j


def lc_groups():
    base = list(itertools.permutations(range(K)))
    def lift(p):
        return tuple(p[i % K] + K * (i // K) for i in range(N_LC))
    H = [lift(p) for p in base]
    H0 = [lift(p) for p in base if set(p[i] for i in T0) == set(T0)]
    return H, H0


def psi_of(g):
    return tuple(T0.index(g[i]) for i in T0)


def is_giant_T(elts):
    s = set(elts)
    return (1, 2, 0) in s and (2, 0, 1) in s


def lc_rand(rng):
    """a completely occupied set invariant under Sym(T_0): the same strings on the three T_0-blocks"""
    part = [(i, i + K) for i in range(K)]
    X = set()
    common = [(rng.randint(0, 1), rng.randint(0, 1)) for _ in range(rng.randint(2, 3))]
    for i in T0:
        for v in common:
            X.add((part[i], v))
    for P in part[len(T0):]:
        for _ in range(rng.randint(1, 3)):
            X.add((P, (rng.randint(0, 1), rng.randint(0, 1))))
    return part, frozenset(X)


def lc_stable_seed(*objs):
    return zlib.crc32(repr(objs).encode())


def run_lc(Z, part, H0, mutant="none"):
    """Toy CanLC: returns (C, flag, data, inv_fail, s_up)"""
    n = len(next(iter(H0)))
    pi = ident(n)
    Lam = list(H0)          # group on the current domain
    tau = {g: g for g in Lam}  # current group element -> element of H0
    cur = Z                 # current object on the current domain, the image of Z^pi
    dom = list(range(N_LC))
    P_cur = part
    W_cur = set()
    F_cur = frozenset()
    inv_fail = 0
    s_up = 0
    psi_tau = lambda l: psi_of(tau[l])
    rounds = 0
    potential = shat(cur, P_cur, W_cur)
    out_prev = vsize(restrict(cur, [a for a in dom if a not in W_cur]), restrict_part(P_cur, [a for a in dom if a not in W_cur]))
    while True:
        rounds += 1
        if rounds > 60:
            return None, "diverged", None, 1, 0
        if not is_giant_T({psi_tau(l) for l in Lam}):
            return _lc_out(pi, Lam, tau, "nonfull", F_cur, inv_fail, s_up)
        # affected points
        Aff = []
        for a in dom:
            st = [l for l in Lam if l[a] == a]
            if not is_giant_T({psi_tau(l) for l in st}):
                Aff.append(a)
        W2 = [a for a in Aff if a not in W_cur]
        if not W2:
            # full: Delta = tau(pointwise stabilizer of dom - W)
            outs = [a for a in dom if a not in W_cur]
            Delta = [l for l in Lam if all(l[a] == a for a in outs)]
            if not all(act(cur, l) == cur for l in Delta):
                inv_fail += 1
            return _lc_out(pi, Lam, tau, "full", F_cur, inv_fail, s_up)
        # Lemma B under Lam
        sigma, Lam2 = lemma_B_group(Lam, P_cur, cur)
        pi = compose(pi, tau[sigma])
        cur = act(cur, sigma)
        psi_t2 = {psi_tau(l) for l in Lam2}
        if not is_giant_T(psi_t2):
            return _lc_out(pi, Lam2, {l: tau[l] for l in Lam2}, "nonfull", F_cur, inv_fail, s_up)
        Lam = list(Lam2)
        tau = {l: tau[l] for l in Lam}
        # windows: Lam-orbits of W2 in (size, least) order, each brute-force canonized under the current R
        R = frozenset(Lam)
        F = F_cur
        U = sorted(W_cur)
        for O in orbits(Lam, W2):
            lamO = lambda r: tuple(key(restrict(act(cur, r), O)))
            restr = {r: restrict(act(cur, r), O) for r in R}
            best = min(key(v) for v in restr.values())
            cands = [r for r in R if key(restr[r]) == best]
            lam = min(cands)
            y = act(cur, lam)
            FV = restr[lam]
            R2 = frozenset(r for r in R if act(FV, r) == FV)
            if not U:
                # no window yet: Lemma W with W1 empty does nothing
                Fplus, E, R3 = lemma_W(R2, (), tuple(O), frozenset(), FV, y)
            else:
                Fplus, E, R3 = lemma_W(R2, tuple(U), tuple(O), F, FV, y)
            s0 = next(iter(E))
            pi = compose(pi, compose(tau[lam], tau[s0]))
            cur = act(y, s0)
            R = R3
            F = Fplus
            U = sorted(set(U) | set(O))
        W_new = set(U)
        Lam = sorted(R)
        tau = {l: tau[l] for l in Lam}
        F_cur = restrict(cur, W_new)
        if F_cur != F:
            inv_fail += 1
        # potential after window extension (it must drop by at least |W2| and the window virtual size)
        pot_after_window = shat(cur, P_cur, W_new)
        if not pot_after_window <= potential - len(W2):
            inv_fail += 1
        # Simplify (Steps 1, 3) and a pseudo-random renormalization relabelling
        if not is_simple(F_cur):
            pts, index, P2, W2p, psi = simp_copy(Lam, P_cur, W_new, F_cur)
            Zp = simp_object(cur, pts, index, W_new)
            n2 = len(pts)
            wp = set(W2p)

            def xstr(Y):
                outs2 = [i for i in range(n2) if i not in wp]
                Yout = restrict(Y, outs2)
                res = {}
                for Q in P2:
                    Qout = tuple(a for a in Q if a not in wp)
                    res[Q] = (m_of(Y, Q), m_of(Yout, Qout) if Qout else 0)
                return res

            x0 = xstr(Zp)
            best = min(tuple(x0[act_block(Q, psi[l])] for Q in P2) for l in Lam)
            coset = [l for l in Lam if tuple(x0[act_block(Q, psi[l])] for Q in P2) == best]
            sigma2 = coset[0]
            Lam3 = [compose(inverse(sigma2), c) for c in coset]
            pi = compose(pi, tau[sigma2])
            cur2 = act(cur, sigma2)
            Zpp = simp_object(cur2, pts, index, W_new)
            if not complete(Zpp, P2):
                inv_fail += 1
            seed_src = key(Z) if mutant == "raw_seed" else (best, tuple(P2), tuple(sorted(W2p)), key(restrict(Zpp, W2p)), tuple(sorted(Lam3)))
            rho = list(range(n2))
            random.Random(lc_stable_seed(seed_src)).shuffle(rho)
            rho_inv = inverse(tuple(rho))
            newpi = {}
            newLam = []
            for l in Lam3:
                im = tuple(rho[psi[l][rho_inv[j]]] for j in range(n2))
                newLam.append(im)
                newpi[im] = tau[l]
            tau = newpi
            Lam = newLam
            P_cur = sorted(tuple(sorted(rho[i] for i in Q)) for Q in P2)
            dom = list(range(n2))
            W_cur = {rho[i] for i in W2p}
            def rel(s):
                Q, x = s
                vals = {rho[a]: v for a, v in zip(Q, x)}
                Q2 = tuple(sorted(vals))
                return (Q2, tuple(vals[a] for a in Q2))
            cur = frozenset(rel(s) for s in Zpp)
            F_cur = restrict(cur, W_cur)
            if not is_simple(F_cur):
                inv_fail += 1
            if not complete(cur, P_cur):
                inv_fail += 1
        else:
            W_cur = W_new
        # invariants: (I2) Lam preserves F on the window; (I4') the corrected potential strictly decreases
        if not all(act(F_cur, l) == F_cur for l in Lam):
            inv_fail += 1
        pot = shat(cur, P_cur, W_cur)
        if pot >= potential:
            inv_fail += 1
        potential = pot
        # the window part is simple, so the corrected potential is the out-of-window virtual size
        outs_chk = [a for a in dom if a not in W_cur]
        chk = vsize(restrict(cur, outs_chk), restrict_part(P_cur, outs_chk)) if outs_chk else 0
        if chk != pot:
            inv_fail += 1
        outs_now = [a for a in dom if a not in W_cur]
        out_val = vsize(restrict(cur, outs_now), restrict_part(P_cur, outs_now)) if outs_now else 0
        if out_val > out_prev:
            s_up += 1
        out_prev = out_val
        F = F_cur


def _lc_out(pi, Lam, tau, flag, F, inv_fail, s_up):
    R = frozenset(tau[l] for l in Lam)
    C = frozenset(compose(pi, r) for r in R)
    return C, flag, key(F), inv_fail, s_up


def lemma_B_group(Lam, part, Z):
    """Lemma B for a general list of permutations, returning (sigma, Lam2) in the Lam frame"""
    n = len(next(iter(Lam)))
    pi = ident(n)
    R = frozenset(Lam)
    dom = sorted({a for P in part for a in P})
    while True:
        z = act(Z, pi)
        unb = []
        for O in orbits(R, dom):
            blocks = restrict_part(part, O)
            zO = restrict(z, O)
            if len({m_of(zO, Q) for Q in blocks}) > 1:
                unb.append(O)
        if not unb:
            return pi, sorted(R)
        O = unb[0]
        blocks = restrict_part(part, O)
        zO = restrict(z, O)
        mu = {Q: m_of(zO, Q) for Q in blocks}
        B = {r: tuple(mu[act_block(Q, inverse(r))] for Q in blocks) for r in R}
        best = min(B.values())
        E = [r for r in R if B[r] == best]
        sigma = sorted(E)[0]
        R = frozenset(compose(inverse(sigma), e) for e in E)
        pi = compose(pi, sigma)


def part_C(rng, trials=40):
    print("C. Toy CanLC loop (H_0 = S_3 x S_2 of S_5 on 10 points, t = 3, psi to Sym(T_0))")
    H, H0 = lc_groups()
    H0set = frozenset(H0)
    ok = True
    results = {}
    for mutant in ("none", "raw_seed"):
        inv = bad = stops_full = stops_nonfull = sups = tried = 0
        loc = random.Random(zlib.crc32(mutant.encode()) ^ 7777)
        for _ in range(trials if mutant == "none" else trials // 2):
            part, Z = lc_rand(loc)
            C, flag, F, ifail, sup = run_lc(Z, part, H0, mutant)
            if C is None:
                inv += 1
                continue
            inv += ifail
            sups += sup
            tried += 1
            if flag == "full":
                stops_full += 1
            else:
                stops_nonfull += 1
            for g in loc.sample(H0, 8):
                Cg, flagg, Fg, _, _ = run_lc(act(Z, g), part, H0, mutant)
                if flagg != flag or Fg != F or Cg != frozenset(compose(inverse(g), c) for c in C):
                    bad += 1
                    break
        results[mutant] = (inv, bad, sups)
        print(f"   mutant {mutant:9s}: instances {tried:3d}, stops full/nonfull {stops_full}/{stops_nonfull},"
              f" invariant failures {inv}, ECM failures {bad}, rounds where s' increased {sups}")
    ok &= results["none"][0] == 0 and results["none"][1] == 0
    ok &= results["raw_seed"][1] > 0
    return ok


def part_E(rng, trials=60):
    print("E. A_k parity construction of Prop. opt1 (k = 5, random 2-ary structures)")
    k = 5
    Sk = list(itertools.permutations(range(k)))

    def parity(g):
        inv = sum(1 for i in range(k) for j in range(i + 1, k) if g[i] > g[j])
        return inv % 2

    Ak = [g for g in Sk if parity(g) == 0]
    t12 = (1, 0) + tuple(range(2, k))

    def actS(A, g):
        return frozenset((g[a], g[b]) for (a, b) in A)

    def canon_S(A):
        return min((tuple(sorted(actS(A, g))) for g in Sk))

    def canon_A(A):
        F = canon_S(A)
        Lam = [g for g in Sk if tuple(sorted(actS(A, g))) == F]
        aut_odd = any(parity(compose(g, inverse(g2))) for g in Lam for g2 in Lam[:1])
        if aut_odd:
            return F, [g for g in Lam if parity(g) == 0]
        if parity(Lam[0]) == 0:
            return F, Lam
        return tuple(sorted(actS(frozenset(F), t12))), [compose(g, t12) for g in Lam]

    bad = 0
    for _ in range(trials):
        A = frozenset((rng.randrange(k), rng.randrange(k)) for _ in range(rng.randint(2, 8)))
        F, L = canon_A(A)
        exact = [g for g in Ak if tuple(sorted(actS(A, g))) == F]
        if sorted(L) != sorted(exact) or not exact:
            bad += 1
        for a in rng.sample(Ak, 6):
            F2, L2 = canon_A(actS(A, a))
            if F2 != F or sorted(L2) != sorted(compose(inverse(a), g) for g in L):
                bad += 1
                break
    print(f"   canonizer failures: {bad}")
    return bad == 0


def part_B2(rng, trials=120):
    print("A2. Lemma B alone: ECM property (diagonal S_3 on 3+3 points, singleton blocks)")
    G = closure([(1, 2, 0, 4, 5, 3), (1, 0, 2, 4, 3, 5)], 6)
    part = [(i,) for i in range(6)]
    res = {}
    for mutant in ("none", "balance_input"):
        bad = 0
        for _ in range(trials):
            X = set()
            for P in part:
                for j in rng.sample(range(5), rng.randint(1, 4)):
                    X.add((P, (j,)))
            Z = frozenset(X)
            pi, R = lemma_B(G, part, Z, mutant)
            C = frozenset(compose(pi, r) for r in R)
            for g in G:
                pi2, R2 = lemma_B(G, part, act(Z, g), mutant)
                if frozenset(compose(pi2, r) for r in R2) != frozenset(compose(inverse(g), c) for c in C):
                    bad += 1
                    break
        res[mutant] = bad
        print(f"   mutant {mutant:14s}: ECM failures {bad}/{trials}")
    return res["none"] == 0 and res["balance_input"] > 0


def main():
    _make_groups()
    rng = random.Random(20261108)
    ok = True
    ok &= part_A(rng)
    ok &= part_B2(rng)
    ok &= part_D()
    ok &= part_B(rng)
    ok &= part_C(rng)
    ok &= part_E(rng)
    print("ALL CHECKS AS EXPECTED" if ok else "UNEXPECTED RESULT")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
