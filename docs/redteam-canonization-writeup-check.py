"""Brute-force check of the canonical Luks reduction in docs/canonization-bounded-degree.md, section 8.

For small connected graphs of maximum degree d (q = d - 1) and every ordered edge (u, v) this
implements the layer step r -> r+1 literally as written:
  * Hhat = S_q wr_L Ahat_r acting on Xi_r = [N_r] + (L x [q]) + (L x [q])^2, ordered as in the text;
  * the slot string x_{lam,beta} (occupancy, "=", "E", "!=", 0 on unoccupied pairs, * on [N_r]);
  * Fhat = lexicographically least image under Hhat (a valid Hhat-canonizer, standing in for Theorem A);
  * CF_{r+1} read off Fhat; mu(lam, beta, hhat); theta on Aut_Hhat(Fhat).
and checks, by exhaustive enumeration:
  Claim 1  every (lam in Lambda_r, beta) gives a string in one Hhat-orbit (same Fhat);
  Claim 3  X_{r+1}^mu = CF_{r+1} for every output mu;
  Claim 4  {mu(lam, beta, hhat)} = Lambda_{r+1} (all rooted labellings onto CF_{r+1});
  Claim 5  theta(Aut_Hhat(Fhat)) = Aut(CF_{r+1}; 1, 2);
  (I_r)    Ahat_r in Gamma_{d-1} is implied by Claim 5 (not tested separately);
and end to end:
  invariance  CF(X, u, v) = CF(X^pi, u^pi, v^pi) for random relabellings pi;
  Step 1      CF(X) = min over ordered edges is invariant, and the union of the minimizing
              Lambda(X, u, v) equals the set of all bijections lam with X^lam = CF(X);
  Step 0      the component rule (components sorted by (size, form)) is invariant under
              relabelling and reordering of the components (disconnected inputs).
Claims 1, 3 and 4 enumerate all (lam, beta) when there are at most MAX_PAIRS of them, otherwise
(lam0, beta0) plus a random sample; Claim 4 is checked as equality with the brute-force Lambda_{r+1}.
Conventions follow section 2.1: right actions, x^g(alpha) = x(alpha^{g^-1}); labels are 0-based
(roots u -> 0, v -> 1). Run: nice python3 -I docs/redteam-canonization-writeup-check.py
"""
import itertools
import random
import sys

random.seed(20261105)
STAR, EQ, EDGE, NEQ = 9, 3, 4, 5  # string symbols; 0/1 = unoccupied/occupied slot, 0 on unoccupied pairs
MAX_PAIRS = 40  # cap on the (lam, beta) pairs enumerated for Claims 1, 3, 4 per layer


def perms(seq):
    return [tuple(p) for p in itertools.permutations(seq)]


def graph_edges_relabel(edges, lab):
    return frozenset(frozenset((lab[a], lab[b])) for a, b in (tuple(e) for e in edges))


def adj_of(n, edges):
    A = {v: set() for v in range(n)}
    for e in edges:
        a, b = tuple(e)
        A[a].add(b)
        A[b].add(a)
    return A


def enc(N, E):
    """Adjacency string of a graph on [N] (upper triangle), for lexicographic comparison."""
    return tuple(1 if frozenset((i, j)) in E else 0 for i in range(N) for j in range(i + 1, N))


def layers(n, A, u, v):
    dist = {u: 0, v: 0}
    frontier = [u, v]
    while frontier:
        nxt = []
        for y in frontier:
            for w in A[y]:
                if w not in dist:
                    dist[w] = dist[y] + 1
                    nxt.append(w)
        frontier = nxt
    R = max(dist.values())
    return [sorted(w for w in dist if dist[w] == r) for r in range(R + 1)], dist


def induced(E, S):
    return frozenset(e for e in E if e <= S)


def rooted_auts(N, E):
    """Aut(CF; 0, 1) by brute force: permutations of [N] fixing 0, 1 and preserving E."""
    out = []
    for p in perms(range(2, N)):
        g = (0, 1) + p
        if all(frozenset((g[a], g[b])) in E for a, b in (tuple(e) for e in E)):
            out.append(g)
    return out


def all_rooted_labellings(Vlist, E, CF, u, v, N):
    """All bijections lam: Vlist -> [N] with u->0, v->1 and E^lam = CF."""
    rest = [w for w in Vlist if w not in (u, v)]
    out = []
    for p in perms(range(2, N)):
        lam = {u: 0, v: 1}
        lam.update(dict(zip(rest, p)))
        if graph_edges_relabel(E, lam) == CF:
            out.append(lam)
    return out


def layer_step(X_E, A, Ls, r, CF_r, Ahat_r, lam0, q, checks=True):
    """One step r -> r+1. Returns CF_{r+1} (edge set on [N_{r+1}]), Ahat_{r+1} (list), mu0."""
    Vle = [w for i in range(r + 1) for w in Ls[i]]
    Vr = Ls[r]
    Vr1 = Ls[r + 1]
    N_r = len(Vle)
    N_r1 = N_r + len(Vr1)
    L = sorted(lam0[y] for y in Vr)  # = I_r, the labels of layer r
    slots = [(l, i) for l in L for i in range(q)]
    pairs = [(s1, s2) for s1 in slots for s2 in slots]
    Xi = [("p", a) for a in range(N_r)] + [("s",) + s for s in slots] + [("q", s1, s2) for s1, s2 in pairs]
    idx = {pt: k for k, pt in enumerate(Xi)}
    down = {y: sorted(w for w in A[y] if w in Vr1) for y in Vr}
    ru = next(y for y in Vle if lam0[y] == 0)  # the roots u -> 0, v -> 1
    rv = next(y for y in Vle if lam0[y] == 1)
    assert all(len(down[y]) <= q for y in Vr), "down-degree > q"

    def string(lam, beta):
        inv = {lam[y]: y for y in Vr}
        slot_end = {}
        for y in Vr:
            for w in down[y]:
                slot_end[(lam[y], beta[y][w])] = w
        x = []
        for pt in Xi:
            if pt[0] == "p":
                x.append(STAR)
            elif pt[0] == "s":
                l, i = pt[1], pt[2]
                x.append(1 if i < len(down[inv[l]]) else 0)
                assert (i < len(down[inv[l]])) == ((l, i) in slot_end)
            else:
                s1, s2 = pt[1], pt[2]
                if s1 in slot_end and s2 in slot_end:
                    w1, w2 = slot_end[s1], slot_end[s2]
                    x.append(EQ if w1 == w2 else (EDGE if frozenset((w1, w2)) in X_E else NEQ))
                else:
                    x.append(0)
        return tuple(x)

    def image_map(ah, s):
        def im(pt):
            if pt[0] == "p":
                return ("p", ah[pt[1]])
            if pt[0] == "s":
                l, i = pt[1], pt[2]
                return ("s", ah[l], s[l][i])
            (l1, i1), (l2, i2) = pt[1], pt[2]
            return ("q", (ah[l1], s[l1][i1]), (ah[l2], s[l2][i2]))
        return [idx[im(pt)] for pt in Xi]

    Sq = perms(range(q))
    Hhat = []
    for ah in Ahat_r:
        for choice in itertools.product(Sq, repeat=len(L)):
            s = dict(zip(L, choice))
            Hhat.append(((ah, s), image_map(ah, s)))

    def act(x, img):
        inv = [0] * len(img)
        for a, b in enumerate(img):
            inv[b] = a
        return tuple([x[a] for a in inv])

    Hinv = []
    for h, img in Hhat:
        inv = [0] * len(img)
        for a, b in enumerate(img):
            inv[b] = a
        Hinv.append((h, img, inv))

    def canon(x):
        best, Lam = None, []
        for h, img, inv in Hinv:
            y = tuple([x[a] for a in inv])  # x^h, using x^h(alpha^h) = x(alpha)
            if best is None or y < best:
                best, Lam = y, [(h, img)]
            elif y == best:
                Lam.append((h, img))
        return best, Lam

    def betas():
        per = []
        for y in Vr:
            k = len(down[y])
            per.append([dict(zip(down[y], p)) for p in itertools.permutations(range(k))])
        for combo in itertools.product(*per):
            yield dict(zip(Vr, combo))

    beta0 = next(betas())
    x0 = string(lam0, beta0)
    Fhat, Lamhat = canon(x0)

    # read off CF_{r+1}
    occ = [s for s in slots if Fhat[idx[("s",) + s]] == 1]
    cls = []
    for s in occ:  # occ is in slot order, so classes come out ordered by least slot
        for c in cls:
            if Fhat[idx[("q", c[0], s)]] == EQ:
                c.append(s)
                break
        else:
            cls.append([s])
    assert len(cls) == len(Vr1)
    cls_of = {s: j for j, c in enumerate(cls) for s in c}
    CF1 = set(CF_r)
    for s in occ:
        CF1.add(frozenset((s[0], N_r + cls_of[s])))
    for s1 in occ:
        for s2 in occ:
            if Fhat[idx[("q", s1, s2)]] == EDGE:
                CF1.add(frozenset((N_r + cls_of[s1], N_r + cls_of[s2])))
    CF1 = frozenset(CF1)

    def mu_of(lam, beta, h):
        (ah, s) = h
        mu = {y: ah[lam[y]] for y in Vle}
        for w in Vr1:
            y = next(y for y in Vr if w in down[y])
            sl = (lam[y], beta[y][w])
            img = (ah[sl[0]], s[sl[0]][sl[1]])
            mu[w] = N_r + cls_of[img]
        return mu

    mu0 = mu_of(lam0, beta0, Lamhat[0][0])
    X1 = induced(X_E, frozenset(Vle + Vr1))
    Ahat1 = rooted_auts(N_r1, CF1)

    if checks:
        # Claim 1: one orbit (same Fhat) for all lam in Lambda_r and all beta
        Lam_r = all_rooted_labellings(Vle, induced(X_E, frozenset(Vle)), CF_r, ru, rv, N_r)
        assert {tuple(sorted(m.items())) for m in Lam_r} == {
            tuple(sorted({y: ah[lam0[y]] for y in Vle}.items())) for ah in Ahat_r}, "Lambda_r != lam0 Ahat_r"
        allpairs = [(lam, beta) for lam in Lam_r for beta in betas()]
        if len(allpairs) > MAX_PAIRS:  # always keep (lam0, beta0); sample the rest
            allpairs = [(lam0, beta0)] + random.sample(allpairs, MAX_PAIRS - 1)
        outs = set()
        for lam, beta in allpairs:
            if True:
                x = string(lam, beta)
                F, Lh = canon(x)
                assert F == Fhat, "Claim 1 fails"
                for h, _ in Lh:
                    mu = mu_of(lam, beta, h)
                    assert graph_edges_relabel(X1, mu) == CF1, "Claim 3 fails"
                    outs.add(tuple(sorted(mu.items())))
        brute = all_rooted_labellings(Vle + Vr1, X1, CF1, ru, rv, N_r1)
        assert outs == {tuple(sorted(m.items())) for m in brute}, "Claim 4 fails"
        # Claim 5: theta(Aut_Hhat(Fhat)) = Aut(CF_{r+1}; 0, 1)
        th = set()
        for h, img in Hhat:
            if act(Fhat, img) == Fhat:
                ah, s = h
                g = list(ah) + [None] * len(Vr1)
                for j, c in enumerate(cls):
                    sl = c[0]
                    im = (ah[sl[0]], s[sl[0]][sl[1]])
                    g[N_r + j] = N_r + cls_of[im]
                th.add(tuple(g))
        assert th == set(Ahat1), "Claim 5 fails"
    return CF1, Ahat1, mu0, len(Xi), len(Hhat)


def canon_rooted(n, E, u, v, q, checks):
    A = adj_of(n, E)
    Ls, _ = layers(n, A, u, v)
    CF = frozenset([frozenset((0, 1))])
    Ahat = [(0, 1)]
    lam = {u: 0, v: 1}
    stats = []
    for r in range(len(Ls) - 1):
        CF, Ahat, lam, xi, hh = layer_step(E, A, Ls, r, CF, Ahat, lam, q, checks)
        stats.append((xi, hh))
    assert graph_edges_relabel(E, lam) == CF
    return CF, lam, Ahat, stats


def canon_connected(n, E, q, checks):
    best, Lam = None, []
    for e in E:
        a, b = tuple(e)
        for u, v in ((a, b), (b, a)):
            CF, lam, Ahat, _ = canon_rooted(n, E, u, v, q, checks)
            k = enc(n, CF)
            if best is None or k < best[0]:
                best, Lam = (k, CF), [(u, v, lam, Ahat)]
            elif k == best[0]:
                Lam.append((u, v, lam, Ahat))
    return best[1], Lam


def all_labellings_onto(n, E, CF):
    return [p for p in perms(range(n)) if graph_edges_relabel(E, dict(enumerate(p))) == CF]


def random_connected(n, d):
    while True:
        E = set()
        deg = [0] * n
        order = list(range(n))
        random.shuffle(order)
        for i in range(1, n):  # random tree first, respecting max degree
            cands = [order[j] for j in range(i) if deg[order[j]] < d]
            if not cands:
                break
            a = random.choice(cands)
            b = order[i]
            E.add(frozenset((a, b)))
            deg[a] += 1
            deg[b] += 1
        else:
            for _ in range(random.randint(0, n)):
                a, b = random.sample(range(n), 2)
                if frozenset((a, b)) not in E and deg[a] < d and deg[b] < d:
                    E.add(frozenset((a, b)))
                    deg[a] += 1
                    deg[b] += 1
            return frozenset(E)


def arithmetic_section7():
    """Section 7.3 Claim, step 4, and the Lemma 7.0(A) semi-regular inequality, checked numerically."""
    import math
    worst = None
    for k in range(13, 5001):
        # largest k' with k'!/2 <= k!/(4/3)^k  (log2 scale, exact via lgamma)
        rhs = (math.lgamma(k + 1) - k * math.log(4 / 3)) / math.log(2)
        kp = max(j for j in range(1, k + 1) if math.lgamma(j + 1) / math.log(2) - 1 <= rhs + 1e-9)
        slack = (k - kp) - k / (3 * math.log2(k))
        assert slack >= 0, (k, kp)
        worst = slack if worst is None else min(worst, slack)
    for b in range(2, 200):
        for K in range(1, 30):
            # per branch: pieces of size <= n/b summing to n; worst case is b pieces of size n/b
            assert b * b * (1 / b) ** (K + 1) <= 1 + 1e-12
    return worst


def main():
    w = arithmetic_section7()
    print(f"section 7.3 step 4: k - k' >= k/(3 log2 k) holds for 13 <= k <= 5000 (min slack {w:.3f})")
    tests = 0
    maxxi = 0
    fixed = {
        "K4": (4, 3, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]),
        "C6": (6, 3, [(i, (i + 1) % 6) for i in range(6)]),
        "prism": (6, 3, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (0, 3), (1, 4), (2, 5)]),
        "K33": (6, 3, [(a, b) for a in range(3) for b in range(3, 6)]),
        "star4+": (6, 4, [(0, 1), (0, 2), (0, 3), (0, 4), (4, 5), (1, 2)]),
        "K5": (5, 4, [(a, b) for a in range(5) for b in range(a + 1, 5)]),
        "W4": (5, 4, [(0, i) for i in range(1, 5)] + [(1, 2), (2, 3), (3, 4), (4, 1)]),
    }
    cases = [(name, n, d, frozenset(frozenset(e) for e in E)) for name, (n, d, E) in fixed.items()]
    for k in range(40):
        d = random.choice([3, 3, 4])
        n = random.choice([5, 6, 7, 8]) if d == 3 else random.choice([5, 6, 7])
        cases.append((f"rand{k}", n, d, random_connected(n, d)))
    for name, n, d, E in cases:
        q = d - 1
        CF, Lam = canon_connected(n, E, q, checks=True)
        # Step 1: union of minimizing Lambda(X,u,v) = all lam with X^lam = CF
        got = set()
        for u, v, lam, Ahat in Lam:
            for ah in Ahat:
                got.add(tuple(ah[lam[w]] for w in range(n)))
        brute = set(all_labellings_onto(n, E, CF))
        assert got == brute, f"Step 1 fails on {name}"
        # invariance under relabelling
        for _ in range(2):
            pi = list(range(n))
            random.shuffle(pi)
            E2 = graph_edges_relabel(E, dict(enumerate(pi)))
            CF2, _ = canon_connected(n, E2, q, checks=False)
            assert CF2 == CF, f"invariance fails on {name}"
        _, _, _, stats = canon_rooted(n, E, *tuple(next(iter(E))), q, checks=False)
        maxxi = max([maxxi] + [s[0] for s in stats])
        tests += 1
        print(f"ok {name:8s} n={n} d={d} |E|={len(E)} |Aut(CF)|={len(brute)} min-edges={len(Lam)}")
    # Step 0: disconnected inputs
    comp_tests = 0
    for k in range(6):
        parts = []
        for _ in range(random.choice([2, 3])):
            m = random.choice([1, 2, 3, 4])
            parts.append((m, random_connected(m, 3) if m > 1 else frozenset()))
        if random.random() < 0.5:
            parts.append(parts[0])  # force a repeated component
        n = sum(m for m, _ in parts)
        E, off, comps = set(), 0, []
        for m, Ec in parts:
            for e in Ec:
                a, b = tuple(e)
                E.add(frozenset((a + off, b + off)))
            comps.append(list(range(off, off + m)))
            off += m
        pi = list(range(n))
        random.shuffle(pi)
        E = graph_edges_relabel(frozenset(E), dict(enumerate(pi)))
        comps = [[pi[w] for w in c] for c in comps]

        def cf_disconnected(E, comps):
            forms = []
            for c in comps:
                loc = {w: i for i, w in enumerate(c)}
                Ec = frozenset(frozenset((loc[a], loc[b])) for a, b in (tuple(e) for e in E) if a in loc and b in loc)
                if len(c) == 1:
                    forms.append((1, enc(1, Ec), Ec))
                else:
                    CFc, _ = canon_connected(len(c), Ec, 2, checks=False)
                    forms.append((len(c), enc(len(c), CFc), CFc))
            forms.sort(key=lambda f: (f[0], f[1]))
            out, off = set(), 0
            for m, _, CFc in forms:
                for e in CFc:
                    a, b = tuple(e)
                    out.add(frozenset((a + off, b + off)))
                off += m
            return frozenset(out)

        CF = cf_disconnected(E, comps)
        pi2 = list(range(n))
        random.shuffle(pi2)
        E2 = graph_edges_relabel(E, dict(enumerate(pi2)))
        comps2 = [[pi2[w] for w in c] for c in comps]
        random.shuffle(comps2)
        assert cf_disconnected(E2, comps2) == CF, "Step 0 invariance fails"
        assert sorted(len(c) for c in comps) == sorted(len(c) for c in comps2)
        comp_tests += 1
    print(f"all checks passed: {tests} connected graphs (all ordered edges, all layers), "
          f"{comp_tests} disconnected; max |Xi_r| = {maxxi}")


if __name__ == "__main__":
    sys.exit(main())
