#!/usr/bin/env python
"""Independent checks for docs/redteam-w27-w28.md (run under nice, one process, minutes at most).

  pin [seed]     Theorem G (rho = 1, 2, twins allowed), by exhaustion over G1 x T2: the equivalence in the proof,
                 branch by branch; plus a control with a non-pinning block (the equivalence must fail somewhere).
  pinplus [seed] Theorem G+ (histograms over r left coordinates), same exhaustive test.
  lem31 [seed]   Lemma 3.1 on a genuinely binary tanglegram (comb spines included), frontier computed from the
                 definition of S(u); group orders and flip patterns from nauty.
  p3 m [seed]    existence of the deletion set R in Prop P3: Alt(T)-invariant, off <T> and <T'>, nauty for Aut.
  p3x m kappa    the explicit O(kappa)-line R proposed in the memo (T' fixed pointwise by Stab_GL(R)); m >= 3 kappa.
"""
import sys, random, itertools, collections

# ---------------------------------------------------------------- Theorem G, G+ by exhaustion
def blocks(b, m):
    return list(itertools.product(range(b), repeat=m))


def perms(b):
    return list(itertools.permutations(range(b)))


def top_elements(b, m, fixed=None):
    """T = S_b^m on [b]^m, as dicts v -> v'. fixed: {coord: perm} restricts those coordinates."""
    P = perms(b)
    V = blocks(b, m)
    choices = [([fixed[j]] if fixed and j in fixed else P) for j in range(m)]
    for ts in itertools.product(*choices):
        yield {v: tuple(ts[j][v[j]] for j in range(m)) for v in V}


def g1_elements(b, m, fixed=None):
    P = perms(b)
    V = blocks(b, m)
    for t in top_elements(b, m, fixed):
        for gs in itertools.product(P, repeat=len(V)):
            yield t, dict(zip(V, gs))


def make_instance(b, m, rng, pinrows, control=False, hist_only=False):
    """x: dict (v,i,vp,c) -> symbol. Twin classes per column block; pinrows = list of row blocks that pin."""
    V = blocks(b, m)
    x = {}
    classes = {}
    for vp in V:
        cs = list(range(b)); rng.shuffle(cs)
        cut = rng.randrange(1, b + 1)            # number of twin classes
        cl = [[] for _ in range(cut)]
        for k, c in enumerate(cs):
            cl[k if k < cut else rng.randrange(cut)].append(c)
        classes[vp] = cl
    for v in V:
        for i in range(b):
            for vp in V:
                for cl in classes[vp]:
                    val = rng.randrange(2)
                    for c in cl:
                        x[(v, i, vp, c)] = val
    if not hist_only:
        # force the classes apart on the pinning rows
        for vp in V:
            k = len(classes[vp])
            for attempt in range(1000):
                seen = set()
                for idx, cl in enumerate(classes[vp]):
                    pat = tuple(x[(v, i, vp, cl[0])] for v in pinrows for i in range(b))
                    if pat in seen:
                        break
                    seen.add(pat)
                else:
                    break
                for cl in classes[vp]:
                    v = rng.choice(pinrows); i = rng.randrange(b); val = rng.randrange(4)
                    for c in cl:
                        x[(v, i, vp, c)] = val
    if control:
        # make two non-twin columns of one block agree on the pinning rows
        vp = V[0]
        cs = sorted(range(b))
        a, c = cs[0], cs[1]
        for v in pinrows:
            for i in range(b):
                x[(v, i, vp, c)] = x[(v, i, vp, a)]
        rows = [(v, i) for v in V if v not in pinrows for i in range(b)]
        r = rng.choice(rows)
        x[(r[0], r[1], vp, a)] = 7; x[(r[0], r[1], vp, c)] = 8
    return x


def act(b, m, x, t1, gam1, t2, gam2):
    return {(t1[v], gam1[v][i], t2[vp], gam2[vp][c]): s for (v, i, vp, c), s in x.items()}


def phi(b, s, vp, c, rowseq):
    return tuple(s[(v, i, vp, c)] for (v, i) in rowseq)


def exists_gamma(b, V, x, y, t1, g1, t, rows):
    """direct definition: is there gamma in K2 making (g1,t,gamma) an isomorphism x -> y?"""
    for vp in V:
        vq = t[vp]
        ok = False
        for gam in perms(b):
            if all(y[(t1[v], g1[v][i], vq, gam[c])] == x[(v, i, vp, c)] for (v, i) in rows for c in range(b)):
                ok = True
                break
        if not ok:
            return False
    return True


def tilde(b, V, s, rows, rowtag, ph):
    """x~(r,v') of Theorem G: tag(r) and the multiset of (phi(v',c), s(r,v',c))"""
    out = {}
    for (v, i) in rows:
        for vp in V:
            out[(v, i, vp)] = (rowtag.get((v, i)), tuple(sorted((ph[(vp, c)], s[(v, i, vp, c)]) for c in range(b))))
    return out


def separated_mod_twins(b, V, s, rows, ph):
    for vp in V:
        for c, d in itertools.combinations(range(b), 2):
            if ph[(vp, c)] == ph[(vp, d)] and any(s[(v, i, vp, c)] != s[(v, i, vp, d)] for (v, i) in rows):
                return False
    return True


def rowseq_of(b, B, gauges):
    return [(v, gauges[k][i]) for k, v in enumerate(B) for i in range(b)]


def test_branches(b, m, x, y, B, fixed=None, hist=None):
    """Compare P (exists gamma, rows of B go as prescribed) and Q (x~ -> y~ under G1 x T2) on every branch."""
    V = blocks(b, m)
    rows = [(v, i) for v in V for i in range(b)]
    idg = {v: tuple(range(b)) for v in V}
    seqx = [(v, i) for v in B for i in range(b)]
    def full_phi(s, seq, sig):
        ph = {(vp, c): phi(b, s, vp, c, seq) for vp in V for c in range(b)}
        if hist is not None:
            I = hist
            for vp in V:
                for c in range(b):
                    h = []
                    for u in itertools.product(range(b), repeat=len(I)):
                        su = u if sig is None else tuple(sig[I[k]][u[k]] for k in range(len(I)))
                        h.append(tuple(sorted(s[(v, i, vp, c)] for (v, i) in rows if tuple(v[j] for j in I) == su)))
                    ph[(vp, c)] = (ph[(vp, c)], tuple(h))
        return ph
    phx = full_phi(x, seqx, None)
    if not separated_mod_twins(b, V, x, rows, phx):
        return None
    tagx = {r: k for k, r in enumerate(seqx)}
    xt = tilde(b, V, x, rows, tagx, phx)
    ntest = ndis = npass = nyes = 0
    topperms = [None] if hist is None else [dict(zip(hist, sig)) for sig in itertools.product(perms(b), repeat=len(hist))]
    imgs = list(itertools.product(V, repeat=len(B)))
    for sig in topperms:
        fx = None if sig is None else {j: sig[j] for j in hist}
        for img in imgs:
            if len(set(img)) != len(img):
                continue
            for gs in itertools.product(perms(b), repeat=len(B)):
                seqy = rowseq_of(b, img, gs)
                phy = full_phi(y, seqy, fx)
                # branch rejected when y fails the pinning condition for these images
                pin_y = separated_mod_twins(b, V, y, rows, phy)
                tagy = {r: k for k, r in enumerate(seqy)}
                yt = tilde(b, V, y, rows, tagy, phy)
                for t1, g1 in g1_elements(b, m, fx):
                    if any(((t1[v], g1[v][i]) != seqy[tagx[(v, i)]]) for (v, i) in seqx):
                        continue
                    for t2 in top_elements(b, m):
                        P = exists_gamma(b, V, x, y, t1, g1, t2, rows)
                        Q = pin_y and all(xt[(v, i, vp)] == yt[(t1[v], g1[v][i], t2[vp])] for v, i, vp in xt)
                        ntest += 1
                        nyes += int(P)
                        if P != Q:
                            ndis += 1
    return ntest, ndis, nyes


def run_pin(seed):
    rng = random.Random(seed)
    print("Theorem G exhaustive equivalence (P = exists gamma, Q = x~ -> y~): instances, tests, disagreements, P-true")
    for (b, m, rho, trials) in [(2, 1, 1, 30), (2, 2, 1, 15), (2, 2, 2, 8), (3, 1, 1, 12), (3, 1, 2, 4)]:
        V = blocks(b, m)
        tot = dis = yes = inst = skipped = 0
        for _ in range(trials):
            B = rng.sample(V, rho)
            x = make_instance(b, m, rng, B)
            t1 = rng.choice(list(top_elements(b, m))); g1 = {v: rng.choice(perms(b)) for v in V}
            t2 = rng.choice(list(top_elements(b, m))); g2 = {v: rng.choice(perms(b)) for v in V}
            y = act(b, m, x, t1, g1, t2, g2)
            if rng.random() < 0.3:
                k = rng.choice(list(y)); y[k] = 5
            r = test_branches(b, m, x, y, B)
            if r is None:
                skipped += 1; continue
            inst += 1; tot += r[0]; dis += r[1]; yes += r[2]
        print(f"  b={b} m={m} rho={rho}: instances {inst} (skipped {skipped}), tests {tot}, disagreements {dis}, P-true {yes}")
    # control: two non-twin columns of one block share phi; y differs from x by swapping their entries on one row.
    # Every row multiset agrees, so Q holds at (id, id), but no gamma exists.
    tot = dis = 0
    for _ in range(40):
        b, m = 3, 1
        V = blocks(b, m)
        B = rng.sample(V, 1)
        x = make_instance(b, m, rng, B)
        vp = rng.choice(V)
        a, c = rng.sample(range(b), 2)
        rows2 = rng.sample([(v, i) for v in V if v not in B for i in range(b)], 2)
        for v in B:                                          # same restriction to the pinning rows
            for i in range(b):
                x[(v, i, vp, c)] = x[(v, i, vp, a)]
        for r in rows2:
            x[(r[0], r[1], vp, a)] = 7; x[(r[0], r[1], vp, c)] = 8
        y = dict(x)
        r = rows2[1]
        y[(r[0], r[1], vp, a)], y[(r[0], r[1], vp, c)] = y[(r[0], r[1], vp, c)], y[(r[0], r[1], vp, a)]
        rows = [(v, i) for v in V for i in range(b)]
        seq = [(v, i) for v in B for i in range(b)]
        tag = {q: k for k, q in enumerate(seq)}
        ph = {(w, d): phi(b, x, w, d, seq) for w in V for d in range(b)}
        phy = {(w, d): phi(b, y, w, d, seq) for w in V for d in range(b)}
        xt, yt = tilde(b, V, x, rows, tag, ph), tilde(b, V, y, rows, tag, phy)
        ident = {v: v for v in V}
        idg = {v: tuple(range(b)) for v in V}
        P = exists_gamma(b, V, x, y, ident, idg, ident, rows)
        Q = all(xt[k] == yt[k] for k in xt)
        tot += 1
        dis += int(P != Q)
    print(f"  control (non-pinning block, b=3,m=1): tests {tot}, P != Q in {dis} (must be > 0 for the test to have power)")


def run_pinplus(seed):
    rng = random.Random(seed)
    print("Theorem G+ exhaustive equivalence, rho=0 (histograms alone) and rho=1")
    for (b, m, I, rho, trials) in [(2, 2, [0], 0, 30), (2, 2, [0], 1, 10), (2, 2, [0, 1], 0, 20), (3, 1, [0], 0, 10), (2, 3, [0, 1], 0, 4)]:
        V = blocks(b, m)
        tot = dis = yes = inst = skipped = 0
        for _ in range(trials):
            B = rng.sample(V, rho)
            x = make_instance(b, m, rng, B if rho else [], hist_only=(rho == 0))
            t1 = rng.choice(list(top_elements(b, m))); g1 = {v: rng.choice(perms(b)) for v in V}
            t2 = rng.choice(list(top_elements(b, m))); g2 = {v: rng.choice(perms(b)) for v in V}
            y = act(b, m, x, t1, g1, t2, g2)
            if rng.random() < 0.3:
                k = rng.choice(list(y)); y[k] = 5
            r = test_branches(b, m, x, y, B, hist=I)
            if r is None:
                skipped += 1; continue
            inst += 1; tot += r[0]; dis += r[1]; yes += r[2]
        print(f"  b={b} m={m} I={I} rho={rho}: instances {inst} (skipped: hypothesis fails {skipped}), tests {tot}, disagreements {dis}, P-true {yes}")


# ---------------------------------------------------------------- Lemma 3.1
def rank_f2(rows):
    bas = []
    for r in rows:
        for b_ in bas:
            r = min(r, r ^ b_)
        if r:
            bas.append(r)
    return len(bas), bas


def checks_of(H, s):
    nvar = s
    out = []
    for row in H:
        vs = [j for j in range(s) if row >> j & 1]
        while len(vs) > 3:
            a = nvar; nvar += 1
            out.append((vs[0], vs[1], a))
            vs = [a] + vs[2:]
        out.append(tuple(vs))
    return out, nvar


class Forest:
    def __init__(self):
        self.parent = {}
        self.colour = {}
    def add(self, node, parent, colour):
        self.parent[node] = parent
        self.colour[node] = colour


def comb(F, top, items, tag, ctag=None):
    """binary comb under node top over the given child nodes (each already a node with parent unset).
    tag names the spine nodes; ctag (default tag) is their colour, so mirrored combs get equal colours."""
    ctag = tag if ctag is None else ctag
    if len(items) == 1:
        F.parent[items[0]] = top
        return
    cur = top
    for k, it in enumerate(items):
        if k >= len(items) - 2:
            F.parent[it] = cur
        else:
            n = (tag, 'spine', k)
            F.add(n, cur, ('spine', ctag, k))
            F.parent[it] = cur
            cur = n


def build_tanglegram(H, s, with_u1=True, with_u2=True):
    checks, nvar = checks_of(H, s)
    T = Forest(); Tp = Forest()
    leaves = {}
    # tree T
    T.add('u', None, 'root')
    if with_u1:
        T.add('u1', 'u', 'u1')
        tops = []
        for c, supp in enumerate(checks):
            supp2 = sorted(set(supp)); k = len(supp2)
            g = ('chk', c); T.add(g, None, ('chk', c)); tops.append(g)
            for bits in itertools.product((0, 1), repeat=k - 1):
                full = bits + (sum(bits) % 2,)
                prev = g
                for d in range(1, k):
                    node = ('gad', c, bits[:d])
                    if node not in T.parent:
                        T.add(node, prev, ('gad', c, d))
                    prev = node
                lvs = []
                for pos, w in enumerate(supp2):
                    leaf = ('L', c, full, w)
                    leaves[leaf] = ('leaf', c, pos)
                    T.add(leaf, None, ('leaf', c, pos))
                    lvs.append(leaf)
                comb(T, prev, lvs, ('bot', c, bits), ('bot', c))
        comb(T, 'u1', tops, 'u1comb')
    if with_u2:
        T.add('u2', 'u', 'u2')
        cher = []
        for j in range(s):
            n = ('cherry', j); T.add(n, None, ('cherry', j)); cher.append(n)
            for i in (0, 1):
                leaf = ('L2', j, i)
                leaves[leaf] = ('leaf2', j)
                T.add(leaf, n, ('leaf2', j))
        comb(T, 'u2', cher, 'u2comb')
    # tree T'
    Tp.add('v', None, 'rootp')
    incid = collections.defaultdict(lambda: collections.defaultdict(list))
    if with_u1:
        for leaf in [l for l in leaves if l[0] == 'L']:
            _, c, full, w = leaf
            supp2 = sorted(set(checks[c]))
            incid[(w, full[supp2.index(w)])][c].append(leaf)
    varnodes = []
    for w in range(nvar):
        if not (with_u2 and w < s) and not incid[(w, 0)] and not incid[(w, 1)]:
            continue      # no leaf would hang below this variable in the restricted instance
        vn = ('var', w); Tp.add(vn, None, ('var', w)); varnodes.append(vn)
        for i in (0, 1):
            q = ('q', w, i); Tp.add(q, vn, ('q', w))
            items = []
            if with_u2 and w < s:
                items.append(('L2', w, i))
            for c in sorted(incid[(w, i)]):
                ls = incid[(w, i)][c]
                g = ('inc', w, i, c); Tp.add(g, None, ('inc', w, c))
                comb(Tp, g, ls, ('incb', w, i, c), ('incb', w, c))
                items.append(g)
            if items:
                comb(Tp, q, items, ('qcomb', w, i), ('qcomb', w))
            else:
                # a side with no leaf (unary check): keep the side as a coloured stub leaf-less node
                Tp.colour[q] = ('q-empty', w)
    comb(Tp, 'v', varnodes, 'vcomb')
    return T, Tp, leaves, checks, nvar


def nauty_group(T, Tp, leaves):
    import pynauty
    verts = {}
    def vid(k):
        if k not in verts:
            verts[k] = len(verts)
        return verts[k]
    adj = collections.defaultdict(set)
    colour = {}
    for F, tag in ((T, 'T'), (Tp, 'P')):
        for n, p in F.parent.items():
            key = ('LEAF', n) if n in leaves else (tag, n)
            colour[key] = ('leaf', F.colour.get(n)) if n in leaves else (tag, F.colour.get(n))
            if p is not None:
                pk = (tag, p)
                adj[vid(key)].add(vid(pk)); adj[vid(pk)].add(vid(key))
    for k in colour:
        vid(k)
    cls = collections.defaultdict(set)
    for k, c in colour.items():
        cls[repr(c)].add(verts[k])
    for k, v in verts.items():
        if k not in colour:
            cls['root'].add(v)
    g = pynauty.Graph(len(verts), adjacency_dict={a: list(b_) for a, b_ in adj.items()},
                      vertex_coloring=[cls[c] for c in sorted(cls)])
    grp = pynauty.autgrp(g)
    return grp, verts


def out_degrees(F):
    d = collections.Counter(p for p in F.parent.values() if p is not None)
    return max(d.values())


def leaf_sets(F, leaves):
    ch = collections.defaultdict(list)
    for n, p in F.parent.items():
        if p is not None:
            ch[p].append(n)
    memo = {}
    def L(n):
        if n in memo:
            return memo[n]
        r = {n} if n in leaves else set().union(*[L(c) for c in ch[n]]) if ch[n] else set()
        memo[n] = r
        return r
    for n in list(F.parent):
        L(n)
    return memo, ch


def run_lem31(seed):
    rng = random.Random(seed)
    tot = ok = 0
    for (s, r) in [(4, 2), (6, 3), (8, 4), (10, 5), (12, 6), (14, 7), (16, 8)]:
        for t in range(5):
            while True:   # every data column non-zero, so that each data pair straddles (see the memo)
                H = [rng.randrange(1, 2 ** s) for _ in range(r)]
                if all(any(row >> j & 1 for row in H) for j in range(s)):
                    break
            rk, _ = rank_f2(H)
            T, Tp, leaves, checks, nvar = build_tanglegram(H, s)
            grp, verts = nauty_group(T, Tp, leaves)
            order = round(grp[1] * 10 ** grp[2])
            pats = []
            good = True
            for p in grp[0]:
                pat = 0
                for j in range(s):
                    a = verts[('P', ('q', j, 0))]; b_ = verts[('P', ('q', j, 1))]
                    if p[a] == b_:
                        pat |= 1 << j
                    elif p[a] != a:
                        good = False
                pats.append(pat)
            in_code = all(bin(pat & row).count('1') % 2 == 0 for pat in pats for row in H)
            rk2, _ = rank_f2(pats)
            deg = max(out_degrees(T), out_degrees(Tp))
            # frontier from the definition
            L2 = {l for l in leaves if l[0] == 'L2'}
            L1 = set(leaves) - L2
            ls, ch = leaf_sets(Tp, leaves)
            S = {n for n in Tp.parent if n not in leaves and ls[n] & L1 and ls[n] & L2}
            bottom = {n for n in S if not any(c in S for c in ch[n])}
            frontier_ok = bottom == {('q', j, i) for j in range(s) for i in (0, 1)}
            # u2 alone: full F_2^s; u1 alone: the code
            T2, Tp2, l2, _, _ = build_tanglegram(H, s, with_u1=False)
            g2, _ = nauty_group(T2, Tp2, l2)
            T1, Tp1, l1, _, _ = build_tanglegram(H, s, with_u2=False)
            g1, v1 = nauty_group(T1, Tp1, l1)
            pats1 = []
            for p in g1[0]:
                pat = 0
                for j in range(s):
                    if ('P', ('q', j, 0)) in v1 and p[v1[('P', ('q', j, 0))]] == v1[('P', ('q', j, 1))]:
                        pat |= 1 << j
                pats1.append(pat)
            rho1_ok = (rank_f2(pats1)[0] == s - rk) and all(bin(pat & row).count('1') % 2 == 0 for pat in pats1 for row in H)
            rho2_ok = round(g2[1] * 10 ** g2[2]) == 2 ** s
            this = (good and in_code and rk2 == s - rk and order == 2 ** (s - rk) and deg <= 2 and frontier_ok and rho1_ok and rho2_ok)
            why = [] if this else [k for k, v in [('good', good), ('in_code', in_code), ('rk2', rk2 == s - rk), ('order', order == 2 ** (s - rk)), ('deg', deg <= 2), ('frontier', frontier_ok), ('rho1', rho1_ok), ('rho2', rho2_ok)] if not v]
            tot += 1; ok += int(this)
            n1 = sum(1 for l in leaves if l[0] == 'L')
            print(f"s={s} r={r} rk={rk} nvar={nvar} |L1|={n1} |L2|={len(L2)} |S(u)|={len(S)} bottom={len(bottom)} maxoutdeg={deg} |Aut|={order} {'OK' if this else 'BAD ' + ','.join(why)}", flush=True)
    print(f"{ok}/{tot}")


# ---------------------------------------------------------------- P3 existence of R
def run_p3(m, seed):
    import pynauty
    rng = random.Random(seed)
    kappa = 5
    def apply_perm_lin(sig, v):
        out = 0
        for c in range(kappa):
            if v >> c & 1:
                out |= 1 << sig[c]
        return out | (v & ~((1 << kappa) - 1))
    T = [1 << c for c in range(kappa)]
    A = [s for s in itertools.permutations(range(kappa)) if sum(1 for i in range(kappa) for j in range(i) if s[i] < s[j]) % 2 == 0]
    span = lambda B: {x for r in range(len(B) + 1) for sub in itertools.combinations(B, r) for x in [__import__('functools').reduce(lambda a, b_: a ^ b_, sub, 0)]}
    pts = list(range(1, 2 ** m))
    # T': generic independent 5-set, disjoint span from <T> as far as possible
    Tprime = []
    while len(Tprime) < kappa:
        v = rng.randrange(1, 2 ** m)
        if v in span(Tprime) or (v & ((1 << kappa) - 1)) == v:
            continue
        Tprime.append(v)
    ST, STp = span(T), span(Tprime)
    allowed = lambda l: not (set(l) & ST) and not (set(l) & STp)
    lineset = {}
    def lines_all():
        return [(a, b_, a ^ b_) for a in pts for b_ in pts if a < b_ and (a ^ b_) > b_]
    all_lines = lines_all()
    print(f"m={m}, |lines|={len(all_lines)}, kappa=5, T=basis, T'={Tprime}")
    for L in (1, 2, 3):
        R = set()
        tries = 0
        while len({tuple(sorted(apply_perm_lin(s, x) for x in l)) for s in A for l in R}) < 0 or tries < L:
            pass
            tries += 1
            for attempt in range(100000):
                l = rng.choice(all_lines)
                orbit = {tuple(sorted(apply_perm_lin(s, x) for x in l)) for s in A}
                if all(allowed(o) for o in orbit):
                    R |= orbit
                    break
        Rset = {tuple(sorted(l)) for l in R}
        kept = [l for l in all_lines if tuple(sorted(l)) not in Rset]
        idx = {p: i for i, p in enumerate(pts)}
        n = len(pts) + len(kept)
        adj = {i: [] for i in range(n)}
        for j, l in enumerate(kept):
            for p in l:
                adj[idx[p]].append(len(pts) + j)
        g = pynauty.Graph(n, adjacency_dict=adj, vertex_coloring=[set(range(len(pts))), set(range(len(pts), n))])
        gens, m1, e1, orbs, norb = pynauty.autgrp(g)
        order = round(m1 * 10 ** e1)
        # does Aut stabilise T' setwise with Alt(T') induced? enumerate the group if small
        induced = None
        if order <= 10 ** 6:
            idn = list(range(n))
            elems = {tuple(idn)}
            frontier = [tuple(idn)]
            while frontier:
                nx = []
                for e in frontier:
                    for gg in gens:
                        ne = tuple(gg[e[i]] for i in range(n))
                        if ne not in elems:
                            elems.add(ne); nx.append(ne)
                frontier = nx
            Tpix = [idx[v] for v in Tprime]
            seen = set()
            for e in elems:
                im = tuple(e[i] for i in Tpix)
                if set(im) == set(Tpix):
                    seen.add(im)
            induced = len(seen)
        print(f"  {L} A-orbits, |R|={len(Rset)}: |Aut|={order} (>= |A|={len(A)}), images of Stab(T') on T': {induced} (Alt(T') would be 60), kept {len(kept)} lines", flush=True)


def asym_graph(n, forbidden):
    """an asymmetric graph on [n] with min degree >= 2, avoiding the forbidden pairs (first one found)."""
    import pynauty
    pairs = [e for e in itertools.combinations(range(n), 2) if e not in forbidden and (e[1], e[0]) not in forbidden]
    rng = random.Random(0)
    for _ in range(200000):
        E = [e for e in pairs if rng.random() < 0.5]
        deg = collections.Counter(x for e in E for x in e)
        if any(deg[i] < 2 for i in range(n)):
            continue
        adj = {i: [] for i in range(n)}
        for a, b_ in E:
            adj[a].append(b_)
        g = pynauty.Graph(n, directed=False, adjacency_dict=adj)
        _, m1, e1, _, _ = pynauty.autgrp(g)
        if round(m1 * 10 ** e1) == 1:
            return E
    raise RuntimeError


def run_p3x(m, kappa):
    """Explicit R for Prop P3: lines inside a complement C of <T>, on an asymmetric graph.
    T = e_0..e_{k-1}, C = <f_0..f_{2k-1}>, T' = {f_i + f_{i+k}}; R = {f_i, f_j, f_i+f_j} for ij in an asymmetric graph
    avoiding the pairs {i, i+k}. Then every element of Stab_GL(R) fixes each f_i, hence T' pointwise, and any permutation of
    T extends to a linear map fixing C pointwise, which preserves R."""
    import pynauty
    assert m >= 3 * kappa
    f = [1 << (kappa + i) for i in range(2 * kappa)]
    Tset = [1 << c for c in range(kappa)]
    Tprime = [f[i] ^ f[i + kappa] for i in range(kappa)]
    forb = {(i, i + kappa) for i in range(kappa)}
    E = asym_graph(2 * kappa, forb)
    R = {tuple(sorted((f[a], f[b_], f[a] ^ f[b_]))) for a, b_ in E}
    def span(B):
        out = {0}
        for v in B:
            out |= {x ^ v for x in out}
        return out
    ST, STp = span(Tset), span(Tprime)
    off = all(not (set(l) & ST) and not (set(l) & STp) for l in R)
    pts = list(range(1, 2 ** m))
    idx = {p: i for i, p in enumerate(pts)}
    kept = [(a, b_, a ^ b_) for a in pts for b_ in pts if a < b_ and (a ^ b_) > b_ and tuple(sorted((a, b_, a ^ b_))) not in R]
    n = len(pts) + len(kept)
    adj = {i: [] for i in range(n)}
    for j, l in enumerate(kept):
        for p in l:
            adj[idx[p]].append(len(pts) + j)
    g = pynauty.Graph(n, adjacency_dict=adj, vertex_coloring=[set(range(len(pts))), set(range(len(pts), n))])
    gens, m1, e1, orbs, norb = pynauty.autgrp(g)
    print(f"m={m} kappa={kappa}: |R|={len(R)} lines off <T>,<T'>: {off}; |Aut|={m1}e{e1}; orbits on points of T: {[orbs[idx[t]] for t in Tset]}; T' orbits: {[orbs[idx[t]] for t in Tprime]} (fixed iff own index)")
    print(f"  T' points fixed by Aut: {all(orbs[idx[t]] == idx[t] for t in Tprime)}; f_i fixed: {all(orbs[idx[x]] == idx[x] for x in f)}; T in one orbit: {len({orbs[idx[t]] for t in Tset}) == 1}")


if __name__ == '__main__':
    mode = sys.argv[1]
    seed = int(sys.argv[-1]) if len(sys.argv) > 2 and sys.argv[-1].isdigit() and mode != 'p3' else 1
    if mode == 'pin':
        run_pin(seed)
    elif mode == 'pinplus':
        run_pinplus(seed)
    elif mode == 'lem31':
        run_lem31(seed)
    elif mode == 'p3':
        run_p3(int(sys.argv[2]), int(sys.argv[3]) if len(sys.argv) > 3 else 1)
    elif mode == 'p3x':
        run_p3x(int(sys.argv[2]), int(sys.argv[3]))
