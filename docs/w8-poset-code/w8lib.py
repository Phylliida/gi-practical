"""w8: string isomorphism under generalized wreath products S_b^{(P)} over a poset P.

Points of Omega = [b]^h are coordinate tuples z (z[i] for poset element i).
G = S_b^{(P)}: g(z)_i = pi_i(z|pred(i))(z_i).

The DP (Theorem 1 of docs/w8-poset.md) fixes a linear extension lam of P.
Level t: J_t = lam[:t] (a down-set), Q_t = lam[t:].  Points are indexed in lam-order
mixed radix (lam[0] most significant), so the fibre over u in [b]^{J_t} is the
contiguous block u*N_t .. (u+1)*N_t - 1, N_t = b^(h-t).

F_t(u,u') = {phi in S_b^{(Q_t)} : y_{u'}(phi(v)) = x_u(v)}, a right coset Aut(x_u) * rep
(gi convention: right action, mul(p,q) = first p then q; g maps x to y iff y[g[i]] = x[i]).

Recurrence at i = lam[t]: R = {k in Q_{t+1} : not i < k} (a down-set of Q_{t+1});
phi <-> (pi, (phi_a)_a) with all rho_R(phi_a) equal; combine = coset intersection in
S_b^{(R)} acting on [b]^R.
"""
import itertools, math, sys
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
from gi.perm import identity, mul, inv
from gi.group import PermGroup, ActionHom


# ----------------------------------------------------------------------------- posets
def closure(h, rel):
    """rel: iterable of (j, i) meaning j < i. Returns pred[i] = set of strict predecessors."""
    pred = [set() for _ in range(h)]
    for j, i in rel:
        pred[i].add(j)
    changed = True
    while changed:
        changed = False
        for i in range(h):
            new = set(pred[i])
            for j in pred[i]:
                new |= pred[j]
            if new != pred[i]:
                pred[i] = new
                changed = True
    for i in range(h):
        assert i not in pred[i], "cycle"
    return pred


def poset_2dim(sigma, rho):
    """P_{sigma,rho}: j < i iff j precedes i in both orders (lists of elements)."""
    h = len(sigma)
    ps = {c: k for k, c in enumerate(sigma)}
    pr = {c: k for k, c in enumerate(rho)}
    return [set(j for j in range(h) if ps[j] < ps[i] and pr[j] < pr[i]) for i in range(h)]


def poset_chains(lengths):
    """Disjoint union of chains; elements numbered chain by chain."""
    rel, h = [], 0
    for L in lengths:
        rel += [(h + k, h + k + 1) for k in range(L - 1)]
        h += L
    return closure(h, rel)


def succ_of(pred):
    h = len(pred)
    return [set(k for k in range(h) if i in pred[k]) for i in range(h)]


def step_cost(pred, Qmask, i):
    """mu-cost of branching on minimal i of Q: max over k in Q, k || i, of |pred(k) & Q|."""
    h = len(pred)
    best = 0
    for k in range(h):
        if k != i and (Qmask >> k) & 1 and i not in pred[k]:
            c = sum(1 for j in pred[k] if (Qmask >> j) & 1)
            best = max(best, c)
    return best


def mu_of_order(pred, lam):
    h = len(pred)
    Q = (1 << h) - 1
    m = 0
    for i in lam:
        m = max(m, step_cost(pred, Q, i))
        Q &= ~(1 << i)
    return m


def best_order(pred):
    """(mu(P), an optimal linear extension), by DP over down-sets (bitmask of processed)."""
    h = len(pred)
    full = (1 << h) - 1
    predmask = [sum(1 << j for j in pred[i]) for i in range(h)]
    memo = {full: (0, None)}

    def rec(J):
        if J in memo:
            return memo[J][0]
        Q = full & ~J
        best, arg = None, None
        for i in range(h):
            if (Q >> i) & 1 and (predmask[i] & Q) == 0:
                c = step_cost(pred, Q, i)
                if best is not None and c >= best:
                    continue
                c = max(c, rec(J | (1 << i)))
                if best is None or c < best:
                    best, arg = c, i
        memo[J] = (best, arg)
        return best

    sys.setrecursionlimit(10000)
    mu = rec(0)
    lam, J = [], 0
    while J != full:
        i = memo[J][1]
        lam.append(i)
        J |= 1 << i
    return mu, lam


def nu_of(pred):
    return max((len(p) for p in pred), default=0)


# ----------------------------------------------------------------------------- coset intersection
def _with_base(H, base):
    """H rebuilt with `base` as base prefix."""
    if list(H.base[:len(base)]) == list(base):
        return H
    return PermGroup(H.n, H.gens, base=list(base), order=H.order())


def find_rep(G, H, f):
    """Some g in G with g * f^-1 in H (i.e. g in G cap H f), or None. Backtrack over G's chain,
    pruned by H-compatibility of the partial base images."""
    n = G.n
    finv = inv(f)
    B = list(G.base)
    k = len(B)
    Hb = _with_base(H, B)
    idn = identity(n)
    HT, HTi = Hb.T, Hb.Ti
    stats = [0]

    def dfs(l, v, w, winv):
        stats[0] += 1
        if l == k:
            g = v
            return g if Hb.contains(mul(g, finv)) else None
        beta = B[l]
        for u in G.T[l].values():
            vv = mul(u, v)
            gam = finv[vv[beta]]
            p = winv[gam]
            if p == beta:
                r = dfs(l + 1, vv, w, winv)
            else:
                if l >= len(HT):
                    continue
                t = HT[l].get(p)
                if t is None:
                    continue
                r = dfs(l + 1, vv, mul(t, w), mul(winv, HTi[l][p]))
            if r is not None:
                return r
        return None

    return dfs(0, idn, idn, idn)


def group_intersection(G, H):
    """G cap H as a PermGroup (Butler-style: build the chain of G cap H bottom-up along G's base)."""
    n = G.n
    B = list(G.base)
    k = len(B)
    if k == 0:
        return PermGroup(n)
    Hb = _with_base(H, B)
    idn = identity(n)
    HT, HTi = Hb.T, Hb.Ti

    def search(j, gamma):
        """an element of G^(j) cap H^(j) mapping B[j] -> gamma, or None"""
        def dfs(l, v, w, winv):
            if l == k:
                return v if Hb.contains(v) else None
            beta = B[l]
            us = [G.T[l][gamma]] if l == j else G.T[l].values()
            for u in us:
                vv = mul(u, v)
                gam = vv[beta]
                p = winv[gam]
                if p == beta:
                    r = dfs(l + 1, vv, w, winv)
                else:
                    if l >= len(HT):
                        continue
                    t = HT[l].get(p)
                    if t is None:
                        continue
                    r = dfs(l + 1, vv, mul(t, w), mul(winv, HTi[l][p]))
                if r is not None:
                    return r
            return None
        return dfs(j, idn, idn, idn)

    gens = []
    for j in range(k - 1, -1, -1):
        beta = B[j]
        orb = {beta}
        queue = [beta]
        for q in queue:
            for s in gens:
                if s[q] not in orb:
                    orb.add(s[q]); queue.append(s[q])
        for gamma in list(G.T[j].keys()):
            if gamma in orb:
                continue
            g = search(j, gamma)
            if g is not None:
                gens.append(g)
                orb = {beta}
                queue = [beta]
                for q in queue:
                    for s in gens:
                        if s[q] not in orb:
                            orb.add(s[q]); queue.append(s[q])
    return PermGroup(n, gens)


# ----------------------------------------------------------------------------- the DP
class PosetSI:
    def __init__(self, b, pred, lam=None):
        self.b = b
        self.pred = pred
        self.h = h = len(pred)
        if lam is None:
            self.mu, lam = best_order(pred)
        else:
            self.mu = mu_of_order(pred, lam)
        self.lam = list(lam)
        pos = {e: s for s, e in enumerate(self.lam)}
        for i in range(h):
            for j in pred[i]:
                assert pos[j] < pos[i], "lam is not a linear extension"
        self.N = b ** h
        self.weights = [b ** (h - 1 - s) for s in range(h)]   # weight of lam[s]
        self.perms_b = list(itertools.permutations(range(b)))
        self.idb = tuple(range(b))
        # per level t: projection data for R_t inside Q_{t+1}
        self.lev = []
        for t in range(h):
            i = self.lam[t]
            Qn = self.lam[t + 1:]
            R = [k for k in Qn if i not in pred[k]]
            Rpos = [s for s, k in enumerate(Qn) if i not in pred[k]]
            N1 = b ** len(Qn)
            m = b ** len(R)
            L = len(Qn)
            wmap = []
            for z in range(N1):
                digs = [(z // b ** (L - 1 - s)) % b for s in range(L)]
                w = 0
                for s in Rpos:
                    w = w * b + digs[s]
                wmap.append(w)
            sect = [None] * m
            for z in range(N1 - 1, -1, -1):
                sect[wmap[z]] = z
            # V_R size (faithful domain used in the theory)
            VR = sum(b ** (1 + len(pred[k] & set(R))) for k in R)
            self.lev.append(dict(i=i, R=R, N1=N1, m=m, wmap=wmap, sect=sect, VR=VR))
        self.stats = dict(aut_states=0, rep_states=0, branches=0, ci_calls=0,
                          max_m=max([l['m'] for l in self.lev] + [1]),
                          max_VR=max([l['VR'] for l in self.lev] + [0]))

    def index(self, z):
        return sum(z[self.lam[s]] * self.weights[s] for s in range(self.h))

    def to_lam_string(self, f):
        """f: dict or callable on coordinate tuples -> tuple indexed by lam-order index"""
        out = [None] * self.N
        for z in itertools.product(range(self.b), repeat=self.h):
            out[self.index(z)] = f[z] if isinstance(f, dict) else f(z)
        return tuple(out)

    def perm_to_coords(self, g):
        """g: perm of lam-indices -> dict on coordinate tuples"""
        zs = {}
        for z in itertools.product(range(self.b), repeat=self.h):
            zs[self.index(z)] = z
        return {zs[p]: zs[g[p]] for p in range(self.N)}

    # projection rho_R at level t (perm of range(N1) -> perm of range(m))
    def proj(self, t, phi):
        L = self.lev[t]
        wm, se = L['wmap'], L['sect']
        return tuple(wm[phi[se[w]]] for w in range(L['m']))

    def assemble(self, t, pi, phis):
        N1 = self.lev[t]['N1']
        out = []
        for a in range(self.b):
            off = pi[a] * N1
            out.extend(off + q for q in phis[a])
        return tuple(out)

    def solve(self, x, y=None):
        """x, y: tuples indexed by lam-order index. Returns (AutGroup, rep or None)."""
        if y is None:
            y = x
        self.x, self.y = x, y
        self._aut, self._rep, self._hom, self._C, self._hist = {}, {}, {}, {}, {}
        A = self.aut(0, 0)
        r = self.rep(0, 0, 0, 1)
        return A, r

    def hist(self, which, t, u):
        key = (which, t, u)
        hs = self._hist.get(key)
        if hs is None:
            s = self.x if which == 0 else self.y
            Nt = self.b ** (self.h - t)
            hs = self._hist[key] = tuple(sorted(s[u * Nt:(u + 1) * Nt]))
        return hs

    def hom(self, t1, v):
        """ActionHom rho_R (level t1-1's R) on Aut(x_v) at level t1."""
        key = (t1, v)
        H = self._hom.get(key)
        if H is None:
            A = self.aut(t1, v)
            t = t1 - 1
            H = self._hom[key] = ActionHom(A, self.lev[t]['m'], lambda g, t=t: self.proj(t, g))
        return H

    def Cchain(self, t, u):
        """[C_0, ..., C_{b-1}], C_a = cap_{a'<=a} rho_R(Aut(x_{u b + a'}))"""
        key = (t, u)
        C = self._C.get(key)
        if C is None:
            C = []
            for a in range(self.b):
                Pa = self.hom(t + 1, u * self.b + a).image_group()
                if a == 0:
                    C.append(Pa)
                else:
                    self.stats['ci_calls'] += 1
                    C.append(group_intersection(C[-1], Pa))
            self._C[key] = C
        return C

    def branch(self, t, u, up, pi, w):
        """rep of the branch pi of F_t(u, up): x-fibre u to (x if w == 0 else y)-fibre up; or None"""
        b = self.b
        self.stats['branches'] += 1
        fs = []
        for a in range(b):
            f = self.rep(t + 1, u * b + a, up * b + pi[a], w)
            if f is None:
                return None
            fs.append(f)
        C = self.Cchain(t, u)
        homs = [self.hom(t + 1, u * b + a) for a in range(b)]
        pf = [self.proj(t, f) for f in fs]
        yy = pf[0]
        for a in range(1, b):
            self.stats['ci_calls'] += 1
            g = find_rep(C[a - 1], homs[a].image_group(), mul(pf[a], inv(yy)))
            if g is None:
                return None
            yy = mul(g, yy)
        phis = [mul(homs[a].lift(mul(yy, inv(pf[a]))), fs[a]) for a in range(b)]
        return self.assemble(t, pi, phis)

    def aut(self, t, u):
        key = (t, u)
        G = self._aut.get(key)
        if G is not None:
            return G
        self.stats['aut_states'] += 1
        b, h = self.b, self.h
        Nt = b ** (h - t)
        if t == h:
            G = self._aut[key] = PermGroup(1)
            return G
        reps = []
        for pi in self.perms_b:
            r = self.branch(t, u, u, pi, 0)
            if r is not None:
                reps.append(r)
        r0 = reps[0]                       # the identity branch is nonempty
        C = self.Cchain(t, u)
        homs = [self.hom(t + 1, u * b + a) for a in range(b)]
        idN1 = identity(self.lev[t]['N1'])
        gens = []
        for c in C[-1].gens:
            gens.append(self.assemble(t, self.idb, [homs[a].lift(c) for a in range(b)]))
        for a in range(b):
            for kap in homs[a].kernel().gens:
                gens.append(self.assemble(t, self.idb, [kap if a2 == a else idN1 for a2 in range(b)]))
        r0i = inv(r0)
        gens += [mul(r, r0i) for r in reps[1:]]
        idN = identity(Nt)
        G = self._aut[key] = PermGroup(Nt, [g for g in gens if g != idN])
        return G

    def rep(self, t, u, up, w):
        memo = self._rep
        key = (w, t, u, up)
        if key in memo:
            return memo[key]
        self.stats['rep_states'] += 1
        h, b = self.h, self.b
        ys = self.y if w else self.x
        if t == h:
            r = (0,) if self.x[u] == ys[up] else None
            memo[key] = r
            return r
        if w == 0 and u == up:
            r = memo[key] = identity(b ** (h - t))
            return r
        if self.hist(0, t, u) != self.hist(w, t, up):
            memo[key] = None
            return None
        r = None
        for pi in self.perms_b:
            r = self.branch(t, u, up, pi, w)
            if r is not None:
                break
        memo[key] = r
        return r


# ----------------------------------------------------------------------------- group membership helpers
def in_gwp(b, h, pred, g_coords):
    """Is the map z -> g_coords[z] (dict on tuples) in S_b^{(P)}?"""
    for i in range(h):
        P = sorted(pred[i])
        table = {}
        for z, w in g_coords.items():
            key = tuple(z[j] for j in P)
            table.setdefault(key, {})
            d = table[key]
            if z[i] in d and d[z[i]] != w[i]:
                return False
            d[z[i]] = w[i]
        for d in table.values():
            if sorted(d.values()) != list(range(b)):
                return False
    return True


def gwp_order(b, pred):
    return math.prod(math.factorial(b) ** (b ** len(p)) for p in pred)


def random_gwp_element(b, h, pred, rng):
    """random element of S_b^{(P)} as dict on coordinate tuples"""
    tabs = []
    for i in range(h):
        P = sorted(pred[i])
        tab = {}
        for key in itertools.product(range(b), repeat=len(P)):
            p = list(range(b)); rng.shuffle(p); tab[key] = p
        tabs.append((P, tab))
    g = {}
    for z in itertools.product(range(b), repeat=h):
        g[z] = tuple(tabs[i][1][tuple(z[j] for j in tabs[i][0])][z[i]] for i in range(h))
    return g


def all_gwp_elements(b, h, pred):
    """all elements (tiny cases only), as dicts"""
    slots = []
    for i in range(h):
        P = sorted(pred[i])
        for key in itertools.product(range(b), repeat=len(P)):
            slots.append((i, P, key))
    for choice in itertools.product(list(itertools.permutations(range(b))), repeat=len(slots)):
        tab = {(s[0], s[2]): c for s, c in zip(slots, choice)}
        g = {}
        for z in itertools.product(range(b), repeat=h):
            g[z] = tuple(tab[(i, tuple(z[j] for j in sorted(pred[i])))][z[i]] for i in range(h))
        yield g
