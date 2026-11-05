"""Permutation groups by generators: Schreier-Sims, orbits, blocks, action
homomorphisms, and recognition of the Johnson action on 2-sets.

Everything here is deterministic. These are the "basic operations" the paper
treats as polynomial-time (Section 3: orbits, fixing points, images, lifting).
"""
import math
from bisect import bisect_left, insort
from collections import OrderedDict
from itertools import compress
from operator import itemgetter, ne

from .perm import identity, mul, inv, maps

_IDENTITY = {}


def _identity(n):
    t = _IDENTITY.get(n)
    if t is None:
        t = _IDENTITY[n] = identity(n)
    return t


# Finished chains, keyed by (n, gens, prescribed base). The construction is
# deterministic, so a hit gives exactly the chain a new construction would
# build. The recursion builds the same groups over and over (e.g. the same
# preimage in many branches), so this saves most of the Schreier-Sims work.
# Transversal dicts and tuples are never mutated after creation, so they are
# shared; the lists are copied. Bounded by the number of stored transversal
# entries times the degree (LRU eviction).
CHAIN_CACHE_LIMIT = 1 << 24
_CHAINS = OrderedDict()
_chains_size = 0


class _Chain:
    __slots__ = ("key", "gens", "base", "S", "T", "Ti", "par", "order", "size", "elements", "nt",
                 "isodata", "orbs", "blocks")


def clear_chain_cache():
    global _chains_size
    _CHAINS.clear()
    _chains_size = 0


class PermGroup:
    """A permutation group on range(n) with a base and strong generating set,
    built by the deterministic incremental Schreier-Sims algorithm.

    base[l] is the l-th base point, S[l] the strong generators fixing
    base[:l], and T[l] maps each point p of the orbit base[l]^<S[l]> to a
    u with base[l]^u = p (Ti[l][p] is u^-1). `gens` lists the generators that
    were accepted (each enlarged the group), so it is irredundant.

    `ambient_base`, if given, must be a base of a group containing <gens>
    (e.g. G.short_base() for a subgroup of G); it does not change the result.

    `order`, if given, must be the exact order of <gens>. Construction then
    stops as soon as the product of the orbit lengths reaches it: at that point
    the chain is complete, so the rest of the algorithm would not change it.
    The result is identical to the one built without `order`.

    Speedups that keep the result identical: Schreier generators already shown
    to lie in the next stabilizer (same transversal elements) are not sifted
    again, BFS tree edges (trivial Schreier generators) are skipped, and
    unchanged transversal elements are reused when an orbit is recomputed.
    """

    def __init__(self, n, gens=(), base=(), order=None, ambient_base=None):
        self.n = n
        self.idn = _identity(n)
        self._target = order
        # A base of some group containing <gens>: only the identity of that
        # group fixes it, which makes identity tests cheap (see _sifts_to_id).
        self._amb = list(ambient_base) if ambient_base and n > 1 else None
        self._snap = None
        self._elems = None              # all elements, once listed (small groups)
        self._isodata = None
        self._orbs = None               # all orbits, once computed
        self._cow = False
        self._plans = None              # sift plans by start level
        self._nt = self._nt_T = None    # nontrivial levels, valid while T is self._nt_T
        if not isinstance(gens, (list, tuple)):
            gens = list(gens)
        key = None
        if gens:
            key = (n, tuple(gens), tuple(base))
            snap = _CHAINS.get(key)
            if snap is not None:
                _CHAINS.move_to_end(key)
                self._load(snap)
                if order is not None and self._order != order:
                    raise ValueError("PermGroup: the given order is wrong")
                self._done = order is not None
                return
        self.gens = []
        self.base, self.S, self.T, self.Ti = [], [], [], []
        self._par, self._ok = [], []    # BFS tree edges; verified Schreier pairs
        self._ginv = {}                 # id(s) -> (s, s^-1) for strong generators
        self._order = 1                 # product of the orbit lengths
        self._ord_T = self.T            # (_order is valid while T is this list)
        self._nt, self._nt_T = [], self.T
        self._done = order == 1
        if base:
            idn = self.idn
            self.base = list(base)
            self.S = [[] for _ in self.base]
            self.T = [{b: idn} for b in self.base]
            self.Ti = [{b: idn} for b in self.base]
            self._par = [{} for _ in self.base]
            self._ok = [{} for _ in self.base]
            self._ord_T = self.T
            self._nt, self._nt_T = [], self.T
        for g in gens:
            if self._done:              # complete: every further generator is redundant
                break
            self.add(g)
        if key is not None:
            self._store(key)

    def _load(self, c):
        self.gens = list(c.gens)
        self.base = list(c.base)
        self.S = list(c.S)              # tuples, copied to lists before any change
        self._cow = True
        self.T, self.Ti, self._par = list(c.T), list(c.Ti), list(c.par)
        self._ok = [{} for _ in c.base]
        self._ginv = {}
        self._order = c.order
        self._ord_T = self.T
        self._nt, self._nt_T = list(c.nt), self.T
        self._snap = c

    def _store(self, key):
        global _chains_size
        size = self.n * (2 * sum(len(t) for t in self.T) + len(self.gens) + 1)
        if size > CHAIN_CACHE_LIMIT // 8:
            return
        c = _Chain()
        c.key = key
        c.gens, c.base = tuple(self.gens), tuple(self.base)
        c.S = tuple(tuple(s) for s in self.S)
        c.T, c.Ti, c.par = tuple(self.T), tuple(self.Ti), tuple(self._par)
        c.order, c.size, c.elements = self._order, size, None
        c.nt, c.isodata = tuple(self._nontrivial()), None
        c.orbs, c.blocks = None, False
        _CHAINS[key] = c
        _chains_size += size
        while _chains_size > CHAIN_CACHE_LIMIT:
            _, old = _CHAINS.popitem(last=False)
            _chains_size -= old.size
        self._snap = c

    # -- Schreier-Sims -----------------------------------------------------
    def _push_base(self, b):
        self._plans = None
        self.base.append(b)
        self.S.append([])
        self.T.append({b: self.idn})
        self.Ti.append({b: self.idn})
        self._par.append({})
        self._ok.append({})

    def _orbit(self, l):
        """Recompute the BFS orbit and transversal of level l, reusing the old
        transversal elements whose tree path is unchanged. The tree edge of q
        is stored as si * n + p (q = S[l][si][p])."""
        b, S, idn, n = self.base[l], self.S[l], self.idn, self.n
        oT, oTi, opar = self.T[l], self.Ti[l], self._par[l]
        T, Ti, par, queue = {b: idn}, {b: idn}, {}, [b]
        ginv = self._ginv
        for p in queue:
            u = T[p]
            same = oT.get(p) is u
            e = p
            for s in S:
                q = s[p]
                if q not in T:
                    if same and opar.get(q) == e:
                        T[q] = oT[q]
                        Ti[q] = oTi[q]
                    else:
                        T[q] = mul(u, s)
                        si = ginv.get(id(s))
                        if si is None or si[0] is not s:
                            si = ginv[id(s)] = (s, inv(s))
                        Ti[q] = mul(si[1], Ti[p])      # (u s)^-1 = s^-1 u^-1
                    par[q] = e
                    queue.append(q)
                e += n
        if len(oT) == 1 and len(T) > 1:
            self._plans = None
            insort(self._nontrivial(), l)
        self._order = self._order // len(oT) * len(T)
        self.T[l], self.Ti[l], self._par[l] = T, Ti, par

    def _extend(self, g, lo, hi):
        """Append g to S[lo..hi]; g fixes base[lo..hi-1] and moves base[hi].
        A trivial orbit stays trivial under a generator fixing its point."""
        S, T = self.S, self.T
        for l in range(lo, hi + 1):
            S[l].append(g)
            if l == hi or len(T[l]) > 1:
                self._orbit(l)

    def _check_done(self):
        t = self._target
        if t is not None:
            if self._order == t:
                self._done = True
            elif self._order > t:
                raise ValueError("PermGroup: the given order is too small")
        return self._done

    def sift(self, g, start=0):
        """Sift g through the levels from `start`: (residue, level where it
        stopped, or len(base))."""
        plans = self._plans
        if plans is None or plans[0] is not self.T or plans[1] != len(self.base):
            plans = self._plans = (self.T, len(self.base), {})
        plan = plans[2].get(start)
        if plan is None:
            plan = plans[2][start] = self._make_plan(start)
        Tis = self.Ti
        for l, b, get, fix in plan:
            if get is None:
                p = g[b]
                if p != b:              # (Ti[l][b] is the identity)
                    t = Tis[l].get(p)
                    if t is None:
                        return g, l
                    g = itemgetter(*g)(t)   # mul(g, t)
            elif get(g) != fix:         # a run of trivial levels: g must fix their points
                base = self.base
                while g[base[l]] == base[l]:
                    l += 1
                return g, l
        return g, len(self.base)

    def _make_plan(self, start):
        """The levels from `start` as steps (l, base point, None, None) for
        nontrivial levels and (l, None, getter, points) for runs of at least
        two trivial levels, which are checked at once."""
        plan, base = [], self.base
        nt = self._nontrivial()
        l = start
        for L in nt[bisect_left(nt, start):] + [len(base)]:
            if L - l >= 2:
                fix = tuple(base[l:L])
                plan.append((l, None, itemgetter(*fix), fix))
            elif L - l == 1:
                plan.append((l, base[l], None, None))
            if L < len(base):
                plan.append((L, base[L], None, None))
            l = L + 1
        return plan

    def _sifts_to_id(self, factors, start):
        """Whether the product of `factors` sifts to the identity from level
        `start` (as sift would find), computing only the images of a few points:
        the base points of the nontrivial levels and the ambient base. Trivial
        levels are not checked: if the product moved such a level's point, the
        later factors (which fix it) cannot make the final residue fix it, and
        a residue fixing the ambient base is the identity."""
        plans = self._plans
        if plans is None or plans[0] is not self.T or plans[1] != len(self.base):
            plans = self._plans = (self.T, len(self.base), {})
        key = -1 - start
        fp = plans[2].get(key)
        if fp is None:
            fp = plans[2][key] = self._make_fast_plan(start)
        P, steps = fp
        g = P
        for f in factors:
            g = itemgetter(*g)(f)
        Tis = self.Ti
        for l, k in steps:
            p = g[k]
            if p != P[k]:
                t = Tis[l].get(p)
                if t is None:
                    return False
                g = itemgetter(*g)(t)
        return g == P

    def _make_fast_plan(self, start):
        base = self.base
        nt = self._nontrivial()
        pts, steps, where = [], [], {}
        for l in nt[bisect_left(nt, start):]:
            where[base[l]] = len(pts)
            steps.append((l, len(pts)))
            pts.append(base[l])
        for b in self._amb:
            if b not in where:
                where[b] = len(pts)
                pts.append(b)
        if len(pts) < 2:                # (itemgetter needs two points)
            pts.append(0 if pts[0] != 0 else 1)
        return tuple(pts), steps

    def short_base(self):
        """The base points of the nontrivial levels (still a base)."""
        base = self.base
        return [base[l] for l in self._nontrivial()]

    def _moved_point(self, g):
        return next(i for i in range(self.n) if g[i] != i)

    def add(self, g):
        """Add a generator. Returns True if the group grew."""
        if self._amb is not None and self._sifts_to_id((g,), 0):
            return False
        r, j = self.sift(g)
        if j == len(self.base) and r == self.idn:
            return False
        self.gens.append(g)
        self._snap = self._elems = self._isodata = self._orbs = None
        if self._cow:
            self.S = [list(x) for x in self.S]
            self._cow = False
        base = self.base
        k = 0
        while k < len(base) and g[base[k]] == base[k]:
            k += 1
        if k == len(base):
            self._push_base(self._moved_point(g))
        self._extend(g, 0, k)
        if not self._check_done():
            self._schreier(k)
        return True

    def _schreier(self, i):
        """Make levels i, i-1, ..., 0 complete (levels > i are complete).
        Every s in S[i] that fixes base[i] is also in S[i+1] (generators are
        appended to a range of levels ending at a level whose point they move),
        so its Schreier generator at the base point lies in <S[i+1]>."""
        idn, base, n = self.idn, self.base, self.n
        amb = self._amb is not None
        while i >= 0:
            T = self.T[i]
            if len(T) == 1:             # all Schreier generators are in S[i+1]
                i -= 1
                continue
            restart = False
            Ti, par, ok, S, b = self.Ti[i], self._par[i], self._ok[i], self.S[i], base[i]
            for p, u in list(T.items()):
                e = p - n
                for s in S:
                    e += n                      # e = si * n + p
                    q = s[p]
                    if par.get(q) == e:         # tree edge: trivial Schreier generator
                        continue
                    if q == b and p == b:       # s fixes b, so s is in S[i+1]
                        continue
                    v = Ti[q]
                    m = ok.get(e)
                    if m is not None and m[0] is u and m[1] is v:
                        continue                # already known to lie in <S[i+1]>
                    ok[e] = (u, v)
                    if amb and self._sifts_to_id((u, s, v), i + 1):
                        continue
                    h = mul(mul(u, s), v)
                    if h == idn:
                        continue
                    r, j = self.sift(h, i + 1)
                    if j < len(base) or r != idn:
                        if j == len(base):
                            self._push_base(self._moved_point(r))
                        self._extend(r, i + 1, j)
                        if self._check_done():
                            return
                        i = j
                        restart = True
                        break
                if restart:
                    break
            if not restart:
                i -= 1

    # -- queries -------------------------------------------------------------
    def order(self):
        if self._ord_T is self.T:
            return self._order
        return math.prod(len(t) for t in self.T)

    def _nontrivial(self):
        """The indices of the levels with a nontrivial orbit (increasing)."""
        if self._nt_T is not self.T:
            self._nt = [l for l, t in enumerate(self.T) if len(t) > 1]
            self._nt_T = self.T
        return self._nt

    def contains(self, g):
        r, j = self.sift(g)
        return j == len(self.base) and r == self.idn

    def strong_gens(self):
        seen, out = set(), []
        for S in self.S:
            for s in S:
                if s not in seen:
                    seen.add(s)
                    out.append(s)
        return out

    def orbits(self, points=None):
        """Orbits of the group, as sorted lists, containing the given points
        (all points by default), ordered by their least element."""
        gens = self.gens
        c = self._orbs
        if c is not None and c[0] is gens and c[1] == len(gens):
            allo = c[2]
        elif self._snap is not None and self._snap.orbs is not None:
            allo = self._snap.orbs
            self._orbs = (gens, len(gens), allo)
        else:
            n = self.n
            seen = [False] * n
            allo = []
            for p in range(n):
                if seen[p]:
                    continue
                seen[p] = True
                orb = [p]
                for a in orb:
                    for g in gens:
                        b = g[a]
                        if not seen[b]:
                            seen[b] = True
                            orb.append(b)
                orb.sort()
                allo.append(orb)
            self._orbs = (gens, len(gens), allo)
            if self._snap is not None:
                self._snap.orbs = allo
        if points is None:
            return [list(o) for o in allo]
        pts = set(points)
        return [list(o) for o in allo if not pts.isdisjoint(o)]

    def elements(self):
        """All elements (only for small groups), in the order of
        product(T[0], ..., T[k-1]); the element is u_{k-1} ... u_0."""
        global _chains_size
        if self._elems is not None:
            return iter(self._elems)
        order = self.order()
        if order * self.n > CHAIN_CACHE_LIMIT // 64:
            return self._elements()
        c = self._snap
        if c is not None:
            if c.elements is None:
                c.elements = tuple(self._elements())
                if _CHAINS.get(c.key) is c:     # (still cached)
                    c.size += order * self.n
                    _chains_size += order * self.n
            self._elems = c.elements
        else:
            self._elems = tuple(self._elements())
        return iter(self._elems)

    def _elements(self):
        levels = [list(t.values()) for t in self.T if len(t) > 1]
        k = len(levels)
        acc = [self.idn] * (k + 1)      # acc[l+1] = u_l ... u_0
        idx = [0] * k
        l = 0
        while True:
            while l < k:
                acc[l + 1] = mul(levels[l][idx[l]], acc[l])
                l += 1
            yield acc[k]
            l = k - 1
            while l >= 0:
                idx[l] += 1
                if idx[l] < len(levels[l]):
                    break
                idx[l] = 0
                l -= 1
            if l < 0:
                return

    def isomorphisms(self, x, y):
        """[g for g in self.elements() if maps(g, x, y)], by a depth-first search
        over the same product with pruning: after the factors of the first j
        nontrivial levels are chosen (prefix v), the rest of the product fixes
        every point p fixed by that level's group, so x[p] == y[v[p]] is needed."""
        lv = self._isodata
        if lv is None:
            c = self._snap
            if c is not None and c.isodata is not None:
                lv = c.isodata
            else:
                lv = self._iso_levels()
                if c is not None:
                    c.isodata = lv
            self._isodata = lv
        levels, newfix = lv
        k = len(levels)
        out = []
        if k == 0:
            return [self.idn] if maps(self.idn, x, y) else []
        last, lastfix = levels[-1], newfix[k]

        def rec(j, v):                  # v passed the checks of newfix[j]
            if j < k - 1:
                nf = newfix[j + 1]
                for u in levels[j]:
                    for p in nf:        # (u v)[p] = v[u[p]], checked before multiplying
                        if x[p] != y[v[u[p]]]:
                            break
                    else:
                        rec(j + 1, mul(u, v))
                return
            for u in last:              # the last level, inline
                for p in lastfix:
                    if x[p] != y[v[u[p]]]:
                        break
                else:
                    w = mul(u, v)
                    if maps(w, x, y):
                        out.append(w)

        for p in newfix[0]:
            if x[p] != y[p]:
                return out
        rec(0, self.idn)
        return out

    def _iso_levels(self):
        """The nontrivial levels' transversals, and for each the points fixed
        by its group but not by the previous one (then up to 8 other points)."""
        n, idn = self.n, self.idn
        moved_of = {}

        def moved(s):
            m = moved_of.get(id(s))
            if m is None:
                m = moved_of[id(s)] = set(compress(range(n), map(ne, s, idn)))
            return m

        levels, newfix = [], []
        prev = set(range(n))            # the points moved by the previous level's group
        for l in self._nontrivial():
            cur = set().union(*[moved(s) for s in self.S[l]])
            newfix.append(sorted(prev - cur))
            levels.append(list(self.T[l].values()))
            prev = cur
        newfix.append(sorted(prev)[:8])  # (then a full check)
        return levels, newfix

    def _tail(self, m):
        """The stabilizer of base[:m], reusing this chain."""
        H = PermGroup(self.n)
        if m < len(self.base):
            H.base = self.base[m:]
            H.S = [list(S) for S in self.S[m:]]
            H.T = self.T[m:]
            H.Ti = self.Ti[m:]
            H._par = self._par[m:]
            H._ok = [{} for _ in H.base]
            H.gens = list(H.S[0])
            H._order = H.order()
            H._ord_T = H.T
        return H

    def pointwise_stabilizer(self, points):
        points = list(points)
        if self.base[:len(points)] == points:
            return self._tail(len(points))
        H = PermGroup(self.n, self.strong_gens(), base=points, order=self.order(),
                      ambient_base=self.short_base())
        return H._tail(len(points))

    def stabilizer(self, p):
        return self.pointwise_stabilizer([p])


def reduce_gens(n, gens, ambient_base=None):
    """An irredundant generating list for <gens>. `ambient_base`: optional base
    of a group containing the gens (only for speed)."""
    idn = _identity(n)
    gens = [g for g in dict.fromkeys(gens) if g != idn]
    if len(gens) <= 4:
        return gens
    return PermGroup(n, gens, ambient_base=ambient_base).gens


def _ident(g):
    return g


class ActionHom:
    """The homomorphism phi: G -> Sym(m) given by `image(g)` for every g in G.

    Lifting and the kernel come from the group generated by g + phi(g) on
    range(n + m), with the m image points first in the base. That group is
    isomorphic to G, so its order is known and Schreier-Sims stops early.
    `image=None` means the identity map (m = n): no combined group is needed.
    """

    def __init__(self, G, m, image):
        if image is None:
            image = _ident
        self.G, self.m, self.image_of = G, m, image
        self._image = None
        self._kernel = None
        self._levels = None             # the nontrivial image levels of C
        self.C = None
        if image is not _ident:
            n = G.n
            comb = [g + tuple(n + v for v in image(g)) for g in G.gens]
            self.C = PermGroup(n + m, comb, base=range(n, n + m), order=G.order(),
                               ambient_base=G.short_base())

    def image_order(self):
        if self.C is None:
            return self.G.order()
        return math.prod(len(self.C.T[l]) for l in range(self.m))

    def image_group(self):
        if self._image is None:
            if self.C is None:
                amb = self.G.short_base()
            else:                       # the nontrivial image levels form a base of the image
                amb = [l for l in range(self.m) if len(self.C.T[l]) > 1]
            self._image = PermGroup(self.m, [self.image_of(g) for g in self.G.gens],
                                    order=self.image_order(), ambient_base=amb)
        return self._image

    def lift(self, p):
        """Some g in G with phi(g) = p. Raises ValueError if p is not in phi(G)."""
        if self.C is None:
            if not self.G.contains(p):
                raise ValueError("not in the image")
            return p
        n, m, C = self.G.n, self.m, self.C
        T, Ti = C.T, C.Ti
        if self._levels is None:
            self._levels = [l for l in range(m) if len(T[l]) > 1]
        g = tuple(n + v for v in p)     # the image coordinates of the combined element
        acc = None
        # Trivial levels contribute nothing; p is in the image iff the residue
        # is trivial after the nontrivial ones.
        for l in self._levels:
            pt = g[l]
            if pt == n + l:             # T[l][base point] is the identity
                continue
            u = T[l].get(pt)
            if u is None:
                raise ValueError("not in the image")
            acc = u[:n] if acc is None else mul(u[:n], acc)
            g = mul(g, Ti[l][pt])
        if g != tuple(range(n, n + m)):
            raise ValueError("not in the image")
        return identity(n) if acc is None else acc

    def kernel(self):
        if self._kernel is None:
            if self.C is None:
                self._kernel = PermGroup(self.G.n)
                return self._kernel
            n, m, C = self.G.n, self.m, self.C
            K = PermGroup(n)
            if m < len(C.base):
                K.base = C.base[m:]
                K.S = [[s[:n] for s in S] for S in C.S[m:]]
                K.T = [{p: u[:n] for p, u in T.items()} for T in C.T[m:]]
                K.Ti = [{p: u[:n] for p, u in T.items()} for T in C.Ti[m:]]
                K._par = [{} for _ in K.base]
                K._ok = [{} for _ in K.base]
                K.gens = list(K.S[0])
                K._order = K.order()
                K._ord_T = K.T
            self._kernel = K
        return self._kernel

    def preimage(self, hs, order=None):
        """phi^-1(<hs>) for hs in phi(G), built as <lifts of hs, ker phi>.
        `order` is |<hs>| if known (else it is computed in degree m)."""
        if order is None:
            order = PermGroup(self.m, hs).order()
        K = self.kernel()
        return PermGroup(self.G.n, [self.lift(h) for h in hs] + K.gens,
                         order=order * K.order(), ambient_base=self.G.short_base())


class RestrictionHom(ActionHom):
    """The restriction G -> Sym(D) to a G-invariant set D of points, with the
    image on range(len(D)) (point D[i] becomes i).

    Same results as ActionHom(G, len(D), restriction), but the chain is built
    on range(n) with D as a prescribed base prefix instead of on range(n + |D|):
    fixing image point i is the same as fixing D[i], so the incremental
    Schreier-Sims runs step for step like the combined one."""

    def __init__(self, G, D):
        D = list(D)
        n, m = G.n, len(D)
        self.G, self.m, self.D = G, m, D
        pos = [None] * n
        for i, d in enumerate(D):
            pos[d] = i
        if m > 1:
            getD = itemgetter(*D)
            self.image_of = lambda g: itemgetter(*getD(g))(pos)
        else:
            self.image_of = lambda g: tuple(pos[g[d]] for d in D)
        self._image = None
        self._kernel = None
        self._levels = None
        self.C = PermGroup(n, G.gens, base=D, order=G.order(), ambient_base=G.short_base())

    def image_order(self):
        return math.prod(len(self.C.T[l]) for l in range(self.m))

    def lift(self, p):
        n, m, C, D = self.G.n, self.m, self.C, self.D
        T, Ti = C.T, C.Ti
        if self._levels is None:
            self._levels = [l for l in range(m) if len(T[l]) > 1]
            self._Dt = tuple(D)
        g = tuple(D[v] for v in p)      # g[i]: current image of D[i]
        acc = None
        for l in self._levels:          # (as in ActionHom.lift)
            pt = g[l]
            if pt == D[l]:
                continue
            u = T[l].get(pt)
            if u is None:
                raise ValueError("not in the image")
            acc = u if acc is None else mul(u, acc)
            g = mul(g, Ti[l][pt])
        if g != self._Dt:
            raise ValueError("not in the image")
        return identity(n) if acc is None else acc

    def kernel(self):
        if self._kernel is None:
            self._kernel = self.C._tail(self.m)
        return self._kernel


# -- blocks ------------------------------------------------------------------
def minimal_block(n, gens, a, b, limit=None):
    """Atkinson's algorithm: labels of the finest invariant partition joining
    a, b (each point is labeled by the least point of its class). With
    `limit`, returns None as soon as the class of a has at least `limit` points."""
    if a > b:
        a, b = b, a
    parent = list(range(n))
    size = [1] * n
    parent[b] = a
    size[a] = 2
    if limit is not None and 2 >= limit:
        return None
    queue = [(a, b)]
    for u, v in queue:                  # the list grows while it is scanned
        for g in gens:
            x, y = g[u], g[v]
            while parent[x] != x:       # parent[x] <= x: roots are class minima
                parent[x] = x = parent[parent[x]]
            while parent[y] != y:
                parent[y] = y = parent[parent[y]]
            if x != y:
                if x > y:
                    x, y = y, x
                parent[y] = x
                size[x] += size[y]
                if limit is not None and x == a and size[a] >= limit:
                    return None
                queue.append((x, y))
    lab = parent
    for v in range(n):                  # parent[v] < v is already final
        lab[v] = lab[lab[v]]
    return lab


def minimal_block_labels(n, gens, reps=None):
    """For a transitive group: labels of a minimal nontrivial block system,
    or None if the group is primitive. It is the system of the first b
    (in increasing order) whose block B(0, b) is smallest.

    `reps`, if given, lists the least point of every orbit of the stabilizer of
    0 except {0}, increasing: B(0, b) is the same for all b in such an orbit,
    so it suffices to try these points. Blocks that cannot beat the best one
    found so far are abandoned early. The result is the same."""
    best, best_size = None, n
    cand = range(1, n) if reps is None else reps
    for b in cand:
        # a nontrivial block has at most n/2 points
        lab = minimal_block(n, gens, 0, b, limit=min(best_size, n // 2 + 1))
        if lab is None:
            continue
        size = lab.count(lab[0])
        if size < best_size:
            best, best_size = lab, size
            if size == 2:
                break
    return best if best_size < n else None


def stabilizer_orbit_reps(G, p=0):
    """For transitive G: the least point of each orbit of the stabilizer G_p
    other than {p}, in increasing order. G_p is conjugate to the stabilizer
    G_b of the first base point b, which the chain already provides."""
    n = G.n
    if not G.base or p not in G.T[0]:
        return None
    u = G.T[0][p]                       # base[0]^u = p, so G_p = u^-1 G_b u
    S1 = G.S[1] if len(G.base) > 1 else []
    seen = [False] * n
    reps = []
    for x in range(n):
        if seen[x]:
            continue
        seen[x] = True
        orb = [x]
        for y in orb:
            for s in S1:
                z = s[y]
                if not seen[z]:
                    seen[z] = True
                    orb.append(z)
        m = min(u[y] for y in orb)
        if m != p:
            reps.append(m)
    reps.sort()
    return reps


def top_block_system(G):
    """For transitive G: a block system on which G acts primitively, reached by
    stacking minimal block systems (the paper's partition hierarchy, read
    bottom-up). Returns the blocks, or None if G is primitive.
    (Remembered with a cached chain: it depends only on the group.)"""
    c = G._snap
    if c is not None and c.blocks is not False:
        return None if c.blocks is None else [list(B) for B in c.blocks]
    blocks = _top_block_system(G)
    if c is not None:
        c.blocks = None if blocks is None else tuple(tuple(B) for B in blocks)
    return blocks


def _top_block_system(G):
    n = G.n
    blocks = [[p] for p in range(n)]
    changed = False
    first = True
    while len(blocks) > 2:
        d = len(blocks)
        if first:                       # the point action itself
            lab = minimal_block_labels(d, G.gens, stabilizer_orbit_reps(G))
            first = False
        else:
            where = [0] * n
            for i, B in enumerate(blocks):
                for p in B:
                    where[p] = i
            bg = [tuple(where[g[B[0]]] for B in blocks) for g in G.gens]
            lab = minimal_block_labels(d, bg)
        if lab is None:
            break
        merged = {}
        for i in range(d):
            merged.setdefault(lab[i], []).extend(blocks[i])
        blocks = sorted((sorted(B) for B in merged.values()), key=lambda B: B[0])
        changed = True
    return blocks if changed else None


def label_support(G, phi, p=0):
    """For transitive G and phi: G -> Sym(m): the labels F fixed by phi(G_p),
    in increasing order, and supp[w] = tuple(phi(u)[a] for a in F) for any u in G
    with p^u = w (it does not depend on u).

    a is in F exactly when the G-orbit of (p, a) on (point, label) pairs has
    one label per point; that orbit is then {(w, supp_a[w])}. So no
    stabilizer chain is needed."""
    n, q = G.n, phi.m
    pairs = [(g, phi.image_of(g)) for g in G.gens]
    F, cols = [], []
    for a in range(q):
        lab = [None] * n
        lab[p] = a
        queue = [p]
        ok = True
        for w in queue:
            c = lab[w]
            for g, im in pairs:
                w2, c2 = g[w], im[c]
                l2 = lab[w2]
                if l2 is None:
                    lab[w2] = c2
                    queue.append(w2)
                elif l2 != c2:
                    ok = False
                    break
            if not ok:
                break
        if ok:
            F.append(a)
            cols.append(lab)
    if not cols:
        return F, [()] * n
    supp = [None if c[0] is None else c for c in zip(*cols)]
    return F, supp


# -- the Johnson action on 2-sets ---------------------------------------------
def johnson_labels(P):
    """If the primitive group P on d points is Sym(m) or Alt(m) acting on the
    2-subsets of an m-set (m >= 5), return (m, f): f maps each element of P to
    the permutation it induces on the m labels. Otherwise None.

    The labels are recovered from the triangular graph T(m) (one suborbit) as
    its m maximal cliques of size m - 1."""
    d = P.n
    m = (1 + math.isqrt(1 + 8 * d)) // 2
    if m * (m - 1) // 2 != d or m < 5:
        return None
    if P.order() not in (math.factorial(m), math.factorial(m) // 2):
        return None
    P0 = PermGroup(d, P.gens, base=[0], order=P.order(), ambient_base=P.short_base())
    for orb in P0._tail(1).orbits():
        if len(orb) != 2 * (m - 2):
            continue
        N0 = set(orb)
        nbr = [None] * d
        for p, u in P0.T[0].items():
            nbr[p] = {u[v] for v in N0}
        if any(s is None for s in nbr):
            return None
        stars = set()
        for b in range(d):
            nb = nbr[b]
            for c in nb:
                if c < b and b in nbr[c]:   # (done as the edge (c, b): symmetric in b, c)
                    continue
                common = nb & nbr[c]
                stars.add(frozenset([b, c] + [v for v in common if not nbr[v].isdisjoint(common)]))
        stars = sorted((s for s in stars if len(s) == m - 1), key=sorted)
        if len(stars) != m:
            continue
        count = [0] * d
        for s in stars:
            for p in s:
                count[p] += 1
        if any(c != 2 for c in count):
            continue
        return m, _star_action(d, stars)
    return None


def _star_action(d, stars):
    """g -> the permutation of the stars induced by g (g maps stars to stars).
    Every point lies in exactly two stars, so the image of a star is usually
    the common star of the images of two of its points; otherwise (or if that
    is ambiguous) the image set is looked up."""
    star_id = {s: i for i, s in enumerate(stars)}
    of = [[] for _ in range(d)]
    for i, s in enumerate(stars):
        for p in s:
            of[p].append(i)
    of = [tuple(x) for x in of]
    reps = [tuple(sorted(s)[:2]) for s in stars]

    def f(g):
        out = []
        for i, (p1, p2) in enumerate(reps):
            a0, a1 = of[g[p1]]
            b = of[g[p2]]
            if (a0 in b) != (a1 in b):
                out.append(a0 if a0 in b else a1)
            else:
                out.append(star_id[frozenset(g[p] for p in stars[i])])
        return tuple(out)

    return f
