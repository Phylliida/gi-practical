"""Permutation groups by generators: Schreier-Sims, orbits, blocks, action
homomorphisms, and verified recognition of Johnson and product actions.

Everything here is deterministic. These are the "basic operations" the paper
treats as polynomial-time (Section 3: orbits, fixing points, images, lifting).
"""
import math
import random
from bisect import bisect_left, insort
from collections import OrderedDict, namedtuple
from itertools import compress
from operator import itemgetter, ne

from .kernel import ck as _ck
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

# Front of the chain cache: (n, the ids of the generator objects, base) -> the
# chain. Hashing a generator costs its degree, and most repeated groups arrive
# as the very same tuple objects. An id may only be compared while its object
# is alive, so every id-key is paired in chain.idkeys with a tuple holding its
# generators (for an alias of the same value, its own objects: these are not
# the ones in chain.key), and the id-keys leave this table when the chain is
# evicted. So a hit means the same generators, and hence the chain that the
# lookup by value would give. The aliases are charged to the cache size.
_CHAIN_IDS = {}


# Levels of a chain with a prescribed base start trivial, and most of them stay
# so. Their containers are shared: the transversal level {b: idn} (one dict per
# (degree, point)), which also serves as Ti, the empty _par dict, and no _ok
# dict. These are safe to share because level dicts are only ever replaced
# (_orbit builds new ones), never written to; only _ok[l] is written to, and
# it is created when a level needs it (_schreier).
_NO_PAR = {}
_TRIVIAL_LEVELS = OrderedDict()         # degree -> list of {b: identity} per point b


def _trivial_levels(n):
    t = _TRIVIAL_LEVELS.get(n)
    if t is None:
        idn = _identity(n)
        t = _TRIVIAL_LEVELS[n] = [{b: idn} for b in range(n)]
        if len(_TRIVIAL_LEVELS) > 64:
            _TRIVIAL_LEVELS.popitem(last=False)
    return t


def _add_alias(c, idk, gens):
    """Let the generator objects `gens` (equal to those of c) find the chain c."""
    global _chains_size
    extra = c.key.k[0] * (len(gens) + 1)
    c.idkeys.append((idk, gens))
    _CHAIN_IDS[idk] = c
    c.size += extra
    _chains_size += extra
    _trim_chains()


def _trim_chains():
    global _chains_size
    while _chains_size > CHAIN_CACHE_LIMIT:
        _, old = _CHAINS.popitem(last=False)
        _chains_size -= old.size
        for k, _ in old.idkeys:
            del _CHAIN_IDS[k]


class _ChainKey:
    """A key of _CHAINS, its hash computed once (dict lookups, move_to_end)."""
    __slots__ = ("k", "h")

    def __init__(self, k):
        self.k, self.h = k, hash(k)

    def __hash__(self):
        return self.h

    def __eq__(self, other):
        return self.k == other.k


class _Chain:
    __slots__ = ("key", "gens", "base", "S", "T", "Ti", "par", "order", "size", "elements", "nt",
                 "isodata", "orbs", "blocks", "idkeys")


def clear_chain_cache():
    global _chains_size
    _CHAINS.clear()
    _CHAIN_IDS.clear()
    _chains_size = 0


class LazyTransversal:
    """A read-only transversal {orbit point: element} for an explicitly given
    chain (PermGroup.from_bsgs): the element of a point is made by make(p) on
    first use and then kept. pts lists the orbit, base point first (its
    element is the identity). Supports what the chain code uses of a dict:
    get, [], in, len, iteration, keys, values, items."""
    __slots__ = ("_pts", "_make", "_got")

    def __init__(self, pts, make, idn):
        self._pts = dict.fromkeys(pts)
        self._make = make
        self._got = {pts[0]: idn}

    def get(self, p, default=None):
        u = self._got.get(p)
        if u is None:
            if p not in self._pts:
                return default
            u = self._got[p] = self._make(p)
        return u

    def __getitem__(self, p):
        u = self.get(p)
        if u is None:
            raise KeyError(p)
        return u

    def __contains__(self, p):
        return p in self._pts

    def __len__(self):
        return len(self._pts)

    def __iter__(self):
        return iter(self._pts)

    def keys(self):
        return self._pts.keys()

    def values(self):
        return [self[p] for p in self._pts]

    def items(self):
        return [(p, self[p]) for p in self._pts]


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
            idk = (n, tuple(map(id, gens)), tuple(base))
            snap = _CHAIN_IDS.get(idk)
            if snap is not None:
                _CHAINS.move_to_end(snap.key)
            else:
                key = _ChainKey((n, tuple(gens), tuple(base)))
                snap = _CHAINS.get(key)
                if snap is not None:
                    _CHAINS.move_to_end(snap.key)   # (first: the alias may trigger a trim)
                    _add_alias(snap, idk, key.k[1])
            if snap is not None:
                self._load(snap)
                if order is not None and self._order != order:
                    raise ValueError("PermGroup: the given order is wrong")
                self._done = order is not None
                return
        self.gens = []
        self.base, self.S, self.T, self.Ti = [], [], [], []
        self._par, self._ok = [], []    # BFS tree edges; verified Schreier pairs
        self._ginv = {}                 # id(s) -> (s, s^-1) for strong generators
        self._scanned = {}              # level -> (T, generators covered by a complete scan)
        self._order = 1                 # product of the orbit lengths
        self._ord_T = self.T            # (_order is valid while T is this list)
        self._nt, self._nt_T = [], self.T
        self._done = order == 1
        if base:
            self.base = list(base)
            k = len(self.base)
            self.S = [()] * k           # (tuples until a level gets a generator)
            self.T = list(map(_trivial_levels(n).__getitem__, self.base))
            self.Ti = list(self.T)
            self._par = [_NO_PAR] * k
            self._ok = [None] * k
            self._ord_T = self.T
            self._nt, self._nt_T = [], self.T
        for g in gens:
            if self._done:              # complete: every further generator is redundant
                break
            self.add(g)
        if key is not None:
            self._store(key, idk)

    # Chains from from_bsgs are explicit; levels 0..k-1 of a chain with
    # _transp = k have transposition transversals (see from_bsgs).
    _explicit = False
    _transp = 0

    @classmethod
    def from_bsgs(cls, n, gens, base, S, T, Ti=None, ambient_base=None, transpositions=0):
        """A group given by an explicit base and strong generating set, built
        without Schreier-Sims. With G = <gens> and G^(l) the pointwise
        stabilizer of base[:l], the caller guarantees for every level l:

          * S[l] generates G^(l) (S[0] generates G), and every s in S[l] that
            fixes base[l] is also in S[l+1] (the convention of _schreier);
          * T[l] maps every point p of the orbit of base[l] under G^(l) to an
            element u of G^(l) with base[l]^u = p, the identity for p =
            base[l] (a dict or a LazyTransversal); Ti[l][p] = u^-1 (Ti=None:
            every u is an involution, and Ti = T).

        Then this is a complete chain: the order is the product of the orbit
        lengths, and sift/contains/lift work as for a built chain.
        transpositions=k declares that for l < k every u = T[l][p] permutes
        the base points as the transposition (base[l] p) does (young_preimage
        relies on it). The chain is not put into the chain cache, where a hit
        must equal the Schreier-Sims result. tests/test_group.py checks the
        explicit constructions against built chains."""
        G = cls.__new__(cls)
        G.n = n
        G.idn = _identity(n)
        G._amb = list(ambient_base) if ambient_base and n > 1 else None
        G._snap = G._elems = G._isodata = G._orbs = G._plans = None
        G._cow = False
        G.gens = list(gens)
        G.base = list(base)
        G.S = [list(s) for s in S]
        G.T = list(T)
        G.Ti = list(T) if Ti is None else list(Ti)
        G._par = [_NO_PAR] * len(G.base)
        G._ok = [None] * len(G.base)
        G._ginv = {}
        G._scanned = {}
        G._order = math.prod(len(t) for t in G.T)
        G._ord_T = G.T
        G._nt, G._nt_T = [l for l, t in enumerate(G.T) if len(t) > 1], G.T
        G._target = G._order            # complete: adding an element outside raises
        G._done = True
        G._explicit = True
        G._transp = transpositions
        return G

    def _load(self, c):
        self.gens = list(c.gens)
        self.base = list(c.base)
        self.S = list(c.S)              # tuples, copied to lists before any change
        self._cow = True
        self.T, self.Ti, self._par = list(c.T), list(c.Ti), list(c.par)
        self._ok = [None] * len(c.base)
        self._ginv = {}
        self._scanned = {}
        self._order = c.order
        self._ord_T = self.T
        self._nt, self._nt_T = list(c.nt), self.T
        self._snap = c

    def _store(self, key, idk):
        global _chains_size
        size = self.n * (2 * sum(map(len, self.T)) + len(self.gens) + 1)
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
        c.idkeys = [(idk, key.k[1])]
        _CHAINS[key] = c
        _CHAIN_IDS[idk] = c
        _chains_size += size
        _trim_chains()
        self._snap = c

    # -- Schreier-Sims -----------------------------------------------------
    def _push_base(self, b):
        self._plans = None
        self.base.append(b)
        self.S.append([])
        self.T.append({b: self.idn})
        self.Ti.append({b: self.idn})
        self._par.append(_NO_PAR)
        self._ok.append(None)

    def _orbit(self, l):
        """Recompute the BFS orbit and transversal of level l, reusing the old
        transversal elements whose tree path is unchanged. The tree edge of q
        is stored as si * n + p (q = S[l][si][p]). When nothing changed (the
        same points in the same order, all elements reused) the old dicts are
        kept: their contents are what would be built, and _schreier can see
        by identity that the level's transversal is unchanged."""
        b, S, idn, n = self.base[l], self.S[l], self.idn, self.n
        oT, oTi, opar = self.T[l], self.Ti[l], self._par[l]
        T, Ti, par, queue = {b: idn}, {b: idn}, {}, [b]
        ginv = self._ginv
        same_all = True
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
                        same_all = False
                        T[q] = mul(u, s)
                        si = ginv.get(id(s))
                        if si is None or si[0] is not s:
                            si = ginv[id(s)] = (s, inv(s))
                        Ti[q] = mul(si[1], Ti[p])      # (u s)^-1 = s^-1 u^-1
                    par[q] = e
                    queue.append(q)
                e += n
        if same_all and len(T) == len(oT) and queue == list(oT):
            return
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
            sl = S[l]
            if sl.__class__ is tuple:   # (a level that was empty so far)
                sl = S[l] = list(sl)
            sl.append(g)
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
        if _ck is not None:
            r = _ck.sift(g, plan, self.Ti, self.base)
            if r is not None:
                return r
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
        if _ck is not None:
            r = _ck.sifts_to_id(P, factors, steps, self.Ti)
            if r is not None:
                return r
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
        if _ck is not None:
            r = _ck.make_fast_plan(base, nt, start, self._amb, self.n)
            if r is not None:
                return r
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
        scanned = self._scanned
        while i >= 0:
            T = self.T[i]
            if len(T) == 1:             # all Schreier generators are in S[i+1]
                i -= 1
                continue
            S = self.S[i]
            d = scanned.get(i)
            start = d[1] if d is not None and d[0] is T else 0
            if start == len(S):
                i -= 1                  # nothing new since the last complete scan
                continue
            # A complete scan verified every (p, s) with s in S[:start] against
            # this T; those stay verified (<S[i+1]> only grows), so a rescan of
            # them does nothing. Only the generators appended since matter.
            restart = False
            Ti, par, b = self.Ti[i], self._par[i], base[i]
            ok = self._ok[i]
            if ok is None:
                ok = self._ok[i] = {}
            news = S[start:]
            for p, u in list(T.items()):
                e = p - n + start * n
                for s in news:
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
                scanned[i] = (T, len(S))
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
        allo = self.orbits_shared()
        if points is None:
            return [list(o) for o in allo]
        pts = set(points)
        return [list(o) for o in allo if not pts.isdisjoint(o)]

    def orbits_shared(self):
        """All orbits, the cached lists themselves: callers must not change them."""
        gens = self.gens
        c = self._orbs
        if c is not None and c[0] is gens and c[1] == len(gens):
            allo = c[2]
        elif self._snap is not None and self._snap.orbs is not None:
            allo = self._snap.orbs
            self._orbs = (gens, len(gens), allo)
        else:
            n = self.n
            allo = _ck.orbits(n, gens) if _ck is not None else None
            if allo is None:
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
        return allo

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
            H._ok = [None] * len(H.base)
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
        return math.prod(map(len, self.C.T[:self.m]))

    def _image_levels(self):
        """The nontrivial levels of C below m, increasing."""
        m, nt = self.m, self.C._nontrivial()
        return nt[:bisect_left(nt, m)]

    def image_group(self):
        if self._image is None:
            if self.C is None:
                amb = self.G.short_base()
            else:                       # the nontrivial image levels form a base of the image
                amb = self._image_levels()
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
            self._levels = self._image_levels()
        g = tuple(map(n.__add__, p))    # the image coordinates of the combined element
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
                K._par = [_NO_PAR] * len(K.base)
                K._ok = [None] * len(K.base)
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
        if G._explicit and G.base[:m] == D:
            # an explicit chain (from_bsgs) with D as its base prefix is reused
            # (a built chain is not: C must stay the one Schreier-Sims gives)
            self.C = G
        else:
            self.C = PermGroup(n, G.gens, base=D, order=G.order(), ambient_base=G.short_base())

    def image_order(self):
        return math.prod(map(len, self.C.T[:self.m]))

    def lift(self, p):
        n, m, C, D = self.G.n, self.m, self.C, self.D
        T, Ti = C.T, C.Ti
        if self._levels is None:
            self._levels = self._image_levels()
            self._Dt = tuple(D)
        g = tuple(map(D.__getitem__, p))    # g[i]: current image of D[i]
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


def young_preimage(psi, classes):
    """H = psi^-1(Young(classes)) with an explicit chain (no Schreier-Sims), or
    None when psi's chain does not allow it.

    psi: a RestrictionHom G -> Sym(m) onto labels D = psi.D whose chain C has
    transposition transversals on its first m levels (C._transp >= m, e.g. a
    chain from from_bsgs that psi reuses). classes: disjoint lists of labels
    (the classes with >= 2 labels of a partition). For labels a < b of one
    class Y, u(a, b) = C.T[a][D[b]] lies in G and acts as the transposition
    (a b) on the labels. It exists for all such a < b when D[Y[0]]'s orbit
    at level Y[0] holds all of D[Y] (checked, else None): then psi(G)
    contains the transpositions (Y[0] b), hence Sym(Y), and the stabilizer
    G^(a) of D[:a] maps onto the stabilizer of the labels < a in psi(G),
    which contains Sym(Y[i:]) for a = Y[i].

    Chain of H: base D[a] for a in each class but its last label, then the
    base of K = ker psi (the tail of C). The level of a = Y[i] (class Y) has
    the orbit {D[b] : b in Y[i:]} with the elements u(a, b) (a view of C.T[a],
    nothing is copied), and strong generators u(Y[i], Y[i+1]) and a lift of
    the cycle (Y[i] ... Y[-1]), then the same two for every later class, then
    K's generators. These elements lie in H (psi of each is in Young(classes)
    and K <= H), fix the earlier base points, and generate the stabilizers:
    the stabilizer of the first labels of H's base is psi^-1 of the Young
    group of the remaining labels, i.e. <lifts of its generators> K. The
    cycle lifts are built backwards with one product each:
    cycle(Y[i:]) = cycle(Y[i+1:]) then (Y[i] Y[i+1])."""
    C, D, m = psi.C, psi.D, psi.m
    if C._transp < m:
        return None
    K = psi.kernel()
    order = K.order()
    idn = C.idn
    levels = []                         # (label, orbit labels, [u, cycle]) per level
    per_class = []
    for Y in classes:
        Y = sorted(Y)
        k = len(Y)
        if k < 2:
            continue
        if any(D[b] not in C.T[Y[0]] for b in Y):
            return None
        u = [C.T[Y[i]][D[Y[i + 1]]] for i in range(k - 1)]
        lv = []
        cyc = u[k - 2]                  # cycle(Y[k-2:]) is the transposition
        for i in range(k - 2, -1, -1):
            if i < k - 2:
                cyc = mul(cyc, u[i])    # cycle(Y[i:]) = cycle(Y[i+1:]) then (Y[i] Y[i+1])
            lv.append((Y[i], Y[i:], [u[i]] if i == k - 2 else [u[i], cyc]))
        lv.reverse()
        levels.append(lv)
        per_class.append(lv[0][2])
        order *= math.factorial(k)
    base, S, T, Ti = [], [], [], []
    for c, lv in enumerate(levels):
        later = [g for gs in per_class[c + 1:] for g in gs] + list(K.gens)
        for a, orb, own in lv:
            pts = [D[b] for b in orb]
            base.append(D[a])
            S.append(own + later)
            T.append(LazyTransversal(pts, C.T[a].__getitem__, idn))
            Ti.append(LazyTransversal(pts, C.Ti[a].__getitem__, idn))
    base += K.base
    S += K.S
    T += K.T
    Ti += K.Ti
    gens = S[0] if S else []
    H = PermGroup.from_bsgs(C.n, gens, base, S, T, Ti, ambient_base=C.short_base())
    if H.order() != order:              # (cannot happen for a valid input)
        raise ValueError("young_preimage: wrong order")
    return H


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




# -- recognition of large primitive groups (Cameron, Maroti) ------------------
#
# By Maroti's form of Cameron's theorem, a primitive group of degree d is
# either small (order < d^(1 + log2 d)) or it lies in Sym(m) wr Sym(r), in the
# product action on r-tuples of k-subsets of an m-set, and contains Alt(m)^r.
# `johnson_structure` handles r = 1 with k >= 2 (k = 1 is the natural action,
# recognized by its order), and `product_action` finds the coordinates when
# r >= 2. Both guess the structure from one orbital graph and then VERIFY it
# against the generators, so a wrong guess can only make them return None:
#   * johnson_structure returns m subsets of the points ("stars") that every
#     generator permutes. Then g -> (induced permutation of the stars) is a
#     homomorphism of P, and its image is checked to be Sym(m) or Alt(m);
#   * product_action returns r classes of "lines" (each class a partition of
#     the points into lines of size D, d = D^r) such that every generator maps
#     lines to lines and classes to classes. Then g -> (induced permutation of
#     the classes) is a homomorphism of P, and its kernel preserves the lines
#     of class 0, a nontrivial block system.
# The results depend only on the group and are cached by its generators.

_RECOG = OrderedDict()
RECOG_CACHE_SIZE = 256


def _recog_cached(kind, P, compute):
    key = (kind, P.n, tuple(P.gens))
    out = _RECOG.get(key, _RECOG)
    if out is not _RECOG:
        _RECOG.move_to_end(key)
        return out
    out = _RECOG[key] = compute(P)
    if len(_RECOG) > RECOG_CACHE_SIZE:
        _RECOG.popitem(last=False)
    return out


def _factorial_degree(order):
    """m with order = m! or (m >= 3) order = m!/2, else None."""
    m, f = 1, 1
    while f < 2 * order:
        m += 1
        f *= m
        if f == order or (m >= 3 and f == 2 * order):
            return m
    return None


def _suborbits(P):
    """For transitive P: (b, T, orbits) with b = P.base[0], T[p] an element
    mapping b to p, and the orbits of the stabilizer of b other than {b}
    (smallest first, then by least point). The chain already provides the
    stabilizer of b: it is generated by S[1]."""
    n = P.n
    if not P.base or len(P.T[0]) != n:
        return None
    b, T = P.base[0], P.T[0]
    S1 = P.S[1] if len(P.base) > 1 else []
    seen = [False] * n
    seen[b] = True
    orbs = []
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
        orbs.append(orb)
    orbs.sort(key=len)
    return b, T, orbs


def _orbital_graph(n, T, b, orb):
    """The orbital graph of the suborbit orb of b, as neighbour sets, or None
    if the orbital is not self-paired (then the graph is directed)."""
    nbr = [None] * n
    for p, u in T.items():
        nbr[p] = {u[v] for v in orb}
    if any(b not in nbr[v] for v in orb):
        return None
    return nbr


# -- Johnson actions -----------------------------------------------------------
def johnson_labels(P):
    """If the primitive group P on d points is Sym(m) or Alt(m) acting on the
    k-subsets of an m-set (m >= 5, 2 <= k < m/2), return (m, f): f maps each
    element of P to the permutation it induces on the m labels, and is a
    homomorphism onto Sym(m) or Alt(m) (verified). Otherwise None."""
    J = johnson_structure(P)
    return None if J is None else (J[0], J[2])


def johnson_structure(P):
    """(m, k, f) as in johnson_labels, or None."""
    return _recog_cached("johnson", P, _johnson_structure)


def _johnson_structure(P):
    d = P.n
    m = _factorial_degree(P.order())
    if m is None or m < 5:
        return None
    ks = [k for k in range(2, (m - 1) // 2 + 1) if math.comb(m, k) == d]
    if not ks:
        return None
    k = ks[0]
    sub = _suborbits(P)
    if sub is None:
        return None
    b, T, orbs = sub
    for orb in orbs:
        if len(orb) != k * (m - k):     # the Johnson graph J(m, k): |A & B| = k - 1
            continue
        nbr = _orbital_graph(d, T, b, orb)
        if nbr is None:
            continue
        stars = _johnson_stars(m, k, nbr)
        if stars is None:
            continue
        f = _star_action(P, stars, k)
        if f is not None:
            return m, k, f
    return None


def _johnson_stars(m, k, nbr):
    """From a graph that should be J(m, k) (neighbour sets nbr), the m stars
    {k-sets containing i} as frozensets of vertices, or None.

    One level at a time: the vertices are the j-sets of J(m, j), and each
    (j-1)-set D is the maximal clique {j-sets containing D} of size m-j+1. The
    common neighbourhood of an edge {b, c} consists of two cliques with no
    edges between them: the other j-sets containing D = b & c (m-j-1 of them)
    and the other j-subsets of b | c (j-1 of them); m > 2j tells them apart.
    Two (j-1)-sets are adjacent in J(m, j-1) iff their cliques share a vertex
    (their union). Nothing here needs to be proved: the caller verifies the
    stars against the group."""
    members = [frozenset([p]) for p in range(len(nbr))]
    for j in range(k, 1, -1):
        N = len(nbr)
        want, size = math.comb(m, j - 1), m - j - 1
        cl_of = [[] for _ in range(N)]
        cliques = [] if m != 2 * j else _half_cliques(j, nbr)
        if cliques is None:
            return None
        for i, cl in enumerate(cliques):
            for p in cl:
                cl_of[p].append(i)
        for b in range(N if m != 2 * j else 0):
            nb = nbr[b]
            for c in nb:
                if any(c in cliques[i] for i in cl_of[b]):
                    continue                    # the edge is in a known clique
                common = nb & nbr[c]
                if len(common) != m - 2:
                    return None
                w = next(iter(common))
                grp = nbr[w] & common
                grp.add(w)
                if len(grp) != size:
                    grp = common - grp
                    if len(grp) != size:
                        return None
                grp.add(b)
                grp.add(c)
                for p in grp:
                    cl_of[p].append(len(cliques))
                cliques.append(frozenset(grp))
                if len(cliques) > want:
                    return None
        if len(cliques) != want or any(len(c) != j for c in cl_of):
            return None
        new = [set() for _ in cliques]
        for p in range(N):
            cs = cl_of[p]
            for a in cs:
                new[a].update(cs)
        for a, s in enumerate(new):
            s.discard(a)
        members = [frozenset().union(*[members[p] for p in cl]) for cl in cliques]
        nbr = new
    return members


def _half_cliques(j, nbr):
    """J(2j, j): both kinds of maximal cliques have j + 1 vertices (the j-sets
    containing a (j-1)-set, and the j-subsets of a (j+1)-set), and the two
    halves of the common neighbourhood of an edge have j - 1 vertices each.
    Two cliques of the same kind share at most one vertex, cliques of
    different kinds share 0 or 2. Returns the cliques of the kind of the first
    one found (complementation swaps the kinds, so either kind is a valid
    choice of "(j-1)-sets"), or None."""
    allc = {}
    for b in range(len(nbr)):
        nb = nbr[b]
        for c in nb:
            if c < b:
                continue
            common = nb & nbr[c]
            if len(common) != 2 * j - 2:
                return None
            w = next(iter(common))
            g1 = nbr[w] & common
            g1.add(w)
            g2 = common - g1
            if len(g1) != j - 1 or len(g2) != j - 1:
                return None
            for g in (g1, g2):
                cl = frozenset(g | {b, c})
                allc.setdefault(cl, len(allc))
    cl = list(allc)
    of = [[] for _ in nbr]
    for i, C in enumerate(cl):
        for p in C:
            of[p].append(i)
    kind = [None] * len(cl)
    kind[0] = 0
    queue = [0]
    for i in queue:
        for p in cl[i]:
            for i2 in of[p]:
                if i2 == i:
                    continue
                t = len(cl[i] & cl[i2])
                if t > 2:
                    return None
                want = kind[i] if t == 1 else 1 - kind[i]
                if kind[i2] is None:
                    kind[i2] = want
                    queue.append(i2)
                elif kind[i2] != want:
                    return None
    if None in kind:
        return None
    return [C for i, C in enumerate(cl) if kind[i] == 0]


def _star_action(P, stars, k):
    """f: g -> the permutation of the stars induced by g, if every generator
    of P permutes the stars and the image is Sym(m) or Alt(m); else None.
    The stars are numbered in a canonical order (by their sorted points).
    f(g)[i] is computed from two points of star i whose stars meet only in i,
    which is correct for every g that permutes the stars."""
    m, d = len(stars), P.n
    stars = sorted(stars, key=sorted)
    of = [[] for _ in range(d)]
    for i, s in enumerate(stars):
        for p in s:
            of[p].append(i)
    if any(len(o) != k for o in of):
        return None
    of = [frozenset(o) for o in of]
    reps = []
    for i, s in enumerate(stars):
        p1 = min(s)
        p2 = next((p for p in s if len(of[p] & of[p1]) == 1), None)
        if p2 is None:
            return None
        reps.append((p1, p2))

    def f(g):
        return tuple(min(of[g[p1]] & of[g[p2]]) for p1, p2 in reps)

    index = {s: i for i, s in enumerate(stars)}
    imgs = []
    for g in P.gens:
        im = tuple(index.get(frozenset(g[p] for p in s), -1) for s in stars)
        if -1 in im or f(g) != im:
            return None
        imgs.append(im)
    # f(P) is a homomorphic image of P, so |f(P)| <= |P|; with |P| as the
    # target order, Schreier-Sims stops early exactly when |f(P)| = |P| and
    # otherwise completes, so order() is the true |f(P)| either way.
    if PermGroup(m, imgs, order=P.order()).order() not in (math.factorial(m),
                                                         math.factorial(m) // 2):
        return None
    f.stars = stars                     # (for inspection and tests)
    return f


# -- product actions -----------------------------------------------------------
ProductAction = namedtuple("ProductAction", "r f lines0 fibers0")


def product_action(P):
    """If the primitive group P on d = D^r points (r >= 2) preserves a product
    structure, return ProductAction(r, f, lines0, fibers0): f maps each element
    of P to the permutation it induces on the r coordinates (a homomorphism,
    verified); lines0 lists the lines of coordinate 0 (the points that differ
    only in that coordinate) and fibers0 the D fibers of coordinate 0 (the
    points with equal coordinate 0). Both are block systems of ker f, which
    acts on fibers0 as the group of coordinate 0. Otherwise None.

    The structure is found from an orbital graph that is a Cartesian product
    of r graphs on D vertices (for Maroti's case Sym(m) wr Sym(r) on r-tuples
    of k-subsets: |A_i & B_i| = k - 1 in one coordinate, equal elsewhere)."""
    return _recog_cached("product", P, _product_action)


def _product_action(P):
    d = P.n
    order = P.order()
    cands = []
    r = 2
    while 3 ** r <= d:
        D = round(d ** (1.0 / r))
        for E in (D - 1, D, D + 1):
            if E >= 3 and E ** r == d and (math.factorial(E) ** r * math.factorial(r)) % order == 0:
                cands.append((r, E))
        r += 1
    if not cands:
        return None
    sub = _suborbits(P)
    if sub is None:
        return None
    b, T, orbs = sub
    for r, D in cands:
        tried = 0
        for orb in orbs:
            if len(orb) % r:
                continue
            tried += 1
            if tried > 6:
                break
            nbr = _orbital_graph(d, T, b, orb)
            if nbr is None:
                continue
            res = _product_lines(P, T, b, orb, nbr, r, D)
            if res is not None:
                return res
    return None


def _product_lines(P, T, b, orb, nbr, r, D):
    """The lines and coordinate classes of a graph that should be a Cartesian
    product of r connected graphs on D vertices, in each of which two vertices
    at distance 2 have at least 3 common neighbours (true for complete graphs
    and Johnson graphs), then verified against P.

    In such a product, two neighbours q, t of a vertex p differ from p in the
    same coordinate iff they are adjacent or have >= 3 common neighbours (in
    different coordinates they have exactly 2: p and the fourth corner of a
    square). This splits the neighbours of b into r local classes; they are
    moved to every point p by T[p]. Lines are the classes of (point, local
    class) pairs joined along edges. Coordinates are propagated from the lines
    through b along a spanning tree: if q is a neighbour of p in coordinate c
    and t one in coordinate c2 != c, the fourth corner s of the square p, q, t
    lies on the line through q in coordinate c2."""
    d = P.n
    O = list(orb)
    # local classes at b
    par = {v: v for v in O}

    def find(v):
        while par[v] != v:
            par[v] = par[par[v]]
            v = par[v]
        return v

    for i, q in enumerate(O):
        nq = nbr[q]
        for t in O[i + 1:]:
            if t in nq or len(nq & nbr[t]) >= 3:
                rq, rt = find(q), find(t)
                if rq != rt:
                    par[rt] = rq
    groups = {}
    for v in O:
        groups.setdefault(find(v), []).append(v)
    if len(groups) != r or any(len(C) * r != len(O) for C in groups.values()):
        return None
    classes = sorted(sorted(C) for C in groups.values())
    cls = [None] * d            # cls[p][q] = local class at p of the neighbour q
    rep = [None] * d            # rep[p][c] = one neighbour of p in local class c
    for p, u in T.items():
        cls[p] = {u[v]: c for c, C in enumerate(classes) for v in C}
        rep[p] = [u[C[0]] for C in classes]
    # lines: union-find on (point, local class) = p * r + c
    up = list(range(d * r))

    def root(v):
        while up[v] != v:
            up[v] = up[up[v]]
            v = up[v]
        return v

    for p in range(d):
        for q, c in cls[p].items():
            if q > p:
                cq = cls[q].get(p)
                if cq is None:
                    return None
                a, z = root(p * r + c), root(q * r + cq)
                if a != z:
                    up[z] = a
    line_at = [[root(p * r + c) for c in range(r)] for p in range(d)]
    pts = {}
    for p in range(d):
        if len(set(line_at[p])) != r:
            return None
        for L in line_at[p]:
            pts.setdefault(L, []).append(p)
    if len(pts) != r * D ** (r - 1) or any(len(v) != D for v in pts.values()):
        return None
    # coordinates of the lines
    coord = {L: c for c, L in enumerate(line_at[b])}
    seen = [False] * d
    seen[b] = True
    queue = [b]
    for p in queue:
        cp = [coord[L] for L in line_at[p]]
        for q, c in cls[p].items():
            if seen[q]:
                continue
            nq = nbr[q]
            for c2 in range(r):
                if c2 == c:
                    continue
                common = nq & nbr[rep[p][c2]]
                common.discard(p)
                if len(common) != 1:
                    return None
                s = common.pop()
                L = line_at[q][cls[q][s]]
                if coord.setdefault(L, cp[c2]) != cp[c2]:
                    return None
            seen[q] = True
            queue.append(q)
    if not all(seen) or len(coord) != len(pts):
        return None
    on = [[None] * d for _ in range(r)]     # on[c][p] = the line in coordinate c through p
    for L, P_L in pts.items():
        c = coord[L]
        for p in P_L:
            if on[c][p] is not None:
                return None
            on[c][p] = L
    # verify: every generator maps lines to lines and coordinates to coordinates
    index = {frozenset(v): L for L, v in pts.items()}
    for g in P.gens:
        img = [None] * r
        for L, v in pts.items():
            L2 = index.get(frozenset(g[p] for p in v))
            if L2 is None:
                return None
            c, c2 = coord[L], coord[L2]
            if img[c] is None:
                img[c] = c2
            elif img[c] != c2:
                return None
        if sorted(img) != list(range(r)):
            return None
    two = [(b, next(p for p in pts[line_at[b][c]] if p != b)) for c in range(r)]
    lines_c = [(c2, on[c2]) for c2 in range(r)]

    def f(g):
        out = []
        for p1, p2 in two:
            q1, q2 = g[p1], g[p2]
            out.append(next(c2 for c2, oc in lines_c if oc[q1] == oc[q2]))
        return tuple(out)

    # fibers of coordinate 0: the points joined by lines of the other coordinates
    up = list(range(d))
    for c in range(1, r):
        for L, v in pts.items():
            if coord[L] == c:
                a = root(v[0])
                for p in v[1:]:
                    z = root(p)
                    if z != a:
                        up[z] = a
    fib = {}
    for p in range(d):
        fib.setdefault(root(p), []).append(p)
    if len(fib) != D or any(len(v) * D != d for v in fib.values()):
        return None
    lines0 = sorted(sorted(v) for L, v in pts.items() if coord[L] == 0)
    return ProductAction(r, f, lines0, sorted(fib.values()))


# -- giants in other actions ---------------------------------------------------
def giant_labels(P):
    """If P (in any faithful action, e.g. Sym(2k) on the k|k bisections) is
    isomorphic to Sym(m) or Alt(m), m >= 5, return (m, f) with f: P -> Sym(m)
    a homomorphism onto Sym(m) or Alt(m) (verified). Otherwise None.

    A transposition t of Sym(m) (a 3-cycle for Alt(m)) is searched for among
    powers g^(o/2) (g^(o/3)) of pseudo-random elements g of order o (product
    replacement with a fixed seed, so the result is deterministic). Its class
    must have C(m, 2) elements (C(m, 3) subgroups <t>). P acts on that class
    by conjugation, a homomorphism; for transpositions (3-cycles) it is the
    Johnson action on 2-sets (3-sets), and johnson_structure recovers the m
    labels and verifies them. f is the composite of the two homomorphisms.
    (For m = 6 the class of t may be that of the triple transpositions; then
    f differs from the natural map by an outer automorphism, which is just
    as good.)"""
    return _recog_cached("giant", P, _giant_labels)


def _perm_order(g):
    seen = bytearray(len(g))
    o = 1
    for i in range(len(g)):
        if not seen[i]:
            L, j = 0, i
            while not seen[j]:
                seen[j] = 1
                j = g[j]
                L += 1
            o = o * L // math.gcd(o, L)
    return o


def _perm_power(g, e):
    out = None
    while e:
        if e & 1:
            out = g if out is None else mul(out, g)
        e >>= 1
        if e:
            g = mul(g, g)
    return out


def _giant_labels(P, tries=300):
    order = P.order()
    m = _factorial_degree(order)
    if m is None or m < 5:
        return None
    sym = order == math.factorial(m)
    if not sym and m < 7 and m != 5:        # Alt(6): 3-sets are not a Johnson action
        return None
    p, size = (2, math.comb(m, 2)) if sym else (3, math.comb(m, 3))
    gens = list(P.gens)
    rng = random.Random(1000003 * m + P.n)
    state = (gens * 10)[:max(10, len(gens))]
    acc = P.idn
    tried = set()
    for _ in range(tries):
        i, j = rng.sample(range(len(state)), 2)
        state[i] = mul(state[i], state[j])
        acc = mul(acc, state[i])
        o = _perm_order(acc)
        if o % p:
            continue
        t = _perm_power(acc, o // p)
        key = t if sym else min(t, mul(t, t))
        if key in tried:
            continue
        tried.add(key)
        res = _class_action(gens, t, size, sym)
        if res is None:
            continue
        imgs, conj = res
        Q = PermGroup(size, imgs, order=order)     # (|Q| <= |P|: see _star_action)
        if Q.order() != order:
            continue
        J = johnson_structure(Q)
        if J is None or J[0] != m:
            continue
        fq = J[2]

        def f(g, fq=fq, conj=conj):
            return fq(conj(g))

        return m, f
    return None


def _class_action(gens, t, size, sym):
    """The conjugacy class of t (sym) or of the subgroup <t> (t of order 3)
    under <gens>, if it has `size` members: (images of gens on it, conj) with
    conj(g) the permutation of the class induced by conjugation with g.
    Conjugation c -> g^-1 c g is a right action, so conj is a homomorphism."""
    if sym:
        def key(c):
            return c
    else:
        def key(c):
            c2 = mul(c, c)
            return c if c < c2 else c2
    ginv = [inv(g) for g in gens]
    cls = [key(t)]
    index = {cls[0]: 0}
    for c in cls:
        for g, gi in zip(gens, ginv):
            e = key(mul(mul(gi, c), g))
            if e not in index:
                if len(cls) == size:
                    return None
                index[e] = len(cls)
                cls.append(e)
    if len(cls) != size:
        return None

    def conj(g):
        gi = inv(g)
        return tuple(index[key(mul(mul(gi, c), g))] for c in cls)

    return [conj(g) for g in gens], conj


# -- Johnson and Hamming graphs on a set of labels -----------------------------
# GiantStep can use these on a color class of the projected label coloring
# (Babai's "Johnson" outcome): when the class is exactly a Johnson graph
# J(m, k) or a Hamming graph H(r, D) on all labels, its embedding is unique up
# to its automorphism group, so every isomorphism maps the embedding of x
# onto that of y.
def johnson_embedding(nbr):
    """If the graph with neighbour sets nbr on range(q) is exactly J(m, k) for
    some m >= 2k >= 4: (m, k, sets), sets[l] a k-subset of range(m), such that
    l ~ l' iff |sets[l] & sets[l']| = k - 1 (verified). The embedding is unique
    up to Sym(m), and complementation when m = 2k. Otherwise None."""
    q = len(nbr)
    if q < 6:
        return None
    deg = len(nbr[0])
    if any(len(v) != deg for v in nbr):
        return None
    k = 2
    while math.comb(2 * k, k) <= q:
        m = 2 * k
        while math.comb(m, k) < q:
            m += 1
        if math.comb(m, k) == q and k * (m - k) == deg:
            stars = _johnson_stars(m, k, nbr)
            if stars is not None:
                sets = [[] for _ in range(q)]
                for i, S in enumerate(stars):
                    for l in S:
                        sets[l].append(i)
                sets = [frozenset(v) for v in sets]
                if _is_johnson(m, k, sets, nbr):
                    return m, k, sets
        k += 1
    return None


def _is_johnson(m, k, sets, nbr):
    index = {}
    for l, v in enumerate(sets):
        if len(v) != k or index.setdefault(v, l) != l:
            return False
    for l, v in enumerate(sets):
        exp = set()
        for a in v:
            rest = v - {a}
            for b in range(m):
                if b not in v:
                    exp.add(index[rest | {b}])
        if exp != nbr[l]:
            return False
    return True


def hamming_embedding(nbr):
    """If the graph with neighbour sets nbr on range(q) is exactly the Hamming
    graph H(r, D) for some r >= 2, D >= 2 (D = 2: the hypercube Q_r):
    (r, D, coords), coords[l] an r-tuple over range(D), such that l ~ l' iff
    their coordinates differ in exactly one place (verified). The embedding is
    unique up to Aut(H(r, D)) = Sym(D) wr Sym(r). The lines (maximal cliques
    of size D) through a vertex are the components of its neighbourhood;
    coordinates of lines are propagated along squares (two neighbours of p in
    different coordinates have exactly one common neighbour besides p);
    coordinate c of a vertex is its fiber under the lines of the other
    coordinates. Otherwise None."""
    q = len(nbr)
    deg = len(nbr[0]) if q else 0
    if q < 4 or any(len(v) != deg for v in nbr):
        return None
    for r in range(2, q.bit_length() + 1):
        D = round(q ** (1.0 / r))
        if D >= 2 and D ** r == q and r * (D - 1) == deg:
            res = _hamming(nbr, r, D)
            if res is not None:
                return r, D, res
    return None


def _hamming(nbr, r, D):
    q = len(nbr)
    lines_at = []
    for l in range(q):
        rest, ls = set(nbr[l]), []
        while rest:
            v = rest.pop()
            comp = (nbr[v] & rest) | {v}
            if len(comp) != D - 1:
                return None
            rest -= comp
            ls.append(frozenset(comp | {l}))
        if len(ls) != r:
            return None
        lines_at.append(ls)
    coord = {L: c for c, L in enumerate(lines_at[0])}
    seen = [False] * q
    seen[0] = True
    queue = [0]
    for p in queue:
        for L in lines_at[p]:
            a = coord[L]
            for v in L:
                if seen[v]:
                    continue
                for L2 in lines_at[p]:
                    if L2 is L:
                        continue
                    t = next(u for u in L2 if u != p)
                    common = nbr[v] & nbr[t]
                    common.discard(p)
                    if len(common) != 1:
                        return None
                    s = common.pop()
                    Lv = next((M for M in lines_at[v] if s in M), None)
                    if Lv is None or coord.setdefault(Lv, coord[L2]) != coord[L2]:
                        return None
                if not any(M == L for M in lines_at[v]):
                    return None
                seen[v] = True
                queue.append(v)
    if not all(seen):
        return None
    for l in range(q):
        if sorted(coord.get(L, -1) for L in lines_at[l]) != list(range(r)):
            return None
    coords = [[0] * r for _ in range(q)]
    for c in range(r):
        up = list(range(q))

        def root(v):
            while up[v] != v:
                up[v] = up[up[v]]
                v = up[v]
            return v

        for L, cl in coord.items():
            if cl != c:
                it = iter(L)
                a = root(next(it))
                for v in it:
                    z = root(v)
                    if z != a:
                        up[z] = a
        fib = {}
        for l in range(q):
            fib.setdefault(root(l), len(fib))
        if len(fib) != D:
            return None
        for l in range(q):
            coords[l][c] = fib[root(l)]
    coords = [tuple(v) for v in coords]
    index = {v: l for l, v in enumerate(coords)}
    if len(index) != q:
        return None
    for l, v in enumerate(coords):
        exp = {index[v[:c] + (b,) + v[c + 1:]] for c in range(r) for b in range(D) if b != v[c]}
        if exp != nbr[l]:
            return None
    return coords
