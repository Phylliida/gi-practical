"""Canonical forms of strings under permutation groups by Luks's recursion
(Luks 1982; Babai-Luks 1983, Sec. 3; docs/w40-solvable.md has the complexity
argument).

    F, lam, gens = luks_canon(P, x, stats)

P is a PermGroup on range(m), x a string (tuple of ints) of length m. F is a
canonical form of x under P: a string in the P-orbit of x that depends only on
P as a set and on the orbit x^P. lam is an element of P with act(x, lam) == F,
and gens generate Aut_P(F); so Lambda_P(x) := {h in P : act(x, h) == F} equals
lam Aut_P(F) (Definition 2.1 / Lemma 2.2 of
docs/canonization-bounded-degree.md).

The function has the interface of gi.canon.perm_canon. It is NOT the least
image: the least image of a string under a permutation group is NP-hard to
compute in general, which is why Luks's form is defined by the recursion below.

Definition of the canonizer C(G, x), for a group G on range(w) and a string x
of length w, returning (lam, U), lam in G, U = Aut_G(act(x, lam)):

 (1) x invariant under G: lam = 1, U = G.
 (2) |G| <= SMALL: lam reaches the least image act(x, lam) over all of G.
 (3) G elementary abelian 2-group: the least image in orbit-major order, by
     Gaussian elimination (gi.ea2.EAAction.canon).
 (4) G intransitive, with orbits O_1, ..., O_t ordered by least point (chain
     rule): C is applied to the restriction of the current group to O_1, then
     the group becomes the stabilizer of the result in the current group, x
     moves along, and the next orbit is treated.
 (5) G transitive on w >= 2 points, with the canonical block system with
     primitive quotient P = G/N on k blocks (gi.group.top_block_system; for a
     primitive G it is the system of points, N = 1):
       * if |P| exceeds enum_limit(k), the fallback (7) applies;
       * otherwise, for every coset N g of N in G: (lam_g, U_g) = C(N, x^g),
         h_g = g lam_g; F_g = act(x, h_g).
       The form is the least F_g; lam is the h_g of a coset attaining it, and
       U = <U_best, h_best^-1 h_t for every coset t attaining it>. If G is
       primitive and Sym(w) or Alt(w), the sorted string (6) is used instead of
       listing G; other primitive G are listed.
 (6) G = Sym(w) or Alt(w) in the natural action: the sorted string (for Alt(w),
     with the last two positions exchanged when all values are distinct and
     sorting is odd), Aut the Young subgroup of the value classes intersected
     with G.
 (7) Fallback, only where |P| > enum_limit(k): gi.canon.perm_canon on (G, x),
     the exact (least image) search over a stabilizer chain, which is
     exponential in the worst case. All decisions depend on G only as a set, so
     the fallback is itself a canonical function; see "Why no work counter"
     below. The limit is never exceeded for solvable G, since a primitive
     solvable group of degree k has order at most 24^(-1/3) k^3.25 (Palfy 1982,
     Wolf 1982), so |P| < k^4 <= enum_limit(k); this is proved in
     docs/w40-solvable.md, and luks_canon can be told to raise
     (LimitExceeded) on a fallback to check it.

Choices are functions of G only (principle P1 of the write-up): every decision
reads the group through objects defined by the set G alone: its order, its
orbits (ordered by least point), whether it is elementary abelian, its
primitive quotient and kernel of the action on the block system of
top_block_system, whose blocks are defined by the ordered domain and G. So the
output depends only on the group as a set and on the orbit of x; different
generating sets (or different coset representatives) give the same F.

Exactness of F as a canonical form.
By induction over the recursion: (1), (2), (3), (6) and (7) give functions of
(G, orbit of x) directly. (4) is the chain rule: the first orbit's result F_1
is a function of (G^{O_1}, orbit of x|O_1), so the set of possible strings on
O_1 after lam is unique, and every possible element lam' of the first step is
lam_1 u with u in the stabilizer U_1 of F_1; the remaining orbits are then
treated under U_1 from the string x^lam_1, determined up to U_1. (5): the
cosets of N are permuted by x -> x^h (h in G), N being normal, and C(N, ...)
is a function of the N-orbit, so the multiset of {F_g} is a function of the
G-orbit of x.

Automorphisms. In (5) let h_b attain the minimum F and let a be in Aut_G(F).
Then x^(h_b a) = F, so h_b a lies in some coset t attaining the minimum, and
h_b a = g_t n with n in N, x^(g_t n) = F. Hence n is in the N-coset
Lambda_N(x^g_t) = lam_t Aut_N(F), so h_b a = h_t u with u in Aut_N(F) and
a = h_b^-1 h_t u. Thus Aut_G(F) = <h_b^-1 h_t> Aut_N(F), and U_best = Aut_N(F)
since x^(h_b) = F. The tie cosets number exactly |Aut_G(F) : Aut_N(F)|, which
gives |U| = t |U_best|.

Why no work counter. A hand-off from a fast search to this canonizer based on
a node count of the search would have to be the same for all strings in an
orbit; perm_canon's node count is not (a string and a relabelled copy can
differ by 8x in nodes; docs/w40-solvable.md Sec. 2). Instead every decision
that selects a method is a function of (G as a set, orbit of x); these are
the predicates of the list above and SMALL and enum_limit.
"""
from math import factorial
from operator import itemgetter

from .perm import identity, mul, inv, act, sym_gens, alt_gens, cycle, parity
from .group import PermGroup, ActionHom, RestrictionHom, top_block_system
from .ea2 import EAAction, EA2, is_ea2

__all__ = ["luks_canon", "luks_canon_group", "enum_limit_default", "SMALL", "LimitExceeded"]

SMALL = 64                              # groups of at most this order are listed


class LimitExceeded(Exception):
    """Raised (in strict mode) when a primitive section exceeds enum_limit."""


def enum_limit_default(k):
    """The largest primitive group of degree k that is enumerated: every
    solvable primitive group fits (k^4 > 24^(-1/3) k^3.25), so does S_7."""
    return max(k * k * k * k, 5040)


class _Run:
    """One call of luks_canon: parameters and counters."""
    __slots__ = ("stats", "limit", "strict", "homs", "memo")

    def __init__(self, stats, limit, strict):
        self.stats, self.limit, self.strict = stats, limit, strict
        self.homs = {}                  # (id(G), orbit) -> RestrictionHom
        self.memo = {}                  # (id(G), x) -> (G, lam, U)

    def count(self, key, by=1):
        if self.stats is not None:
            self.stats[key] += by


def _invariant_gens(gens, x):
    """Whether x^g == x for every permutation g of gens."""
    for g in gens:
        if _getter(g)(x) != x:
            return False
    return True


def _getter(t):
    """itemgetter(*t) returning a tuple also for len(t) == 1."""
    if len(t) == 1:
        a = t[0]
        return lambda x: (x[a],)
    return itemgetter(*t)


def _list_group(G, x, run):
    """(2): the least image over all of G, by listing it."""
    run.count("canon_luks_listed")
    best, bg, auts, count = None, None, [], 0
    for g in G.elements():
        y = act(x, g)
        if best is None or y < best:
            best, bg, auts, count = y, g, [], 1
        elif y == best:
            count += 1
            auts.append(g)
    binv = inv(bg)
    gens = [mul(binv, g) for g in auts]
    return bg, PermGroup(G.n, gens, order=count) if gens else PermGroup(G.n)


def _ea_group(G, x, run):
    """(3): the least image in orbit-major order, for G elementary abelian."""
    run.count("canon_luks_ea")
    w = G.n
    E = EA2(w, G.gens)
    c, N = EAAction(len(E.gens), E.gens, w).canon(x)
    lam = E.elem(c) if c else identity(w)
    gens = [E.elem(v) for v in N]
    return lam, PermGroup(w, gens, order=1 << len(gens)) if gens else PermGroup(w)


def _giant_points(G, x, run):
    """G = Sym(w) or Alt(w) natural (recognized by its order): the least image
    is the sorted string, with the last two positions exchanged when G is
    Alt(w), the values are all distinct and the sorting permutation is odd.
    Aut is the Young subgroup of the value classes (intersected with Alt(w)).
    A function of (G, orbit of x)."""
    run.count("canon_luks_giant")
    w = G.n
    alt = G.order() != factorial(w)
    order = sorted(range(w), key=lambda i: (x[i], i))
    # lam: position order[j] -> j (the sorted string), first candidate
    lam = [0] * w
    for j, i in enumerate(order):
        lam[i] = j
    F = [x[i] for i in order]
    # the value classes in F (intervals of positions)
    classes = []
    i = 0
    while i < w:
        j = i + 1
        while j < w and F[j] == F[i]:
            j += 1
        classes.append(range(i, j))
        i = j
    dup = any(len(c) >= 2 for c in classes)
    if alt:
        if parity(tuple(lam)):
            if dup:
                # make lam even: exchange the images of two equal values
                c = next(c for c in classes if len(c) >= 2)
                a, b = order[c[0]], order[c[1]]
                lam[a], lam[b] = lam[b], lam[a]
            else:
                # all distinct and odd: the least even image swaps the last two
                a, b = order[w - 2], order[w - 1]
                lam[a], lam[b] = lam[b], lam[a]
    lam = tuple(lam)
    if not dup:
        return lam, PermGroup(w)
    gens = []
    order_u = 1
    big = [c for c in classes if len(c) >= 2]
    for c in big:
        for v in range(2, len(c) + 1):
            order_u *= v
    if not alt:
        for c in big:
            gens += sym_gens(w, list(c))
    else:
        order_u //= 2
        for c in big:
            if len(c) >= 3:
                gens += alt_gens(w, list(c))
        t0 = big[0]
        for c in big:                   # double transpositions across classes
            if c is not t0:
                gens.append(mul(cycle(w, [t0[0], t0[1]]), cycle(w, [c[0], c[1]])))
    if order_u == 1:
        return lam, PermGroup(w)
    return lam, PermGroup(w, gens, order=order_u)


def _ea_possible(G):
    """A cheap necessary condition (generators of PermGroup are irredundant)."""
    return G.order() == 1 << len(G.gens)


def _restriction(G, O, run):
    """The restriction G -> G^O, cached per group object."""
    key = (id(G), tuple(O))
    hom = run.homs.get(key)
    if hom is None:
        hom = RestrictionHom(G, O)
        run.homs[key] = hom
    return hom


def _solve(G, x, run):
    """C(G, x): (lam, U), lam in G with act(x, lam) the canonical form and
    U = Aut_G(act(x, lam)), for a group G on range(len(x)). Results are
    remembered per (group object, string) for the rest of the luks_canon
    call (the entry keeps the group alive, so the key stays valid)."""
    key = (id(G), x)
    r = run.memo.get(key)
    if r is not None:
        run.count("canon_luks_memo")
        return r[1], r[2]
    lam, U = _solve_node(G, x, run)
    run.memo[key] = (G, lam, U)
    return lam, U


def _solve_node(G, x, run):
    """The node of _solve (see the module docstring)."""
    run.count("canon_luks_nodes")
    gens = G.gens
    w = G.n
    if not gens or _invariant_gens(gens, x):
        return identity(w), G
    order = G.order()
    if order <= SMALL:
        return _list_group(G, x, run)
    if _ea_possible(G) and is_ea2(gens, w):
        return _ea_group(G, x, run)
    orbs = G.orbits_shared()
    if len(orbs) > 1:
        return _chain(G, orbs, x, run)
    return _transitive(G, x, run)


def _chain(G, orbs, x, run):
    """(4): the chain rule over the orbits of G (a list of sorted lists,
    ordered by least point). When G is the direct product of its restrictions
    to the orbits (a property of the group as a set) the orbits are
    independent: the same recursion, without restricting the group after each
    orbit, each orbit canonized on its own (and identical subproblems shared
    through the memo of _solve)."""
    w = G.n
    moving = [O for O in orbs if len(O) > 1]
    if len(moving) > 1 and _gens_split(G, moving, w):
        homs = [_restriction(G, O, run) for O in moving]
        return _chain_product(G, moving, homs, x, run)
    lam, H = identity(w), G
    cur = x
    for O in moving:
        xO = _getter(O)(cur)
        v0 = xO[0]
        for v in xO:
            if v != v0:
                break
        else:
            continue                    # (constant on O: nothing to do)
        if not H.gens:
            break
        hom = _restriction(H, O, run)
        Gs = hom.image_group()
        l, Us = _solve(Gs, xO, run)
        if l != Gs.idn:
            g = hom.lift(l)
            lam = mul(lam, g)
            cur = act(cur, g)
        if Us is not Gs:
            H = hom.preimage(Us.gens, order=Us.order())
    return lam, H


def _gens_split(G, moving, w):
    """Whether every generator of G moves points of only one orbit in moving
    (then G is the direct product of its restrictions to the orbits, a
    sufficient condition, read off the generators; the product path computes
    the same result as the general chain rule, so the test may miss products)."""
    where = [-1] * w
    for i, O in enumerate(moving):
        for p in O:
            where[p] = i
    for g in G.gens:
        s = -1
        for p, q in enumerate(g):
            if p != q:
                if s == -1:
                    s = where[p]
                elif s != where[p]:
                    return False
    return True


def _chain_product(G, moving, homs, x, run):
    """(4) for G the direct product of its restrictions to the orbits in
    moving: each orbit is canonized separately, and the element and the group
    are assembled from the parts (elements of the factors are extended by the
    identity, which lies in G since G is the full product)."""
    run.count("canon_luks_products")
    w = G.n
    lam = list(range(w))
    gens = []
    order = 1
    for O, hom in zip(moving, homs):
        xO = _getter(O)(x)
        Gs = hom.image_group()
        if Gs.gens:
            l, Us = _solve(Gs, xO, run)
        else:
            l, Us = Gs.idn, Gs
        for j, p in enumerate(O):
            lam[p] = O[l[j]]
        order *= Us.order()
        for u in Us.gens:
            g = list(range(w))
            for j, p in enumerate(O):
                g[p] = O[u[j]]
            gens.append(tuple(g))
    return tuple(lam), (PermGroup(w, gens, order=order) if gens else PermGroup(w))


def _fallback(G, x, run):
    """(7): the exact least-image search on (G, x), used only when the
    primitive quotient is too large for the limit. Function of (G, orbit)."""
    if run.strict:
        raise LimitExceeded()
    from .canon import perm_canon       # (gi.canon imports this module)
    run.count("canon_luks_fallback")
    _, lam, gens = perm_canon(G, x, run.stats)
    if not gens:
        return lam, PermGroup(G.n)
    return lam, PermGroup(G.n, gens, ambient_base=G.short_base())


def _transitive(G, x, run):
    """(5): G transitive on w >= 2 points, x not invariant."""
    w = G.n
    blocks = top_block_system(G)
    if blocks is None:                  # G is primitive (points = blocks)
        k = w
        o = G.order()
        if k >= 2 and (o == factorial(k) or (k >= 3 and o * 2 == factorial(k))):
            return _giant_points(G, x, run)
        if run.limit is not None and o > run.limit(k):
            return _fallback(G, x, run)
        return _list_group(G, x, run)
    k = len(blocks)
    where = [0] * w
    for i, B in enumerate(blocks):
        for p in B:
            where[p] = i
    reps = [B[0] for B in blocks]

    def blockact(g):
        return tuple([where[g[p]] for p in reps])

    hom = ActionHom(G, k, blockact)
    P = hom.image_group()
    if run.limit is not None and P.order() > run.limit(k):
        return _fallback(G, x, run)
    run.count("canon_luks_cosets", P.order())
    N = hom.kernel()
    best, best_h, best_U = None, None, None
    ties = []
    seen = {}                           # x^g (on W) -> (lam_g, U_g, F)
    for p in P.elements():
        g = hom.lift(p)
        y = act(x, g)
        r = seen.get(y)
        if r is None:
            lamN, UN = _solve(N, y, run)
            F = act(y, lamN)
            seen[y] = (lamN, UN, F)
        else:
            lamN, UN, F = r
        if best is None or F < best:
            best, best_h, best_U = F, mul(g, lamN), UN
            ties = []
        elif F == best:
            ties.append(mul(g, lamN))
    if not ties:
        return best_h, best_U
    binv = inv(best_h)
    extra = [mul(binv, h) for h in ties]
    gens = list(best_U.gens) + extra
    order = best_U.order() * (len(ties) + 1)
    return best_h, PermGroup(w, gens, order=order, ambient_base=G.short_base())


def luks_canon(P, x, stats=None, enum_limit=enum_limit_default, strict=False):
    """The canonical form of the string x under the permutation group P (see
    the module docstring). Returns (F, lam, gens): act(x, lam) == F and gens
    generate Aut_P(F).

    enum_limit(k): the largest primitive quotient of degree k that is
    enumerated (None: no limit, Babai-Luks's unconditional bound); above it
    the node falls back to the exact least-image search (gi.canon.perm_canon),
    or raises LimitExceeded when strict is set."""
    F, lam, U = luks_canon_group(P, x, stats, enum_limit, strict)
    return F, lam, list(U.gens)


def luks_canon_group(P, x, stats=None, enum_limit=enum_limit_default, strict=False):
    """luks_canon, with the group Aut_P(F) (a PermGroup with its order) in place
    of the list of its generators: (F, lam, U)."""
    m = P.n
    x = tuple(x)
    gens = P.gens
    if not gens or _invariant_gens(gens, x):
        return x, identity(m), P
    run = _Run(stats, enum_limit, strict)
    if stats is not None:
        stats["canon_luks_calls"] += 1
        stats["canon_luks_max_degree"] = max(stats["canon_luks_max_degree"], m)
    lam, U = _solve(P, x, run)
    return act(x, lam), lam, U
