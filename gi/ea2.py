"""Elementary abelian 2-groups given by an independent basis of commuting
involutions, and string isomorphism under them by linear algebra over F_2
(no Schreier-Sims).

An element is a vector a in F_2^k (an int bitmask): g(a) is the product of the
basis elements g_i with bit i set (in any order, since they commute). With an
independent basis, a -> g(a) is an isomorphism F_2^k -> G, so |G| = 2^k.

String isomorphism. Let G act on positions 0..m-1, basis element i by the
permutation act[i]. Iso_G(x, y) = {g : x^g = y} (y[g[q]] = x[q] for all q,
the convention of gi.perm) is computed orbit by orbit:

  * On an orbit O with base point p0, G acts through the abelian group G/K_O,
    K_O = Stab(p0), which is regular on O. A BFS from p0 labels each q in O by
    lam(q) with g(lam(q)) mapping p0 to q (lam(q) = lam(parent) + e_i along
    the tree edge q = act[i][parent]). K_O is spanned by the Schreier vectors
    lam(q) + e_i + lam(act[i][q]) (Schreier's lemma for the transversal
    g(lam(q)); in an abelian group the subgroup they generate is their span).
  * An element g mapping p0 to t acts on O as q = w(p0) -> w(t) for any w with
    w(p0) = q (g and w commute). So along the BFS tree its images are
    phi(q) = act[i][phi(parent)], phi(p0) = t, and g maps x|O onto y|O iff
    y[phi(q)] = x[q] for all q, a condition on t alone. The solutions on O
    are the union over the valid t of the cosets lam(t) + K_O: an affine
    subspace c_O + U_O, U_O = K_O + span(lam(t) - lam(t0)) (the solution set
    of a string isomorphism problem is empty or a coset of Aut_G(x|O) >= K_O).
  * c_O + U_O = {a : r.a = r.c_O for every r in a basis of the annihilator of
    U_O}. The equations of all orbits together are solved by Gaussian
    elimination: no solution means Iso is empty; otherwise the solution set
    is a0 + N, and N (the null space) is Aut_G(x) in coordinates.
"""
from .perm import identity
from .kernel import ck as _ck

__all__ = ["EA2", "SparseEA", "EAAction", "is_ea2", "XorBasis", "nullspace", "compose"]


def _parity(v):
    return v.bit_count() & 1


class XorBasis:
    """Linear equations r.a = s over F_2 (r an int bitmask, s a bit) in
    echelon form: each stored row has a distinct pivot, its highest bit."""
    __slots__ = ("rows",)

    def __init__(self):
        self.rows = {}                  # pivot -> (row, rhs)

    def add(self, row, rhs=0):
        """Add an equation; False if it contradicts the stored ones."""
        rows = self.rows
        while row:
            p = row.bit_length() - 1
            e = rows.get(p)
            if e is None:
                rows[p] = (row, rhs)
                return True
            row ^= e[0]
            rhs ^= e[1]
        return rhs == 0

    def reduce(self, v):
        """v reduced by the rows (0 iff v is in their span)."""
        rows = self.rows
        while v:
            e = rows.get(v.bit_length() - 1)
            if e is None:
                return v
            v ^= e[0]
        return 0

    def rank(self):
        return len(self.rows)

    def full_reduce(self, v):
        """The canonical representative of v + span(rows): v with every pivot
        bit cleared (pivots in decreasing order; a row only touches bits up to
        its pivot). Linear in v."""
        rows = self.rows
        for p in sorted(rows, reverse=True):
            if v >> p & 1:
                v ^= rows[p][0]
        return v

    def solution(self, k):
        """One solution in F_2^k (free variables 0); the system must be
        consistent (add never returned False)."""
        a = 0
        for p in sorted(self.rows):
            row, rhs = self.rows[p]
            if rhs ^ _parity(row & a & ~(1 << p)):
                a |= 1 << p
        return a

    def kernel(self, k):
        """A basis of {a in F_2^k : r.a = 0 for every row r}, one vector per
        free variable."""
        piv = sorted(self.rows)
        out = []
        for f in range(k):
            if f in self.rows:
                continue
            a = 1 << f
            for p in piv:
                if _parity(self.rows[p][0] & a & ~(1 << p)):
                    a |= 1 << p
            out.append(a)
        return out


def nullspace(vectors, k):
    """A basis of the annihilator {r : r.v = 0 for all v} of the span of
    vectors in F_2^k."""
    B = XorBasis()
    for v in vectors:
        B.add(v)
    return B.kernel(k)


def is_ea2(gens, n):
    """Whether gens are commuting involutions on range(n)."""
    idn = identity(n)
    for i, g in enumerate(gens):
        if tuple(g[j] for j in g) != idn:
            return False
        for h in gens[:i]:
            if any(h[g[j]] != g[h[j]] for j in range(n)):
                return False
    return True


class EA2:
    """An elementary abelian 2-group on range(n) with an independent basis of
    commuting involutions (the caller guarantees independence)."""
    __slots__ = ("n", "gens")

    def __init__(self, n, gens):
        self.n, self.gens = n, list(gens)

    def order(self):
        return 1 << len(self.gens)

    def elem(self, a):
        """g(a), the product of the basis elements with bits set in a."""
        g = None
        i = 0
        gens = self.gens
        while a:
            if a & 1:
                h = gens[i]
                g = h if g is None else tuple(h[j] for j in g)
            a >>= 1
            i += 1
        return identity(self.n) if g is None else g


def compose(dicts):
    """The product of commuting involutions given as dicts {moved point: image}
    (each maps its keys among themselves): a dict of the moved points of the
    product. Costs O(sum of the supports). (Involutions are their own
    inverses, so the x with c(x) = y is c(y); order does not matter.)"""
    if _ck is not None:
        r = _ck.ea_compose(dicts)
        if r is not None:
            return r
    c = {}
    for g in dicts:
        ups = [(c.get(y, y), g[y]) for y in g]
        for x, z in ups:
            if z == x:
                c.pop(x, None)
            else:
                c[x] = z
    return c


class SparseEA:
    """An elementary abelian 2-group on points given by an independent basis of
    commuting involutions, each stored sparsely as a dict {moved point: image}
    (gens: {id: dict}), with who[p] = the set of generator ids moving p. Work
    on a layer depends on the generators that actually move its points, not
    on |G| * n. Generators may be extended to new points in place: their
    images of old points never change, so older code that holds a dict can
    keep reading the old points."""
    __slots__ = ("gens", "who", "_next")

    def __init__(self, gens=()):
        self.gens, self.who, self._next = {}, {}, 0
        for g in gens:
            self.add(g)

    @classmethod
    def from_tuples(cls, gens):
        """From permutations given as tuples (identity points are dropped)."""
        return cls({p: q for p, q in enumerate(g) if p != q} for g in gens)

    def __len__(self):
        return len(self.gens)

    def order(self):
        return 1 << len(self.gens)

    def add(self, g):
        """Add the involution g (a dict {moved point: image}); returns its id."""
        gid = self._next
        self._next = gid + 1
        self.gens[gid] = g
        who = self.who
        if _ck is not None and _ck.ea_who_add(who, g, gid) is not None:
            return gid
        for p in g:
            w = who.get(p)
            if w is None:
                who[p] = {gid}
            else:
                w.add(gid)
        return gid

    def remove(self, gid):
        g = self.gens.pop(gid)
        who = self.who
        if _ck is not None and _ck.ea_who_remove(who, g, gid) is not None:
            return
        for p in g:
            w = who[p]
            if len(w) == 1:
                del who[p]
            else:
                w.remove(gid)

    def extend(self, gid, moves):
        """Add entries {new point: image} to generator gid."""
        g, who = self.gens[gid], self.who
        g.update(moves)
        if _ck is not None and _ck.ea_who_add(who, moves, gid) is not None:
            return
        for p in moves:
            w = who.get(p)
            if w is None:
                who[p] = {gid}
            else:
                w.add(gid)

    def active_on(self, points):
        """Sorted ids of the generators moving some point of `points`."""
        who = self.who
        ids = set()
        for p in points:
            w = who.get(p)
            if w:
                ids.update(w)
        return sorted(ids)

    def restrict(self, ids, N):
        """Replace the generators `ids` by the combinations N (bitmasks over
        the indices of ids); returns the new ids parallel to N. A combination
        of one generator keeps that generator."""
        gens = self.gens
        out, kept, make = [None] * len(N), set(), []
        for i, v in enumerate(N):
            if v & (v - 1) == 0:
                out[i] = ids[v.bit_length() - 1]
                kept.add(out[i])
            else:
                c = []
                while v:
                    b = v & -v
                    c.append(gens[ids[b.bit_length() - 1]])
                    v ^= b
                make.append((i, compose(c)))
        for gid in ids:
            if gid not in kept:
                self.remove(gid)
        for i, c in make:
            out[i] = self.add(c)
        return out

    def dense(self, gid, n):
        """Generator gid as a tuple on range(n)."""
        g = list(range(n))
        for p, q in self.gens[gid].items():
            g[p] = q
        return tuple(g)

    def tuples(self, n):
        """All generators as tuples on range(n)."""
        return [self.dense(gid, n) for gid in self.gens]


class _Orbit:
    __slots__ = ("pts", "steps", "lam", "K", "dimK", "red")


class EAAction:
    """The action of an elementary abelian 2-group with k basis elements on
    positions 0..m-1 (act[i]: the permutation of basis element i). Orbit data
    is computed once and reused for every pair (x, y)."""

    def __init__(self, k, act, m):
        self.k, self.act, self.m = k, act, m
        self._orbits = None

    def orbits(self):
        if self._orbits is None:
            k, act, m = self.k, self.act, self.m
            seen = [False] * m
            out = []
            for p0 in range(m):
                if seen[p0]:
                    continue
                O = _Orbit()
                seen[p0] = True
                pts, steps, lam = [p0], [], {p0: 0}
                for q in pts:               # BFS; steps: (point, parent, generator)
                    lq = lam[q]
                    for i in range(k):
                        u = act[i][q]
                        if u not in lam:
                            lam[u] = lq ^ (1 << i)
                            seen[u] = True
                            pts.append(u)
                            steps.append((u, q, i))
                O.pts, O.steps, O.lam = pts, steps, lam
                O.K = O.red = None
                out.append(O)
            self._orbits = out
        return self._orbits

    def _kernel(self, O):
        """K_O = Stab(p0) as an XorBasis of the Schreier vectors (stops once
        its dimension is k - log2 |O|)."""
        if O.K is None:
            k, act, lam = self.k, self.act, O.lam
            target = k - (len(O.pts).bit_length() - 1)
            K = XorBasis()
            if len(O.pts) == 1:
                for i in range(k):
                    K.add(1 << i)
            else:
                for q in O.pts:
                    if K.rank() >= target:
                        break
                    lq = lam[q]
                    for i in range(k):
                        v = lq ^ (1 << i) ^ lam[act[i][q]]
                        if v:
                            K.add(v)
                    if K.rank() >= target:
                        break
            if K.rank() != target:      # |O| = |G : K_O| = 2^(k - dim K_O)
                raise AssertionError("EAAction: the group is not elementary abelian")
            O.K = K
        return O.K

    def iso(self, x, y):
        """Iso_G(x, y) as (a0, N): the solutions are a0 + span(N), and N is a
        basis of Aut_G(x) (in coordinates); None if there is none."""
        k, act = self.k, self.act
        eqs = XorBasis()
        for O in self.orbits():
            pts = O.pts
            p0 = pts[0]
            if len(pts) == 1:
                if x[p0] != y[p0]:
                    return None
                continue
            xv = [x[q] for q in pts]
            yv = [y[q] for q in pts]
            if sorted(xv) != sorted(yv):
                return None
            if xv.count(xv[0]) == len(xv):  # x and y constant on O: no condition
                continue
            steps, lam = O.steps, O.lam
            x0 = x[p0]
            valid = []
            for t in pts:
                if y[t] != x0:
                    continue
                phi = {p0: t}
                for u, q, i in steps:
                    v = act[i][phi[q]]
                    if y[v] != x[u]:
                        break
                    phi[u] = v
                else:
                    valid.append(t)
            if not valid:
                return None
            K = self._kernel(O)
            c0 = lam[valid[0]]
            U = XorBasis()
            U.rows = dict(K.rows)
            for t in valid[1:]:
                U.add(lam[t] ^ c0)
            if U.rank() == k:
                continue
            for r in U.kernel(k):       # the annihilator of U
                if not eqs.add(r, _parity(r & c0)):
                    return None
        return eqs.solution(k), eqs.kernel(k)

    def _reduced(self, O):
        """(sorted points of O, rl, pt): rl[q] is lam(q) fully reduced modulo
        K_O (the canonical representative of its coset), and pt maps reduced
        labels back to points. Reduction is linear, so g(a) maps q to
        pt[reduce(a) ^ rl[q]]."""
        if O.red is None:
            K = self._kernel(O)
            rl = {q: K.full_reduce(v) for q, v in O.lam.items()}
            O.red = (sorted(O.pts), rl, {v: q for q, v in rl.items()})
        return O.red

    def canon(self, x):
        """A canonical form of x under G (x^g = act(x, g); every g is an
        involution, so x^g[q] = x[g[q]]): the lexicographically least x^g over
        all g in G, positions read in orbit-major order (the orbits by their
        least point, each orbit's points increasing). This order depends on G
        only, so the least image depends only on the G-orbit of x.

        Returns (c, N): x^g(c) is the least image, and the g(a) attaining it
        are exactly a in c + span(N), so N is a basis of Aut_G(x) in
        coordinates (G is abelian, so Aut_G(x) = Aut_G(least image)).

        Orbit by orbit: the minimizers so far form an affine subspace c + U.
        On an orbit O, g(a) acts through a mod K_O, and the translates
        t = reduce(c + u) (u in U) are at most |O|; the least string on O is
        found by filtering the translates position by position. The
        minimizing translates form a coset m0 + D of (U + K_O)/K_O (the
        minimizers of an invariant set's restriction are a coset of its
        stabilizer), so the new minimizer set is c + U intersected with
        m0 + D + K_O, added as linear equations (the annihilator of D + K_O)."""
        k = self.k
        eqs = XorBasis()
        c, U = 0, [1 << i for i in range(k)]
        for O in self.orbits():
            pts = O.pts
            if len(pts) == 1 or not U:
                continue
            x0 = x[pts[0]]
            for q in pts:
                if x[q] != x0:
                    break
            else:
                continue                # x constant on O: every translate gives the same
            K = self._kernel(O)
            D, basis = XorBasis(), []
            for u in U:
                v = K.full_reduce(u)
                if D.reduce(v):         # (a membership test: v not in span(basis))
                    D.add(v)
                    basis.append(v)
            if not basis:
                continue                # one translate only: nothing to choose
            srt, rl, pt = self._reduced(O)
            cands = [K.full_reduce(c)]
            for v in basis:
                cands += [t ^ v for t in cands]
            for q in srt:
                rq = rl[q]
                best, keep = None, None
                for t in cands:
                    val = x[pt[t ^ rq]]
                    if best is None or val < best:
                        best, keep = val, [t]
                    elif val == best:
                        keep.append(t)
                cands = keep
                if len(cands) == 1:
                    break
            m0 = cands[0]
            W = XorBasis()
            W.rows = dict(K.rows)
            for t in cands[1:]:
                W.add(t ^ m0)
            if W.rank() == k:
                continue
            for r in W.kernel(k):       # a in m0 + D + K_O
                if not eqs.add(r, _parity(r & m0)):
                    raise AssertionError("EAAction.canon: inconsistent minimizers")
            c, U = eqs.solution(k), eqs.kernel(k)
        return c, U
