"""The baseline (unoptimized) perm and group code, kept as a reference for
tests/test_group.py: the optimized gi.group must give identical results."""
import math
from itertools import product


def identity(n):
    return tuple(range(n))


def mul(p, q):
    """p then q."""
    return tuple(map(q.__getitem__, p))


def inv(p):
    r = [0] * len(p)
    for i, j in enumerate(p):
        r[j] = i
    return tuple(r)


def is_identity(p):
    return all(i == j for i, j in enumerate(p))


def act(x, g):
    """The relabeled coloring x^g, with x^g[g[i]] = x[i]."""
    r = [None] * len(x)
    for i, c in enumerate(x):
        r[g[i]] = c
    return tuple(r)


def maps(g, x, y):
    """Whether x^g == y."""
    return all(y[g[i]] == c for i, c in enumerate(x))


def parity(p):
    seen = [False] * len(p)
    par = 0
    for i in range(len(p)):
        if not seen[i]:
            j, length = i, 0
            while not seen[j]:
                seen[j] = True
                j = p[j]
                length += 1
            par ^= (length - 1) & 1
    return par


def cycle(n, pts):
    """The cyclic permutation pts[0] -> pts[1] -> ... -> pts[0] on range(n)."""
    p = list(range(n))
    pts = list(pts)
    for a, b in zip(pts, pts[1:] + pts[:1]):
        p[a] = b
    return tuple(p)


def alt_gens(n, pts):
    """Generators of Alt(pts) as permutations of range(n)."""
    pts = list(pts)
    return [cycle(n, [pts[0], pts[1], pts[j]]) for j in range(2, len(pts))]


def sym_gens(n, pts):
    """Generators of Sym(pts) as permutations of range(n)."""
    pts = list(pts)
    if len(pts) < 2:
        return []
    gens = [cycle(n, pts[:2])]
    if len(pts) > 2:
        gens.append(cycle(n, pts))
    return gens




class PermGroup:
    """A permutation group on range(n) with a base and strong generating set,
    built by the deterministic incremental Schreier-Sims algorithm.

    base[l] is the l-th base point, S[l] the strong generators fixing
    base[:l], and T[l] maps each point p of the orbit base[l]^<S[l]> to a
    u with base[l]^u = p (Ti[l][p] is u^-1). `gens` lists the generators that
    were accepted (each enlarged the group), so it is irredundant.
    """

    def __init__(self, n, gens=(), base=()):
        self.n = n
        self.idn = identity(n)
        self.gens = []
        self.base, self.S, self.T, self.Ti = [], [], [], []
        for b in base:
            self._push_base(b)
        for g in gens:
            self.add(g)

    # -- Schreier-Sims -----------------------------------------------------
    def _push_base(self, b):
        self.base.append(b)
        self.S.append([])
        self.T.append({b: self.idn})
        self.Ti.append({b: self.idn})

    def _orbit(self, l):
        b, S = self.base[l], self.S[l]
        T, Ti, queue = {b: self.idn}, {b: self.idn}, [b]
        for p in queue:
            u = T[p]
            for s in S:
                q = s[p]
                if q not in T:
                    v = mul(u, s)
                    T[q] = v
                    Ti[q] = inv(v)
                    queue.append(q)
        self.T[l], self.Ti[l] = T, Ti

    def sift(self, g, start=0):
        for l in range(start, len(self.base)):
            p = g[self.base[l]]
            Ti = self.Ti[l]
            if p not in Ti:
                return g, l
            g = mul(g, Ti[p])
        return g, len(self.base)

    def _moved_point(self, g):
        return next(i for i in range(self.n) if g[i] != i)

    def add(self, g):
        """Add a generator. Returns True if the group grew."""
        r, j = self.sift(g)
        if j == len(self.base) and r == self.idn:
            return False
        self.gens.append(g)
        k = 0
        while k < len(self.base) and g[self.base[k]] == self.base[k]:
            k += 1
        if k == len(self.base):
            self._push_base(self._moved_point(g))
        for l in range(k + 1):
            self.S[l].append(g)
            self._orbit(l)
        self._schreier(k)
        return True

    def _schreier(self, i):
        while i >= 0:
            restart = False
            T, Ti = self.T[i], self.Ti[i]
            for p in list(T):
                u = T[p]
                for s in list(self.S[i]):
                    h = mul(mul(u, s), Ti[s[p]])
                    if h == self.idn:
                        continue
                    r, j = self.sift(h, i + 1)
                    if j < len(self.base) or r != self.idn:
                        if j == len(self.base):
                            self._push_base(self._moved_point(r))
                        for l in range(i + 1, j + 1):
                            self.S[l].append(r)
                            self._orbit(l)
                        i = j
                        restart = True
                        break
                if restart:
                    break
            if not restart:
                i -= 1

    # -- queries -------------------------------------------------------------
    def order(self):
        return math.prod(len(t) for t in self.T)

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
        pts = range(self.n) if points is None else points
        done, out = set(), []
        gens = self.gens
        for p in pts:
            if p in done:
                continue
            orb, queue = {p}, [p]
            for a in queue:
                for g in gens:
                    b = g[a]
                    if b not in orb:
                        orb.add(b)
                        queue.append(b)
            done |= orb
            out.append(sorted(orb))
        out.sort(key=lambda o: o[0])
        return out

    def elements(self):
        """All elements (only for small groups)."""
        levels = [list(t.values()) for t in self.T]
        for us in product(*levels):
            g = self.idn
            for u in us:            # element = u_{k-1} ... u_0
                g = mul(u, g)
            yield g

    def _tail(self, m):
        """The stabilizer of base[:m], reusing this chain."""
        H = PermGroup(self.n)
        if m < len(self.base):
            H.base = self.base[m:]
            H.S = [list(S) for S in self.S[m:]]
            H.T = self.T[m:]
            H.Ti = self.Ti[m:]
            H.gens = list(H.S[0])
        return H

    def pointwise_stabilizer(self, points):
        points = list(points)
        if self.base[:len(points)] == points:
            return self._tail(len(points))
        H = PermGroup(self.n, self.strong_gens(), base=points)
        return H._tail(len(points))

    def stabilizer(self, p):
        return self.pointwise_stabilizer([p])


def reduce_gens(n, gens):
    """An irredundant generating list for <gens>."""
    gens = [g for g in dict.fromkeys(gens) if any(i != j for i, j in enumerate(g))]
    if len(gens) <= 4:
        return gens
    return PermGroup(n, gens).gens


class ActionHom:
    """The homomorphism phi: G -> Sym(m) given by `image(g)` for every g in G.

    Lifting and the kernel come from the group generated by g + phi(g) on
    range(n + m), with the m image points first in the base.
    """

    def __init__(self, G, m, image):
        self.G, self.m, self.image_of = G, m, image
        n = G.n
        comb = [g + tuple(n + v for v in image(g)) for g in G.gens]
        self.C = PermGroup(n + m, comb, base=range(n, n + m))
        self._image = None
        self._kernel = None

    def image_order(self):
        return math.prod(len(self.C.T[l]) for l in range(self.m))

    def image_group(self):
        if self._image is None:
            self._image = PermGroup(self.m, [self.image_of(g) for g in self.G.gens])
        return self._image

    def lift(self, p):
        """Some g in G with phi(g) = p. Raises ValueError if p is not in phi(G)."""
        n, m, C = self.G.n, self.m, self.C
        g = identity(n) + tuple(n + v for v in p)
        acc = C.idn
        for l in range(m):
            pt = g[C.base[l]]
            if pt not in C.T[l]:
                raise ValueError("not in the image")
            acc = mul(C.T[l][pt], acc)
            g = mul(g, C.Ti[l][pt])
        return acc[:n]

    def kernel(self):
        if self._kernel is None:
            n, m, C = self.G.n, self.m, self.C
            K = PermGroup(n)
            if m < len(C.base):
                K.base = C.base[m:]
                K.S = [[s[:n] for s in S] for S in C.S[m:]]
                K.T = [{p: u[:n] for p, u in T.items()} for T in C.T[m:]]
                K.Ti = [{p: u[:n] for p, u in T.items()} for T in C.Ti[m:]]
                K.gens = list(K.S[0])
            self._kernel = K
        return self._kernel


# -- blocks ------------------------------------------------------------------
def minimal_block(n, gens, a, b):
    """Atkinson's algorithm: labels of the finest invariant partition joining a, b."""
    parent = list(range(n))

    def find(v):
        root = v
        while parent[root] != root:
            root = parent[root]
        while parent[v] != root:
            parent[v], v = root, parent[v]
        return root

    queue = []

    def union(u, v):
        ru, rv = find(u), find(v)
        if ru != rv:
            if ru > rv:
                ru, rv = rv, ru
            parent[rv] = ru
            queue.append((ru, rv))

    union(a, b)
    i = 0
    while i < len(queue):
        u, v = queue[i]
        i += 1
        for g in gens:
            union(g[u], g[v])
    return [find(v) for v in range(n)]


def minimal_block_labels(n, gens):
    """For a transitive group: labels of a minimal nontrivial block system,
    or None if the group is primitive."""
    best, best_size = None, n
    for b in range(1, n):
        lab = minimal_block(n, gens, 0, b)
        size = lab.count(lab[0])
        if size < best_size:
            best, best_size = lab, size
            if size == 2:
                break
    return best if best_size < n else None


def top_block_system(G):
    """For transitive G: a block system on which G acts primitively, reached by
    stacking minimal block systems (the paper's partition hierarchy, read
    bottom-up). Returns the blocks, or None if G is primitive."""
    n = G.n
    blocks = [[p] for p in range(n)]
    changed = False
    while len(blocks) > 2:
        d = len(blocks)
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
    P0 = PermGroup(d, P.gens, base=[0])
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
            for c in nbr[b]:
                common = nbr[b] & nbr[c]
                stars.add(frozenset([b, c] + [v for v in common if nbr[v] & common]))
        stars = sorted((s for s in stars if len(s) == m - 1), key=sorted)
        if len(stars) != m:
            continue
        count = [0] * d
        for s in stars:
            for p in s:
                count[p] += 1
        if any(c != 2 for c in count):
            continue
        star_id = {s: i for i, s in enumerate(stars)}

        def f(g, stars=stars, star_id=star_id):
            return tuple(star_id[frozenset(g[p] for p in s)] for s in stars)

        return m, f
    return None
