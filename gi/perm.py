"""Permutations of range(n), stored as tuples.

Convention (right action, as in the paper): point i is sent to p[i], and the
product mul(p, q) means "first p, then q".  A coloring x is a tuple of colors
indexed by points; relabeling by g gives x^g with x^g[g[i]] = x[i].  So g is an
isomorphism from x to y exactly when act(x, g) == y.
"""


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
