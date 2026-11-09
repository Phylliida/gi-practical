"""Tests of the w14-solver additions: the worklist 1-WL (gi/wl.py), the staged
root classes, sparse elementary abelian groups, and pipeline dispatch."""
import os
import random
import sys
from collections import Counter

import pytest

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.setrecursionlimit(100000)

from gi.wl import refine as wl_refine


def naive_1wl(nbr, col, roots=()):
    """Round-based 1-WL (coarsest equitable partition refining the initial
    one, with the roots individualized): the classes as a set of frozensets."""
    n = len(nbr)
    c = list(col)
    for i, r in enumerate(roots):
        c[r] = ("root", i)
    while True:
        sig = [(c[v], tuple(sorted(map(repr, (c[w] for w in nbr[v]))))) for v in range(n)]
        rank = {s: i for i, s in enumerate(sorted(set(sig), key=repr))}
        new = [rank[s] for s in sig]
        if len(set(new)) == len(set(map(repr, c))):
            return partition(new)
        c = new


def partition(col):
    classes = {}
    for v, c in enumerate(col):
        classes.setdefault(c, set()).add(v)
    return {frozenset(s) for s in classes.values()}


def random_graph(n, rng, p=None):
    p = rng.choice((0.1, 0.2, 0.3, 0.5)) if p is None else p
    nbr = [[] for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < p:
                nbr[i].append(j)
                nbr[j].append(i)
    return nbr


def random_regular_multigraph_free(n, d, rng):
    """A connected-or-not simple d-regular graph by rejection (small n)."""
    while True:
        pts = [i for i in range(n) for _ in range(d)]
        rng.shuffle(pts)
        E = set()
        ok = True
        for a, b in zip(pts[0::2], pts[1::2]):
            if a == b or (min(a, b), max(a, b)) in E:
                ok = False
                break
            E.add((min(a, b), max(a, b)))
        if ok:
            nbr = [[] for _ in range(n)]
            for a, b in E:
                nbr[a].append(b)
                nbr[b].append(a)
            return nbr


def shuffled_copy(nbr, col, rng):
    n = len(nbr)
    p = list(range(n))
    rng.shuffle(p)
    out = [None] * n
    outcol = [None] * n
    for v in range(n):
        out[p[v]] = sorted(p[w] for w in nbr[v])
        outcol[p[v]] = col[v]
    return out, outcol, p


@pytest.mark.parametrize("seed", range(150))
def test_refine_equals_naive_and_is_canonical(seed):
    rng = random.Random(seed)
    n = rng.randint(2, 40)
    if seed % 3 == 0:
        nbr = random_regular_multigraph_free(n + (n % 2) + 2, 3, rng)
        n = len(nbr)
    else:
        nbr = random_graph(n, rng)
    col = [rng.randrange(1, 4) for _ in range(n)] if seed % 2 else [0] * n
    roots = tuple(rng.sample(range(n), rng.choice((0, 1, 2)))) if n >= 2 else ()
    c = wl_refine(nbr, col, roots)
    assert partition(c) == naive_1wl(nbr, col, roots)
    # stable start: refining a stable coloring further with roots gives the same
    # partition as running everything together
    c0 = wl_refine(nbr, col)
    c1 = wl_refine(nbr, c0, roots, True)
    assert partition(c1) == partition(c)
    # names are canonical: relabelling the graph relabels the names
    nbr2, col2, p = shuffled_copy(nbr, col, rng)
    roots2 = tuple(p[r] for r in roots)
    c2 = wl_refine(nbr2, col2, roots2)
    assert all(c2[p[v]] == c[v] for v in range(n))
    c3 = wl_refine(nbr2, wl_refine(nbr2, col2), roots2, True)
    assert all(c3[p[v]] == c1[v] for v in range(n))
