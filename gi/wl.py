"""Canonical 1-dimensional Weisfeiler-Leman (color refinement) on neighbour
lists, by a worklist (Hopcroft / Paige-Tarjan): O(m log n) per run instead of
O(rounds * m) for round-by-round refinement.

refine(nbr, col, roots=(), stable=False) returns the stable coloring (the
coarsest equitable partition refining the initial one) as a list of int cell
names. Every decision of the run (the order of the initial cells, of the
splitters, of the split cells, of the parts of a split cell, and which part
keeps the old name) is a function of the sizes, the counts and the input colors
only, so the names are a function of the isomorphism type of (graph, colors,
roots, in order): if tau is an isomorphism (of the colored graphs, with
tau(roots) = roots'), then cid[v] == cid'[tau(v)].

The part of a split cell that keeps the old name is the largest one, and it
is not put on the worklist (Hopcroft's trick; the counts into it are the
difference between the counts into the old cell and those into the other parts).
"""
from collections import deque

from .kernel import ck as _ck

__all__ = ["refine"]


def refine(nbr, col, roots=(), stable=False):
    """Stable 1-WL coloring of the graph with neighbour lists nbr. col: the
    initial colors (ints, or anything sortable); roots: vertices (in order) to
    individualize first. stable: the initial coloring is known to be equitable,
    so only the individualized cells start on the worklist."""
    if _ck is not None:
        r = _ck.wl_refine(nbr, col, roots, stable)
        if r is not None:
            return r
    n = len(nbr)
    members = {}
    for v in range(n):
        members.setdefault(col[v], []).append(v)
    cids = sorted(members)
    cells = [set(members[c]) for c in cids]
    index = {c: i for i, c in enumerate(cids)}
    cid = [index[c] for c in col]
    queue = deque() if stable else deque(range(len(cells)))
    for r in roots:
        c = cid[r]
        if len(cells[c]) > 1:
            cells[c].remove(r)
            cid[r] = len(cells)
            cells.append({r})
            queue.append(cid[r])
    cnt = [0] * n
    while queue:
        C = queue.popleft()
        touched = []
        for v in cells[C]:
            for w in nbr[v]:
                if not cnt[w]:
                    touched.append(w)
                cnt[w] += 1
        byc = {}
        for w in touched:
            byc.setdefault(cid[w], []).append(w)
        for D in sorted(byc):
            tv = byc[D]
            size = len(cells[D])
            parts = {}
            for w in tv:
                parts.setdefault(cnt[w], []).append(w)
            if len(parts) == 1 and len(tv) == size:
                continue                # one part: nothing to split
            rest = size - len(tv)       # the untouched vertices (count 0)
            items = sorted(parts.items())
            big, bigsize = -1, rest     # the largest part; ties to the least count
            for i, (val, ws) in enumerate(items):
                if len(ws) > bigsize:
                    big, bigsize = i, len(ws)
            if big < 0:                 # the untouched part keeps the old name
                cD = cells[D]
                for w in tv:
                    cD.remove(w)
            else:                       # a touched part keeps it; rest is moved
                restset = cells[D].difference(tv) if rest else None
                cells[D] = set(items[big][1])
                if rest:
                    new = len(cells)
                    cells.append(restset)
                    for w in restset:
                        cid[w] = new
                    queue.append(new)
            for i, (val, ws) in enumerate(items):
                if i == big:
                    continue
                new = len(cells)
                cells.append(set(ws))
                for w in ws:
                    cid[w] = new
                queue.append(new)
        for w in touched:
            cnt[w] = 0
    return cid
