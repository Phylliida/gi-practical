"""w27: height-2 two-top posets (A_m<k) + (A_m<k): SI under G1 x G2, G_i = S_b wr_{[b]^m} S_b^m.
Point = (a_1..a_m, c, a'_1..a'_m, c') in [b]^{2m+2}. Poset element indices:
a_i = 0..m-1, k = m, a'_i = m+1..2m, k' = 2m+1."""
import itertools, os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'w8-poset-code'))
from w8lib import *  # noqa
import pynauty


def ht2_pred(m):
    rel = [(i, m) for i in range(m)] + [(m + 1 + i, 2 * m + 1) for i in range(m)]
    return closure(2 * m + 2, rel)


def points(b, m):
    return list(itertools.product(range(b), repeat=2 * m + 2))


def pbs_graph(b, pred, colour):
    """poset block structure graph: points + one class vertex per class of each F_{D[i]}."""
    h = len(pred)
    pts = list(itertools.product(range(b), repeat=h))
    vid = {('P', z): k for k, z in enumerate(pts)}
    adj = {}
    for i in range(h):
        Di = sorted(pred[i] | {i})
        for z in pts:
            key = ('C', i, tuple(z[j] for j in Di))
            if key not in vid:
                vid[key] = len(vid)
            a, c = vid[('P', z)], vid[key]
            adj.setdefault(a, set()).add(c); adj.setdefault(c, set()).add(a)
    cols = sorted(set(colour.values()), key=repr)
    cells = [set() for _ in cols] + [set() for _ in range(h)]
    ci = {c: k for k, c in enumerate(cols)}
    for key, v in vid.items():
        if key[0] == 'P':
            cells[ci[colour[key[1]]]].add(v)
        else:
            cells[len(cols) + key[1]].add(v)
    return pynauty.Graph(len(vid), adjacency_dict={a: list(s) for a, s in adj.items()},
                         vertex_coloring=cells), cols


def nauty_cert_and_order(b, pred, colour, all_cols):
    h = len(pred)
    pts = list(itertools.product(range(b), repeat=h))
    vid = {('P', z): k for k, z in enumerate(pts)}
    adj = {}
    for i in range(h):
        Di = sorted(pred[i] | {i})
        for z in pts:
            key = ('C', i, tuple(z[j] for j in Di))
            if key not in vid:
                vid[key] = len(vid)
            a, c = vid[('P', z)], vid[key]
            adj.setdefault(a, set()).add(c); adj.setdefault(c, set()).add(a)
    cells = [set() for _ in all_cols] + [set() for _ in range(h)]
    ci = {c: k for k, c in enumerate(all_cols)}
    for key, v in vid.items():
        if key[0] == 'P':
            cells[ci[colour[key[1]]]].add(v)
        else:
            cells[len(all_cols) + key[1]].add(v)
    g = pynauty.Graph(len(vid), adjacency_dict={a: list(s) for a, s in adj.items()},
                      vertex_coloring=[c for c in cells if c])
    grp = pynauty.autgrp(g)
    order = grp[1] * 10 ** grp[2]
    return pynauty.certificate(g), order, tuple(len(c) for c in cells)


def apply_g(x, g):
    """y(g(z)) = x(z)"""
    return {g[z]: x[z] for z in x}


def theorem_G(b, m, x, y, vstar=None):
    """Theorem G: x has a pinning row block; reduce to SI under G1 x T2.
    Returns (iso?, |Aut(x)| as computed with y=x, or None when y is not x)."""
    h = 2 * m + 2
    Vs = list(itertools.product(range(b), repeat=m))
    # pinning row block v0: first one pinning every column block in x
    def phis(s, v, sigma):
        out = {}
        for vp in Vs:
            for c in range(b):
                out[(vp, c)] = tuple(s[(*v, sigma[i], *vp, c)] for i in range(b))
        return out

    def is_pinning(ph):
        return all(len({ph[(vp, c)] for c in range(b)}) == b for vp in Vs)

    idp = tuple(range(b))
    v0 = None
    for v in Vs:
        if is_pinning(phis(x, v, idp)):
            v0 = v
            break
    if v0 is None:
        return 'NO_PIN', None
    px = phis(x, v0, idp)

    pred2 = closure(2 * m + 1, [(i, m) for i in range(m)])

    def tagged(s, base, sigma):
        ph = phis(s, base, sigma)
        if not is_pinning(ph):
            return None
        d = {}
        for a in Vs:
            for c in range(b):
                r = (*a, c)
                tag = -1
                if a == base:
                    tag = sigma.index(c)
                for vp in Vs:
                    vals = sorted((ph[(vp, cp)], s[(*a, c, *vp, cp)]) for cp in range(b))
                    d[(*a, c, *vp)] = (tag, tuple(vals))
        return d

    xt = tagged(x, v0, idp)
    ps = PosetSI(b, pred2)
    keymap = {}
    def enc(d):
        return tuple(keymap.setdefault(d[z], len(keymap)) for z in sorted(d, key=ps.index))

    xs = enc(xt)
    ps_a = ps.solve(xs, xs)
    Aut0 = ps_a[0]
    valid = 0
    iso = False
    for w0 in Vs:
        for sigma in itertools.permutations(range(b)):
            yt = tagged(y, w0, sigma)
            if yt is None:
                continue
            ys = enc(yt)
            r = ps.solve(xs, ys)
            if r[1] is not None:
                valid += 1
                iso = True
    return iso, Aut0.order() * valid if iso else None
