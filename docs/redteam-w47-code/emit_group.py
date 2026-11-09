#!/usr/bin/env python3
"""Emit GAP code: GL(V)_ell acting on W, on R, and on the labels Gamma = points + lines.
Written independently of docs/w47-code. Usage: emit_group.py M > group_M.g"""
import sys
import pg

def perm_on(objs, g):
    idx = {o: i for i, o in enumerate(objs)}
    return [idx[tuple(sorted(pg.act(g, x) for x in o))] for o in objs]

def gapperm(p):
    return "PermList([" + ",".join(str(i + 1) for i in p) + "])"

m = int(sys.argv[1])
W, R = pg.classify(m)
gens = pg.gl_stab_ell_gens(m)
print(f"m:={m};;")
print("genW:=[" + ",\n".join(gapperm(perm_on(W, g)) for g in gens) + "];;")
print("genR:=[" + ",\n".join(gapperm(perm_on(R, g)) for g in gens) + "];;")
# which pairs of W-lines are 'generic': dim(ell + w1 + w2) = 6
def rank(vecs):
    basis = []
    for v in vecs:
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v)
    return len(basis)
print("Wlines:=[" + ",".join("[" + ",".join(str(x) for x in w) + "]" for w in W) + "];;")
