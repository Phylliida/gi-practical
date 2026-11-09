"""E3: folded n-cube, H = 2^(n-1):S_n. Largest subgroups E of H fixing a cycle z with |z| odd (r(z)=1): 
m_H = min orbit size of odd F_2-cycles = |H| / max |E|. n=5 exact via subgroup climb."""
import itertools, sys, time
from gainlib import *
import random
n = int(sys.argv[1]) if len(sys.argv) > 1 else 5
full = (1 << n) - 1
canon = lambda x: min(x, x ^ full)
verts = sorted({canon(x) for x in range(1 << n)})
vid = {v: i for i, v in enumerate(verts)}
edges = sorted({tuple(sorted((vid[canon(v)], vid[canon(v ^ (1 << i))]))) for v in verts for i in range(n)})
eid = {e: i for i, e in enumerate(edges)}
print("b", len(verts), "edges", len(edges))


def apply_perm_translate(sigma, t, x):
    """vertex map x -> sigma(x) ^ t; x a bitmask in the canonical range"""
    y = 0
    for i in range(n):
        if x >> i & 1: y |= 1 << sigma[i]
    return canon(y ^ t)


def edge_perm(sigma, t):
    out = [None] * len(edges)
    for (a, c), i in eid.items():
        A = apply_perm_translate(sigma, t, verts[a]); C = apply_perm_translate(sigma, t, verts[c])
        e = tuple(sorted((vid[A], vid[C])))
        out[i] = eid[e]
    return tuple(out)


# group elements as edge permutations (faithful for n>=3)
print("building group...", flush=True)
gens = [edge_perm(tuple(range(1, n)) + (0,), 0), edge_perm((1, 0) + tuple(range(2, n)), 0), edge_perm(tuple(range(n)), 1)]
elts = {tuple(range(len(edges)))}
frontier = list(elts)
while frontier:
    nf = []
    for g in frontier:
        for s in gens:
            h = tuple(s[g[i]] for i in range(len(edges)))
            if h not in elts:
                elts.add(h); nf.append(h)
    frontier = nf
print("|H| =", len(elts), flush=True)
elts = list(elts)

# constraints: z in F_2^edges: boundary =0 at each vertex; g z = z
bd = []
for v in range(len(verts)):
    m = 0
    for e, i in eid.items():
        if v in e: m |= 1 << i
    bd.append(m)
ALL1 = (1 << len(edges)) - 1


def odd_fixed_exists(gens_E):
    """exists z with boundary 0, g z = z for g in gens_E, sum z = 1 mod 2? Row reduce constraints; check whether the functional sum is in the span of constraints."""
    cons = list(bd)
    for g in gens_E:
        for i in range(len(edges)):
            j = g[i]
            if j != i:
                cons.append((1 << i) | (1 << j))
    sp = F2Span()
    for c in cons: sp.add(c)
    # is ALL1 in span of constraints?  (constraints form the row space; functional in row space => forced 0)
    v = ALL1
    for _ in range(len(edges) + 1):
        if v == 0: break
        h = v.bit_length() - 1
        if h in sp.b: v ^= sp.b[h]
        else: return True
    return v != 0


def closure(gset):
    gl = list(gset)
    S = {tuple(range(len(edges)))}
    fr = list(S)
    while fr:
        nfr = []
        for a in fr:
            for g in gl:
                b = tuple(g[a[i]] for i in range(len(edges)))
                if b not in S:
                    S.add(b); nfr.append(b)
        fr = nfr
    return frozenset(S)



def good(gs): return odd_fixed_exists(gs)

import random
rng = random.Random(1)
idn = tuple(range(len(edges)))
elts_noid = [g for g in elts if g != idn]
seen = set()
best = 1; bestE = frozenset([idn]); bestgens = []
stack = [([], frozenset([idn]))]
seen.add(frozenset([idn]))
t0 = time.time()
cap = float(sys.argv[2]) if len(sys.argv) > 2 else 300
visited = 0
while stack and time.time() - t0 < cap:
    gens_E, E = stack.pop()
    visited += 1
    if len(E) > best:
        best = len(E); bestE = E; bestgens = gens_E
        print("best order", best, "gens", len(gens_E), f"t={time.time()-t0:.0f}", flush=True)
    candidates = elts_noid[:]
    rng.shuffle(candidates)
    tried = set()
    for g in candidates:
        if g in E or g in tried: continue
        F = closure(gens_E + [g])
        tried |= set(x for x in F if x not in E)  # all elements of F\E give subgroups contained in F containing E; heuristic pruning
        if F in seen: continue
        seen.add(F)
        if good(gens_E + [g]):
            stack.append((gens_E + [g], F))
print(f"n={n}: max subgroup fixing an odd cycle found: order {best}; |H|={len(elts)}; m_H<={len(elts)//best}; good subgroups visited {visited}; t={time.time()-t0:.0f}s stack_left={len(stack)}")
