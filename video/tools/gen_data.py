#!/usr/bin/env python3
"""Generate the real data shown in the video. Run from the repo root:
    python3 video/tools/gen_data.py
Writes video/js/data.js (JSON assigned to window.DATA). Uses the repo's gi package
for permutation-group facts and plain Python elsewhere. Every structure drawn in the
video comes from here, so nothing is a hand-faked picture."""
import itertools, json, math, os, random, sys
from collections import Counter, defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, ROOT)
from gi.group import PermGroup, minimal_block
from gi.graph import graph_iso
from gi.refine import wl2, atomic_pairs

D = {}

# ------------------------------------------------------------------ helpers
def adj_matrix(n, edges):
    A = [[0]*n for _ in range(n)]
    for a, b in edges:
        A[a][b] = A[b][a] = 1
    return A

def aut_gens_and_order(A):
    n = len(A)
    res = graph_iso(A, A)
    assert res is not None
    sigma, gens = res
    return gens, PermGroup(n, gens).order()

def four_cycles(A):
    n = len(A); cnt = 0
    for a, b, c, d in itertools.permutations(range(n), 4):
        if a < b and a < c and a < d and b < d and A[a][b] and A[b][c] and A[c][d] and A[d][a]:
            cnt += 1
    return cnt

def cr_rounds(A):
    """Colour refinement, returning the colouring after every round."""
    n = len(A)
    col = [0]*n; rounds = [list(col)]
    while True:
        sig = [(col[v], tuple(sorted(col[u] for u in range(n) if A[v][u]))) for v in range(n)]
        names = {s: i for i, s in enumerate(sorted(set(sig)))}
        new = [names[s] for s in sig]
        rounds.append(new)
        if len(set(new)) == len(set(col)):
            break
        col = new
    return rounds

# ------------------------------------------------------------------ 1. Petersen and prism
subs = [frozenset(c) for c in itertools.combinations(range(1, 6), 2)]
ORD = [(1,2),(3,4),(5,1),(2,3),(4,5)]           # outer pentagon, consecutive disjoint
outer = [frozenset(p) for p in ORD]
inner = []
for i, S in enumerate(outer):
    nbrs = [T for T in subs if not (S & T)]
    ring = {outer[(i+1) % 5], outer[(i-1) % 5]}
    spoke = [T for T in nbrs if T not in ring][0]
    inner.append(spoke)
verts = outer + inner
pos = {S: i for i, S in enumerate(verts)}
P_edges = [(i, j) for i, j in itertools.combinations(range(10), 2) if not (verts[i] & verts[j])]
A_pet = adj_matrix(10, P_edges)
prism_edges = [(i, (i+1) % 5) for i in range(5)] + [(5+i, 5+(i+1) % 5) for i in range(5)] + [(i, 5+i) for i in range(5)]
A_pri = adj_matrix(10, prism_edges)
assert len(P_edges) == 15 and len(prism_edges) == 15
assert all(sum(r) == 3 for r in A_pet) and all(sum(r) == 3 for r in A_pri)
gens_p, ord_p = aut_gens_and_order(A_pet)
gens_pr, ord_pr = aut_gens_and_order(A_pri)
assert graph_iso(A_pet, A_pri) is None
c4p, c4pr = four_cycles(A_pet), four_cycles(A_pri)
# orbits of Aut(Petersen) on ordered pairs
def pair_orbits(n, gens):
    seen = {}
    orbs = []
    for a in range(n):
        for b in range(n):
            if (a, b) in seen: continue
            orb = [(a, b)]; seen[(a, b)] = len(orbs)
            for x, y in orb:
                for g in gens:
                    nx_, ny_ = g[x], g[y]
                    if (nx_, ny_) not in seen:
                        seen[(nx_, ny_)] = len(orbs); orb.append((nx_, ny_))
            orbs.append(orb)
    return orbs
porbs = pair_orbits(10, gens_p)
D['petersen'] = {
    'edges': P_edges, 'labels': [sorted(S) for S in verts], 'A': A_pet,
    'aut_gens': gens_p, 'aut_order': ord_p, 'c4': c4p,
    'pair_orbit_sizes': sorted(len(o) for o in porbs),
    'colours_cr': cr_rounds(A_pet),
}
D['prism'] = {'edges': prism_edges, 'A': A_pri, 'aut_order': ord_pr, 'c4': c4pr, 'colours_cr': cr_rounds(A_pri)}

# all 120 elements of Aut(Petersen) as vertex perms, check S5 structure + primitivity
G_pet = PermGroup(10, gens_p)
assert G_pet.order() == 120
elts = list(G_pet.elements())
D['petersen']['n_gens'] = len(gens_p)
# primitive: every pair generates all ten points as a block
blocks_pet = [minimal_block(10, gens_p, 0, b) for b in range(1, 10)]
assert all(len(set(b)) == 1 for b in blocks_pet)
D['petersen']['primitive'] = True

# ------------------------------------------------------------------ 2. Colour refinement example (a real asymmetric graph)
rng = random.Random(7)
def find_asym():
    for tries in range(100000):
        n = 8
        edges = [e for e in itertools.combinations(range(n), 2) if rng.random() < 0.3]
        if len(edges) < 8 or len(edges) > 10:
            continue
        A = adj_matrix(n, edges)
        # connected, CR discretizes in 3 or more rounds and several colour classes persist
        from collections import deque
        seen = {0}; q = deque([0])
        while q:
            v = q.popleft()
            for u in range(n):
                if A[v][u] and u not in seen:
                    seen.add(u); q.append(u)
        if len(seen) != n:
            continue
        rs = cr_rounds(A)
        if len(set(rs[-1])) == n and len(rs) >= 4:
            return edges, A, rs
    raise SystemExit('no asymmetric graph found')
edges, A, rs = find_asym()
D['cr_example'] = {'n': 8, 'edges': edges, 'rounds': rs,
                   'classes': [len(set(r)) for r in rs]}

# ------------------------------------------------------------------ 3. CFI over K4 (own builder, with a layout)
base_edges = list(itertools.combinations(range(4), 2))
def cfi_k4(twist_set):
    """Vertices: for each base vertex v the even subsets of its incident edges (m-nodes),
    for each endpoint (v,e) and bit b a node a(v,e,b). twist_set = set of base edge indices."""
    idx = {}; names = []
    def node(x):
        if x not in idx:
            idx[x] = len(names); names.append(x)
        return idx[x]
    E = []
    for v in range(4):
        inc = [e for e in base_edges if v in e]
        for bits in itertools.product((0, 1), repeat=3):
            if sum(bits) % 2 == 0:
                m = node(('m', v, bits))
                for e, b in zip(inc, bits):
                    E.append((m, node(('a', v, e, b))))
    for k, e in enumerate(base_edges):
        u, v = e
        t = 1 if k in twist_set else 0
        for b in (0, 1):
            E.append((node(('a', u, e, b)), node(('a', v, e, b ^ t))))
    return names, E
names0, E0 = cfi_k4(set())
names1, E1 = cfi_k4({0})
assert names0 == names1
n_cfi = len(names0)
A0 = adj_matrix(n_cfi, E0); A1 = adj_matrix(n_cfi, E1)
assert graph_iso(A0, A1) is None
# twisting two edges at a common vertex is still isomorphic to untwisted
_, E2 = cfi_k4({0, 1})  # edges 0=(0,1) and 1=(0,2) share vertex 0
A2 = adj_matrix(n_cfi, E2)
assert graph_iso(A0, A2) is not None
r0, r1 = cr_rounds(A0), cr_rounds(A1)
PX0, PX1 = atomic_pairs(A0), atomic_pairs(A1)
same_wl2 = wl2(PX0, PX1) is not None
D['cfi'] = {'n': n_cfi, 'names': names0, 'edges0': E0, 'edges1': E1,
            'cr_hist0': sorted(Counter(r0[-1]).values()), 'cr_hist1': sorted(Counter(r1[-1]).values()),
            'cr_same_final': Counter(r0[-1]) == Counter(r1[-1]) and sorted(r0[-1]) == sorted(r1[-1]),
            'wl2_identical': bool(same_wl2),
            'nonisomorphic': True, 'two_twists_isomorphic': True,
            'base_edges': base_edges, 'n_m': 16, 'n_a': 24}

# ------------------------------------------------------------------ 5. Hexagon, D6
n = 6
rot = tuple((i+1) % 6 for i in range(6)); refl = tuple((6-i) % 6 for i in range(6))
Hex = PermGroup(6, [rot, refl])
assert Hex.order() == 12
elts6 = [tuple(p) for p in Hex.elements()]
def blocks_of(n, gens):
    """All nontrivial block systems, from minimal_block's labelling of the points."""
    sys = set()
    for a in range(n):
        for b in range(a+1, n):
            lab = minimal_block(n, gens, a, b)
            classes = defaultdict(list)
            for pt in range(n):
                classes[lab[pt]].append(pt)
            parts = sorted(sorted(v) for v in classes.values())
            if len(parts) in (1, n):
                continue
            sys.add(tuple(tuple(p) for p in parts))
    return [[list(p) for p in s] for s in sys]
hex_sys = blocks_of(6, [rot, refl])
hex_sys.sort(key=lambda s: len(s[0]))
kernel_pairs = [p for p in elts6 if all(p[i] == i or p[i] == (i+3) % 6 for i in range(6))]
D['hexagon'] = {'order': 12, 'gens': [list(rot), list(refl)], 'elements': [list(p) for p in elts6],
                'systems': hex_sys, 'kernel_pairs_size': len(kernel_pairs),
                'kernel_pairs': [list(p) for p in kernel_pairs]}
# action on 3 antipodal blocks
quot = set()
for p in elts6:
    quot.add(tuple(p[i] % 3 for i in range(3)))
assert len(quot) == 6
D['hexagon']['quotient_order_on_pairs'] = len(quot)

# ------------------------------------------------------------------ 5b. Luks worked run on the hexagon with a real string
xs = "RRBRBB"; ys = "BRRBRB"
def perm_str(s, p):
    out = [None]*len(s)
    for i in range(len(s)):
        out[p[i]] = s[i]
    return ''.join(out)
iso = [p for p in elts6 if perm_str(xs, p) == ys]
aut = [p for p in elts6 if perm_str(xs, p) == xs]
D['luks_run'] = {'x': xs, 'y': ys, 'iso': [list(p) for p in iso], 'aut': [list(p) for p in aut],
                 'num_iso': len(iso)}

# ------------------------------------------------------------------ 7. The window procedure on a real string
# G = Alt(7) acting on labels {1..7}; positions are the 21 pairs; a 2-colouring; κ = 3 for the picture.
pts = list(range(7))
def sign(p):
    s = 1
    seen = set()
    for i in range(len(p)):
        if i in seen: continue
        j, l = i, 0
        while j not in seen:
            seen.add(j); j = p[j]; l += 1
        if l % 2 == 0: s = -s
    return s
A7 = [p for p in itertools.permutations(range(7)) if sign(p) == 1]
assert len(A7) == 2520
pairs = list(itertools.combinations(range(7), 2))
pid = {frozenset(p): i for i, p in enumerate(pairs)}
onpos = {g: tuple(pid[frozenset((g[a], g[b]))] for a, b in pairs) for g in A7}
def window_run(T, x):
    T = tuple(T)
    Tset = set(T)
    def phi(g): return tuple(g[t] for t in T)
    P_T = [g for g in A7 if set(g[t] for t in T) == Tset and sign([T.index(g[t]) for t in T]) == 1]
    AltT = set(phi(g) for g in P_T)
    assert len(AltT) == 3
    W = set(); A = list(P_T); log = []
    for step in range(25):
        im = set(phi(g) for g in A)
        if im != AltT:
            log.append({'kind': 'nonfull', 'window': sorted(W), 'A': len(A)})
            return log, 'nonfull'
        rest = [v for v in range(21) if v not in W]
        E = [v for v in rest if set(phi(g) for g in A if onpos[g][v] == v) != AltT]
        if E:
            V = E; kind = 'affected'
        else:
            K = [g for g in A if all(onpos[g][v] == v for v in rest)]
            if set(phi(g) for g in K) == AltT:
                log.append({'kind': 'full', 'window': sorted(W), 'A': len(A), 'K': len(K)})
                return log, 'full'
            orbs = []
            seen = set()
            for v in rest:
                if v in seen: continue
                orb = {onpos[g][v] for g in A}
                seen |= orb; orbs.append(orb)
            V = []
            for Dl in orbs:
                Kd = [g for g in A if all(onpos[g][v] == v for v in Dl)]
                if set(phi(g) for g in Kd) == {tuple(T)}:
                    V += list(Dl)
            kind = 'visible'
            if not V:
                log.append({'kind': 'stuck', 'window': sorted(W), 'A': len(A)})
                return log, 'stuck'
        A2 = [g for g in A if all(x[onpos[g][v]] == x[v] for v in V)]
        log.append({'kind': kind, 'added': sorted(V), 'window': sorted(W), 'A': len(A), 'after': len(A2)})
        A = A2; W |= set(V)
    return log, 'overflow'
best = None
rng2 = random.Random(11)
def rand_colouring():
    # structured: colour pairs by a coarse pattern on labels, then flip a little
    part = [rng2.randrange(3) for _ in range(7)]
    tbl = {}
    x = []
    for a, b in pairs:
        k = tuple(sorted((part[a], part[b])))
        if k not in tbl: tbl[k] = rng2.randrange(2)
        x.append(tbl[k])
    for _ in range(rng2.randrange(3)):
        i = rng2.randrange(21); x[i] ^= 1
    return x
tests = list(itertools.combinations(range(7), 3))
for trial in range(700):
    x = rand_colouring()
    if not (5 <= sum(x) <= 16): continue
    runs = {}
    bad = False
    for T in tests:
        log, out = window_run(T, x)
        runs[T] = (log, out)
        if out in ('stuck', 'overflow'):
            bad = True; break
    if bad: continue
    outs = Counter(r[1] for r in runs.values())
    if outs['full'] and outs['nonfull']:
        kinds = Counter(st['kind'] for r in runs.values() for st in r[0])
        depth = max(len(r[0]) for r in runs.values())
        score = (kinds['visible'] > 0, min(outs['full'], outs['nonfull']), depth)
        if best is None or score > best[0]:
            best = (score, x, runs)
assert best, 'no window example'
_, x_win, runs = best
D['window'] = {'q': 7, 'kappa': 3, 'pairs': [[a+1, b+1] for a, b in pairs], 'x': x_win,
               'runs': [{'T': [t+1 for t in T], 'log': r[0], 'outcome': r[1]} for T, r in runs.items()]}
print('window example string', x_win, 'outcomes', Counter(r[1] for r in runs.values()), 'score', best[0], file=sys.stderr)

# ------------------------------------------------------------------ 12. Hoffman--Singleton rectangle
idx = {}
def v(t, a, b):
    return idx.setdefault((t, a, b), len(idx))
HS_edges = set()
for a in range(5):
    for b in range(5):
        HS_edges.add(tuple(sorted((v('P', a, b), v('P', a, (b+1) % 5)))))
        HS_edges.add(tuple(sorted((v('Q', a, b), v('Q', a, (b+2) % 5)))))
for a in range(5):
    for b in range(5):
        for c in range(5):
            HS_edges.add(tuple(sorted((v('P', a, b), v('Q', c, (a*c+b) % 5)))))
HS_edges = sorted(HS_edges)
nHS = len(idx)
AHS = adj_matrix(nHS, HS_edges)
assert nHS == 50 and all(sum(r) == 7 for r in AHS)
# strongly regular (50,7,0,1)
for a in range(50):
    for b in range(a+1, 50):
        common = sum(1 for c in range(50) if AHS[a][c] and AHS[b][c])
        assert common == (0 if AHS[a][b] else 1)
v0 = 0
R = [u for u in range(50) if AHS[v0][u]]
W = [u for u in range(50) if u != v0 and not AHS[v0][u]]
assert len(R) == 7 and len(W) == 42
Rord = sorted(R); r_of = {u: Rord.index(next(x for x in Rord if AHS[u][x])) for u in W}
# each w has exactly one neighbour in R
for u in W:
    assert sum(AHS[u][x] for x in R) == 1
Word = sorted(W, key=lambda u: r_of[u])
matrix = [[AHS[u][x] for x in Rord] for u in Word]
twins = Counter(r_of[u] for u in W)
assert set(twins.values()) == {6}
rect_degrees_W = sorted(set(sum(row) for row in matrix))
rect_degrees_R = sorted(set(sum(matrix[i][j] for i in range(42)) for j in range(7)))
D['hs'] = {'n': 50, 'degree': 7, 'lambda': 0, 'mu': 1, 'W': 42, 'R': 7, 'matrix': matrix,
           'twin_size': 6, 'twin_classes': 7, 'deg_W': rect_degrees_W, 'deg_R': rect_degrees_R,
           'width_bound': max(42//2, 7, 50-42), 'wr_product': 42*7, 'bound_eta': 0.75*0.25*2500}

# ------------------------------------------------------------------ 20. tightness numbers
agl = []
for k in range(1, 11):
    N = 2**k
    o = N
    for i in range(k):
        o *= (N - 2**i)
    prod = 1.0
    for j in range(1, k+1):
        prod *= (1 - 2**(-j))
    agl.append({'k': k, 'N': N, 'order': o, 'bound': N**(k+1), 'ratio': o / N**(k+1), 'prod': prod,
                'log10order': math.log10(o), 'log2order': math.log2(o)})
D['agl'] = agl

# ------------------------------------------------------------------ 23. barrier family numbers
bar = []
for Dd in (3, 5, 9, 33):
    d = Dd - 1
    log2factD = math.lgamma(Dd+1)/math.log(2)
    for m in (4, 16, 256, 4096):
        expo = 1 + log2factD/(Dd-1) + (math.log2(m))/((Dd-1)*m)
        bar.append({'D': Dd, 'd': d, 'm': m, 'N_log2': d*m, 'exponent': expo,
                    'floor': math.log2(Dd) - 0.443})
D['barrier'] = bar

# ------------------------------------------------------------------ constants
kappa = 64; q0 = 4*kappa+2
a_min = math.lgamma(q0+1)/math.log(2)**2
gamma = 0.9; astar = a_min/gamma
A_enum = 3*(a_min + astar/math.log(2))
A_dom = (a_min/gamma)/(0.5*math.log(4/3))
D['constants'] = {'kappa': kappa, 'q0': q0, 'log_q0_fact': math.lgamma(q0+1), 'a_min': a_min, 'A_enum': A_enum, 'A_domain': A_dom,
                  'C_star': 128, 'A_times_C': A_enum*128, 'eta': 0.75, 'beta': 0.9, 'theta': 0.75,
                  'alpha': 0.4, 'gamma': 0.9, 'delta': 0.25, 'c_theta': 0.5*math.log(4/3), 'c_beta': math.log(10/9),
                  'H_series': 1/(1-0.9**2)}

out = os.path.join(ROOT, 'video', 'js', 'data.js')
with open(out, 'w') as f:
    f.write('window.DATA=' + json.dumps(D, separators=(',', ':')) + ';\n')
print('wrote', out, os.path.getsize(out), 'bytes', file=sys.stderr)
print(json.dumps({k: v for k, v in D['cfi'].items() if k not in ('names', 'edges0', 'edges1')}, indent=0)[:600], file=sys.stderr)
print(D['constants'], file=sys.stderr)
print('petersen orbits', D['petersen']['pair_orbit_sizes'], 'c4', c4p, c4pr, 'aut', ord_p, ord_pr, file=sys.stderr)
print('hs', D['hs']['deg_W'], D['hs']['deg_R'], 'cr classes', D['cr_example']['classes'], file=sys.stderr)
print('hex systems', D['hexagon']['systems'], 'luks', D['luks_run'], file=sys.stderr)
print(D['agl'][2], file=sys.stderr)
