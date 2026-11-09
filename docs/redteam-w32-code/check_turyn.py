"""Exact checks of w32 Lemma 4.1 / Thm 4.2.

Lemma 4.1 is checked on *all* generic triples for v in {5,9,13} (and two inequivalent order-25
factors on a random sample), with V1 != V2 allowed.  Collision statistics are computed exactly.
Definitions (w32 sec 3.1 / 4.2):
  p(x,y) = fraction of (a,b) in V^2 that do NOT test (x,y); (a,b) tests (x,y) iff a != b,
           a,b not in {x,y}, T(a,b,x) != T(a,b,y).          [no sign condition]
  P(x,y) = fraction of (a,b) in V^2 giving a collision: a,b,x,y distinct, T(a,b,x)=T(a,b,y),
           V(a,x)=V(a,y), V(b,x)=V(b,y).                      [sign condition]
"""
import sys, itertools, time
sys.path.insert(0, '.')
from rt_common import *

def T_tensor(C):
    C = C.astype(np.int64); n = len(C)
    return np.einsum('ax,bx,vx->abv', C, C, C) if n <= 100 else None

def lemma41_exhaustive(V1, V2, trials=None, seed=1):
    """all generic triples, or `trials` random ones"""
    v = len(V1); W = turyn(V1, V2).astype(np.int64)
    V1i = V1.astype(np.int64); V2i = V2.astype(np.int64)
    Tv1 = None if v > 100 else T_tensor(V1i); Tv2 = None if v > 100 else T_tensor(V2i)
    def tv(M, a, b, x, Tt):
        return Tt[a, b, x] if Tt is not None else int((M[a] * M[b] * M[x]).sum())
    if trials is None:
        trip = list(itertools.permutations(range(v), 3))
        it = ((t1, t2) for t1 in trip for t2 in trip)
    else:
        import random
        rng = random.Random(seed)
        it = ((tuple(rng.sample(range(v), 3)), tuple(rng.sample(range(v), 3))) for _ in range(trials))
    bad = 0; cnt = 0
    for (a1, b1, x1), (a2, b2, x2) in it:
        cnt += 1
        s, t, u = V1i[a1, b1], V1i[a1, x1], V1i[b1, x1]; sp, tp, up = V2i[a2, b2], V2i[a2, x2], V2i[b2, x2]
        R = -(s*t+s*u+t*u) + (sp*tp+sp*up+tp*up) - (s*tp+s*up+t*sp+t*up+u*sp+u*tp)
        a, b, x = a1*v+a2, b1*v+b2, x1*v+x2
        lhs = int((W[a]*W[b]*W[x]).sum())
        rhs = tv(V1i, a1, b1, x1, Tv1) * tv(V2i, a2, b2, x2, Tv2) + R
        if lhs != rhs: bad += 1
    return cnt, bad

def exact_pP(C):
    """exact p and P for every unordered pair; returns dict (x,y)->(p,P) with integer numerators and n^2 denominators"""
    C = C.astype(np.int64); n = len(C)
    # T[a,b,v] tensor
    TT = np.einsum('ax,bx,vx->abv', C, C, C)
    res = {}
    for x in range(n):
        for y in range(x + 1, n):
            D = (TT[:, :, x] - TT[:, :, y])
            allowed = np.ones((n, n), dtype=bool)
            allowed[x, :] = allowed[y, :] = False; allowed[:, x] = allowed[:, y] = False
            np.fill_diagonal(allowed, False)
            tests = allowed & (D != 0)
            sa = C[:, x] == C[:, y]
            coll = allowed & (D == 0) & sa[:, None] & sa[None, :]
            res[(x, y)] = (int(n*n - tests.sum()), int(coll.sum()))
    return n, res

def main():
    t0 = time.time()
    P5 = seidel(paley_adj(5)); P9 = seidel(paley_adj(9)); P13 = seidel(paley_adj(13))
    print('Lemma 4.1 exhaustive:')
    for name, V1, V2 in [('P5xP5', P5, P5), ('P9xP9', P9, P9), ('P13xP13', P13, P13)]:
        print(' ', name, 'triples, mismatches =', lemma41_exhaustive(V1, V2), f'[{time.time()-t0:.0f}s]', flush=True)
    sp = parse_rows(SPENCE + '/25-12-5-6', 25)
    print('  inequivalent order-25 factors (Spence #0, #1), random 200000 generic triples: ',
          lemma41_exhaustive(seidel(sp[0]), seidel(sp[1]), trials=200000), flush=True)
    # conference-ness at every level
    print('Conference-ness (exact C^2 = nI-J etc):')
    skew3 = paley_tournament_V(3)
    fams = {'skew3': (skew3, 3), 'P5': (P5, 2), 'P9': (P9, 2), 'P13': (P13, 1), 'skew7': (paley_tournament_V(7), 1), 'skew11': (paley_tournament_V(11), 1)}
    for name, (V, L) in fams.items():
        for i, W in enumerate(turyn_iterates(V, L)):
            n = len(W)
            ok = check_conf_matrix(W) if n <= 2000 else None
            print(f'  {name} level {i+1}: n={n}, conference-type: {ok}', flush=True)
    # P(9): exact collision numbers
    for name, C in [('P(5)', P5), ('P(9)', P9), ('P(13)', P13), ('W(skew3,skew3)', turyn(skew3, skew3))]:
        n, res = exact_pP(C)
        best = max(res.items(), key=lambda kv: kv[1][1])
        maxp = max(v[0] for v in res.values()); maxP = max(v[1] for v in res.values())
        print(f'{name}: n={n}, exact max p = {maxp}/{n*n} = {maxp/n/n:.5f}; exact max P = {maxP}/{n*n} = {maxP/n/n:.5f}; argmax P pair {best[0]}', flush=True)
    # constants
    for v, PV in [(9, 6/81)]:
        import math
        prod = 1.0; L = 0; vv = v
        for i in range(40):
            prod *= (1-1/vv)*(1-2/vv); vv *= vv
            if vv > 1e300: break
        print(f'Constant: v={v}, P_V={PV:.5f}, inf product={prod:.6f}, c = {PV*prod:.6f}')
    # n = 81 exact: every pair
    W81 = turyn(P9, P9)
    print('W(P9,P9): C^2 ok =', check_conf_matrix(W81), f'[{time.time()-t0:.0f}s]', flush=True)
    n, res = exact_pP(W81)
    maxp = max(v[0] for v in res.values()); maxP = max(v[1] for v in res.values())
    print(f'n=81 (W(P9,P9)): exact max p = {maxp}/{n*n} = {maxp/n/n:.5f}, exact max P = {maxP}/{n*n} = {maxP/n/n:.5f}', flush=True)
    # Thm 4.2 at level 0->1 exactly on all (x1,x2),(x1,y2) pairs and the mirror pairs
    n9, res9 = exact_pP(P9)
    bad = 0; tot = 0; minratio = 9.9
    for x1 in range(9):
        for x2 in range(9):
            for y2 in range(x2+1, 9):
                x, y = x1*9+x2, x1*9+y2
                Pw = res[(x, y)][1]/81**2
                Pv = res9[(x2, y2)][1]/81
                bound = (1-1/9)*(1-2/9)*Pv
                tot += 1
                if Pw + 1e-12 < bound: bad += 1
                if Pv > 0: minratio = min(minratio, Pw/Pv)
    print(f'Thm 4.2 level 0->1, all {tot} pairs (x1,x2),(x1,y2): violations {bad}; min P_W/P_V = {minratio:.4f}; bound (8/9)(7/9) = {(8/9)*(7/9):.4f}', flush=True)
    # mirror pairs (x1,x2),(y1,x2)
    bad = 0; tot = 0; minratio = 9.9
    for x2 in range(9):
        for x1 in range(9):
            for y1 in range(x1+1, 9):
                x, y = x1*9+x2, y1*9+x2
                Pw = res[(x, y)][1]/81**2
                Pv = res9[(x1, y1)][1]/81
                tot += 1
                if Pw + 1e-12 < (1-1/9)*(1-2/9)*Pv: bad += 1
                if Pv > 0: minratio = min(minratio, Pw/Pv)
    print(f'Thm 4.2 mirror pairs (x1,x2),(y1,x2), {tot}: violations {bad}; min P_W/P_V = {minratio:.4f}', flush=True)
main()
