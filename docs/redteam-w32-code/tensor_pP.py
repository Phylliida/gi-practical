"""Exact p, P at n=625, 6561; shared code in tensor_lib.py."""
import sys, time
sys.path.insert(0, '.')
from rt_common import *
from tensor_lib import *

def main():
    name = sys.argv[1]; S = int(sys.argv[2]); K = int(sys.argv[3])
    t0 = time.time()
    base = {'P9L2': (seidel(paley_adj(9)), 1), 'skew3L3': (paley_tournament_V(3), 2),
            'P5L2': (seidel(paley_adj(5)), 1), 'P9L1': (seidel(paley_adj(9)), 0),
            'skew3L2': (paley_tournament_V(3), 1)}[name]
    V0, levels = base
    its = turyn_iterates(V0, levels)
    V = its[-1] if levels else V0
    v = len(V); n = v * v
    W = turyn(V, V)
    print(f'{name}: n={n}, v={v}; building done [{time.time()-t0:.0f}s]', flush=True)
    # exact conference check at n=6561 via matvec on random vectors (Freivalds) plus row sums
    rng = np.random.default_rng(1)
    good = True
    for _ in range(4):
        z = rng.integers(-3, 4, size=n).astype(np.float64)
        Wz = matvec(V.astype(np.float64), v, z).reshape(n)
        Wz2 = matvec(V.astype(np.float64), v, Wz).reshape(n)
        if not np.allclose(Wz2, n * z - z.sum()): good = False
    print('Freivalds C^2 = nI - J (4 random vectors):', good, '; row sums zero:', bool(np.all(W.astype(np.int64).sum(axis=1) == 0)), flush=True)
    eq, coll, tot = stage1(W, V, v, S, 7)
    est = eq / np.maximum(tot, 1); estP = coll / np.maximum(tot, 1)
    order = np.argsort(-est)
    print(f'stage1 S={S} [{time.time()-t0:.0f}s]; max pc-est {est.max():.4f}, mean pc-est {est[1:].mean():.4f}; max P-est {estP.max():.4f}', flush=True)
    # histogram of pc-est
    for thr in (0.05, 0.1, 0.15, 0.2, 0.25, 0.3):
        print(f'  #y with pc-est >= {thr}: {int((est >= thr).sum())} (of {n-1})')
    def digits(y, b, m):
        d = []
        for _ in range(m):
            d.append(y % b); y //= b
        return d
    import math
    for b, m in ((3, int(round(math.log(n, 3)))) if abs(round(math.log(n,3))-math.log(n,3))<1e-9 else (0,0),
                 (9, int(round(math.log(n, 9)))) if abs(round(math.log(n,9))-math.log(n,9))<1e-9 else (0,0),
                 (5, int(round(math.log(n, 5)))) if abs(round(math.log(n,5))-math.log(n,5))<1e-9 else (0,0),
                 (25, int(round(math.log(n, 25)))) if abs(round(math.log(n,25))-math.log(n,25))<1e-9 else (0,0),
                 (81, 2) if n == 6561 else (0,0)):
        if b == 0: continue
        # mean estimate by Hamming weight of y in base b
        bins = {}
        for y in range(1, n):
            h = sum(1 for d in digits(y, b, m) if d)
            bins.setdefault(h, []).append(est[y])
        s = ', '.join(f'wt{h}: n={len(a)} mean {np.mean(a):.4f} max {np.max(a):.4f}' for h, a in sorted(bins.items()))
        print(f'  coords base {b}^{m}: {s}', flush=True)
    res = []
    for y in order[:K]:
        y = int(y)
        pn, cn, eqn, totn = exact_pair(W, V, v, 0, y)
        res.append((pn, cn, eqn, totn, y))
        print(f'  exact pair (0,{y}): p = {pn}/{n*n} = {pn/n/n:.5f}; pc = {eqn}/{totn} = {eqn/totn:.5f}; P = {cn}/{n*n} = {cn/n/n:.5f}; pc-est was {est[y]:.4f} [{time.time()-t0:.0f}s]', flush=True)
    print('max exact over top-K: p', max(r[0] for r in res)/n/n, 'pc', max(r[2]/r[3] for r in res), 'P', max(r[1] for r in res)/n/n)
    if name == 'P9L2':
        pn, cn, eqn, totn = exact_pair(W, V, v, 0, 1)
        print(f'lift pair (0,1) in W_2(P9): P = {cn}/{n*n} = {cn/n/n:.5f} (Thm 4.2 target >= P_V*prod)', flush=True)
main()
