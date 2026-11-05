"""w8 E4: the parameter mu(P) (optimal over linear extensions) on random 2-dimensional posets
P_{id,rho} and on named families; compared with width, height, nu."""
import random, sys, statistics, time
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from w8lib import *

rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)


def lis(seq):
    import bisect
    t = []
    for v in seq:
        k = bisect.bisect_left(t, v)
        if k == len(t): t.append(v)
        else: t[k] = v
    return len(t)


def width_height_2dim(rho):
    pos = [0] * len(rho)
    for k, c in enumerate(rho): pos[c] = k
    seq = [pos[i] for i in range(len(rho))]      # j<i iff j<i and pos[j]<pos[i]
    return lis([-v for v in seq]), lis(seq)       # width = longest decreasing, height = longest increasing


print("random 2-dim posets P_{id,rho}: mu(P) distribution")
for h in [6, 8, 10, 12, 14, 16, 18]:
    mus, ws, hs, nus, mus_id = [], [], [], [], []
    t0 = time.time()
    samples = 200 if h <= 14 else 60
    for _ in range(samples):
        rho = list(range(h)); rng.shuffle(rho)
        pred = poset_2dim(list(range(h)), rho)
        mu, lam = best_order(pred)
        mus.append(mu); nus.append(nu_of(pred))
        mus_id.append(mu_of_order(pred, list(range(h))))
        w, ht = width_height_2dim(rho); ws.append(w); hs.append(ht)
    def dist(v):
        c = {}
        for a in v: c[a] = c.get(a, 0) + 1
        return dict(sorted(c.items()))
    print(f"h={h:2d} n={samples}: mu {dist(mus)} | mu(sigma-order) mean {statistics.mean(mus_id):.2f} | "
          f"nu mean {statistics.mean(nus):.2f} | width mean {statistics.mean(ws):.2f} | "
          f"height mean {statistics.mean(hs):.2f} | {time.time()-t0:.1f}s", flush=True)

print("\nnamed families")
fam = []
for m in [2, 3, 4, 6]:
    fam.append((f"C_{m}+C_{m}", poset_chains([m, m])))
    fam.append((f"C_{m}+C_1", poset_chains([m, 1])))
    fam.append((f"C_{m}+antichain_{m}", poset_chains([m] + [1] * m)))
    # (A_m < k) + (A_m < k)
    rel = [(a, m) for a in range(m)] + [(m + 1 + a, 2 * m + 1) for a in range(m)]
    fam.append((f"(A_{m}<k)+(A_{m}<k)", closure(2 * m + 2, rel)))
    # weak order: levels of size m, 2 levels
    rel = [(a, m + c) for a in range(m) for c in range(m)]
    fam.append((f"A_{m} < A_{m} (weak order)", closure(2 * m, rel)))
    # tree poset: root < two chains of length m
    rel = [(0, 1), (0, m + 1)] + [(k, k + 1) for k in range(1, m)] + [(k, k + 1) for k in range(m + 1, 2 * m)]
    fam.append((f"root<(C_{m}+C_{m})", closure(2 * m + 1, rel)))
    # crown / standard example S_m: a_i < b_j for i != j
    rel = [(i, m + j) for i in range(m) for j in range(m) if i != j]
    fam.append((f"standard example S_{m}", closure(2 * m, rel)))
for name, pred in fam:
    mu, lam = best_order(pred)
    print(f"{name:28s} h={len(pred):2d} mu={mu} nu={nu_of(pred)}")
