"""Exact check of w32 Lemmas 2.1, 2.2, 2.4 and Prop 2.5 on every graph of Spence's lists and on Paley,
Turyn samples.  T(a,b,v) = sum_x C(a,x)C(b,x)C(v,x), C = J - I - 2A."""
import sys, itertools, time
sys.path.insert(0, '.')
from rt_common import *

def check(A, name, full_triples=True):
    n = len(A); C = seidel(A).astype(np.int64)
    if not is_conference_graph(A): raise SystemExit(name + ' not conference')
    # Lemma 2.1
    TT = np.einsum('ax,bx,vx->abv', C, C, C)
    s = (TT.astype(np.int64) ** 2).sum(axis=2)
    off = ~np.eye(n, dtype=bool)
    e21 = int(np.any(s[off] != n * (n - 2) - 1)) + int(np.any(TT.sum(axis=2)[off] != 0))
    # Lemma 2.2 on all distinct triples, including the degenerate-excluded case
    a, b, v = np.meshgrid(np.arange(n), np.arange(n), np.arange(n), indexing='ij')
    dist = (a != b) & (a != v) & (b != v)
    t = TT[dist]; ss = C[a[dist], b[dist]]; tt = C[a[dist], v[dist]]; uu = C[b[dist], v[dist]]
    pred = (6 - n + 2 * (ss + tt + uu) + ss * tt + ss * uu + tt * uu) % 8
    e22a = int(np.any((t - pred) % 8)); e22b = int(np.any(t % 4 != 2)); e22c = int(np.any(t == 0))
    # Lemma 2.4 on all pairs
    M = TT  # M_v = TT[:,:,v]
    bad24 = 0
    for x in range(n):
        for y in range(x + 1, n):
            d = (TT[:, :, x] - TT[:, :, y]).astype(np.int64)
            if int((d ** 2).sum()) != 2 * n * n * (n - 2): bad24 += 1
    # Prop 2.5
    r = rank2(A); rI = rank2(A ^ np.eye(n, dtype=np.uint8))
    want = ((n - 1) // 2, (n + 1) // 2) if n % 8 == 1 else (n - 1, n)
    e25 = 0 if (r, rI) == want else 1
    return (e21, e22a, e22b, e22c, bad24, e25), int(np.abs(t).max())

def main():
    t0 = time.time()
    totals = {}
    def run(name, Gs):
        err = np.zeros(6, dtype=int); m = 0
        for A in Gs:
            e, mt = check(A, name); err += np.array(e); m = max(m, mt)
        print(f'{name}: {len(Gs)} graphs; violations [L2.1, mod8, mod4, T=0, L2.4, rank] = {err.tolist()}; max|T| over distinct triples = {m} [{time.time()-t0:.0f}s]', flush=True)
    which = sys.argv[1]
    if which == 'spence':
        for n, f in [(25, '25-12-5-6'), (29, '29-14-6-7'), (37, '37-18-8-9.bz2'), (41, 'conf2graph.42'), (45, 'conf2graph.46'), (49, 'conf2graph.50')]:
            run(f'list {f}', parse_rows(SPENCE + '/' + f, n))
    if which == 'families':
        run('Paley q<=125', [paley_adj(q) for q in range(5, 126, 4) if factor_pp(q)])
        P9 = seidel(paley_adj(9)); W = turyn(P9, P9)
        run('W(P9,P9)', [adj_of_C(W)])
        run('W(P5,P5)', [adj_of_C(turyn(seidel(paley_adj(5)), seidel(paley_adj(5))))])
main()
