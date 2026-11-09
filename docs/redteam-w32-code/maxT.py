"""Extreme triple correlations: max|T| on Spence graphs and the Lemma 4.1 lift to Turyn products."""
import sys, math, itertools
sys.path.insert(0, '.')
from rt_common import *

def T_exact(C, a, b, x):
    C = C.astype(np.int64)
    return int((C[a]*C[b]*C[x]).sum())

for n, f in [(25, '25-12-5-6'), (41, 'conf2graph.42'), (49, 'conf2graph.50')]:
    best = (0, None, None)
    for i, A in enumerate(parse_rows(SPENCE + '/' + f, n)):
        C = seidel(A).astype(np.int64)
        TT = np.einsum('ax,bx,vx->abv', C, C, C)
        a, b, v = np.meshgrid(np.arange(n), np.arange(n), np.arange(n), indexing='ij')
        mask = (a != b) & (a != v) & (b != v)
        m = np.abs(TT)[mask].max()
        if m > best[0]:
            idx = np.argwhere((np.abs(TT) == m) & mask)[0]
            best = (int(m), i, tuple(int(x) for x in idx))
    m, i, (a, b, v) = best
    A = parse_rows(SPENCE + '/' + f, n)[i]
    C = seidel(A)
    print(f'{f} n={n}: max|T| = {m} = n-{n-m} (graph #{i}, triple {(a,b,v)}, T={T_exact(C,a,b,v)}, signs s,t,u = {int(C[a,b])},{int(C[a,v])},{int(C[b,v])}); log_n|T| = {math.log(m)/math.log(n):.4f}', flush=True)
    # Lift through two Turyn levels using exact computation of T^W for W(V,V) with (a,a),(b,b),(v,v)
    W = turyn(C, C); N = n * n; i1, i2, i3 = (a*n+a, b*n+b, v*n+v)
    t2 = T_exact(W, i1, i2, i3)
    print(f'   W(V,V) n={N}: exact T at the lifted triple = {t2} (Lemma 4.1 predicts T^2 + R, R in [-12,12]), log_N|T| = {math.log(abs(t2))/math.log(N):.4f}', flush=True)
    t3 = m
    for L in range(1, 6):
        t3 = t3**2 - 12
        print(f'   recursion lower bound level {L}: n={n**(2**L)}, |T| >= {t3}, exponent {math.log(t3)/math.log(n**(2**L)):.4f}')
    if N == 625:
        print(f'   check T^W / N at n=625: {abs(t2)/N:.3f}')
