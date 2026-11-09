"""Exact P(x,y) on W_2(P9) (n=6561) for x=0 and y on the subcube {0,1}^4 (base-9 coordinates):
checks the report's Prop R1 and gives a concrete B_c clique."""
import sys, itertools
sys.path.insert(0, '.')
from rt_common import *
from tensor_lib import exact_pair

P9 = seidel(paley_adj(9))
V = turyn(P9, P9); v = len(V); n = v * v
W = turyn(V, V)
pi = 6 / 81
C0 = 1.0; vv = 9
for i in range(30):
    C0 *= (1 - 1 / vv) * (1 - 2 / vv); vv = vv * vv
    if vv > 1e300: break
digit = [729, 81, 9, 1]     # digits (d3,d2,d1,d0) with value d3*729 + d2*81 + d1*9 + d0
cube = []
for J in itertools.product([0, 1], repeat=4):
    y = sum(d * e for d, e in zip(J, digit))
    cube.append((y, J))
vals = {}
print(f'pi = {pi:.5f}, C0 = {C0:.5f}, n={n}')
for y, J in cube:
    if y == 0: continue
    pn, cn, eq, tot = exact_pair(W, V, v, 0, y)
    w = sum(J)
    bound = (pi * C0) ** w
    vals[J] = cn / n / n
    print(f'  J={J} weight {w}: exact P(0,{y}) = {cn}/{n*n} = {cn/n/n:.6f}; exact p = {pn/n/n:.6f}; bound (pi*C0)^w = {bound:.6f}; ok={cn/n/n >= bound}', flush=True)
minP = min(vals.values())
import math
print(f'min over nonzero subcube elements of exact P(0,y) = {minP:.6f}; c with n^(-c)=minP: {-math.log(minP)/math.log(n):.4f}')
print(f'Every pair inside the subcube {{0,1}}^4 differs on a set J; by translation-type symmetry (x->x+g coordinatewise is not assumed) see report.')

# exact P on all 120 pairs of the subcube Q = {0,1}^4 (base-9 digits, vertex = sum d_i 9^i), exact
Q = sorted(y for y, J in cube)
worst = (9.9, None)
res2 = {}
for x, y in itertools.combinations(Q, 2):
    pn, cn, eq, tot = exact_pair(W, V, v, x, y)
    res2[(x, y)] = cn / n / n
    if cn / n / n < worst[0]: worst = (cn / n / n, (x, y))
print(f'all {len(res2)} pairs inside Q (|Q|=16): min exact P = {worst[0]:.6f} at {worst[1]}; '
      f'so Q is a clique of B_c (via p >= P) for every c >= {-math.log(worst[0])/math.log(n):.4f}', flush=True)
vals_w = sorted(set(round(v3, 6) for v3 in res2.values()))
print('distinct exact P values on pairs of Q:', vals_w)
