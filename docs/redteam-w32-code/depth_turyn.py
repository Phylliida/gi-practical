"""Exact 1-WL depth on Turyn iterates and on products the memo did not test.
Lower bound k=2: exhaustive over pairs through vertex 0 when n <= 625 (vertex transitivity: Aut(W)
>= Aut(V)xAut(V)), else |Aut| > n^2 from the explicit lower bound 2|Aut V|^2 (V self-complementary,
see report).  Upper bound: an exact-refinement witness."""
import sys, random, time
sys.path.insert(0, '.')
from rt_common import *
from depth_families_lib import *

def search(A, k, trials, seed=3):
    """random k-subsets containing vertex 0; returns (#discrete, #trials, witness)"""
    rng = random.Random(seed); n = len(A); disc = 0; wit = None
    for _ in range(trials):
        S = [0] + rng.sample(range(1, n), k - 1)
        if is_discrete(A, S):
            disc += 1
            wit = wit or S
    return disc, trials, wit

def report(name, V1, V2, autlb=None, ktrials=60):
    W = turyn(V1, V2); n = len(W)
    A = adj_of_C(W)
    ok = check_conf_matrix(W) if n <= 2000 else None
    if n <= 700:
        order, orb, _ = aut_info(A)
        disc2 = sum(1 for v in range(1, n) if is_discrete(A, (0, v)))
        k2 = f'k=2 exhaustive through 0: {disc2}/{n-1} discrete'
    else:
        order = None
        disc2 = None; k2 = f'k=2 not enumerated (n large); |Aut| lower bound {autlb}, n^2={n**2}'
    t = time.time()
    res = []
    for k in (3, 4):
        d, tr, w = search(A, k, ktrials if k == 3 else max(12, ktrials // 5))
        res.append((k, d, tr, w))
        if d: break
    print(f'{name}: n={n}, conf(n<=2000)={ok}, |Aut|={order}, {k2}, sampled: {res} [{time.time()-t:.0f}s]', flush=True)

def main():
    what = sys.argv[1]
    P5 = seidel(paley_adj(5)); P9 = seidel(paley_adj(9)); P13 = seidel(paley_adj(13))
    skew3 = paley_tournament_V(3); skew7 = paley_tournament_V(7); skew11 = paley_tournament_V(11)
    if what == 'small':
        W2s = turyn(skew3, skew3); W2s2 = turyn(W2s, W2s)
        W1P5 = turyn(P5, P5); W1P9 = turyn(P9, P9)
        report('W(skew3,skew3)', skew3, skew3)
        report('W2(skew3)', W2s, W2s)
        report('W(P5,P5)', P5, P5)
        report('W2(P5)', W1P5, W1P5)
        report('W(P9,P9)', P9, P9)
        report('W(P13,P13)', P13, P13)
        report('W(skew7,skew7)', skew7, skew7)
        report('W(skew11,skew11)', skew11, skew11)
        P25 = seidel(paley_adj(25))
        report('W(P25,P25)', P25, P25)
    if what == 'big':
        W2s = turyn(skew3, skew3); W2s2 = turyn(W2s, W2s)
        report('W3(skew3) n=6561', W2s2, W2s2, autlb=2*10368**2)
        W1P9 = turyn(P9, P9)
        report('W2(P9) n=6561', W1P9, W1P9, autlb=2*10368**2)
    if what == 'exotic':
        # products the memo did not test
        P81 = seidel(paley_adj(81))
        pe81 = seidel(peisert(81))
        L9 = seidel(lines_graph(9, [0, 1, 2, 3, 4]))
        report('W(P81,P81) n=6561', P81, P81, autlb=2*12960**2)
        report('W(Peisert81,Peisert81) n=6561', pe81, pe81, autlb=2*38880**2)
        report('W(P81,Peisert81) n=6561', P81, pe81)
        report('W(lines9,lines9) n=6561', L9, L9, autlb=2*10368**2)
        report('W(W(P9,P9),Peisert81) n=6561', turyn(P9, P9), pe81)
main()
