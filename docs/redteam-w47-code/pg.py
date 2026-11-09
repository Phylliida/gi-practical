"""PG(m-1,2): points are nonzero ints < 2^m, lines are frozensets {a,b,a^b}.
Written independently of docs/w47-code."""
import itertools

def all_lines(m):
    n = 1 << m
    seen = set()
    out = []
    for a in range(1, n):
        for b in range(a + 1, n):
            c = a ^ b
            if c > b:
                L = (a, b, c)
                if L not in seen:
                    seen.add(L)
                    out.append(L)
    return out

def classify(m, ell=(1, 2, 3)):
    """W = lines skew to ell, R = lines meeting ell in exactly one point."""
    ellset = set(ell)
    W, R = [], []
    for L in all_lines(m):
        k = len(ellset & set(L))
        if k == 0:
            W.append(L)
        elif k == 1:
            R.append(L)
    return W, R

def gl_stab_ell_gens(m):
    """Generators of GL(V)_ell, ell=<e1,e2> with e_i = 1<<(i-1), as images of basis vectors."""
    e = [1 << i for i in range(m)]
    gens = []
    # GL(ell): swap e1,e2; e1->e1+e2
    g = list(e); g[0], g[1] = e[1], e[0]; gens.append(g)
    g = list(e); g[0] = e[0] ^ e[1]; gens.append(g)
    # GL(U), U=<e3..em>: cycle, transvection
    g = list(e)
    g[2:] = e[3:] + [e[2]]
    gens.append(g)
    g = list(e); g[2] = e[2] ^ e[3]; gens.append(g)
    # Hom(U,ell): e3 -> e3+e1
    g = list(e); g[2] = e[2] ^ e[0]; gens.append(g)
    return gens

def act(g, x):
    """apply linear map given by images of basis vectors"""
    r = 0
    i = 0
    while x:
        if x & 1:
            r ^= g[i]
        x >>= 1
        i += 1
    return r

def gl_order(k):
    r = 1
    for i in range(k):
        r *= (1 << k) - (1 << i)
    return r
