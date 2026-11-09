#!/usr/bin/env python3
# check_lemmas.py: numeric checks of the exact identities in docs/w32-conference.md.
# (1) T(a,b,v)=sum_x C(a,x)C(b,x)C(v,x): L2 identity sum_v T^2 = n(n-2)-1 (a!=b); T==2 mod 4 and the
#     mod-8 formula from the induced triangle; (2) GF(2) rank of A and A+I; (3) Turyn product formula
#     T^W = T1*T2 + R on generic triples, and its collision consequence.
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen

def seidel(A):
    n = len(A)
    return [[0 if i == j else (-1 if A[i][j] else 1) for j in range(n)] for i in range(n)]

def T(C, a, b, v):
    return sum(C[a][x]*C[b][x]*C[v][x] for x in range(len(C)))

def rank2(M):
    rows = [int(''.join(map(str, r)), 2) for r in M]; r = 0
    n = len(M)
    for col in reversed(range(n)):
        piv = None
        for i in range(r, n):
            if rows[i] >> col & 1: piv = i; break
        if piv is None: continue
        rows[r], rows[piv] = rows[piv], rows[r]
        for i in range(n):
            if i != r and rows[i] >> col & 1: rows[i] ^= rows[r]
        r += 1
    return r

def check_identities(A, name):
    C = seidel(A); n = len(A); bad = 0
    for a in range(n):
        for b in range(a+1, n):
            s2 = sum(T(C, a, b, v)**2 for v in range(n))
            if s2 != n*(n-2)-1: bad += 1
    triangle_bad = 0; mod4_bad = 0
    for a in range(n):
        for b in range(a+1, n):
            for v in range(b+1, n):
                t = T(C, a, b, v)
                s, u, w = C[a][b], C[a][v], C[b][v]
                pred = (6 - n + 2*(s+u+w) + (s*u+s*w+u*w)) % 8
                if t % 8 != pred: triangle_bad += 1
                if t % 4 != 2: mod4_bad += 1
    rA = rank2(A); rAI = rank2([[A[i][j] ^ (i == j) for j in range(n)] for i in range(n)])
    print(f"{name} n={n}: L2 violations={bad}, mod8 violations={triangle_bad}, mod4 violations={mod4_bad}, rank2(A)={rA}, rank2(A+I)={rAI}, (n-1)/2={(n-1)//2}", flush=True)

def turyn_formula_check(V1, V2, trials=4000, seed=5):
    v = len(V1); W = gen.turyn(V1, V2); rng = random.Random(seed); bad = 0; tested = 0
    def Tw(a, b, x): return sum(W[a][y]*W[b][y]*W[x][y] for y in range(v*v))
    def Tv(Vm, a, b, x): return sum(Vm[a][y]*Vm[b][y]*Vm[x][y] for y in range(v))
    while tested < trials:
        a1, b1, x1 = rng.sample(range(v), 3); a2, b2, x2 = rng.sample(range(v), 3)
        s, t, u = V1[a1][b1], V1[a1][x1], V1[b1][x1]; s2, t2, u2 = V2[a2][b2], V2[a2][x2], V2[b2][x2]
        # R for symmetric V1, V2 (see doc)
        R = -(s*t + s*u + t*u) + (s2*t2 + s2*u2 + t2*u2) - (s*t2 + s*u2 + t*s2 + t*u2 + u*s2 + u*t2)
        a = a1*v+a2; b = b1*v+b2; x = x1*v+x2
        lhs = Tw(a, b, x); rhs = Tv(V1, a1, b1, x1)*Tv(V2, a2, b2, x2) + R
        if lhs != rhs: bad += 1
        tested += 1
    print(f"Turyn formula v={v}: {bad} mismatches of {tested}", flush=True)

def collision_lift_check(V, levels_pairs=200, seed=7):
    # p-tilde lift: pairs x=(x1,x2), y=(x1,y2) in W=T(V,V): compare collision frequency to the V-level collision+sign rate.
    v = len(V); W = gen.turyn(V, V); N = v*v; rng = random.Random(seed)
    def Tw(a, b, x): return sum(W[a][y]*W[b][y]*W[x][y] for y in range(N))
    def Tv(a, b, x): return sum(V[a][y]*V[b][y]*V[x][y] for y in range(v))
    res = []
    for _ in range(levels_pairs):
        x1 = rng.randrange(v); x2, y2 = rng.sample(range(v), 2)
        x = x1*v+x2; y = x1*v+y2
        total_w = 0; coll_w = 0; total_v = 0; coll_v = 0
        for _ in range(800):
            a1, b1 = rng.randrange(v), rng.randrange(v); a2, b2 = rng.randrange(v), rng.randrange(v)
            if len({a1, b1, x1}) < 3 or len({a2, b2, x2, y2}) < 4: continue
            a = a1*v+a2; b = b1*v+b2
            cw = Tw(a, b, x) == Tw(a, b, y); total_w += 1; coll_w += cw
            cv = (Tv(a2, b2, x2) == Tv(a2, b2, y2)) and V[a2][x2] == V[a2][y2] and V[b2][x2] == V[b2][y2]
            total_v += 1; coll_v += cv
            if cv and not cw:
                print("  LIFT VIOLATION", x, y, a, b)
        res.append(coll_w/max(total_w, 1) - coll_v/max(total_v, 1))
    print(f"lift (T-collision in W minus sign-matched V-collision) mean={sum(res)/len(res):.4f} min={min(res):.4f} (should be >= 0 up to sampling)", flush=True)

def main():
    root='/tmp/claude-1000/-home-bepis-math/117a2777-2472-4276-845a-e0dfeb712755/scratchpad/r4-sources/w32-spence-data'
    for q in [13, 17, 25, 29, 37, 49]:
        check_identities(gen.paley(q), f"paley{q}")
    for n in [25, 29, 41, 45, 49]:
        p, nv = gen.spence_files(root)[n]
        graphs = list(gen.parse_spence(p, nv))
        for g in graphs[:3]:
            check_identities(g, f"spence{n}")
    for q in [5, 9, 13]:
        V = gen.seidel_of_adj(gen.paley(q))
        A = gen.adj_of_seidel(gen.turyn(V, V))
        check_identities(A, f"turyn{q}")
    V5 = gen.seidel_of_adj(gen.paley(5)); turyn_formula_check(V5, V5, 200)
    V9 = gen.seidel_of_adj(gen.paley(9)); turyn_formula_check(V9, V9, 300)
    V13 = gen.seidel_of_adj(gen.paley(13)); turyn_formula_check(V13, V13, 500)
    collision_lift_check(V9, 60)
    collision_lift_check(V13, 30)

if __name__ == '__main__':
    main()
