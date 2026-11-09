"""E5: code-level check of Theorem B': generators S_F = disjoint union over I in F of S^I (n directions per coordinate), code
C = {c in F_2^{S_F}: for every j the direction marginal mu_j(c) lies in {0, 1^n}}, C_0 = {c: mu_j(c)=0 for all j}.
Checks: rank(rectangles + cross elements) == dim C_0, dim C - dim C_0 == rank of indicator vectors of F, for odd n and various F."""
import itertools, sys
from gainlib import F2Span
for n, M, F in [(3, 2, [(0, 1)]), (5, 2, [(0, 1)]), (5, 3, [(0, 1), (1, 2)]), (5, 3, [(0, 1, 2)]), (7, 3, [(0, 1), (1, 2)]),
                (5, 3, [(0,), (1,), (2,)]), (5, 2, [(0,), (1,), (0, 1)]), (5, 3, [(0, 1), (1, 2), (0, 2)]), (5, 4, [(0, 1, 2), (1, 2, 3)])]:
    S_F = []  # generators: (I index, tuple of directions per coordinate in I)
    for Ii, I in enumerate(F):
        for dirs in itertools.product(range(n), repeat=len(I)):
            S_F.append((Ii, dict(zip(I, dirs))))
    m = len(S_F)
    # marginal: map bit vector to mu_j
    def marg(cbits):
        out = {}
        for pos in range(m):
            if cbits >> pos & 1:
                Ii, d = S_F[pos]
                for j, a in d.items():
                    out[j] = out.get(j, 0) ^ (1 << a)
        return out
    # constraints for C_0: each mu_j coordinate = 0 (M*n linear functionals)
    rows0 = []
    for j in range(M):
        for a in range(n):
            f = 0
            for pos, (Ii, d) in enumerate(S_F):
                if d.get(j) == a: f |= 1 << pos
            rows0.append(f)
    sp0 = F2Span(); [sp0.add(r) for r in rows0]
    dimC0 = m - sp0.rank
    # C: mu_j in {0,1^n}: constraints mu_j(a)+mu_j(0)=0 for a=1..n-1 and all j
    rows = []
    for j in range(M):
        base = 0
        for pos, (Ii, d) in enumerate(S_F):
            if d.get(j) == 0: base |= 1 << pos
        for a in range(1, n):
            f = 0
            for pos, (Ii, d) in enumerate(S_F):
                if d.get(j) == a: f |= 1 << pos
            rows.append(f ^ base)
    sp = F2Span(); [sp.add(r) for r in rows]
    dimC = m - sp.rank
    # indicator rank of F
    ind = F2Span()
    for I in F:
        v = 0
        for j in I: v |= 1 << j
        ind.add(v)
    # rectangles and cross elements as vectors; index map
    index = {}
    for pos, (Ii, d) in enumerate(S_F):
        index[(Ii, tuple(sorted(d.items())))] = pos
    def bitof(Ii, d): return 1 << index[(Ii, tuple(sorted(d.items())))]
    sp2 = F2Span()
    # rectangles: within pattern I, coordinates j<l, directions a!=a', c!=c', base
    for Ii, I in enumerate(F):
        for j, l in itertools.combinations(I, 2):
            rest = [x for x in I if x not in (j, l)]
            for rdirs in itertools.product(range(n), repeat=len(rest)):
                base = dict(zip(rest, rdirs))
                for a, a2 in itertools.combinations(range(n), 2):
                    for c, c2 in itertools.combinations(range(n), 2):
                        v = 0
                        for (x, y) in [(a, c), (a2, c), (a, c2), (a2, c2)]:
                            d = dict(base); d[j] = x; d[l] = y
                            v ^= bitof(Ii, d)
                        sp2.add(v)
    # cross elements: patterns I1 != I2 sharing j: 4 generators s,t,s*,t* as described
    for Ii, I1 in enumerate(F):
        for Ik, I2 in enumerate(F):
            if Ik <= Ii: continue
            for j in set(I1) & set(I2):
                rest1 = [x for x in I1 if x != j]; rest2 = [x for x in I2 if x != j]
                for r1 in itertools.product(range(n), repeat=len(rest1)):
                    for r2 in itertools.product(range(n), repeat=len(rest2)):
                        d1 = dict(zip(rest1, r1)); d2 = dict(zip(rest2, r2))
                        for a, a2 in itertools.combinations(range(n), 2):
                            v = 0
                            dd = dict(d1); dd[j] = a; v ^= bitof(Ii, dd)
                            dd = dict(d1); dd[j] = a2; v ^= bitof(Ii, dd)
                            dd = dict(d2); dd[j] = a; v ^= bitof(Ik, dd)
                            dd = dict(d2); dd[j] = a2; v ^= bitof(Ik, dd)
                            sp2.add(v)
    print(f"n={n} M={M} F={F}: |S_F|={m} dim C={dimC} dim C_0={dimC0} rank(rect+cross)={sp2.rank} dim C-dim C_0={dimC-dimC0} rank(D)={ind.rank}", flush=True)
