#!/usr/bin/env python3
"""Standalone check of the claim about Neuen 2020, Thm 4.17(G).  See docs/verify-neu417.md.

Implements Step 1 of the proof of Thm 4.17 (Omega', P', X', W'; arXiv v2, lines 1974-2003) and the
d-virtual size (line 1572) exactly as defined.  X[A] is a *set* of restricted strings (line 1040).
Step 2 (Renormalize, Thm 4.9) is not simulated: in the instances below every orbit A of
Gamma''_B on P'[B] is a singleton, so (IV) and surjectivity of f' give |f'^{-1}(P')| = 1, and (III), (V), (VII)
make X*, W* relabelled copies of X', W'.

Blocks are sorted tuples of points; a string on a block is a tuple of values in that order.
"""
import random


def restrict(X, A):
    out = set()
    for P, x in X:
        kept = [(a, v) for a, v in zip(P, x) if a in A]
        if kept:
            out.add((tuple(a for a, _ in kept), tuple(v for _, v in kept)))
    return out


def mult(X):
    m = {}
    for P, _ in X:
        m[P] = m.get(P, 0) + 1
    return m


def vs(X, f):
    return sum(len(P) * c ** (f + 1) for P, c in mult(X).items())


def shat(X, U, f):
    """The potential s-hat(X,U) = sum_P |P minus U| m_X(P)^(f+1).  It equals the virtual size of the
    outside part counted with the multiplicities of the whole instance."""
    return sum(sum(1 for a in P if a not in U) * c ** (f + 1) for P, c in mult(X).items())


def step1(X, W):
    Xp, Wp = set(), set()
    for P, x in X:
        z = tuple((a, v) for a, v in zip(P, x) if a in W)
        Pp = tuple(sorted((a, z) for a in P))
        vals = dict(zip(P, x))
        Xp.add((Pp, tuple(vals[a] for a, _ in Pp)))
        Wp |= {(a, z) for a in P if a in W}
    return Xp, Wp


def report(name, X, Omega, W, fs=(0, 1, 5)):
    Xp, Wp = step1(X, W)
    Omegap = {pt for P, _ in Xp for pt in P}
    simple = all(c <= 1 for c in mult(restrict(Xp, Wp)).values())
    occupied = {a for P, _ in X for a in P} == Omega
    print(f"{name}: completely occupied={occupied}, X[W] simple={all(c <= 1 for c in mult(restrict(X, W)).values())}, "
          f"X'[W'] simple={simple}")
    for f in fs:
        out, outp = vs(restrict(X, Omega - W), f), vs(restrict(Xp, Omegap - Wp), f)
        print(f"  f={f}: (F) {vs(Xp, f)} <= {vs(X, f)} | (G) virtual size outside W: {out} -> {outp}"
              f"{'  VIOLATED' if outp > out else ''} | s-hat: {shat(X, W, f)} -> {shat(Xp, Wp, f)}")
        assert vs(Xp, f) <= vs(X, f)
        assert shat(Xp, Wp, f) <= shat(X, W, f)
        assert shat(Xp, Wp, f) == outp  # X'[W'] simple, so s-hat is the outside virtual size


def trivial_witness(X, Omega):
    """Literal witness for (E), (F), (G) of the theorem as stated: Gamma* := Aut_Gamma(X_r), Omega* := Omega,
    W* := Omega, X* := one constant string per block, same partition sequence.  (A)-(D) hold by Observation obs:sequence-of-partitions and
    the definition of Iso; see docs/verify-neu417.md."""
    Xs = {(P, (0,) * len(P)) for P in {P for P, _ in X}}
    for f in (0, 1, 5):
        assert all(c == 1 for c in mult(restrict(Xs, Omega)).values())  # (E)
        assert vs(Xs, f) <= vs(X, f)  # (F)
        assert vs(restrict(Xs, set()), f) == 0  # (G): the outside part is empty
    return True


def inst(*pairs):
    return {(tuple(P), tuple(x)) for P, x in pairs}


# 1. The red-team instance.  Gamma = 1, sequence {Omega} > P > singletons.
X1 = inst(("ab", (0, 0)), ("ab", (1, 0)), ("cd", (0, 0)))
report("Instance 1 (Gamma=1)", X1, set("abcd"), set("ac"))
assert trivial_witness(X1, set("abcd"))

# 2. The same mechanism at Line 'simplify' of Algorithm LocalCertificates (Thm 4.24).
#    Gamma = Sym(T) on T + {u} + {v}, |T| = k = t = 9, d = 10: t > max(8, 2+log2 d); phi = identity.
#    P = {T + {u}, {v}}, sequence {Omega} > P > singletons (|T + {u}| = 10 <= d).  W' = Aff(Gamma, id) = T,
#    since u, v are fixed.  The two strings are constant on T, so Lambda' = Sym(T) and the loop continues.
#    Sym(T) fixes both constant strings, so the copies of the block are not permuted: orbits are singletons.
T = tuple(range(9))
P1 = tuple(sorted(T + (100,)))     # 100 = u
X2 = {(P1, tuple(0 if a == 100 else b for a in P1)) for b in (0, 1)} | {((200,), (0,))}  # 200 = v
report("Instance 2 (Gamma=Sym(9), d=10, Line simplify)", X2, set(T) | {100, 200}, set(T))

# 3. Random instances with Gamma = 1: (G) fails often, s-hat never increases.
rnd = random.Random(417)
fail = 0
total = 0
for _ in range(2000):
    Omega, X, W = set(), set(), set()
    for b in range(rnd.randint(1, 3)):
        P = tuple(sorted((b, j) for j in range(rnd.randint(2, 4))))
        Omega |= set(P)
        W |= {p for p in P if rnd.random() < 0.5}
        for _ in range(rnd.randint(1, 4)):
            X.add((P, tuple(rnd.randint(0, 1) for _ in P)))
    Xp, Wp = step1(X, W)
    Omegap = {pt for P, _ in Xp for pt in P}
    if all(c <= 1 for c in mult(restrict(X, W)).values()):
        continue
    total += 1
    for f in (0, 1, 3):
        assert shat(Xp, Wp, f) <= shat(X, W, f)
        assert vs(Xp, f) <= vs(X, f)
    if vs(restrict(Xp, Omegap - Wp), 1) > vs(restrict(X, Omega - W), 1):
        fail += 1
print(f"Random, Gamma=1, X[W] not simple: (G) for the construction fails on {fail}/{total}; (F) and s-hat hold on all.")
