"""Toy check of the single-object local-certificate bookkeeping of docs/w8-hypercanon.md.

Checks, by brute force on hypergraphs over 6 points:
  * Lemma E2/E3: a two-stage canonizer whose second stage runs on an auxiliary
    domain built with ARBITRARY choices (a pseudo-random relabelling) is an
    H0-equivariant coset map (ECM), provided the choices are a function of the
    canonical prefix only (stand-in for Simplify + Renormalize at a prefix).
  * Two mutants in which the auxiliary choices depend on non-canonical data
    (the untransported object; the transported object for a "first" pi) must
    fail.  They model running renormalization on non-canonical data.
  * Lemma T^set (a), (b), (c) for the colours c(Z, T) built from the ECM.
  * Lemma E1: Aut_{H0}(Z) <= pi R pi^{-1}.

Run:  nice python3 -I docs/redteam-w8-hypercanon-check.py
"""
import itertools
import random
import sys
import zlib

N = 6
T0 = (0, 1)
W = frozenset(T0)            # window: an H0-invariant set
OMEGA = range(N)


def compose(g, h):           # right action: x^(gh) = (x^g)^h
    return tuple(h[g[i]] for i in range(len(g)))


def inverse(g):
    inv = [0] * len(g)
    for i, gi in enumerate(g):
        inv[gi] = i
    return tuple(inv)


def act(Z, g):
    return frozenset(frozenset(g[v] for v in E) for E in Z)


def key(Z):
    return tuple(sorted(tuple(sorted(E)) for E in Z))


SN = list(itertools.permutations(range(N)))
H0 = [g for g in SN if set(g[i] for i in T0) == set(T0)]   # setwise stabiliser of T0


def window(Z):
    return frozenset(E & W for E in Z if E & W)


def stage1(Z):
    """canonical placement coset of the window part under H0"""
    best, C = None, []
    for g in H0:
        k = key(window(act(Z, g)))
        if best is None or k < best:
            best, C = k, [g]
        elif k == best:
            C.append(g)
    return best, C


def relabel(seed):
    rng = random.Random(seed)
    p = list(range(2 * N))
    rng.shuffle(p)
    return tuple(p)


def lift(Z, rho):
    """injective, equivariant map to an auxiliary domain (copies of W)"""
    out = set()
    for E in Z:
        L = {rho[2 * v] for v in E} | {rho[2 * v + 1] for v in E & W}
        out.add(frozenset(L))
    return frozenset(out)


def stage2(Zp, R1, rho):
    """canonical placement coset of the lifted object under iota(R1), pulled back"""
    rho_inv = inverse(rho)
    best, C = None, []
    for r in R1:
        # iota(r) = rho^{-1} (r x id) rho on the auxiliary domain
        rr = tuple(rho[2 * r[rho_inv[j] // 2] + rho_inv[j] % 2] for j in range(2 * N))
        k = key(act(lift(Zp, rho), rr))
        if best is None or k < best:
            best, C = k, [r]
        elif k == best:
            C.append(r)
    return frozenset(C)


def canon(Z, mode="prefix"):
    F, C1 = stage1(Z)
    pi = C1[0]
    R1 = [compose(inverse(pi), c) for c in C1]          # right group of stage 1
    if mode == "prefix":
        seed = zlib.crc32(repr(F).encode())             # choices = function of the prefix
    elif mode == "raw":
        seed = zlib.crc32(repr(key(Z)).encode())        # choices see the untransported object
    elif mode == "first_pi":
        seed = zlib.crc32(repr(key(act(Z, pi))).encode())  # choices see Z^pi for the first pi
    else:
        raise ValueError(mode)
    rho = relabel(seed)
    out = set()
    for p in C1:                                        # every pi in C1 gives the same set (E2)
        Zp = act(Z, p)
        part = frozenset(compose(p, c) for c in stage2(Zp, [compose(inverse(p), c) for c in C1], rho))
        out.add(part)
    return out


def random_hypergraph(rng):
    m = rng.randint(3, 5)
    Z = set()
    while len(Z) < m:
        Z.add(frozenset(rng.sample(range(N), rng.choice((2, 3)))))
    return frozenset(Z)


def check_ecm(mode, trials, rng):
    bad_pi = bad_eq = bad_coset = 0
    for _ in range(trials):
        Z = random_hypergraph(rng)
        parts = canon(Z, mode)
        if len(parts) != 1:
            bad_pi += 1
            continue
        C = next(iter(parts))
        c0 = next(iter(C))
        R = {compose(inverse(c0), c) for c in C}
        if not all(compose(a, b) in R for a in R for b in R):
            bad_coset += 1
        for g in rng.sample(H0, 12):
            parts_g = canon(act(Z, g), mode)
            Cg = next(iter(parts_g))
            if Cg != frozenset(compose(inverse(g), c) for c in C):
                bad_eq += 1
                break
    return bad_pi, bad_coset, bad_eq


def C_of(Z):
    return next(iter(canon(Z, "prefix")))


def colour(Z, T, sigma_choice, rng):
    """c(Z, T-vector) of Lemma T^set; sigma chosen by the given rule"""
    Tset = set(T)
    sigmas = [s for s in SN if set(s[i] for i in Tset) == set(T0)]
    sigma = sigmas[0] if sigma_choice == "first" else rng.choice(sigmas)
    Zs = act(Z, sigma)
    C = C_of(Zs)
    c0 = next(iter(C))
    R = frozenset(compose(inverse(c0), c) for c in C)
    E = [compose(sigma, c) for c in C]
    e = rng.choice(E)
    Tvec = tuple(e[x] for x in T)                       # ordering of T0
    orbit = min(tuple(r[x] for x in Tvec) for r in R)   # psi(R)-orbit, by least member
    return (tuple(sorted(R)), orbit), R


def main():
    rng = random.Random(20261105)
    ok = True
    for mode, expect_fail in (("prefix", False), ("raw", True), ("first_pi", True)):
        bp, bc, be = check_ecm(mode, 60, rng)
        fail = (bp + bc + be) > 0
        print(f"ECM mode={mode:9s}: pi-dependence {bp:3d}, not-a-coset {bc:3d}, equivariance failures {be:3d}"
              f"  -> {'FAILS' if fail else 'passes'} (expected {'fail' if expect_fail else 'pass'})")
        ok &= (fail == expect_fail)

    # Lemma T^set
    a_bad = b_bad = c_bad = e1_bad = 0
    nonfull = full = 0
    for _ in range(25):
        Z = random_hypergraph(rng)
        # E1 on the reference object
        C = C_of(Z)
        pi = next(iter(C))
        R = {compose(inverse(pi), c) for c in C}
        aut = [g for g in H0 if act(Z, g) == Z]
        conj = {compose(compose(pi, r), inverse(pi)) for r in R}
        if not set(aut) <= conj:
            e1_bad += 1
        for T in itertools.combinations(range(N), 2):
            cols = {}
            for Tvec in (T, T[::-1]):
                c1, Rm = colour(Z, Tvec, "first", rng)
                c2, _ = colour(Z, Tvec, "random", rng)
                if c1 != c2:
                    a_bad += 1
                cols[Tvec] = c1
                h = rng.choice(SN)
                ch, _ = colour(act(Z, h), tuple(h[x] for x in Tvec), "random", rng)
                if ch != c1:
                    b_bad += 1
            if cols[T] == cols[T[::-1]]:
                full += 1
                psiR = {tuple(r[x] for x in T0) for r in Rm}
                if len(psiR) != 2:
                    c_bad += 1
            else:
                nonfull += 1
    print(f"T^set: (a) failures {a_bad}, (b) failures {b_bad}, (c) failures {c_bad}; "
          f"E1 failures {e1_bad}; test sets with equal colours {full}, unequal {nonfull}")
    ok &= (a_bad + b_bad + c_bad + e1_bad) == 0
    print("ALL CHECKS AS EXPECTED" if ok else "UNEXPECTED RESULT")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
