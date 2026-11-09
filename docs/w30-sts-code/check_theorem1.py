"""Check of Lemma 1 (closure-rank duality) and Theorem 1 (PG fibration above a maximizer of
Psi_lambda(T) = log2(|T|+1) - lambda*rho(T)) on small STS. Everything exhaustive up to rho <= RMAX over seed
subsets, so the 'maximizer' is exact only for systems where every subsystem has rho <= RMAX; the script says when."""
import itertools, math, random, sys, time
import sts

LOG2 = math.log2


def all_closures(Q, rmax):
    """Map frozenset-of-subsystem -> minimal generating size found (rho, exact if rho < rmax, else upper bound)."""
    n = len(Q)
    found = {frozenset(): 0}
    for r in range(1, rmax + 1):
        for T in itertools.combinations(range(n), r):
            mask = sts.closure(Q, T)
            fs = frozenset(i for i in range(n) if mask[i])
            if fs not in found:
                found[fs] = r
    return found


def exact_rank_from(found, n):
    return found.get(frozenset(range(n)))


def check_lemma1(Q, found):
    n = len(Q)
    r = exact_rank_from(found, n)
    if r is None:
        return None
    best = min(rho + math.floor(LOG2((n + 1) / (len(T) + 1))) for T, rho in found.items())
    return r, best


def theorem1_check(Q, lam=1.05, rmax=4, verbose=False):
    n = len(Q)
    found = all_closures(Q, rmax)
    X = frozenset(range(n))
    if X not in found:
        return "rank>rmax"
    # maximizer of Psi_lambda
    S = max(found.items(), key=lambda kv: (LOG2(len(kv[0]) + 1) - lam * kv[1], len(kv[0])))
    Sset = S[0]
    s = len(Sset)
    if len(Sset) == n:
        return "S=X (no structure asserted)"
    # cosets
    outside = [x for x in range(n) if x not in Sset]
    cosets = {}
    coset_of = {}
    for x in outside:
        if x in coset_of:
            continue
        T = sts.closure(Q, list(Sset) + [x])
        members = [v for v in outside if T[v]]
        for v in members:
            assert v not in coset_of, "coset partition fails"
            coset_of[v] = len(cosets)
        cosets[len(cosets)] = members
    sizes = sorted({len(c) for c in cosets.values()})
    assert len(sizes) == 1 and sizes[0] >= s + 1, ("cosets", sizes, s)
    a = sizes[0]
    # coset products: x in C1, y in C2 land in a third coset determined by (C1, C2)
    p = len(cosets)
    third = {}
    for i in range(p):
        for j in range(i + 1, p):
            ts = set()
            for x in cosets[i]:
                for y in cosets[j]:
                    t = Q[x][y]
                    assert t not in Sset, "product into S"
                    ts.add(coset_of[t])
            assert len(ts) == 1, ("not single third coset", i, j, ts)
            third[(i, j)] = ts.pop()
    # P is an STS and every triangle generates a Fano (PG)
    P = [[-1] * p for _ in range(p)]
    for i in range(p):
        P[i][i] = i
    for (i, j), t in third.items():
        assert t != i and t != j
        P[i][j] = P[j][i] = t
    assert sts.is_sts(P), "quotient not STS"
    d = LOG2(p + 1)
    assert d == int(d), ("p+1 not a power of 2", p)
    for i, j, k in itertools.combinations(range(p), 3):
        if P[i][j] != k:
            assert sts.closure_size(P, [i, j, k]) == 7, "quotient triangle not Fano"
    return f"S size {s} rho {S[1]}: {p} cosets of size {a}, quotient PG({int(d)-1},2), a==s+1: {a==s+1}"


def make_all():
    rng = random.Random(30)
    F1 = None
    while True:
        F1 = sts.patterned_factorization_k8(rng)
        nf, sp, T = sts.f1_acceptable(F1, 3)
        if nf and sp:
            break
    fam = []
    fam.append(("PG(2,2)", sts.pg(3)))
    fam.append(("PG(3,2)", sts.pg(4)))
    fam.append(("PG(4,2)", sts.pg(5)))
    fam.append(("AG(2,3)", sts.ag3(2)))
    fam.append(("AG(3,3)", sts.ag3(3)))
    # central extensions by F_2 (k=1): n = 2^(d+1)-1, random line cochain g
    for d in [3, 4]:
        g = sts.random_g(d, 1, rng)
        fam.append((f"X_g k=1 d={d}", sts.x_fib(d, 1, lambda c: 0, {1: [(0, 1)]}, g)))
    # X_chi k=3 d=2 (n=31)
    fam.append(("X_chi d=2 chi=1000", sts.x_fib(2, 3, lambda c: 1 if c == 1 else 0, F1)))
    fam.append(("X_chi d=2 chi=111", sts.x_fib(2, 3, lambda c: 1, F1)))
    # doubling of PG(3,2) by random 1-factorization
    fam.append(("double(PG(3,2))", sts.doubling(sts.pg(4), rng)))
    # random STS
    fam.append(("hillclimb STS(15)", sts.random_sts_hillclimb(15, rng)))
    fam.append(("hillclimb STS(19)", sts.random_sts_hillclimb(19, rng)))
    fam.append(("hillclimb STS(31)", sts.random_sts_hillclimb(31, rng)))
    return fam


if __name__ == "__main__":
    fam = make_all()
    t0 = time.time()
    print("name, n, 2-char dim, exact rank (rmax 4), lemma-1 min, Theorem-1 result (lambda=1.05)")
    for name, Q in fam:
        n = len(Q)
        rmax = 4
        found = all_closures(Q, rmax) if n <= 31 else None
        rk = "-"
        l1 = "-"
        if found is not None:
            res = check_lemma1(Q, found)
            if res is not None:
                rk, l1 = res
        try:
            t1 = theorem1_check(Q, 1.05, rmax=rmax if n <= 31 else 3)
        except AssertionError as e:
            t1 = f"THEOREM CHECK FAILED: {e}"
        print(name, n, sts.char_space_dim(Q), "rk", rk, "L1", l1, "|", t1, f"({time.time()-t0:.1f}s)", flush=True)
