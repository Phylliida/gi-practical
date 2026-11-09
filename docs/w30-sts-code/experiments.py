"""w30-sts experiments: closure growth from random seeds, greedy rank upper bound, characters,
1-WL / 2-WL individualization depth, on explicit STS families and random (hill-climbing) STS.
Single process, intended under `nice`. Hashing in wl.c is 64-bit, sampling elsewhere is noted."""
import math, random, statistics, sys, time
import sts, runwl

SEEDS = 7


def closure_stats(Q, t, trials, rng):
    n = len(Q)
    out = []
    for _ in range(trials):
        T = rng.sample(range(n), t)
        out.append(sts.closure_size(Q, T))
    return min(out), int(statistics.median(out)), max(out)


def greedy_rank_ub(Q, rng, restarts=3, samples=30):
    n = len(Q)
    best = 10 ** 9
    chains = None
    for _ in range(restarts):
        chain, gens = sts.greedy_chain(Q, rng, pick_max=True, samples=samples)
        if len(gens) < best:
            best = len(gens)
            chains = chain
    return best, chains


def hn_points(chain):
    return [(r, round(math.log2(s + 1), 2)) for r, s in chain]


def families(rng):
    F1 = None
    while True:
        F1 = sts.patterned_factorization_k8(rng)
        nf, sp, T = sts.f1_acceptable(F1, 3)
        if nf and sp:
            break
    fam = []
    for m in (5, 6, 7, 8):
        fam.append((f"PG({m-1},2)", sts.pg(m), "PG"))
    for m in (3, 4, 5):
        fam.append((f"AG({m},3)", sts.ag3(m), "AG"))
    fam.append(("HTS(81) non-affine", sts.hts81(), "HTS"))
    fam.append(("Bose Z_5", sts.bose_zp(5, 1), "Bose"))
    fam.append(("Bose Z_5^2", sts.bose_zp(5, 2), "Bose"))
    fam.append(("Bose Z_3^3", sts.bose_zp(3, 3), "Bose"))
    fam.append(("Bose Z_7^2", sts.bose_zp(7, 2), "Bose"))
    fam.append(("Skolem 6t+1,t=10", sts.skolem(10), "Skolem"))
    fam.append(("PG(2,2)xPG(2,2)", sts.product(sts.pg(3), sts.pg(3)), "prod"))
    fam.append(("STS(13)xPG(2,2)", sts.product(sts.skolem(2), sts.pg(3)), "prod"))
    # doubling tower
    Q = sts.pg(3)
    for i in range(1, 5):
        Q = sts.doubling(Q, rng)
        fam.append((f"random doubling tower, height {i} (from PG(2,2))", Q, "dbl"))
    # central extensions with random line cochain; k=1 fibres
    for d in (5, 6, 7):
        g = sts.random_g(d, 1, rng)
        fam.append((f"X_g random line cochain d={d} k=1", sts.x_fib(d, 1, lambda c: 0, {1: [(0, 1)]}, g), "Xg"))
    # X_chi k=3 with random colourings
    for d in (4, 5):
        chi = {c: rng.randrange(2) for c in range(1, 1 << d)}
        fam.append((f"X_chi random d={d} k=3", sts.x_fib(d, 3, lambda c: chi[c], F1), "Xchi"))
    # sparse Pasch-switched PG
    fam.append(("PG(6,2) +3 Pasch switches", sts.pasch_switch_pg(7, 3, rng), "trade"))
    fam.append(("PG(7,2) +3 Pasch switches", sts.pasch_switch_pg(8, 3, rng), "trade"))
    fam.append(("PG(6,2) +40 Pasch switches", sts.pasch_switch_pg(7, 40, rng), "trade"))
    fam.append(("Bose Z_5^3", sts.bose_zp(5, 3), "Bose"))
    # random (hill-climbing)
    for n in (63, 127, 255, 301):
        fam.append((f"hill-climbing STS({n})", sts.random_sts_hillclimb(n, rng), "rand"))
    return fam


def main():
    rng = random.Random(SEEDS)
    fam = families(rng)
    print("name | n | d2=F2-char dim | d3=F3-char dim-1 | rank UB | closure t=3 (min,med,max) | t=5 | t=8 | 1WL depth(trace) | 2WL depth(trace)")
    for name, Q, tag in fam:
        n = len(Q)
        t0 = time.time()
        assert sts.is_sts(Q), name
        d2 = sts.char_space_dim(Q)
        d3 = sts.char_space_dim_3(Q) - 1 if n <= 300 else "-"
        rub, chain = greedy_rank_ub(Q, rng)
        c3 = closure_stats(Q, 3, 40, rng)
        c5 = closure_stats(Q, 5, 30, rng)
        c8 = closure_stats(Q, 8, 15, rng) if n >= 9 else None
        which = 1 | (2 if n <= 260 else 0)
        wlres = runwl.wl(Q, which=which)
        w1 = wlres.get("1wl")
        w2 = wlres.get("2wl")
        print(f"{name} | {n} | {d2} | {d3} | {rub} | {c3} | {c5} | {c8} | {w1} | {w2} | {hn_points(chain)} | {time.time()-t0:.1f}s", flush=True)


if __name__ == "__main__":
    main()
