"""Exact check of Theorem 2, d=3, by invariants: isomorphic colourings give isomorphic STS by the explicit map
(checked directly), and pairwise distinct invariants across GL(3,2)-orbits certify non-isomorphism."""
import random, itertools, sys
import sts, runwl

def gl3():
    res = []
    for c0 in range(1, 8):
        for c1 in range(1, 8):
            if c1 == c0: continue
            for c2 in range(1, 8):
                if c2 in (c0, c1, c0 ^ c1): continue
                res.append((c0, c1, c2))
    return res

def apply(A, x):
    r = 0
    for i in range(3):
        if x >> i & 1:
            r ^= A[i]
    return r

rng = random.Random(7)
while True:
    F1 = sts.patterned_factorization_k8(rng)
    nf, sp, T = sts.f1_acceptable(F1, 3)
    if nf and sp:
        break
print("F1 found: non-PG T^1:", nf, "span condition:", sp)

GL = gl3()
assert len(GL) == 168
def transform(chi, A):
    r = 0
    for c in range(1, 8):
        if chi >> (c - 1) & 1:
            r |= 1 << (apply(A, c) - 1)
    return r
# orbits of colourings of F_2^3\0 (chi != 0)
seen = {}
orbits = []
for chi in range(1, 128):
    if chi in seen: continue
    oid = len(orbits)
    orb = sorted({transform(chi, A) for A in GL})
    for o in orb: seen[o] = oid
    orbits.append(orb)
print("GL(3,2)-orbits on nonzero colourings:", len(orbits), [len(o) for o in orbits])

def build(chi):
    Q = sts.x_fib(3, 3, lambda c: (chi >> (c - 1)) & 1, F1)
    assert sts.is_sts(Q)
    return Q

# 1. forward direction: check the explicit map (z |-> z, (c,a) |-> (Ac,a)) is an isomorphism
for chi in [1, 3, 11, 37, 101, 53]:
    A = rng.choice(GL)
    chi2 = transform(chi, A)
    Q, Q2 = build(chi), build(chi2)
    def phi(p):
        if p < 7: return p
        p -= 7
        c = p // 8 + 1
        a = p % 8
        return 7 + (apply(A, c) - 1) * 8 + a
    ok = all(Q2[phi(x)][phi(y)] == phi(Q[x][y]) for x in range(len(Q)) for y in range(len(Q)))
    assert ok, chi
print("forward direction: explicit map is an isomorphism on 6 samples: OK")
print("characters: chi2 dim of X_chi (should be d=3 for nonzero chi):", sorted({sts.char_space_dim(build(c)) for c in [1,3,7,127]}))

# 2. invariants on orbit reps
sigs = []
for oid, orb in enumerate(orbits):
    r = runwl.wl(build(orb[0]), which=12)["sig"]
    sigs.append(r)
    print("orbit", oid, "size", len(orb), "sig", r, flush=True)
print("distinct invariants among", len(orbits), "orbit reps:", len(set(sigs)))
for c in [5, 77]:
    A = rng.choice(GL)
    s1 = runwl.wl(build(c), which=12)["sig"]
    s2 = runwl.wl(build(transform(c, A)), which=12)["sig"]
    assert s1 == s2, "invariant mismatch on equivalent colourings"
print("equivalent-colouring invariants agree (4 samples).")
