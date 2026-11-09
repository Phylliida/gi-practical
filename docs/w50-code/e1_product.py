"""E1: exact least k (values per coordinate) such that k-box cycles span the cycle space, over F_2 and F_3,
for C = H^M and Gamma a union of C-orbitals on [b]^M. Includes 2-transitive H (Theorem A predicts k <= 4) and others."""
import itertools, random, sys, time
from gainlib import *
seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
rng = random.Random(seed)


def closure(gens, b):
    seen = {tuple(range(b))}; q = [tuple(range(b))]
    for g in q:
        for s in gens:
            h = tuple(s[g[i]] for i in range(b))
            if h not in seen: seen.add(h); q.append(h)
    return sorted(seen)


def orbitals_of(group, b):
    """orbitals on ordered pairs (a,c); list of frozensets"""
    pairs = [(a, c) for a in range(b) for c in range(b)]
    seen = set(); out = []
    for pr in pairs:
        if pr in seen: continue
        o = {(g[pr[0]], g[pr[1]]) for g in group}
        seen |= o; out.append(frozenset(o))
    return out


def sym_closed(orb_idx, orbs):
    """symmetrised orbital index"""
    o = orbs[orb_idx]; a, c = next(iter(o))
    return next(i for i, oo in enumerate(orbs) if (c, a) in oo)


def build(b, M, orbs, F):
    """F: set of tuples in range(len(orbs))^M; u~v iff (u_j,v_j) in orb[F_tuple[j]] for some tuple in F. returns adj"""
    adj = defaultdict(set)
    verts = list(itertools.product(range(b), repeat=M))
    for u in verts:
        adj[u]  # ensure key
    F = set(F)
    for u in verts:
        for pattern in F:
            # enumerate neighbours: per coordinate, values c with (u_j,c) in orb
            choices = [[c for c in range(b) if (u[j], c) in orbs[pattern[j]]] for j in range(M)]
            for w in itertools.product(*choices):
                if w != u:
                    adj[u].add(w); adj[w].add(u)
    # keep only non-isolated
    adj = {u: sorted(nb) for u, nb in adj.items() if nb}
    return adj


def report(name, b, M, group, nF=3, trials=3):
    orbs = orbitals_of(group, b)
    idx = list(range(len(orbs)))
    diag = next(i for i, o in enumerate(orbs) if all(a == c for a, c in o))
    for tr in range(trials):
        # random symmetric pattern family: not all diagonal
        F = set()
        while len(F) < nF:
            f = tuple(rng.choice(idx) for _ in range(M))
            if all(x == diag for x in f): continue
            F.add(f); F.add(tuple(sym_closed(x, orbs) for x in f))
        adj = build(b, M, orbs, F)
        if not adj: continue
        eid = edge_index(adj)
        for p in (2, 3):
            t0 = time.time()
            k, tbl = min_k(adj, eid, b, M, p, kmax=min(b, 5), maxboxes=300000, rng=rng)
            print(f"{name} b={b} M={M} |F|={len(F)} V={len(adj)} E={len(eid)} p={p} mink={k} tbl={ {kk:v for kk,v in tbl.items()} } ({time.time()-t0:.1f}s)", flush=True)


def S(b): return closure([tuple((i + 1) % b for i in range(b)), tuple([1, 0] + list(range(2, b)))], b)
def A(b): return closure([tuple((i + 1) % b for i in range(b)), tuple([1, 2, 0] + list(range(3, b)))], b)
def Zc(b): return closure([tuple((i + 1) % b for i in range(b))], b)
def AGL1(q): return closure([tuple((i + 1) % q for i in range(q)), tuple(2 * i % q for i in range(q))], q)  # q=5
def V4(): return closure([(1, 0, 3, 2), (2, 3, 0, 1)], 4)

if __name__ == "__main__":
    report("S4", 4, 2, S(4))
    report("S4", 4, 3, S(4))
    report("S5", 5, 2, S(5))
    report("S5", 5, 3, S(5))
    report("A5", 5, 3, A(5))
    report("A4", 4, 3, A(4))
    report("V4reg", 4, 3, V4())
    report("Z4", 4, 3, Zc(4))
    report("Z5", 5, 3, Zc(5))
    report("AGL15", 5, 3, AGL1(5))
