"""E4: non-product C. C = diag(S_b) or diag(A_b) on [b]^M (one class), or a product of two diagonal classes on [b]^(M1+M2).
Random unions of C-orbitals on V=[b]^M; exact least k for k-box generation over F_2, F_3 (homology level only)."""
import itertools, random, sys, time
from gainlib import *
from e1_product import closure as grp_closure  # noqa (e1 runs its reports on import; guarded below)
seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
rng = random.Random(seed)


def S(b): return grp_closure([tuple((i + 1) % b for i in range(b)), tuple([1, 0] + list(range(2, b)))], b)
def A(b): return grp_closure([tuple((i + 1) % b for i in range(b)), tuple([1, 2, 0] + list(range(3, b)))], b)


def build_group(b, classes, base):
    """classes: list of lists of coordinate indices; group = product over classes of diag(base). Elements as tuples of b-perms per class."""
    return list(itertools.product(base, repeat=len(classes)))


def act(elt, classes, v):
    w = list(v)
    for g, cl in zip(elt, classes):
        for j in cl:
            w[j] = g[w[j]]
    return tuple(w)


def orbitals(b, M, elts, classes, maxpairs=None):
    verts = list(itertools.product(range(b), repeat=M))
    seen = {}
    orbs = []
    for u in verts:
        for v in verts:
            if (u, v) in seen: continue
            o = set()
            for g in elts:
                o.add((act(g, classes, u), act(g, classes, v)))
            idx = len(orbs); orbs.append(o)
            for p in o: seen[p] = idx
    return verts, orbs


def report(name, b, M, classes, base, trials=4, nunion=3):
    elts = build_group(b, classes, base)
    verts, orbs = orbitals(b, M, elts, classes)
    nontrivial = [o for o in orbs if not any(u == v for u, v in o)]
    print(f"{name}: b={b} M={M} |C|={len(elts)} orbitals={len(orbs)} nondiag={len(nontrivial)}", flush=True)
    for tr in range(trials):
        pick = rng.sample(range(len(nontrivial)), min(nunion, len(nontrivial)))
        adj = defaultdict(set)
        for i in pick:
            for u, v in nontrivial[i]:
                adj[u].add(v); adj[v].add(u)
        adj = {u: sorted(nb) for u, nb in adj.items()}
        eid = edge_index(adj)
        for p in (2, 3):
            t0 = time.time()
            k, tbl = min_k(adj, eid, b, M, p, kmax=min(b, 5), maxboxes=100000, rng=rng)
            print(f"   tr{tr} V={len(adj)} E={len(eid)} p={p} least k={k} tbl={tbl} ({time.time()-t0:.1f}s)", flush=True)


if __name__ == "__main__":
    report("diag S4 M=2", 4, 2, [[0, 1]], S(4))
    report("diag S4 M=3", 4, 3, [[0, 1, 2]], S(4))
    report("diag S5 M=2", 5, 2, [[0, 1]], S(5))
    report("diag A5 M=3", 5, 3, [[0, 1, 2]], A(5))
    report("two diag classes S4, M=4", 4, 4, [[0, 1], [2, 3]], S(4), trials=2, nunion=2)
