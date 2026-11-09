"""Recompute the folded-cube and odd-graph numbers of w50 E2/E5 with this harness: F_p ranks, integer quotient H_1/B (Smith), pi_1 quotient (Tietze)."""
import itertools, sys, time
sys.path.insert(0, '.')
from rtlib import *


def quotient(adj, walks, label):
    """rank over 2,3,5 and integer invariants of H_1 / <walks>"""
    C = Cycles(adj)
    rows = []
    seen = set()
    for w in walks:
        v = C.vector(w)
        if v:
            key = tuple(sorted(v.items()))
            if key not in seen:
                seen.add(key)
                rows.append(v)
    res = {}
    for p in (2, 3, 5):
        sp = make_span(p)
        for v in rows:
            sp.addv(v)
            if sp.rank == C.rank:
                break
        res[p] = C.rank - sp.rank
    rk, inv = smith_invariants(rows, C.rank)
    print(f"{label}: V={len(adj)} E={num_edges(adj)} comps={C.comps} cycle rank={C.rank} coranks {res} ; integer rank {rk}, non-unit invariants {inv}", flush=True)
    return res, rk, inv


def pi1_quotient(adj, walks, label):
    C = Cycles(adj)
    rels = []
    seen = set()
    for w in walks:
        word = C.word(w)
        if word:
            t = tuple(free_reduce(word))
            if t and t not in seen:
                seen.add(t)
                rels.append(list(t))
    t0 = time.time()
    try:
        alive, left = tietze_simplify(rels, C.rank, maxlen=2000)
    except RuntimeError:
        print(label, "tietze blow-up")
        return None
    left = sorted(left, key=len)[:8]
    print(f"{label}: pi_1/<<walks>> presentation after Tietze: {len(alive)} generators, relators (shortest 8) {left} ({time.time()-t0:.1f}s)", flush=True)


def m1_exact():
    for n in (3, 5):
        local, *_ = folded_cube(n)
        b = len(local)
        adj = {(u,): [(v,) for v in local[u]] for u in local}
        for p in (2, 3, 5):
            k, tbl = least_k(adj, b, 1, p, kmax=b if n == 3 else 6)
            print(f"folded n={n} b={b} p={p}: least k={k}, table={tbl}")
    for n in (5, 7):
        local, *_ = folded_cube(n)
        adj = {(u,): [(v,) for v in local[u]] for u in local}
        walks = list(closed_walks_upto(adj, 4))
        quotient(adj, walks, f"folded n={n} M=1 <=4 walks")
        pi1_quotient(adj, walks, f"folded n={n} M=1")


def m2_patterns():
    n = 5
    local, *_ = folded_cube(n)
    b = len(local)
    for name, F in [("cartesian", [(0,), (1,)]), ("tensor", [(0, 1)]), ("mix", [(0,), (0, 1)]), ("three(dependent)", [(0,), (1,), (0, 1)])]:
        adj = pattern_graph(local, b, 2, F)
        t0 = time.time()
        walks = list(closed_walks_upto(adj, 4))
        print(name, "walks", len(walks), f"{time.time()-t0:.1f}s", flush=True)
        # parity map check
        def r(w):
            out = [0, 0]
            for a, c in zip(w, w[1:]):
                for j in range(2):
                    if a[j] != c[j]:
                        out[j] ^= 1
            return tuple(out)
        assert all(r(w) == (0, 0) for w in walks), "<=4 walk with nonzero parity"
        C = Cycles(adj)
        for p in (2, 3):
            sp = make_span(p)
            for w in walks:
                sp.addv(C.vector(w))
                if sp.rank == C.rank:
                    break
            rkD = Span2()
            for I in F:
                rkD.add(sum(1 << j for j in I))
            print(f"  folded n=5 M=2 {name}: p={p} cycle rank {C.rank}, corank of <=4 walks {C.rank - sp.rank}; rk D={rkD.rank}", flush=True)


def odd_tests():
    for t in (2, 3, 4):
        local, verts = odd_graph(t)
        adj = {(u,): [(v,) for v in local[u]] for u in local}
        L = 6 if t >= 3 else 6
        walks = list(closed_walks_upto(adj, L))
        quotient(adj, walks, f"odd graph t={t} b={len(local)} M=1 <={L} walks (g={2*t+1})")
    local, verts = odd_graph(2)
    adj = {(u,): [(v,) for v in local[u]] for u in local}
    for p in (2, 3):
        print("Petersen least k p=", p, least_k(adj, 10, 1, p, kmax=6))


def lifted_relators(local, b, F, M, L):
    """Rectangles, cross elements, commutators (= all closed 4-walks through two steps of each kind) and lifts of local L-cycles with the
    other coordinates in the pattern oscillating.  Span is a lower bound; it is compared with the upper bound cycle rank - rk D."""
    cyc = [w for w in closed_walks_upto({(u,): [(v,) for v in local[u]] for u in local}, L) if len(w) - 1 >= 4]
    cyc = [[v[0] for v in w] for w in cyc]
    adj = pattern_graph(local, b, M, F)
    # all closed 4-walks without backtrack
    walks = list(closed_walks_upto(adj, 4))
    # lifted local cycles
    for I in F:
        for j in I:
            others = [l for l in I if l != j]
            for c in cyc:
                L0 = len(c) - 1
                if L0 % 2:
                    continue
                rest = [l for l in range(M) if l not in I]
                for base in itertools.product(range(b), repeat=len(rest)):
                    for x in range(b):
                        for osc in itertools.product(*[local[x] for _ in others]):
                            v0 = [None] * M
                            for l, val in zip(rest, base):
                                v0[l] = val
                            w = []
                            for s in range(L0 + 1):
                                v = list(v0)
                                v[j] = c[s]
                                for l, y in zip(others, osc):
                                    v[l] = x if s % 2 == 0 else y
                                w.append(tuple(v))
                            walks.append(w)
    return adj, walks


def odd_pattern():
    t = 3
    local, verts = odd_graph(t)
    b = len(local)
    for name, F in [("cartesian", [(0,), (1,)]), ("tensor", [(0, 1)])]:
        adj, walks = lifted_relators(local, b, F, 2, 6)
        C = Cycles(adj)
        print("odd t=3", name, "V", len(adj), "E", num_edges(adj), "walks", len(walks), flush=True)
        for p in (2, 3):
            sp = make_span(p)
            for w in walks:
                sp.addv(C.vector(w))
                if sp.rank == C.rank:
                    break
            rkD = Span2()
            for I in F:
                rkD.add(sum(1 << j for j in I))
            print(f"  O_4 M=2 {name}: p={p} cycle rank {C.rank}, corank {C.rank - sp.rank}; rk D={rkD.rank}", flush=True)


if __name__ == "__main__":
    {"m1": m1_exact, "m2": m2_patterns, "odd": odd_tests, "oddp": odd_pattern}[sys.argv[1]]()
