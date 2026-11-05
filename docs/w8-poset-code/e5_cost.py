"""w8 E5: cost of the poset DP across posets at fixed N, verified with nauty on the poset block
structure graph (points + one class vertex per class of each principal partition F_{D[i]})."""
import itertools, random, sys, time
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from w8lib import *
import pynauty

seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
rng = random.Random(seed)


def pbs_graph(b, pred, colour):
    h = len(pred)
    pts = list(itertools.product(range(b), repeat=h))
    vid = {('P', z): k for k, z in enumerate(pts)}
    adj = {}
    for i in range(h):
        Di = sorted(pred[i] | {i})
        for z in pts:
            key = ('C', i, tuple(z[j] for j in Di))
            if key not in vid:
                vid[key] = len(vid)
            a, c = vid[('P', z)], vid[key]
            adj.setdefault(a, set()).add(c); adj.setdefault(c, set()).add(a)
    cols = sorted(set(colour.values()))
    cells = [set() for _ in cols] + [set() for _ in range(h)]
    ci = {c: k for k, c in enumerate(cols)}
    for key, v in vid.items():
        if key[0] == 'P':
            cells[ci[colour[key[1]]]].add(v)
        else:
            cells[len(cols) + key[1]].add(v)
    return pynauty.Graph(len(vid), adjacency_dict={a: list(s) for a, s in adj.items()},
                         vertex_coloring=cells)


def same_order(order, m1, m2):
    import math
    if order < 10 ** 12:
        return order == round(m1 * 10 ** m2)
    e = int(math.floor(math.log10(m1))) + m2
    return abs(order / 10 ** e - m1 / 10 ** math.floor(math.log10(m1))) < 1e-9 * 10


def families(b, h):
    fam = [("antichain", poset_chains([1] * h)), ("chain", poset_chains([h]))]
    m = h // 2
    fam.append((f"C{m}+C{h-m}", poset_chains([m, h - m])))
    if h >= 6:
        fam.append((f"C{h-2}+C1+C1", poset_chains([h - 2, 1, 1])))
        a = (h - 2) // 2
        rel = [(x, a) for x in range(a)] + [(a + 1 + x, 2 * a + 1) for x in range(a)]
        fam.append((f"(A{a}<k)+(A{a}<k)", closure(2 * a + 2, rel)))
        rel = [(i, j) for i in range(m) for j in range(m, h)]
        fam.append((f"A{m}<A{h-m}", closure(h, rel)))
        rel = [(i, m + j) for i in range(m) for j in range(m) if i != j]
        if 2 * m == h:
            fam.append((f"S{m} (standard ex.)", closure(h, rel)))
    for _ in range(2):
        rho = list(range(h)); rng.shuffle(rho)
        fam.append((f"2dim{rho}", poset_2dim(list(range(h)), rho)))
    return fam


tot = ok = 0
for b, h in [(2, 8), (3, 5)]:
    pts = list(itertools.product(range(b), repeat=h))
    for name, pred in families(b, h):
        if len(pred) != h:
            continue
        mu, lam = best_order(pred)
        for cname in ["rand2", "mark3", "quad"]:
            if cname == "rand2":
                xs = {z: rng.randrange(2) for z in pts}
            elif cname == "mark3":
                xs = {z: 0 for z in pts}
                for z in rng.sample(pts, 3): xs[z] = 1
            else:
                prs = [(i, j) for i in range(h) for j in range(i + 1, h) if rng.random() < 0.4]
                xs = {z: sum(z[i] * z[j] for i, j in prs) % 2 for z in pts}
            S = PosetSI(b, pred, lam)
            x = S.to_lam_string(xs)
            t0 = time.time()
            A, _ = S.solve(x, x)
            dt = time.time() - t0
            m1, m2 = pynauty.autgrp(pbs_graph(b, pred, xs))[1:3]
            good = same_order(A.order(), m1, m2)
            tot += 1; ok += good
            st = S.stats
            print(f"E5 b={b} h={h} {name:22s} mu={mu} nu={nu_of(pred)} {cname:5s} |Aut|={A.order():.4g} "
                  f"nauty={m1:.4g}e{m2} ok={good} t={dt:6.2f}s rep_states={st['rep_states']:6d} "
                  f"branches={st['branches']:6d} ci={st['ci_calls']:6d} max|[b]^R|={st['max_m']:4d} max|V_R|={st['max_VR']:4d}",
                  flush=True)
print(f"E5 total: {ok}/{tot} agree")
