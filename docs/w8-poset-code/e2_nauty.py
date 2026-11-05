"""w8 E2: the poset DP on coloured coordinate tanglegrams (T_sigma, T_rho, leaf colouring) against
nauty. E3: complete-tree tanglegrams with twisted leaf bijections, encoded as coloured coordinate
tanglegrams over the width-2 poset C_h + C_h on [b]^{2h} (Prop H), against nauty on the original."""
import itertools, math, random, sys, time
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from w8lib import *
import pynauty

seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
which = sys.argv[2] if len(sys.argv) > 2 else "E2E3"
rng = random.Random(seed)


def tangle_graph(b, h, order1, order2, leafmap, colour):
    """leaves = tuples in [b]^h; tree k splits coordinates in order_k; leaf x of tree 1 is
    identified with leaf leafmap[x] of tree 2; colour: dict leaf -> colour (of tree-1 leaf x)."""
    leaves = list(itertools.product(range(b), repeat=h))
    vid = {}
    def v(key):
        if key not in vid: vid[key] = len(vid)
        return vid[key]
    for x in leaves: v(('L', x))
    adj = {}
    def edge(a, c): adj.setdefault(a, set()).add(c); adj.setdefault(c, set()).add(a)
    for tag, order, mp in (('X', order1, None), ('Y', order2, leafmap)):
        for x in leaves:
            y = x if mp is None else mp[x]
            prev = v((tag, ()))
            for k in range(1, h):
                key = (tag, tuple((order[i], y[order[i]]) for i in range(k)))
                cur = v(key); edge(prev, cur); prev = cur
            edge(prev, v(('L', x)))
    n = len(vid)
    cols = sorted(set(colour.values()))
    cls = [set(), set()] + [set() for _ in cols]
    ci = {c: 2 + k for k, c in enumerate(cols)}
    for key, i in vid.items():
        if key[0] == 'X': cls[0].add(i)
        elif key[0] == 'Y': cls[1].add(i)
        else: cls[ci[colour[key[1]]]].add(i)
    return pynauty.Graph(n, adjacency_dict={a: list(s) for a, s in adj.items()}, vertex_coloring=cls)


def nauty_aut(g):
    gens, m1, m2, orbits, norb = pynauty.autgrp(g)
    return m1, m2


def same_order(order, m1, m2):
    """compare exact order with nauty's (m1 * 10^m2) to 12 significant digits"""
    if order < 10 ** 12:
        return order == round(m1 * 10 ** m2)
    s = f"{order:.12e}"
    mant, ex = s.split('e')
    return int(ex) == m2 + int(math.floor(math.log10(m1))) and abs(float(mant) - m1 / 10 ** math.floor(math.log10(m1))) < 1e-9


def colourings(b, h, pred, rng):
    pts = list(itertools.product(range(b), repeat=h))
    out = []
    out.append(('const', {z: 0 for z in pts}))
    out.append(('rand2', {z: rng.randrange(2) for z in pts}))
    out.append(('rand3', {z: rng.randrange(3) for z in pts}))
    out.append(('sum', {z: sum(z) % b for z in pts}))
    inc = [(i, j) for i in range(h) for j in range(i + 1, h) if i not in pred[j] and j not in pred[i]]
    if inc:
        i, j = rng.choice(inc)
        out.append((f'xor{i}{j}', {z: (z[i] - z[j]) % b for z in pts}))
    # sparse twist: two leaves marked
    c = {z: 0 for z in pts}
    for z in rng.sample(pts, 2): c[z] = 1
    out.append(('mark2', c))
    # one-hot on a fibre product: z[i]==z[j]==z[k] for random coords
    ks = rng.sample(range(h), min(3, h))
    out.append(('eq3', {z: int(len(set(z[k] for k in ks)) == 1) for z in pts}))
    return out


def run_E2(shapes, ntrees):
    tot = ok = 0
    for b, h in shapes:
        for tr in range(ntrees):
            rho = list(range(h)); rng.shuffle(rho)
            if tr == 0: rho = list(range(h))[::-1]          # digit reversal: antichain
            pred = poset_2dim(list(range(h)), rho)
            for name, xs in colourings(b, h, pred, rng):
                t0 = time.time()
                S = PosetSI(b, pred)
                g0 = random_gwp_element(b, h, pred, rng)
                pts = list(xs)
                if rng.random() < 0.5:
                    ys = {g0[z]: xs[z] for z in pts}; expect_iso = True
                else:      # perturb: swap two leaves of different colours (if any), then relabel
                    zs = dict(xs)
                    a = rng.choice(pts); diff = [z for z in pts if xs[z] != xs[a]]
                    if diff:
                        c = rng.choice(diff); zs[a], zs[c] = zs[c], zs[a]
                    ys = {g0[z]: zs[z] for z in pts}; expect_iso = None
                x = S.to_lam_string(xs); y = S.to_lam_string(ys)
                A, r = S.solve(x, y)
                dt = time.time() - t0
                gx = tangle_graph(b, h, list(range(h)), rho, None, xs)
                m1, m2 = nauty_aut(gx)
                if sorted(xs.values()) == sorted(ys.values()):
                    gy = tangle_graph(b, h, list(range(h)), rho, None, ys)
                    niso = pynauty.certificate(gx) == pynauty.certificate(gy)
                else:
                    niso = False
                good = same_order(A.order(), m1, m2) and ((r is not None) == niso)
                if expect_iso: good &= r is not None
                if r is not None:
                    gc = S.perm_to_coords(r)
                    good &= in_gwp(b, h, pred, gc) and all(ys[gc[z]] == xs[z] for z in pts)
                for gen in A.gens:
                    gc = S.perm_to_coords(gen)
                    good &= in_gwp(b, h, pred, gc) and all(xs[gc[z]] == xs[z] for z in pts)
                tot += 1; ok += good
                st = S.stats
                print(f"E2 b={b} h={h} rho={rho} mu={S.mu} nu={nu_of(pred)} col={name:7s} "
                      f"|Aut|={A.order():.4g} nauty={m1:.4g}e{m2} iso={r is not None}/{niso} "
                      f"ok={good} t={dt:.2f}s states={st['aut_states']}+{st['rep_states']} "
                      f"br={st['branches']} ci={st['ci_calls']} maxm={st['max_m']} maxVR={st['max_VR']}",
                      flush=True)
    print(f"E2 total: {ok}/{tot} agree")


def run_E3(shapes, reps):
    """complete-tree tanglegrams (T_id, T_rho o phi) with phi = identity + a few transpositions
    or random; encode as string M on [b]^{2h} under S_b^{(C_h + C_h)}."""
    tot = ok = 0
    for b, h in shapes:
        leaves = list(itertools.product(range(b), repeat=h))
        for tr in range(reps):
            rho = list(range(h)); rng.shuffle(rho)
            kind = ['coord', 'swap1', 'swap2', 'random'][tr % 4]
            mp = {x: x for x in leaves}
            if kind in ('swap1', 'swap2'):
                for _ in range(1 if kind == 'swap1' else 2):
                    a, c = rng.sample(leaves, 2); mp[a], mp[c] = mp[c], mp[a]
            elif kind == 'random':
                perm = leaves[:]; rng.shuffle(perm); mp = dict(zip(leaves, perm))
            g = tangle_graph(b, h, list(range(h)), rho, mp, {x: 0 for x in leaves})
            m1, m2 = nauty_aut(g)
            # poset: chain 0<1<..<h-1 ; chain h+rho[0] < h+rho[1] < ...
            rel = [(k, k + 1) for k in range(h - 1)] + [(h + rho[k], h + rho[k + 1]) for k in range(h - 1)]
            pred = closure(2 * h, rel)
            t0 = time.time()
            S = PosetSI(b, pred)
            M = {z: int(tuple(z[h:]) == mp[tuple(z[:h])]) for z in itertools.product(range(b), repeat=2 * h)}
            x = S.to_lam_string(M)
            A, _ = S.solve(x, x)
            dt = time.time() - t0
            good = same_order(A.order(), m1, m2)
            tot += 1; ok += good
            st = S.stats
            print(f"E3 b={b} h={h} rho={rho} {kind:6s} |Aut(tanglegram)| nauty={m1:.4g}e{m2} "
                  f"DP on C_h+C_h (mu={S.mu}): {A.order():.4g} ok={good} t={dt:.2f}s "
                  f"states={st['aut_states']}+{st['rep_states']} maxm={st['max_m']}", flush=True)
    print(f"E3 total: {ok}/{tot} agree")


if "E2" in which:
    run_E2([(2, 4), (2, 5), (3, 3), (2, 6), (3, 4), (4, 3)], 3)
if "E3" in which:
    run_E3([(2, 2), (2, 3), (3, 2), (2, 4)], 8)


def colourings_twisted(b, h, pred, rng):
    """extra 'twist' colourings: a quadratic form along the poset relations, a third tree's
    level-2 nodes, and random marks; plus the E2 ones"""
    pts = list(itertools.product(range(b), repeat=h))
    out = colourings(b, h, pred, rng)
    rels = [(j, i) for i in range(h) for j in pred[i]]
    out.append(('quadP', {z: sum(z[j] * z[i] for j, i in rels) % 2 for z in pts}))
    inc = [(i, j) for i in range(h) for j in range(i + 1, h) if i not in pred[j] and j not in pred[i]]
    out.append(('quadInc', {z: sum(z[i] * z[j] for i, j in inc) % 2 for z in pts}))
    tau = list(range(h)); rng.shuffle(tau)
    marked = set((a, c) for a in range(b) for c in range(b) if rng.random() < 0.5)
    out.append(('tree3', {z: int((z[tau[0]], z[tau[1]]) in marked) for z in pts}))
    return out


def run_E2b(shapes, per_shape, mu_min):
    tot = ok = 0
    for b, h in shapes:
        got = 0
        tries = 0
        while got < per_shape and tries < 5000:
            tries += 1
            rho = list(range(h)); rng.shuffle(rho)
            pred = poset_2dim(list(range(h)), rho)
            mu, lam = best_order(pred)
            if mu < mu_min:
                continue
            got += 1
            for name, xs in colourings_twisted(b, h, pred, rng):
                t0 = time.time()
                S = PosetSI(b, pred, lam)
                g0 = random_gwp_element(b, h, pred, rng)
                pts = list(xs)
                if rng.random() < 0.5:
                    ys = {g0[z]: xs[z] for z in pts}; expect_iso = True
                else:
                    zs = dict(xs)
                    a = rng.choice(pts); diff = [z for z in pts if xs[z] != xs[a]]
                    if diff:
                        c = rng.choice(diff); zs[a], zs[c] = zs[c], zs[a]
                    ys = {g0[z]: zs[z] for z in pts}; expect_iso = None
                x = S.to_lam_string(xs); y = S.to_lam_string(ys)
                A, r = S.solve(x, y)
                dt = time.time() - t0
                gx = tangle_graph(b, h, list(range(h)), rho, None, xs)
                m1, m2 = nauty_aut(gx)
                if sorted(xs.values()) == sorted(ys.values()):
                    gy = tangle_graph(b, h, list(range(h)), rho, None, ys)
                    niso = pynauty.certificate(gx) == pynauty.certificate(gy)
                else:
                    niso = False
                good = same_order(A.order(), m1, m2) and ((r is not None) == niso)
                if expect_iso: good &= r is not None
                if r is not None:
                    gc = S.perm_to_coords(r)
                    good &= in_gwp(b, h, pred, gc) and all(ys[gc[z]] == xs[z] for z in pts)
                for gen in A.gens:
                    gc = S.perm_to_coords(gen)
                    good &= in_gwp(b, h, pred, gc) and all(xs[gc[z]] == xs[z] for z in pts)
                tot += 1; ok += good
                st = S.stats
                print(f"E2b b={b} h={h} rho={rho} mu={S.mu} nu={nu_of(pred)} col={name:7s} "
                      f"|Aut|={A.order():.4g} nauty={m1:.4g}e{m2} iso={r is not None}/{niso} "
                      f"ok={good} t={dt:.2f}s states={st['aut_states']}+{st['rep_states']} "
                      f"br={st['branches']} ci={st['ci_calls']} maxm={st['max_m']} maxVR={st['max_VR']}",
                      flush=True)
    print(f"E2b total: {ok}/{tot} agree")


if "E2b" in which:
    run_E2b([(2, 7), (2, 8), (3, 5), (2, 9)], 2, 1)
if "E2c" in which:
    run_E2b([(2, 10), (3, 6), (5, 3)], 1, 1)
if "E2d" in which:
    run_E2b([(5, 3)], 2, 0)
if "E2e" in which:
    run_E2b([(5, 4)], 1, 1)
