"""E3: counting barrier gadget. A binary tanglegram whose group, projected to s swappable pairs,
is exactly a prescribed code ker H over F_2 (parity-check gadgets with auxiliary variables).
Checks with nauty: |Aut| = 2^(s-rank H) and every generator's swap pattern on the data pairs lies in ker H,
and the data-pair swap patterns of all automorphism generators span ker H."""
import itertools, random, sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'w8-poset-code'))
import pynauty

seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
rng = random.Random(seed)

def rank_rows(rows):
    rows = [r for r in rows]; rk = 0
    bas = []
    for r in rows:
        for b in bas:
            r = min(r, r ^ b)
        if r:
            bas.append(r); rk += 1
    return rk, bas

def in_span(v, bas):
    for b in bas:
        v = min(v, v ^ b)
    return v == 0

def build(H, s):
    """H: list of int masks (parity checks over s data bits). Returns graph, data pair vertex ids.
    Variables: 0..s-1 data; aux from s up. 3-checks by chaining."""
    nvar = s
    checks3 = []
    for row in H:
        vs = [j for j in range(s) if row >> j & 1]
        if len(vs) == 0:
            continue
        if len(vs) == 1:
            checks3.append((vs[0],))  # unary check forces this bit to 0
            continue
        while len(vs) > 3:
            a = nvar; nvar += 1
            checks3.append((vs[0], vs[1], a))
            vs = [a] + vs[2:]
        if len(vs) == 2:
            a = nvar; nvar += 1
            checks3.append((vs[0], vs[1], a))
            checks3.append((a,))  # force a=0 via unary check
        else:
            checks3.append(tuple(vs))
    return checks3, nvar

def to_graph(checks, nvar, s):
    """Tanglegram-like coloured graph: tree1 over check gadget leaves, tree2 over variable pairs.
    We build the incidence structure directly as a coloured graph (bounded degree) with
    gadget vertices m_{c,A} (A even subset of check support) adjacent to w^i (i=[w in A])
    -- exactly the T2 §5.1 multipede form (the tree encoding is the rigid-top one)."""
    vid = {}
    def v(k):
        if k not in vid: vid[k] = len(vid)
        return vid[k]
    adj = {}
    def e(a, b): adj.setdefault(a, set()).add(b); adj.setdefault(b, set()).add(a)
    colours = {}
    for w in range(nvar):
        for i in (0, 1):
            x = v(('W', w, i)); colours[x] = ('w', w)
    for c, supp in enumerate(checks):
        supp2 = sorted(set(supp))
        for bits in itertools.product((0, 1), repeat=len(supp2)):
            if sum(bits) % 2 == 0:
                x = v(('M', c, bits)); colours[x] = ('m', c)
                for w, b in zip(supp2, bits):
                    e(x, v(('W', w, b)))
    n = len(vid)
    cols = sorted(set(colours.values()), key=repr)
    ci = {c: i for i, c in enumerate(cols)}
    cells = [set() for _ in cols]
    for x, cc in colours.items():
        cells[ci[cc]].add(x)
    return pynauty.Graph(n, adjacency_dict={a: list(s_) for a, s_ in adj.items()},
                         vertex_coloring=[c for c in cells if c]), vid

def tanglegram_graph(checks, nvar, s_data):
    """Binary-ish tanglegram: leaves are incidences ((c,A),w). Tree1: rigid comb over checks -> gadget
    tree on A bits -> leaf comb over w. Tree2: rigid comb over vars -> pair w^0,w^1 -> incidences.
    Leaves carry colours (c, position) so the two trees are rigid except for the gadget/pair swaps."""
    vid = {}
    def v(k):
        if k not in vid: vid[k] = len(vid)
        return vid[k]
    adj = {}
    def e(a, b): adj.setdefault(a, set()).add(b); adj.setdefault(b, set()).add(a)
    colours = {}
    def col(k, c):
        colours[v(k)] = c
    # Tree 2 skeleton: var nodes with two pair children
    for w in range(nvar):
        col(('T2var', w), ('t2var', w))
        for i in (0, 1):
            e(v(('T2var', w)), v(('T2pair', w, i))); colours[v(('T2pair', w, i))] = ('t2pair', w)
    for c, supp in enumerate(checks):
        supp2 = sorted(set(supp))
        k = len(supp2)
        col(('T1check', c), ('t1check', c))
        # gadget tree: binary by first k-1 bits, last bit determined by parity
        for bits in itertools.product((0, 1), repeat=max(0, k - 1)):
            par = sum(bits) % 2
            full = bits + (par,)
            prev = ('T1check', c)
            for d in range(1, len(bits) + 1):
                node = ('T1gad', c, bits[:d])
                colours[v(node)] = ('t1gad', c, d)
                e(v(prev), v(node)); prev = node
            for pos, w in enumerate(supp2):
                leaf = ('L', c, full, w)
                e(v(prev), v(leaf)); colours[v(leaf)] = ('leaf', c, pos)
                # tree 2: leaf hangs under pair w^{bit} via a chain node keyed by (c)
                node2 = ('T2inc', w, full[pos], c)
                e(v(('T2pair', w, full[pos])), v(node2))
                colours[v(node2)] = ('t2inc', w, c)
                e(v(node2), v(leaf))
    # child u_2: extra leaf under each pair side of a data variable, cherries in tree 1
    for j in range(s_data):
        col(('Cherry', j), ('cherry', j))
        for i in (0, 1):
            leaf = ('L2', j, i)
            colours[v(leaf)] = ('leaf2', j)
            e(v(('T2pair', j, i)), v(leaf))
            e(v(('Cherry', j)), v(leaf))
    n = len(vid)
    cols = sorted(set(colours.values()), key=repr)
    ci = {c: i for i, c in enumerate(cols)}
    cells = [set() for _ in cols]
    for x, cc in colours.items():
        cells[ci[cc]].add(x)
    return pynauty.Graph(n, adjacency_dict={a: list(s_) for a, s_ in adj.items()},
                         vertex_coloring=[c for c in cells if c]), vid

tot = ok = 0
for s, r in [(4, 2), (6, 3), (8, 4), (10, 5), (12, 6)]:
    for t in range(5):
        H = [rng.randrange(1, 2 ** s) for _ in range(r)]
        rk, bas = rank_rows(H)
        checks, nvar = build(H, s)
        g, vid = to_graph(checks, nvar, s)
        grp = pynauty.autgrp(g)
        gens = grp[0]
        order = grp[1] * 10 ** grp[2]
        # data pattern of a generator: bit j flips iff W j 0 -> W j 1
        pats = []
        for p in gens:
            pat = 0
            for j in range(s):
                a = vid[('W', j, 0)]; b = vid[('W', j, 1)]
                if p[a] == b:
                    pat |= 1 << j
                elif p[a] != a:
                    pat = None; break
            if pat is None: break
            pats.append(pat)
        expect = 2 ** (s - rk)
        # code ker H: dual check
        def in_code(pat):
            return all(bin(pat & row).count('1') % 2 == 0 for row in H)
        all_code = pats is not None and all(in_code(p) for p in pats)
        rk2, _ = rank_rows([p for p in pats])
        g2, vid2 = tanglegram_graph(checks, nvar, s)
        grp2 = pynauty.autgrp(g2)
        order2 = grp2[1] * 10 ** grp2[2]
        # flip patterns on the data pairs inside the tanglegram (with child 2 attached)
        pats2 = []
        for p in grp2[0]:
            pat = 0
            for j in range(s):
                a_ = vid2[('T2pair', j, 0)]; b_ = vid2[('T2pair', j, 1)]
                if p[a_] == b_:
                    pat |= 1 << j
                else:
                    assert p[a_] == a_
            pats2.append(pat)
        tg_code = all(in_code(p) for p in pats2)
        rk3, _ = rank_rows(pats2)
        good = (round(order) == expect) and all_code and rk2 == s - rk and round(order2) == expect and tg_code and rk3 == s - rk
        tot += 1; ok += int(good)
        print(f"s={s} r={r} rankH={rk} nvar={nvar} n={g.number_of_vertices} |Aut|={order} expected={expect} patterns_in_code={all_code} patterns_rank={rk2} expected_rank={s-rk} tanglegram_|Aut|={order2} tg_patterns_in_code={tg_code} tg_rank={rk3} tg_n={g2.number_of_vertices} {'OK' if good else 'BAD'}")
print(f"{ok}/{tot}")
