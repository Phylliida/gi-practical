"""Homotopy certificate for the referee's strengthening of Theorem A: k = 3.
Runs the recolouring on random closed walks in Gamma_F(K_b) and checks every elementary move.
Moves are 'replace a subpath A by B' with A + reverse(B) a closed walk in the graph having <=3 values per coordinate, and
insertion/deletion of backtracks.  So the final walk differs from the input by lassos on 3-narrow closed walks.
The input walk is arbitrary; nothing here is sampled except the walks."""
import random, sys, itertools


class G:
    def __init__(self, b, M, F):
        self.b, self.M = b, M
        self.F = {frozenset(I) for I in F}

    def diff(self, u, v):
        return frozenset(j for j in range(self.M) if u[j] != v[j])

    def edge(self, u, v):
        return self.diff(u, v) in self.F

    def narrow(self, tile, k=3):
        return all(len({v[j] for v in tile}) <= k for j in range(self.M))

    def check_tile(self, tile):
        assert tile[0] == tile[-1]
        assert all(self.edge(a, c) for a, c in zip(tile, tile[1:])), ("non-edge in tile", tile)
        assert self.narrow(tile), ("wide tile", tile)


def setv(v, j, x):
    w = list(v)
    w[j] = x
    return tuple(w)


class Walk:
    def __init__(self, g, path):
        self.g, self.p = g, list(path)
        self.moves = 0

    def replace(self, i, A, B):
        assert self.p[i:i + len(A)] == list(A)
        assert A[0] == B[0] and A[-1] == B[-1]
        self.g.check_tile(list(A) + list(reversed(B))[1:])
        self.p[i:i + len(A)] = list(B)
        self.moves += 1

    def insert_backtrack(self, i, x):
        assert self.g.edge(self.p[i], x)
        self.p[i + 1:i + 1] = [x, self.p[i]]
        self.moves += 1

    def delete_backtrack(self, i):
        assert self.p[i] == self.p[i + 2]
        del self.p[i + 1:i + 3]
        self.moves += 1


def third(g, *avoid):
    return next(x for x in range(g.b) if x not in avoid)


def subdivide(g, w, j):
    i = 0
    while i < len(w.p) - 1:
        v, u = w.p[i], w.p[i + 1]
        if v[j] != u[j] and v[j] != 0 and u[j] != 0:
            I = g.diff(v, u)
            y = list(v)
            for l in I:
                # keep processed coordinates inside {0,1,2}
                y[l] = 0 if l == j else third(g, v[l], u[l])
            y = tuple(y)
            w.replace(i, [v, u], [v, y, u])
            i += 2
        else:
            i += 1


def rotate_to_zero(w, j):
    i = next(k for k, v in enumerate(w.p) if v[j] == 0)
    w.p = w.p[i:] + w.p[1:i + 1]


def recolour_coordinate(g, w, j):
    if len({v[j] for v in w.p}) == 1:
        return
    I0 = next(g.diff(a, c) for a, c in zip(w.p, w.p[1:]) if a[j] != c[j])
    subdivide(g, w, j)
    rotate_to_zero(w, j)
    i = 1
    while i < len(w.p):
        c = w.p[i][j]
        if c in (0, 1):
            i += 1
            continue
        s = i
        t = s
        while w.p[t + 1][j] == c:
            t += 1
        n_run = t - s + 1
        assert w.p[s - 1][j] == 0 and w.p[t + 1][j] == 0
        p = w.p
        run = p[s:t + 1]
        prime = lambda x: setv(x, j, 1)
        left = p[s - 1]
        # initial rung at s is the vertex v_{s-1}; state path from index s: v_s', w, v_s, v_{s+1}, ...
        w.insert_backtrack(s - 1, prime(run[0]))
        pos = s  # position of v_i'
        cur_rung = left
        for q in range(n_run - 1):
            vi, vn = run[q], run[q + 1]
            # hexagon rungs with <=2 values off j
            ri = list(vi)
            rn = list(vn)
            ri[j] = 0
            rn[j] = 0
            for l in I0:
                if l == j:
                    continue
                if vi[l] != vn[l]:
                    ri[l], rn[l] = vn[l], vi[l]
                else:
                    z = third(g, vi[l])
                    ri[l], rn[l] = z, z
            ri, rn = tuple(ri), tuple(rn)
            assert g.diff(ri, vi) == I0 and g.diff(rn, vn) == I0 and I0 in g.F
            # rung change at q if needed
            if cur_rung != ri:
                w.replace(pos, [prime(vi), cur_rung, vi], [prime(vi), ri, vi])
            # hexagon: replace (vi', ri, vi, vn) by (vi', vn', rn, vn)
            w.replace(pos, [prime(vi), ri, vi, vn], [prime(vi), prime(vn), rn, vn])
            pos += 1
            cur_rung = rn
        # final rung change to v_{t+1} and delete backtrack
        last = run[-1]
        nxt = w.p[pos + 3]
        if cur_rung != nxt:
            w.replace(pos, [prime(last), cur_rung, last], [prime(last), nxt, last])
        w.delete_backtrack(pos + 1)
        assert w.p[pos][j] == 1 and w.p[pos + 1] == nxt
        i = pos + 1


def certify(b, M, F, L, rng):
    g = G(b, M, F)
    start = tuple(rng.randrange(b) for _ in range(M))
    # random walk then close it with a path through a spanning search
    F_list = list(g.F)
    p = [start]
    for _ in range(L):
        v = p[-1]
        I = rng.choice(F_list)
        u = list(v)
        for j in I:
            u[j] = rng.choice([x for x in range(b) if x != v[j]])
        p.append(tuple(u))
    # close by walking back along a random path of pattern steps if possible, else retrace (retrace is still a closed walk)
    p = p + p[-2::-1]
    # perturb the retrace so that the walk is not null-homotopic: splice random triangles
    for _ in range(L // 2):
        i = rng.randrange(len(p) - 1)
        v, u = p[i], p[i + 1]
        I = g.diff(v, u)
        y = list(v)
        for l in I:
            y[l] = rng.choice([x for x in range(b) if x not in (v[l], u[l])])
        p[i + 1:i + 1] = [tuple(y)]
    assert all(g.edge(a, c) for a, c in zip(p, p[1:])) and p[0] == p[-1]
    w = Walk(g, p)
    for j in range(M):
        recolour_coordinate(g, w, j)
    assert all(g.edge(a, c) for a, c in zip(w.p, w.p[1:])) and w.p[0] == w.p[-1]
    vals = [len({v[j] for v in w.p}) for j in range(M)]
    assert max(vals) <= 3, vals
    return w.moves, len(p), max(vals)


if __name__ == "__main__":
    rng = random.Random(1)
    tot = 0
    mv = 0
    wid = 0
    for trial in range(int(sys.argv[1]) if len(sys.argv) > 1 else 3000):
        b = rng.randint(3, 9)
        M = rng.randint(1, 6)
        subs = [c for r in range(1, M + 1) for c in itertools.combinations(range(M), r)]
        F = rng.sample(subs, rng.randint(1, min(len(subs), 6)))
        m, l, v = certify(b, M, F, rng.randint(3, 40), rng)
        tot += 1
        mv += m
        wid = max(wid, v)
    print(f"certified {tot} random closed walks; total elementary moves {mv}; all tiles closed, edges present, <=3 values per coordinate; final walks <=3 values (max seen {wid})")
