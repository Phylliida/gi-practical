#!/usr/bin/env python3
"""Lemma L: nauty's generators of Aut(W,R;meet) are all induced by linear maps in GL(V)_ell.
Generators in GL(V)_ell plus 'the generators generate Aut' gives Aut(B) = image of GL(V)_ell
exactly, a stronger statement than comparing orders.  Uses the dreadnaut binary directly."""
import sys, subprocess, re
import pg

DREADNAUT = "/nix/store/4kd2j9xhcgz2p6msmflmr81pqms9cy05-nauty-2.9.1/bin/dreadnaut"

def build(m):
    W, R = pg.classify(m)
    pts_of_r = [set(r) for r in R]
    inc = {}
    for i, r in enumerate(R):
        for p in r:
            inc.setdefault(p, []).append(i)
    adj = []
    for w in W:
        nb = set()
        for p in w:
            for i in inc.get(p, []):
                nb.add(i)
        adj.append(sorted(nb))
    return W, R, adj

def run_nauty(nW, nR, adj):
    V = nW + nR
    lines = [f"n={V} g"]
    for i, nb in enumerate(adj):
        lines.append(f"{i}: " + " ".join(str(nW + j) for j in nb) + ";")
    lines.append(".")
    lines.append("x")
    lines.append("o")
    lines.append("q")
    out = subprocess.run([DREADNAUT], input="\n".join(lines), capture_output=True, text=True, timeout=1500)
    return out.stdout

def parse(out, V):
    # generator cycles are printed in lines before 'grpsize'; collect those starting with '('
    gens = []
    buf = ""
    gs = None
    for ln in out.splitlines():
        s = ln.strip()
        if ln.startswith("("):            # a new generator starts in column 0
            if buf:
                gens.append(buf)
            buf = s
        elif ln.startswith("   (") and buf:  # continuation of the current generator
            buf += " " + s
        else:
            if buf:
                gens.append(buf)
                buf = ""
            mm = re.search(r"grpsize=([0-9.e+*^]+)", ln)
            if mm:
                gs = mm.group(1)
    if buf:
        gens.append(buf)
    perms = []
    for g in gens:
        p = list(range(V))
        for cyc in re.findall(r"\(([^)]*)\)", g):
            c = [int(t) for t in cyc.split()]
            for i in range(len(c)):
                p[c[i]] = c[(i + 1) % len(c)]
        perms.append(p)
    return perms, gs

def reconstruct(m, W, R, sigma):
    nW = len(W)
    Wsets = [frozenset(w) for w in W]
    Rsets = [frozenset(r) for r in R]
    idxW = {w: i for i, w in enumerate(Wsets)}
    idxR = {r: i for i, r in enumerate(Rsets)}
    # lines through each point
    thru = {}
    for i, w in enumerate(Wsets):
        for x in w:
            thru.setdefault(x, []).append(i)
    g = {}
    for x, ws in thru.items():
        a, b = ws[0], ws[1]
        img_a = Wsets[sigma[a]]
        img_b = Wsets[sigma[b]]
        inter = img_a & img_b
        if len(inter) != 1:
            return False, f"point {x}: images of two lines do not meet in one point"
        g[x] = next(iter(inter))
    # consistency with all W lines
    for i, w in enumerate(Wsets):
        if frozenset(g[x] for x in w) != Wsets[sigma[i]]:
            return False, "W line not mapped by g"
    # ell labels
    ell = {1, 2, 3}
    # pick x not in ell; for p in ell, label by g[x]^g[x^p]
    x0 = 4
    labels = {}
    for p in ell:
        q = g[x0] ^ g[x0 ^ p]
        labels[p] = q
    if set(labels.values()) != ell:
        return False, "ell not preserved"
    for p, q in labels.items():
        g[p] = q
    # additivity over all pairs
    pts = list(range(1, 1 << m))
    for a in pts:
        for b in pts:
            if a != b:
                if a ^ b == 0:
                    continue
                if g[a ^ b] != g[a] ^ g[b]:
                    return False, f"not additive at {a},{b}"
    # check action on R
    for i, r in enumerate(Rsets):
        img = frozenset(g[x] for x in r)
        if img != Rsets[sigma[nW + i] - nW]:
            return False, "R action mismatch"
    return True, g

def main():
    for m in [int(a) for a in sys.argv[1:]]:
        W, R, adj = build(m)
        out = run_nauty(len(W), len(R), adj)
        perms, gs = parse(out, len(W) + len(R))
        print(f"m={m}: |W|={len(W)} |R|={len(R)} nauty generators={len(perms)} grpsize={gs}")
        ok = True
        for k, p in enumerate(perms):
            # the sides must be preserved
            if any(p[i] >= len(W) for i in range(len(W))):
                print("  generator", k, "swaps sides"); ok = False; break
            good, res = reconstruct(m, W, R, p)
            if not good:
                print("  generator", k, "FAILS:", res); ok = False; break
        target = pg.gl_order(m) // (((1 << m) - 1) * ((1 << (m - 1)) - 1) // 3)
        print(f"  all generators induced by GL(V)_ell: {ok}; |GL(V)_ell|={target}")

if __name__ == "__main__":
    main()
