#!/usr/bin/env python3
"""Exact nauty computations, written independently of docs/w49-code:
  bil d e        : |Aut(Cay(Phi,R1))| vs 2^{de}|GL(d)||GL(e)| (with vertex 0 not fixed)
  x d e          : |Aut(Cay(Phi,R1 u H))| vs 2^{de}|Sp(d)||Sp(e)|
  rect d e [b c] : |Aut(B_{b,c})| for B=(W,R_b; rk(w-r)=c), default (b,c)=(1,e-1); for (1,e-1) every
                   generator is reconstructed as a pair of linear maps (alpha,gamma) and verified
"""
import sys, subprocess, re
from common import *

def run(lines_of_adj, want_gens=False):
    n = len(lines_of_adj)
    inp = ["As", ("" if want_gens else "-a"), "-m", f"n={n} $=0 g"]
    for v, nbrs in enumerate(lines_of_adj):
        inp.append(f"{v}: " + " ".join(map(str, sorted(u for u in nbrs if u > v))) + ";")
    inp.append(".")
    inp.append("x")
    inp.append("q")
    r = subprocess.run(["nice", "-n", "19", "timeout", "3000", DREADNAUT], input="\n".join(inp) + "\n",
                       capture_output=True, text=True)
    return r.stdout

def grpsize(out):
    m = re.search(r"grpsize=([^;]+);", out.replace("\n", " "))
    return m.group(1) if m else None

def size_to_int(s):
    s = s.strip()
    if "*" in s:  # form a*10^b (nauty prints e.g. 3.2e14 or 3.2*10^14 for large)
        pass
    return s

def parse_gens(out):
    gens = []; cur = None
    # generators are printed one per line of cycles "(0 1)(2 3)"; a generator may wrap across lines
    buf = out.replace("\n   ", " ").split("\n")
    for line in buf:
        if line.lstrip().startswith("("):
            cycles = re.findall(r"\(([^)]*)\)", line)
            p = {}
            for c in cycles:
                pts = list(map(int, c.split()))
                for x, y in zip(pts, pts[1:] + pts[:1]): p[x] = y
            gens.append(p)
    return gens

def bil(d, e):
    n = 1 << (d*e); R = list(pure_tensors(d, e))
    print(f"Bil({d},{e}) n={n} deg={len(R)} expected={2**(d*e)*glorder(d)*glorder(e)}", flush=True)
    adj = [[v ^ r for r in R] for v in range(n)]
    out = run(adj); print("  grpsize", grpsize(out))

def xgraph(d, e):
    n = 1 << (d*e); R = pure_tensors(d, e); Qt = Q_table(d, e)
    S = sorted(set(R) | {M for M in range(1, n) if Qt[M]})
    print(f"x({d},{e}) n={n} deg={len(S)} expected={2**(d*e)*sporder(d)*sporder(e)}", flush=True)
    adj = [[v ^ s for s in S] for v in range(n)]
    out = run(adj); print("  grpsize", grpsize(out))

def rect(d, e, b=1, c=None, verify=True):
    if c is None: c = e-1
    W = injective_matrices(d, e); Wi = {M: i for i, M in enumerate(W)}
    # R_b = rank b matrices
    all_mats = range(1, 1 << (d*e))
    Rb = [M for M in all_mats if rank(M, d, e) == b]
    Ri = {M: i for i, M in enumerate(Rb)}
    nW = len(W); nR = len(Rb)
    print(f"B({d},{e};b={b},c={c}): |W|={nW} |R|={nR} expected GLxGL={glorder(d)*glorder(e)}", flush=True)
    adj = [[] for _ in range(nW + nR)]
    edges = 0
    for wi, w in enumerate(W):
        for r in Rb:
            if rank(w ^ r, d, e) == c:
                ri = Ri[r]; adj[wi].append(nW + ri); adj[nW + ri].append(wi); edges += 1
    print(f"  edges={edges}", flush=True)
    out = run(adj, want_gens=(b == 1 and c == e-1 and verify))
    print("  grpsize", grpsize(out), flush=True)
    if b == 1 and c == e-1 and verify:
        check_linear(out, d, e, W, Wi, Rb, Ri, nW)

def check_linear(out, d, e, W, Wi, Rb, Ri, nW):
    gens = parse_gens(out)
    # numeric group size from the printed grpsize
    ok = 0
    tensors = {M: k for M, k in pure_tensors(d, e).items()}
    # basis of V, U
    for p in gens:
        fx = lambda x: p.get(x, x)
        # image of pure tensor (a,b)
        def img(a, b):
            M = 0
            for i in range(d):
                if a >> i & 1: M |= b << (i*e)
            return tensors[Rb[fx(nW + Ri[M]) - nW]]
        # alpha from a=e_i with b=1; gamma from a=1,b=e_j
        alpha = [img(1 << i, 1)[0] for i in range(d)]
        gamma = [img(1, 1 << j)[1] for j in range(e)]
        # alpha, gamma must be linear: alpha(a) = xor of alpha(e_i).  Verify on all pairs (a,b) and on W.
        def apply_lin(lin, x):
            y = 0
            for i, c in enumerate(lin):
                if x >> i & 1: y ^= c
            return y
        for a in range(1, 1 << d):
            for b in range(1, 1 << e):
                assert img(a, b) == (apply_lin(alpha, a), apply_lin(gamma, b)), "not a linear (alpha,gamma) on R1"
        # W action: M-> alpha M gamma^T, i.e. (M phi) -> alpha M (phi o gamma)
        for wi, w in enumerate(W):
            img_w = W[fx(wi)]
            # Check: pushing N_B. For (a,b) adjacent to w: image adjacent to img_w; equivalent to formula
            # M' = alpha M gamma^T: M'_ij = sum_{k,l} alpha_ik M_kl gamma_jl ... computed via action on (phi,b)
            # build M' explicitly
            rows = [0]*d
            # column view: M = list of e columns in F_2^d.  gamma^T acts on columns: col'_j = sum_l gamma(e_j)_l col_l ?
            cols = [0]*e
            for j in range(e):
                c_ = 0
                for i in range(d):
                    if (w >> (i*e + j)) & 1: c_ |= 1 << i
                cols[j] = c_
            # col'_j' := alpha(sum_j [gamma^{-T}]...) -- instead test the defining relation below
            # relation: rk(w + r)=e-1 iff rk(img_w + fx(r))=e-1 is implied by nauty; test identity of M':
            # we derive M' by phi-values: (M phi, b) in N(w) -> (alpha M phi, gamma b) in N(img).
            # so img_w(phi o gamma^{-1}) = alpha(w(phi)); check on phi = basis:
            # compute gamma inverse via search
            ginv = {apply_lin(gamma, b): b for b in range(1, 1 << e)}
            def w_apply(m, phi):  # phi as bitmask of e bits; M phi = xor of columns j with phi_j=1
                v = 0
                for j in range(e):
                    if phi >> j & 1:
                        c_ = 0
                        for i in range(d):
                            if (m >> (i*e + j)) & 1: c_ |= 1 << i
                        v ^= c_
                return v
            for phi in range(1, 1 << e):
                # phi o gamma^{-1} as bitmask: value at e_j is phi(gamma^{-1}(e_j))
                pg = 0
                for j in range(e):
                    if bin(ginv[1 << j] & phi).count("1") % 2: pg |= 1 << j
                assert w_apply(img_w, pg) == apply_lin(alpha, w_apply(w, phi)), "W action not M->alpha M gamma^*"
        ok += 1
    print(f"  all {ok}/{len(gens)} nauty generators reconstructed as (alpha,gamma) linear, acting as M->alpha M gamma^* on W", flush=True)

if __name__ == "__main__":
    mode = sys.argv[1]; args = list(map(int, sys.argv[2:]))
    {"bil": bil, "x": xgraph, "rect": rect}[mode](*args)
