"""Independent harness for the red team of docs/w49-pruned.md.

Written from the memo's *statements*, not its scripts.  Matrices are d-by-e binary, encoded as
ints with bit (i*e+j) = entry (i,j); columns are read as vectors of F_2^d, rows as vectors of
F_2^e.  Q is built here from the polar form on the elementary tensor basis, independently of the
author's sum-of-minors formula, and the equality of the two is checked by tests in this file's
__main__.
"""
import itertools, subprocess, sys

DREADNAUT = "/nix/store/4kd2j9xhcgz2p6msmflmr81pqms9cy05-nauty-2.9.1/bin/dreadnaut"
GAP = "/nix/store/c3j0pyb3skjp6f8bqaxfajhzj6864y9l-gap-4.15.1/bin/gap"

def row_masks(M, d, e):
    return [(M >> (i * e)) & ((1 << e) - 1) for i in range(d)]

def rank_rows(rows):
    rows = list(rows); r = 0
    for bit in range(64):
        piv = next((i for i in range(r, len(rows)) if rows[i] >> bit & 1), None)
        if piv is None: continue
        rows[r], rows[piv] = rows[piv], rows[r]
        for i in range(len(rows)):
            if i != r and rows[i] >> bit & 1: rows[i] ^= rows[r]
        r += 1
        if r == len(rows): break
    return r

def rank(M, d, e): return rank_rows(row_masks(M, d, e))

def omega(k):
    """standard symplectic form on F_2^k as a k-by-k bit matrix (dict of (i,j)->1)."""
    return {(2*t, 2*t+1) for t in range(k//2)} | {(2*t+1, 2*t) for t in range(k//2)}

def beta(M, Mp, d, e):
    """omega(x)omega' applied to matrices M,Mp."""
    om = omega(d); om2 = omega(e); v = 0
    for (i, ip) in om:
        for (j, jp) in om2:
            v ^= ((M >> (i*e+j)) & 1) & ((Mp >> (ip*e+jp)) & 1)
    return v

def Q_table(d, e):
    """The unique quadratic form with polar form omega(x)omega', vanishing on the basis E_ij:
    Q(sum c_ij E_ij) = sum_{(i,j)<(i',j') in basis order} beta(E_ij,E_i'j') c_ij c_i'j'.
    Returns an list of length 2^(de)."""
    n = d*e
    pol = []  # pairs (u,v) of basis indices, u<v, with beta(E_u,E_v)=1
    om = omega(d); om2 = omega(e)
    for u in range(n):
        iu, ju = u//e, u%e
        for v in range(u+1, n):
            iv, jv = v//e, v%e
            if ((iu, iv) in om) and ((ju, jv) in om2):
                pol.append((u, v))
    tab = bytearray(1 << n)
    # incremental: gray-code style dynamic programming on the top bit
    for M in range(1, 1 << n):
        top = M.bit_length() - 1
        rest = M ^ (1 << top)
        par = tab[rest]
        for (u, v) in pol:
            if v == top and (rest >> u) & 1: par ^= 1
        tab[M] = par
    return tab

def pure_tensors(d, e):
    out = {}
    for a in range(1, 1 << d):
        for b in range(1, 1 << e):
            M = 0
            for i in range(d):
                if a >> i & 1: M |= b << (i*e)
            out[M] = (a, b)
    return out

def glorder(k):
    o = 1
    for i in range(k): o *= (2**k - 2**i)
    return o

def sporder(k):
    m = k//2; o = 2**(m*m)
    for i in range(1, m+1): o *= 4**i - 1
    return o

def injective_matrices(d, e):
    """all rank-e d-by-e matrices, as ints; columns are independent vectors of F_2^d."""
    out = []
    def rec(cols, span):
        if len(cols) == e:
            M = 0
            for j, c in enumerate(cols):
                for i in range(d):
                    if c >> i & 1: M |= 1 << (i*e + j)
            out.append(M); return
        for v in range(1, 1 << d):
            if v in span: continue
            rec(cols + [v], span | {s ^ v for s in span})
    rec([], {0})
    return out

def run_dreadnaut(edge_lists, partition=None, sparse=True, want_gens=False, timeout=3000):
    """edge_lists: list (index=vertex) of iterables of neighbours (undirected, any repeated ok).
    Returns (grpsize, orbits_text/gens text)."""
    n = len(edge_lists)
    lines = [("As" if sparse else "") + (" -a" if not want_gens else " +a"), f"n={n} $=0 g"]
    for v, nb in enumerate(edge_lists):
        lines.append(" ".join(str(u) for u in nb if u > v) + ";")
    lines.append(".")  # end of graph marker not needed but harmless to some versions
    # write in the format dreadnaut expects: after 'g', one line per vertex terminated by ';' and final '.'
    inp = "\n".join(lines)
    if partition:
        inp += "\nf=[" + " | ".join(" ".join(map(str, c)) for c in partition) + "]"
    inp += "\nx\nq\n"
    r = subprocess.run(["nice", "-n", "19", "timeout", str(timeout), DREADNAUT],
                       input=inp, capture_output=True, text=True)
    return r.stdout, r.stderr

if __name__ == "__main__":
    # sanity: Q equals the sum-of-2x2-minors definition and vanishes on pure tensors
    def Q_minors(M, d, e):
        q = 0
        for t in range(d//2):
            for s in range(e//2):
                a, a2 = 2*t, 2*t+1; b, b2 = 2*s, 2*s+1
                m = lambda i, j: (M >> (i*e+j)) & 1
                q ^= (m(a,b) & m(a2,b2)) ^ (m(a,b2) & m(a2,b))
        return q
    for d, e in [(2,2),(4,2),(4,4),(6,2)]:
        tab = Q_table(d, e)
        for M in range(1 << (d*e)):
            assert tab[M] == Q_minors(M, d, e), (d, e, M)
        for M in pure_tensors(d, e): assert tab[M] == 0
        print(f"(d,e)=({d},{e}): Q (from polar form on tensor basis) == sum of minors; zero on R1")
