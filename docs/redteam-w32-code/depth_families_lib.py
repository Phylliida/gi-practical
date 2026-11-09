"""Exact 1-WL depth on algebraic families, with independently computed Aut orders (dreadnaut).
Lower bounds: k=1 is never discrete (proved); k=2 ruled out exhaustively on pairs or by |Aut| > n^2;
upper bounds are explicit witnesses checked by exact refinement."""
import sys, itertools, random, subprocess, time, re
sys.path.insert(0, '.')
from rt_common import *

DREADNAUT = "/nix/store/4kd2j9xhcgz2p6msmflmr81pqms9cy05-nauty-2.9.1/bin/dreadnaut"

def dread_graph(A):
    n = len(A)
    lines = [f'n={n} $=0 g']
    for i in range(n):
        nb = ' '.join(str(j) for j in np.nonzero(A[i])[0] if j > i)
        lines.append(f'{i}: {nb};')
    return '\n'.join(lines) + '\n'

def aut_info(A, fixed=()):
    """(group order as a float, #orbits, orbits list of the pointwise stabilizer of `fixed`)."""
    n = len(A)
    s = 'l=0 -a -m\n' + dread_graph(A)
    if fixed:
        s += 'f=[' + ' | '.join(str(x) for x in fixed) + ']\n'
    s += 'x o q\n'
    out = subprocess.run([DREADNAUT], input=s, capture_output=True, text=True, timeout=7200).stdout
    m = re.search(r'grpsize=([0-9.e+]+)', out)
    orb = re.search(r'(\d+) orbits?;', out)
    return float(m.group(1)), int(orb.group(1)) if orb else None, out

def conf(A):
    return is_conference_graph(A)

def field_logs(F):
    g = F.generator(); log = {}; x = 1
    for i in range(F.q - 1):
        log[x] = i; x = F.mul1(x, g)
    return g, log

def cyclotomic_graph(q, N, classes):
    F = Field(q); g, log = field_logs(F)
    S = np.zeros(q, dtype=bool)
    for x, k in log.items():
        if k % N in classes: S[x] = True
    A = S[F.sub_table()].astype(np.uint8)
    return A

def peisert(q):
    return cyclotomic_graph(q, 4, {0, 1})

def lines_graph(q, lineset):
    F = Field(q); n = q * q
    D1 = F.sub_table()
    idx = lambda x, y: x * q + y
    S = np.zeros(n, dtype=bool)
    for L in lineset:
        for t in range(1, q):
            if L == q: S[idx(0, t)] = True
            else: S[idx(t, F.mul1(L, t))] = True
    A = np.zeros((n, n), dtype=np.uint8)
    for a in range(n):
        ax, ay = a // q, a % q
        for b in range(n):
            bx, by = b // q, b % q
            A[a, b] = S[idx(int(D1[ax, bx]), int(D1[ay, by]))]
    return A


def canon_string(A):
    """nauty canonical graph of A as a string (only the relabelled adjacency lines of `b`)."""
    s = 'c -a -m l=0\n' + dread_graph(A) + 'x b q\n'
    out = subprocess.run([DREADNAUT], input=s, capture_output=True, text=True, timeout=3600).stdout
    lines = out.split('\n')
    body = []; on = False
    for l in lines:
        ls = l.strip()
        if ls.startswith('0 :') or ls.startswith('0:'): on = True
        if on and ls: body.append(ls)
    return ' '.join(body)
