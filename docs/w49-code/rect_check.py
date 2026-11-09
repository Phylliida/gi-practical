#!/usr/bin/env python3
"""w49 Lemma L': Aut(B) of the first rectangle (W,R1; rank(w-r)=e-1) of the d-by-e bilinear forms scheme.

Vertices: W = injective d-by-e matrices (rank e), R1 = (a,b), a in V\\0, b in U\\0.
N(M) = {(M phi, b) : phi in U*, b in U, phi(b)=1}.  Expected |Aut(B)| = |GL(d,2)| |GL(e,2)|.
Run: rect_check.py d e [sparse]"""
import sys, subprocess, time
DREADNAUT = "/nix/store/4kd2j9xhcgz2p6msmflmr81pqms9cy05-nauty-2.9.1/bin/dreadnaut"

def glorder(k):
    o=1
    for i in range(k):
        o*=(2**k-2**i)
    return o

def apply(rows,phi):
    # rows: d ints (e-bit columns each is one row of M). (M phi)_i = parity(rows[i] & phi)
    a=0
    for i,r in enumerate(rows):
        if bin(r&phi).count('1')%2: a|=1<<i
    return a

def main():
    d,e=int(sys.argv[1]),int(sys.argv[2]); sparse=len(sys.argv)>3
    vecs=[v for v in range(1,1<<d)]
    # enumerate injective M as e columns c_1..c_e in V, independent
    W=[]
    def rec(cols,span):
        if len(cols)==e:
            W.append(tuple(cols)); return
        for v in range(1,1<<d):
            if v not in span:
                ns=span|{s^v for s in span}|{v}
                rec(cols+[v],ns)
    rec([],{0})
    # column basis -> M as columns; M phi = xor of columns j with phi_j=1
    nR=(2**d-1)*(2**e-1)
    def rid(a,b): return (a-1)*(2**e-1)+(b-1)
    nW=len(W); n=nW+nR
    pairs=[]  # phi,b with phi(b)=1
    for phi in range(1,1<<e):
        for b in range(1,1<<e):
            if bin(phi&b).count('1')%2==1: pairs.append((phi,b))
    t0=time.time()
    with open(f"/tmp/claude-1000/-home-bepis-math/117a2777-2472-4276-845a-e0dfeb712755/scratchpad/w49_rect_{d}_{e}.dre","w") as f:
        f.write(("As\n" if sparse else "")+f"n={n} $=0 g\n")
        for wi,cols in enumerate(W):
            nb=set()
            for phi,b in pairs:
                a=0
                for j in range(e):
                    if phi>>j &1: a^=cols[j]
                nb.add(nW+rid(a,b))
            f.write(f"{wi}: "+" ".join(map(str,sorted(nb)))+";\n")
        # R vertices: no outgoing needed (edges given as undirected by dreadnaut g input lists)
        for ri in range(nW,n):
            f.write(f"{ri}: ;\n")
        f.write("-m\n$$\n")
    fn=f.name
    print(f"(d,e)=({d},{e}) W={nW} R={nR} n={n} expected={glorder(d)*glorder(e)} built in {time.time()-t0:.1f}s",flush=True)
    cmd=f"nice -n 19 timeout 3000 {DREADNAUT}"
    # need 'x' command; append
    inp=open(fn).read().replace("$$\n","")+"x\nq\n"
    r=subprocess.run(cmd,input=inp,shell=True,capture_output=True,text=True)
    for line in r.stdout.splitlines():
        if "grpsize" in line: print(line)
    if r.stderr: print("ERR",r.stderr[:500])

main()
