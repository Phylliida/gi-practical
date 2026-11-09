#!/usr/bin/env python3
"""w49: build the tensor/symplectic Cayley graph x=Cay(V(x)U, R1 u H) and related objects.

V=F_2^d, U=F_2^e (d,e even).  Vertices = d-by-e binary matrices M (ints: bit (i,j)=M[i][j]).
R1 = pure tensors a(x)b (rank 1).  Q(M)=sum_{t,s} det of the 2x2 minor on the t-th
hyperbolic pair of rows and s-th hyperbolic pair of columns: the tensor quadratic form
polarizing to omega(x)omega', vanishing on pure tensors.  H=Q^{-1}(1).
"""
import itertools, subprocess, sys
DREADNAUT = "/nix/store/4kd2j9xhcgz2p6msmflmr81pqms9cy05-nauty-2.9.1/bin/dreadnaut"

def bit(d,e,i,j): return 1 << (i*e+j)

def mat(d,e,M):
    return [[(M>>(i*e+j))&1 for j in range(e)] for i in range(d)]

def rank(d,e,M):
    rows=[(M>>(i*e)) & ((1<<e)-1) for i in range(d)]
    r=0
    for j in range(e):
        p=None
        for i in range(r,d):
            if rows[i]>>j &1: p=i;break
        if p is None: continue
        rows[r],rows[p]=rows[p],rows[r]
        for i in range(d):
            if i!=r and rows[i]>>j &1: rows[i]^=rows[r]
        r+=1
    return r

def Q(d,e,M):
    q=0
    for t in range(d//2):
        a,a_=2*t,2*t+1
        for s in range(e//2):
            b,b_=2*s,2*s+1
            m=lambda i,j:(M>>(i*e+j))&1
            q^= (m(a,b)&m(a_,b_))^(m(a,b_)&m(a_,b))
    return q

def pure_tensors(d,e):
    S=set()
    for a in range(1,1<<d):
        for b in range(1,1<<e):
            M=0
            for i in range(d):
                if a>>i &1:
                    M |= b<<(i*e)
            S.add(M)
    return S

def connection_set(d,e):
    R1=pure_tensors(d,e)
    H={M for M in range(1,1<<(d*e)) if Q(d,e,M)==1}
    assert not (R1&H)
    return R1,H

def lambdas(d,e,S):
    n=1<<(d*e)
    # lambda(v)=|S cap (S+v)|, by class reps of (rank,Q)
    Sset=set(S)
    reps={}
    for v in range(1,n):
        k=(rank(d,e,v),Q(d,e,v),v in Sset)
        reps.setdefault(k,v)
    out={}
    for k,v in sorted(reps.items()):
        out[k]=sum(1 for s in Sset if (s^v) in Sset)
    return out

def aut_group(d,e,S):
    n=1<<(d*e)
    lines=[f"n={n} $=0 g"]
    for v in range(n):
        lines.append(f"{v}: "+" ".join(str(v^s) for s in S if (v^s)>v)+";")
    lines.append(".")
    lines.append("-m x")  # no vertex-invariant output suppressed; print automorphisms off
    inp="\n".join(lines)+"\nq\n"
    r=subprocess.run([DREADNAUT],input=inp,capture_output=True,text=True,timeout=3000)
    return r.stdout

if __name__=="__main__":
    d=int(sys.argv[1]); e=int(sys.argv[2])
    R1,H=connection_set(d,e)
    S=R1|H
    print(f"(d,e)=({d},{e}) n={1<<(d*e)} |R1|={len(R1)} |H|={len(H)} |S|={len(S)}")
    if d*e<=16:
        print("lambda by (rank,Q,inS):",lambdas(d,e,S))
    if d*e<=12:
        out=aut_group(d,e,S)
        for line in out.splitlines():
            if "grpsize" in line or "automorphism" in line.lower():
                print(line)
