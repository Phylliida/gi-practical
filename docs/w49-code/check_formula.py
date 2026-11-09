#!/usr/bin/env python3
"""w49: verify the codegree formula lambda(v)=|S cap (S+v)| for S=R1 u H, classes by (rank,Q)."""
import sys
sys.path.insert(0,'.')
from construct import *
def predict(d,e):
    m=d*e//2; C=2**(2*m-2)-2**(m-1); r=(2**d-1)*(2**e-1)
    tau=lambda rho:(2**d-2**(d-rho))*2**(e-1)
    c=lambda rho:{1:2**d+2**e-4,2:6}.get(rho,0)
    out={}
    for rho in range(1,e+1):
        out[(rho,0)]=c(rho)+2*tau(rho)+C if rho==1 else None
        out[(rho,1)]=c(rho)+2*(r-tau(rho))+C
    return out
for d,e in [(4,2),(6,2),(4,4)]:
    R1,H=connection_set(d,e); S=R1|H
    L=lambdas(d,e,S); P=predict(d,e)
    print((d,e)); 
    for k,v in L.items():
        rho,q,ins=k
        pr=P.get((rho,q)) if ins else None
        print(k,"lam=",v,"pred(if in S)=",pr, "OK" if (pr is None or pr==v) else "MISMATCH")
