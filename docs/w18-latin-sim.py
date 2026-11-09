#!/usr/bin/env python
"""HJ LocalCertificate windows, bipartite model of PG(m-1,2): positions W x P.
level 0: G = Sym(W) x Sym(P), T subset P.
level 1: G = Sym(Wt1) x H_1 on Wt1 x P_1, T subset Q_1 (cosets of D_1).
Sampled affected tests per position type; nauty group computations."""
import sys, time, math, random
from pynauty import Graph, autgrp
random.seed(7)
def span(vs):
    S={0}
    for v in vs: S|={s^v for s in S}
    return S
def closure(gens,k):
    idn=tuple(range(k))
    seen={idn}; fr=[idn]
    while fr:
        nx=[]
        for a in fr:
            for g in gens:
                b=tuple(g[x] for x in a)
                if b not in seen: seen.add(b); nx.append(b)
        fr=nx
    return seen
def even(p):
    seen=[False]*len(p); s=1
    for i in range(len(p)):
        if not seen[i]:
            l=0;j=i
            while not seen[j]: seen[j]=True;j=p[j];l+=1
            if l%2==0: s=-s
    return s==1
def altsize(k): return math.factorial(k)//2
class Bip:
    def __init__(s,W,P,adj,labelled,tlabels,kappa):
        # W,P lists of objects; adj set of (w,p) objects; labelled: list of (label,p1,p2)
        # tlabels: dict p-> label index on T (for phi) or None
        s.W=W; s.P=P; s.nW=len(W); s.nP=len(P); s.wid={w:i for i,w in enumerate(W)}
        s.pid={p:i for i,p in enumerate(P)}
        s.adj={(s.wid[w],s.pid[p]) for w,p in adj}
        s.lab=[(l,s.pid[a],s.pid[b]) for l,a,b in labelled]
        s.kappa=kappa; s.window=set()
        s.tlab={s.pid[p]:v for p,v in tlabels.items()}
        s.Tp=sorted(s.tlab)
    def nv(s): return s.nW+2*s.nP+len(s.lab)
    def auto(s,classesW,classesP,indivW=(),indivP=()):
        nP=s.nP
        activeW=sorted({w for w,p in s.window}|set(indivW))
        nW=len(activeW)
        widx={w:i for i,w in enumerate(activeW)}
        nv=nW+2*nP+len(s.lab)
        ad={i:[] for i in range(nv)}
        for p in range(nP): ad[nW+p].append(nW+nP+p)
        for (w,p) in s.window:
            ad[widx[w]].append(nW+nP+p)
            if (w,p) in s.adj: ad[widx[w]].append(nW+p)
        mids=[]
        for i,(l,a,b) in enumerate(s.lab):
            m=nW+2*nP+i; mids.append((l,m))
            ad[nW+a].append(m); ad[nW+b].append(m)
        cols=[]
        indivWs=set(indivW); indivPs=set(indivP)
        for c in classesW:
            r=[widx[x] for x in c if x in widx and x not in indivWs]
            if r: cols.append(set(r))
        cols+= [{widx[w]} for w in indivW]
        for c in classesP:
            r=[x for x in c if x not in indivPs]
            if r: cols.append({nW+x for x in r}); cols.append({nW+nP+x for x in r})
        for p in indivP: cols.append({nW+p}); cols.append({nW+nP+p})
        labs={}
        for l,m in mids: labs.setdefault(l,set()).add(m)
        cols+= list(labs.values())
        g=Graph(nv,directed=False,adjacency_dict=ad,vertex_coloring=cols)
        res=autgrp(g)
        # Project generators to actions on P (layer 0) indices, with offset nW
        gens=[[gv-nW if nW<=gv<nW+nP else None for gv in gen[nW:nW+nP]] for gen in res[0]]
        return gens,res[1],res[2]
    def phi_gens(s,gens):
        ims=[]
        for g in gens:
            ims.append(tuple(s.lab2index(g[s.first[v]]) for v in range(s.kappa)))
        return ims
    def lab2index(s,pid_): return s.tlab[pid_]
    def prepare_first(s):
        s.first={}
        for p,v in s.tlab.items():
            if v not in s.first: s.first[v]=p
    def imgAlt(s,gens):
        ims=s.phi_gens(gens)
        im=closure(ims,s.kappa)
        return sum(1 for p in im if even(p))>=altsize(s.kappa), im
def lines(m):
    L=set()
    for a in range(1,1<<m):
        for b in range(a+1,1<<m): L.add(tuple(sorted((a,b,a^b))))
    return sorted(L)
def run(level,m,kappa,samples):
    B=lines(m)
    if level==0:
        Wt=B; P=list(range(1,1<<m)); T=[1<<i for i in range(kappa)]
        D2=span(T); Sigma=0
        for t in T: Sigma^=t
        Sset={Sigma}; D1={0}; labelled=[]; cosetT={t:i for i,t in enumerate(T)}
        desc={}
        def ptype(p):
            if p in cosetT: return "pT"
            if p in Sset: return "pS"
            if p in D2: return "pD*"
            return "P+"
    else:
        D1=span([1<<i for i in range(kappa)]); Sigma0=(1<<kappa)-1; Z={Sigma0}
        Wt=[b for b in B if not (set(b)&(D1-Z-{0}))]
        P=[p for p in range(1,1<<m) if p not in D1]
        T1=[1<<(kappa+i) for i in range(kappa)]
        D2=span([1<<i for i in range(2*kappa)])
        cosetT={}
        for i,t in enumerate(T1):
            for d in D1: cosetT[t^d]=i
        Sigma=0
        for t in T1: Sigma^=t
        Sset={Sigma^d for d in D1}
        labelled=[]
        for i in range(kappa):
            d=1<<i
            for p in P:
                if p<(p^d): labelled.append((i,p,p^d))
        def ptype(p):
            if p in cosetT: return "pT"
            if p in Sset: return "pS"
            if p in D2: return "pD*"
            return "P+"
    tset=set(cosetT)
    def btype(b):
        s=set(b)
        if s&tset: return "bT"
        z=Sset|{0}
        o={x for x in s&D2 if x not in z and x not in D1}
        if o: return "bD*"
        if s&Sset: return "bS"
        return "bF"
    adj=[(b,p) for b in Wt for p in b if p in P or (level==0)]
    Pset=set(P)
    adj=[(b,p) for b in Wt for p in b if p in Pset]
    sim=Bip(Wt,P,adj,labelled,cosetT,kappa)
    sim.prepare_first()
    if level==0:
        classesP=[sorted(tset and {sim.pid[p] for p in tset}), sorted({sim.pid[p] for p in P if p not in tset})]
    else:
        tverts={sim.pid[p] for p in tset}
        classesP=[sorted(tverts), sorted({sim.pid[p] for p in P if p not in tset})]
    classesW=[sorted(range(len(Wt)))]
    vtW={sim.wid[b]:btype(b) for b in Wt}
    vtP={sim.pid[p]:ptype(p) for p in P}
    allpos=[(sim.wid[b],sim.pid[p]) for b in Wt for p in P]
    print(f"level{level} m={m} kappa={kappa} |W|={len(Wt)} |P|={len(P)} |Omega|={len(allpos)} |D_next|={len(D2)}",flush=True)
    t0=time.time(); step=0
    while step<14:
        gens,g1,g2=sim.auto(classesW,classesP)
        ok,im=sim.imgAlt(gens)
        print(f"step {step}: |A|~{g1:.3g}e{g2} imageAlt={ok} |W_window|={len(sim.window)} (t={time.time()-t0:.1f})",flush=True)
        if not ok: print("NONFULL"); return
        rest=[p for p in allpos if p not in sim.window]
        if not rest: print("window complete -> FULL"); return
        types={}
        for (w,p) in rest: types.setdefault((vtW[w],vtP[p]),[]).append((w,p))
        aff={}
        for key,plist in sorted(types.items()):
            sample=random.sample(plist,min(samples,len(plist)))
            res=[]
            for (w,p) in sample:
                sg,_,_=sim.auto(classesW,classesP,(w,),(p,))
                res.append(not sim.imgAlt(sg)[0])
            if all(res): aff[key]=True
            elif any(res): aff[key]="mixed:"+str(sum(res))+"/"+str(len(res))
        E=[k for k in aff]
        if E:
            for k in E: sim.window|=set(types[k])
            print("  V[affected]:",[(k,len(types[k]),aff[k]) for k in E],flush=True)
            step+=1; continue
        Wv={w for w,p in rest}; Pv={p for w,p in rest}
        sg,_,_=sim.auto(classesW,classesP,sorted(Wv),sorted(Pv))
        if sim.imgAlt(sg)[0]: print("step3: K onto Alt -> FULL"); return
        print("  step3: phi(K) proper. Step 4:",flush=True)
        vis={}
        for key,plist in sorted(types.items()):
            Dw={w for w,p in plist}; Dp={p for w,p in plist}
            sg,_,_=sim.auto(classesW,classesP,sorted(Dw),sorted(Dp))
            vis[key]=(len(closure(sim.phi_gens(sg),kappa))==1)
        names=[k for k,v in vis.items() if v]
        print("  V[VISIBLE]:",[(k,len(types[k])) for k in names],"invisible:",[k for k,v in vis.items() if not v],flush=True)
        if not names: print("none"); return
        for k in names: sim.window|=set(types[k])
        step+=1

def run_ls(m,kappa,samples):
    """Level-0 instance for LS(Z_2^m): W = Off cells (a,b), R = 3 lines through (0,0)."""
    V=range(1,1<<m)
    Wt=[(a,b) for a in V for b in V if a!=b]
    def hedge(a,b):
        return [('R',b),('R',a^b),('C',a),('C',a^b),('S',a),('S',b)]
    P=[(l,x) for l in 'RCS' for x in V]
    T=[1<<i for i in range(kappa)]
    Tp=[('R',t) for t in T]
    D=span(T); Sigma=0
    for t in T: Sigma^=t
    cosetT={('R',t):i for i,t in enumerate(T)}
    def ptype(p):
        l,x=p
        if p in cosetT: return "pT:"+l
        if x==Sigma: return "pS:"+l
        if x in D: return "pD*:"+l
        return "P+:"+l
    tset=set(cosetT)
    Dpts={('R',x) for x in D if x!=0}|{('C',x) for x in D if x!=0}|{('S',x) for x in D if x!=0}
    def btype(w):
        e=set(hedge(*w))
        if e&tset: return "bT"
        o={p for p in e&Dpts if p[1]!=Sigma}
        if o: return "bD*"
        if e&Dpts: return "bS"
        return "bF"
    adj=[(w,p) for w in Wt for p in hedge(*w)]
    sim=Bip(Wt,P,adj,[],cosetT,kappa)
    sim.prepare_first()
    tverts={sim.pid[p] for p in tset}
    classesP=[sorted(tverts),sorted({sim.pid[p] for p in P if p not in tset})]
    classesW=[sorted(range(len(Wt)))]
    vtW={sim.wid[b]:btype(b) for b in Wt}
    vtP={sim.pid[p]:ptype(p) for p in P}
    allpos=[(sim.wid[b],sim.pid[p]) for b in Wt for p in P]
    print(f"LS level0 m={m} kappa={kappa} |W|={len(Wt)} |R|={len(P)} |Omega|={len(allpos)}",flush=True)
    t0=time.time(); step=0
    while step<14:
        gens,g1,g2=sim.auto(classesW,classesP)
        ok,im=sim.imgAlt(gens)
        print(f"step {step}: |A|~{g1:.3g}e{g2} imageAlt={ok} |Wind|={len(sim.window)} (t={time.time()-t0:.1f})",flush=True)
        if not ok: print("NONFULL"); return
        rest=[p for p in allpos if p not in sim.window]
        if not rest: print("window complete -> FULL"); return
        types={}
        for (w,p) in rest: types.setdefault((vtW[w],vtP[p]),[]).append((w,p))
        aff={}
        for key,plist in sorted(types.items()):
            sample=random.sample(plist,min(samples,len(plist)))
            res=[]
            for (w,p) in sample:
                sg,_,_=sim.auto(classesW,classesP,(w,),(p,))
                res.append(not sim.imgAlt(sg)[0])
            if all(res): aff[key]=True
            elif any(res): aff[key]="mixed:"+str(sum(res))+"/"+str(len(res))
        E=[k for k in aff]
        if E:
            for k in E: sim.window|=set(types[k])
            print("  V[affected]:",[(k,len(types[k]),aff[k]) for k in E],flush=True)
            step+=1; continue
        Wv={w for w,p in rest}; Pv={p for w,p in rest}
        sg,_,_=sim.auto(classesW,classesP,sorted(Wv),sorted(Pv))
        if sim.imgAlt(sg)[0]: print("step3: K onto Alt -> FULL"); return
        print("  step3: phi(K) proper. Step 4:",flush=True)
        vis={}
        for key,plist in sorted(types.items()):
            Dw={w for w,p in plist}; Dp={p for w,p in plist}
            sg,_,_=sim.auto(classesW,classesP,sorted(Dw),sorted(Dp))
            vis[key]=(len(closure(sim.phi_gens(sg),kappa))==1)
        names=[k for k,v in vis.items() if v]
        print("  V[VISIBLE]:",[(k,len(types[k])) for k in names],"invisible:",[k for k,v in vis.items() if not v],flush=True)
        if not names: print("none"); return
        for k in names: sim.window|=set(types[k])
        step+=1

def run_blockgraph(m,kappa,samples):
    """Level-0 instance for block graph of PG(m-1,2): R = blocks through point of w0={1,2,3}
    (other than w0), W = blocks disjoint from w0, adjacency = intersection."""
    B=lines(m)
    w0=(1,2,3); s0=set(w0)
    R=[b for b in B if set(b)&s0 and b!=w0]
    Wt=[b for b in B if not (set(b)&s0)]
    # T' = kappa blocks through point 1: {1, a, a^1} with a = 2^(2+i)
    T=[]
    for i in range(kappa):
        a=1<<(2+i)
        T.append(tuple(sorted((1,a,a^1))))
    assert all(t in R for t in T), T
    D=span([1,2]+[1<<(2+i) for i in range(kappa)])  # contains span of T's and w0
    cosetT={t:i for i,t in enumerate(T)}
    def rtype(r):
        if r in cosetT: return "rT"
        pts=set(r)-s0
        if len(pts&D)>=1: return "rD"
        return "rF"
    def wtype(w):
        pts=set(w)
        if pts & {x for t in T for x in t}: return "wT"
        if pts&D: return "wD"
        return "wF"
    adjm={}
    adj=[]
    for w in Wt:
        sw=set(w)
        for r in R:
            if sw&set(r): adj.append((w,r))
    sim=Bip(Wt,R,adj,[],cosetT,kappa)
    sim.prepare_first()
    tverts={sim.pid[p] for p in cosetT}
    classesP=[sorted(tverts),sorted({sim.pid[p] for p in R if p not in cosetT})]
    classesW=[sorted(range(len(Wt)))]
    vtW={sim.wid[b]:wtype(b) for b in Wt}
    vtP={sim.pid[p]:rtype(p) for p in R}
    allpos=[(sim.wid[b],sim.pid[p]) for b in Wt for p in R]
    print(f"STSblock level0 m={m} kappa={kappa} |W|={len(Wt)} |R|={len(R)} |Omega|={len(allpos)}",flush=True)
    t0=time.time(); step=0
    while step<14:
        gens,g1,g2=sim.auto(classesW,classesP)
        ok,im=sim.imgAlt(gens)
        print(f"step {step}: |A|~{g1:.3g}e{g2} imageAlt={ok} |Wind|={len(sim.window)} (t={time.time()-t0:.1f})",flush=True)
        if not ok: print("NONFULL"); return
        rest=[p for p in allpos if p not in sim.window]
        if not rest: print("window complete -> FULL"); return
        types={}
        for (w,p) in rest: types.setdefault((vtW[w],vtP[p]),[]).append((w,p))
        aff={}
        for key,plist in sorted(types.items()):
            sample=random.sample(plist,min(samples,len(plist)))
            res=[]
            for (w,p) in sample:
                sg,_,_=sim.auto(classesW,classesP,(w,),(p,))
                res.append(not sim.imgAlt(sg)[0])
            if all(res): aff[key]=True
            elif any(res): aff[key]="mixed:"+str(sum(res))+"/"+str(len(res))
        E=[k for k in aff]
        if E:
            for k in E: sim.window|=set(types[k])
            print("  V[affected]:",[(k,len(types[k]),aff[k]) for k in E],flush=True)
            step+=1; continue
        Wv={w for w,p in rest}; Pv={p for w,p in rest}
        sg,_,_=sim.auto(classesW,classesP,sorted(Wv),sorted(Pv))
        if sim.imgAlt(sg)[0]: print("step3: K onto Alt -> FULL"); return
        print("  step3: phi(K) proper. Step 4:",flush=True)
        vis={}
        for key,plist in sorted(types.items()):
            Dw={w for w,p in plist}; Dp={p for w,p in plist}
            sg,_,_=sim.auto(classesW,classesP,sorted(Dw),sorted(Dp))
            vis[key]=(len(closure(sim.phi_gens(sg),kappa))==1)
        names=[k for k,v in vis.items() if v]
        print("  V[VISIBLE]:",[(k,len(types[k])) for k in names],"invisible:",[k for k,v in vis.items() if not v],flush=True)
        if not names: print("none"); return
        for k in names: sim.window|=set(types[k])
        step+=1

if __name__=="__main__":
    if sys.argv[1]=="stsb": run_blockgraph(int(sys.argv[2]),int(sys.argv[3]),1)
    elif sys.argv[1]=="ls": run_ls(int(sys.argv[2]),int(sys.argv[3]),int(sys.argv[4]) if len(sys.argv)>4 else 1)
    else: run(int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]),int(sys.argv[4]) if len(sys.argv)>4 else 2)
