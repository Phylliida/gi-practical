#!/usr/bin/env python3
"""w45: for alternating 4-forms tau on F_2^d: smallest random t (and spans of functionals
tau(u_i,u_j,u_k,.)) and sampled min pair-contraction rank. Pure Python. Usage: check_pins.py"""
import itertools, random
def rank(M):
    M=list(M); r=0
    for b in range(64):
        p=None
        for k in range(r,len(M)):
            if M[k]>>b&1: p=k;break
        if p is None: continue
        M[r],M[p]=M[p],M[r]
        for k in range(len(M)):
            if k!=r and M[k]>>b&1: M[k]^=M[r]
        r+=1
    return r
def gamma4(tau,d,a,b):
    """alternating matrix tau(a,b,.,.) as list of d ints (rows). tau: set of sorted 4-tuples."""
    M=[0]*d
    bits_a=[i for i in range(d) if a>>i&1]; bits_b=[i for i in range(d) if b>>i&1]
    for q in tau:
        S=q
        for x,y in itertools.permutations(S,2):
            if a>>x&1 and b>>y&1:
                rest=[v for v in S if v!=x and v!=y]
                M[rest[0]]^=1<<rest[1]; M[rest[1]]^=1<<rest[0]
    return M
def functional(tau,d,u,v,w):
    """row vector tau(u,v,w,.)"""
    M=gamma4(tau,d,u,v)
    r=0
    for c in range(d):
        bit=bin(M[c]&w).count('1')&1
        if bit: r|=1<<c
    return r
def minpins(tau,d,rng,tmax=None):
    tmax=tmax or d
    us=[rng.randrange(1,1<<d) for _ in range(tmax)]
    fs=[]
    for t in range(1,tmax+1):
        for i,j in itertools.combinations(range(t-1),2):
            fs.append(functional(tau,d,us[i],us[j],us[t-1]))
        if t>=3 and fs and rank(fs)==d: return t
    return None
def sample_minpair(tau,d,rng,n=400):
    m=d
    for _ in range(n):
        a=rng.randrange(1,1<<d); b=rng.randrange(1,1<<d)
        if a==b: continue
        m=min(m,rank(gamma4(tau,d,a,b)))
    return m
def fam(name,d,rng):
    if name=='random':
        return {q for q in itertools.combinations(range(d),4) if rng.random()<.5}
    if name=='disjoint':
        return {tuple(range(i,i+4)) for i in range(0,d-3,4)}
    if name=='prod2':  # 2 pair-products: top form of q1*q2, q random (disjoint halves)
        h=d//2; t=set()
        for a,b in itertools.combinations(range(h),2):
            for c,e in itertools.combinations(range(h,d),2):
                if rng.random()<.5: t.add((a,b,c,e))
        return t
    if name=='lowchain':  # x_1 x_2 * (random quadratic on rest): low "2+2"
        rest=range(2,d)
        return {(0,1,a,b) for a,b in itertools.combinations(rest,2) if rng.random()<.5}
    if name=='radical': # random form on first d-3 coordinates only
        return {q for q in itertools.combinations(range(d-3),4) if rng.random()<.5}
rng=random.Random(5)
for d in (10,12,14):
    for name in ('random','disjoint','prod2','lowchain','radical'):
        res=[]
        for _ in range(4):
            tau=fam(name,d,rng)
            t=minpins(tau,d,rng,tmax=d)
            s=sample_minpair(tau,d,rng,150)
            res.append((t,s))
        print(f"d={d:2d} {name:9s} (min random pins t, sampled min pair rank s):",res)
