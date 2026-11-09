#!/usr/bin/env python3
"""w45: checks for the graph gadget H_h and the pattern-space stabilizer lemma.
Pure Python. Usage: check_graph.py [hmax]"""
import itertools, sys

def Hgraph(h):
    """H_h: bipartite on X_0..X_{h-1}, Y_0..Y_{h-1}; 2h-cycle X_iY_i, X_{i+1}Y_i
    plus chords X_0-Y_3 and X_1-Y_5 (indices mod h; matches doc with shifted labels)."""
    E=set()
    for i in range(h):
        E.add((i,i)); E.add(((i+1)%h,i))
    E.add((0,3)); E.add((1,5))
    return E

def adj(E,h):
    nx={i:set() for i in range(h)}; ny={i:set() for i in range(h)}
    for x,y in E: nx[x].add(y); ny[y].add(x)
    return nx,ny

def c4_free(E,h):
    nx,_=adj(E,h)
    return all(len(nx[a]&nx[b])<=1 for a,b in itertools.combinations(range(h),2))

def connected(E,h):
    nx,ny=adj(E,h)
    seen={('x',0)}; st=[('x',0)]
    while st:
        s,v=st.pop()
        for w in (nx[v] if s=='x' else ny[v]):
            t=('y' if s=='x' else 'x',w)
            if t not in seen: seen.add(t); st.append(t)
    return len(seen)==2*h

def side_auts(E,h):
    """All side-preserving automorphisms of bipartite graph, by backtracking on X with Y forced."""
    nx,ny=adj(E,h)
    Es=set(E); res=[]
    def rec(px):
        i=len(px)
        if i==h:
            # derive py: y -> the unique vertex adjacent appropriately; brute over consistency
            # py(y) must be such that N(py(y))=px(N(y)); determined when neighbourhoods distinct
            py={}
            for y in range(h):
                img=frozenset(px[x] for x in ny[y])
                cands=[v for v in range(h) if frozenset(ny[v])==img]
                if not cands: return
                py[y]=cands
            # all neighbourhoods distinct in C4-free min-deg-2 graph, so at most one candidate each
            ys=[c[0] for c in py.values()]
            if len(set(ys))==h and all((px[x],py[y][0]) in Es for x,y in E):
                res.append((tuple(px),tuple(ys)))
            return
        for v in range(h):
            if v in px: continue
            if len(nx[v])!=len(nx[i]): continue
            # pruning: common-neighbour counts with previously assigned
            if any(len(nx[i]&nx[j])!=len(nx[v]&nx[px[j]]) for j in range(i)): continue
            rec(px+[v])
    rec([])
    return res

def gl_elts(n):
    """All elements of GL(n,2) as tuples of column ints."""
    out=[]
    def rec(cols,span):
        if len(cols)==n: out.append(tuple(cols)); return
        for v in range(1,1<<n):
            if v in span: continue
            ns=set(span)|{s^v for s in span}
            rec(cols+[v],ns)
    rec([],{0})
    return out

def stabilizer_count(E,hx,hy):
    """Pairs (g,gp) in GL(hx,2)xGL(hy,2) with g Sp(H) gp^T = Sp(H).
    Sp(H)=matrices supported on E. Column j of gp is constrained independently."""
    Es=set(E)
    def in_sp(a,b):
        # a is hx-bit vector, b hy-bit vector; rank-one a b^T in Sp?
        return all((i,j) in Es for i in range(hx) if a>>i&1 for j in range(hy) if b>>j&1)
    ny={j:[x for x,y in E if y==j] for j in range(hy)}
    gls=gl_elts(hx); perms=0; total=0; bad=0
    # g acts: rows of matrix in Sp multiplied; g E_ij gp^T = (g e_i)(gp e_j)^T
    for g in gls:
        allowed=[]
        for j in range(hy):
            al=[v for v in range(1,1<<hy) if all(in_sp(g[i],v) for i in ny[j])]
            allowed.append(al)
        if not all(allowed): continue
        for combo in itertools.product(*allowed):
            # invertibility of combo as hy x hy matrix
            span={0}; ok=True
            for v in combo:
                if v in span: ok=False;break
                span|={s^v for s in span}
            if not ok: continue
            total+=1
            is_perm=all(bin(c).count('1')==1 for c in g) and all(bin(c).count('1')==1 for c in combo)
            if is_perm: perms+=1
            else: bad+=1
    return total,perms,bad

if __name__=='__main__':
    hmax=int(sys.argv[1]) if len(sys.argv)>1 else 40
    for h in range(9,hmax+1):
        E=Hgraph(h)
        a=side_auts(E,h)
        assert c4_free(E,h) and connected(E,h), h
        assert all(sum(1 for e in E if e[0]==i)>=2 for i in range(h))
        assert all(sum(1 for e in E if e[1]==j)>=2 for j in range(h))
        assert len(a)==1, (h,len(a))
    print("H_h: C4-free, connected, min-deg>=2, trivial side-automorphism group for h=9..%d"%hmax)
    # stabilizer lemma exhaustive on small graphs
    cases={ 'C6(3,3)':([(0,0),(1,0),(1,1),(2,1),(2,2),(0,2)],3,3),
            'C8(4,4)':([(i,i) for i in range(4)]+[((i+1)%4,i) for i in range(4)],4,4)}
    for name,(E,hx,hy) in cases.items():
        t,p,b=stabilizer_count(E,hx,hy)
        print(name,'stabilizer pairs',t,'permutation pairs',p,'non-permutation',b)
