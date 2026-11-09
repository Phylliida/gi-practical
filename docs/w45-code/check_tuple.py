#!/usr/bin/env python3
"""w45: test harness for Theorem T (tuple-of-cubics -> quadratic form space, GL(a) on the tuple index).
Forms on N variables: upper-triangular coefficient sets {(i,j): i<=j}, formal quadratic forms over F_2.
Pure Python. Usage: check_tuple.py [trials]"""
import random, itertools, sys
def form_compose(Q,S,N):
    """Q as set of (i,j) i<=j. S as list of N row-bitmasks: x'_i = S[i].x. Return Q(Sx) as formal form."""
    out=set()
    for (i,j) in Q:
        a=S[i]; b=S[j]
        for p in range(N):
            if a>>p&1:
                for q in range(N):
                    if b>>q&1:
                        k=(min(p,q),max(p,q))
                        out ^= {k}
    return out
def polar(Q,N):
    M=[0]*N
    for (i,j) in Q:
        if i!=j: M[i]^=1<<j; M[j]^=1<<i
    return M
def rank(M):
    M=list(M); r=0
    for bit in range(64):
        piv=None
        for k in range(r,len(M)):
            if M[k]>>bit&1: piv=k;break
        if piv is None: continue
        M[r],M[piv]=M[piv],M[r]
        for k in range(len(M)):
            if k!=r and M[k]>>bit&1: M[k]^=M[r]
        r+=1
    return r
def span_vec(forms):
    """reduce list of frozensets to a canonical echelon basis (over F_2), return frozenset of basis tuples"""
    keys=sorted({k for f in forms for k in f})
    idx={k:i for i,k in enumerate(keys)}
    vecs=[sum(1<<idx[k] for k in f) for f in forms]
    # gaussian elimination to RREF
    basis={}
    for v in vecs:
        for p in sorted(basis,reverse=True):
            if v>>p&1: v^=basis[p]
        if v:
            p=v.bit_length()-1
            for q in list(basis):
                if basis[q]>>p&1: basis[q]^=v
            basis[p]=v
    return frozenset(basis.values()),keys
def same_span(A,B):
    # compare via combined key set
    allk=sorted({k for f in A+B for k in f})
    idx={k:i for i,k in enumerate(allk)}
    def rr(fs):
        basis={}
        for f in fs:
            v=sum(1<<idx[k] for k in f)
            for p in sorted(basis,reverse=True):
                if v>>p&1: v^=basis[p]
            if v:
                p=v.bit_length()-1
                for q in list(basis):
                    if basis[q]>>p&1: basis[q]^=v
                basis[p]=v
        return frozenset(basis.items())
    return rr(A)==rr(B)
# Boolean poly of degree <=3 on n vars: dict mono->1 where mono is a sorted tuple
def rand_cubic(n,rng):
    f=set()
    for r in (1,2,3):
        for m in itertools.combinations(range(n),r):
            if rng.random()<0.45: f.add(m)
    return f
def poly_compose(f,L,n):
    """f(Lx) with L list of n row-bitmasks; output multilinear ANF"""
    out=set()
    for m in f:
        # product of (L[i].x) over i in m
        terms={()}
        for i in m:
            new=set()
            for t in terms:
                for v in range(n):
                    if L[i]>>v&1:
                        t2=tuple(sorted(set(t+(v,))))
                        new ^= {t2}
            terms=new
        out^=terms
    return out
def poly_add(fs):
    r=set()
    for f in fs: r^=f
    return r
def rand_gl(n,rng):
    while True:
        M=[rng.randrange(1,1<<n) for _ in range(n)]
        if rank(M)==n: return M
def mat_mul(A,B,n):  # rows: (AB)[i]=sum_j A_ij B[j]
    return [ __x for __x in [ (lambda r: __reduce(r,B))(A[i]) for i in range(n)] ]
def __reduce(r,B):
    v=0
    for j in range(len(B)):
        if r>>j&1: v^=B[j]
    return v
def transpose(A,n):
    out=[0]*n
    for i in range(n):
        for j in range(n):
            if A[i]>>j&1: out[j]|=1<<i
    return out
def inverse(A,n):
    M=[A[i]|(1<<(n+i)) for i in range(n)]
    for col in range(n):
        piv=next(k for k in range(col,n) if M[k]>>col&1)
        M[col],M[piv]=M[piv],M[col]
        for k in range(n):
            if k!=col and M[k]>>col&1: M[k]^=M[col]
    return [M[i]>>n for i in range(n)]
# Gamma_e_k of cubic part: Gamma_a(x)=sum over monomials ijk (a_i x_j x_k + x_i a_j x_k + x_i x_j a_k)
# as formal quadratic form in x, zero diagonal
def Gamma_of(fi,n,a):
    Q=set()
    for m in fi:
        if len(m)!=3: continue
        i,j,k=m
        if a>>i&1: Q^={(j,k)}
        if a>>j&1: Q^={(i,k)}
        if a>>k&1: Q^={(i,j)}
    return Q
def lowparts(fi,n):
    Q=set(); ell=set()
    for m in fi:
        if len(m)==2: Q^={m}
        if len(m)==1: ell^={(m[0],m[0])}   # linear x_i recorded as diagonal (x_i^2)
    return Q,ell
def build_Phi(fs,n):
    """Phi on N=n(a+1) vars: x_0..x_{n-1}, u^{(i)}_k = n+i*n+k."""
    a=len(fs); N=n*(a+1); forms=[]
    for i,fi in enumerate(fs):
        for k in range(n):
            e=1<<k
            Q=Gamma_of(fi,n,e)^{(n+i*n+k,n+i*n+k)}
            forms.append(frozenset(Q))
        Qf,ell=lowparts(fi,n)
        cross={(t,n+i*n+t) for t in range(n)}
        forms.append(frozenset(Qf^ell^cross))
    return forms,N
def build_S(fs,L,n):
    """pinned map: S(x,u)=(Lx, L^{-T}u^{(i)}+C_i x), C_i=L^{-T} N^i, N^i_{bj}=Gamma^{f_i}_{Le_b}(Le_j).
    L given as rows over x; returns list of N rows for substitution x'_v=S[v].(x,u)."""
    a=len(fs); N=n*(a+1); Linv=inverse(L,n); Lit=transpose(Linv,n)
    S=[0]*N
    for v in range(n):  # x_v -> (Lx)_v
        S[v]=L[v]
    # images of basis Le_b need columns of L: Lcol[b] = bitmask over x index v with L[v]>>b&1
    Lcol=[sum(((L[v]>>b)&1)<<v for v in range(n)) for b in range(n)]
    for i,fi in enumerate(fs):
        # N^i matrix b,j
        Nm=[]
        for b in range(n):
            Gq=Gamma_of(fi,n,Lcol[b])
            row=0
            for j in range(n):
                # evaluate form Gq at Lcol[j]
                val=0
                for (p,q) in Gq:
                    val^=(Lcol[j]>>p&1)&(Lcol[j]>>q&1)
                if val: row|=1<<j
            Nm.append(row)
        C=[__reduce(Lit[b],Nm) for b in range(n)]  # C=L^{-T}N: row b = sum_c Lit[b,c] Nm[c]
        for k in range(n):
            var=n+i*n+k
            # u^{(i)}_k -> (L^{-T}u^{(i)}+C_i x)_k
            r=C[k]  # x-part, bits 0..n-1
            for t in range(n):
                if Lit[k]>>t&1: r|=1<<(n+i*n+t)
            S[var]=r
    return S,N
def main(trials,seed=1):
    rng=random.Random(seed); ok=0
    for T in range(trials):
        n=rng.choice([4,5,6]); a=rng.choice([1,2,3])
        fs=[rand_cubic(n,rng) for _ in range(a)]
        # conciseness: common radical of tau_f_i is 0
        # test: find x!=0 with all Gamma_x polars zero
        def commonrad(fs):
            for x in range(1,1<<n):
                if all(not polar(Gamma_of(fi,n,x),n)==[0]*n and False or all(v==0 for v in polar(Gamma_of(fi,n,x),n)) for fi in fs):
                    return True
            return False
        if commonrad(fs): continue
        L=rand_gl(n,rng)
        gs=[poly_compose(fi,L,n) for fi in fs]  # g_i = f_i o L
        Phif,N=build_Phi(fs,n); Phig,_=build_Phi(gs,n)
        S,_=build_S(fs,L,n)
        comp=[frozenset(form_compose(q,S,N)) for q in Phif]
        assert same_span(comp,[frozenset(q) for q in Phig]), ("pinned forward failed",n,a,T)
        # rank claims
        Q_only=[q for idx,q in enumerate(Phif) if (idx+1)%(n+1)!=0]
        for _ in range(30):
            comb=set()
            for q in Q_only:
                if rng.random()<0.5: comb^=q
            assert rank(polar(comb,N))<=n, 'Q rank'
        F_only=[q for idx,q in enumerate(Phif) if (idx+1)%(n+1)==0]
        for _ in range(30):
            comb=set(); pick=0
            for fi,q in enumerate(F_only):
                if rng.random()<0.5: comb^=q; pick+=1
            if not pick: continue
            for q in Q_only:
                if rng.random()<0.5: comb^=q
            assert rank(polar(comb,N))>=2*n, 'F rank'
        # radical of Phi_Q = U (check dimension via combined polars rowspace: U-dim= N-n)
        Ms=[]
        for q in Q_only:
            Ms.extend(polar(q,N))
        assert rank(Ms)==n, 'radical dim'
        ok+=1
    print("forward+rank+radical passed on",ok,"concise instances of",trials,"trials")
    # mixed beta action: g_i = sum_j beta_ij (f_j o L). Check Phi(f)oS o T_beta = Phi(g)?
    rng=random.Random(seed+1); okb=0; tries=0
    for T in range(trials):
        n=rng.choice([4,5]); a=rng.choice([2,3])
        fs=[rand_cubic(n,rng) for _ in range(a)]
        L=rand_gl(n,rng); beta=rand_gl(a,rng)
        gs=[poly_add([poly_compose(fs[j],L,n) for j in range(a) if beta[i]>>j&1]) for i in range(a)]
        Phif,N=build_Phi(fs,n); Phig,_=build_Phi(gs,n)
        S,_=build_S(fs,L,n)
        comp=[frozenset(form_compose(q,S,N)) for q in Phif]
        # now need relabel of u-blocks: try the two candidates beta^{-1} and beta^{-T}
        tries+=1
        for name,M in (('inv',inverse(beta,a)),('invT',transpose(inverse(beta,a),a)),('beta',beta),('betaT',transpose(beta,a))):
            # T: u'^{(i)} = sum_j M_ij u^{(j)}, x unchanged
            Trow=[0]*N
            for v in range(n): Trow[v]=1<<v
            for i in range(a):
                for k in range(n):
                    r=0
                    for j in range(a):
                        if M[i]>>j&1: r|=1<<(n+j*n+k)
                    Trow[n+i*n+k]=r
            c2=[frozenset(form_compose(q,Trow,N)) for q in comp]
            if same_span(c2,[frozenset(q) for q in Phig]):
                okb+=1; 
                if T==0: print("mixed case: relabel via",name)
                break
    print("mixed beta case: matched",okb,"of",tries)
if __name__=='__main__':
    main(int(sys.argv[1]) if len(sys.argv)>1 else 60)
