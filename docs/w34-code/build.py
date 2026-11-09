#!/usr/bin/env python3
# build.py: writes graphs in vctool format using w32 generators.
import sys, os, bz2
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'w32-code'))
import gen
root='/tmp/claude-1000/-home-bepis-math/117a2777-2472-4276-845a-e0dfeb712755/scratchpad/r4-sources/w32-spence-data'
def out(name, A):
    n=len(A); print("G",name); print(n)
    for r in A: print("".join(str(c) for c in r))
def seidel(A): return gen.seidel_of_adj(A)
def adj(B): return gen.adj_of_seidel(B)
if __name__=='__main__':
    kind=sys.argv[1]
    if kind=='paley':
        for q in sys.argv[2:]:
            q=int(q); out(f"paley{q}", gen.paley(q))
    elif kind=='turyn':
        # turyn base levels: base = skewNN or qNN
        spec=sys.argv[2]; levels=int(sys.argv[3])
        if spec.startswith('skew'): V=gen.paley_skew(int(spec[4:]))
        else: V=gen.seidel_of_adj(gen.paley(int(spec)))
        cur=V
        for L in range(1,levels+1):
            cur=gen.turyn(cur,cur)
            out(f"turyn_{spec}_L{L}", adj(cur))
    elif kind=='spence':
        n=int(sys.argv[2]); limit=int(sys.argv[3]) if len(sys.argv)>3 else None
        p,nv=gen.spence_files(root)[n]
        gs=list(gen.parse_spence(p,nv))
        if limit: gs=gs[:limit]
        for i,A in enumerate(gs): out(f"sp{n}_{i}",A)
