"""Canonicity fuzz on graphs of max degree <= 5 (and a few above): forms under relabelling, nauty cross-check,
counters canon_ir / canon_luks_fallback, for many structured families."""
import os, sys as _s
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
_s.path.insert(0, ROOT); _s.path.insert(0, HERE)

import sys, random, time, itertools, json, signal
sys.path.insert(0, ROOT)
sys.setrecursionlimit(100000)
from collections import Counter
import networkx as nx
import pynauty
from gi.canon import canonical_form_lists, canonical_labeling_lists, canonical_form_lists as cf
from bench import irhard
from bench.adversary import cfi3, tree_matching, add_triple

def nauty_cert(nbr, col=None):
    n=len(nbr)
    if n==0: return b''
    if col is None:
        vc=[set(range(n))]
    else:
        d={}
        for v,c in enumerate(col): d.setdefault(c,set()).add(v)
        vc=[d[k] for k in sorted(d)]
    g=pynauty.Graph(n,adjacency_dict={i:list(nbr[i]) for i in range(n)},vertex_coloring=vc)
    return pynauty.certificate(g)

def relabel(nbr,col,rng):
    n=len(nbr); p=list(range(n)); rng.shuffle(p)
    out=[None]*n
    for v in range(n): out[p[v]]=sorted(p[w] for w in nbr[v])
    c2=None
    if col is not None:
        c2=[None]*n
        for v in range(n): c2[p[v]]=col[v]
    return out,c2,p

def nxl(G):
    G=nx.convert_node_labels_to_integers(G)
    return [sorted(G[v]) for v in G]

def voltage_lift(base_edges,nb,m,rng,grp="z"):
    """Z_m voltage lift of a base graph. Random voltage per edge."""
    nbr=[set() for _ in range(nb*m)]
    for u,v in base_edges:
        t=rng.randrange(m)
        for a in range(m):
            x=u*m+a; y=v*m+((a+t)%m)
            if x!=y:
                nbr[x].add(y); nbr[y].add(x)
    return [sorted(s) for s in nbr]

def cayley(elts,mul,gens):
    idx={e:i for i,e in enumerate(elts)}
    S=set(gens)
    return [sorted({idx[mul(e,s)] for s in S}-{idx[e]}) for e in elts]

def add_pendants(nbr,rng,prob):
    nbr=[list(r) for r in nbr]
    n=len(nbr)
    for v in range(n):
        if len(nbr[v])<5 and rng.random()<prob:
            w=len(nbr); nbr.append([v]); nbr[v].append(w)
    return nbr

def union(*gs):
    out=[];off=0
    for g in gs:
        for r in g: out.append([w+off for w in r])
        off+=len(g)
    return out

def gen_instances(rng):
    while True:
        k=rng.randrange(19)
        col=None
        if k==0:
            n=2*rng.randint(2,40); d=rng.choice([3,4,5])
            if d>=n: d=n-1
            if (n*d)%2: continue
            g=nxl(nx.random_regular_graph(d,n,seed=rng.randrange(1<<30)))
            name=f"reg{d}-{n}"
        elif k==1:
            b=rng.choice([2,3,4]); dep=rng.randint(1,3)
            if b**dep>64: continue
            g=tree_matching(b,dep,rng); name=f"tm{b}-{dep}"
        elif k==2:
            b=2*rng.randint(2,4)
            E=irhard.random_cubic(b,rng)
            g=cfi3(b,E,{}); name=f"cfi3-{b}"
        elif k==3:
            b=2*rng.randint(2,5)
            E=irhard.random_cubic(b,rng)
            g=add_triple(irhard.cfi_lists(b,E,set())); name=f"cfit-{b}"
        elif k==4:
            b=2*rng.randint(2,8); E=irhard.random_cubic(b,rng); m=rng.randint(2,5)
            g=voltage_lift(E,b,m,rng); name=f"lift{m}-{b}"
        elif k==5:
            # cycle products
            a=rng.randint(3,7);c=rng.randint(3,7)
            G=nx.cartesian_product(nx.cycle_graph(a),nx.cycle_graph(c)); g=nxl(G); name=f"torus{a}x{c}"
        elif k==6:
            g=nxl(rng.choice([nx.petersen_graph(),nx.dodecahedral_graph(),nx.icosahedral_graph(),nx.heawood_graph(),nx.moebius_kantor_graph(),nx.pappus_graph(),nx.desargues_graph(),nx.tutte_graph(),nx.frucht_graph(),nx.truncated_cube_graph(),nx.octahedral_graph(),nx.cubical_graph(),nx.chvatal_graph(),nx.hoffman_singleton_graph() if False else nx.krackhardt_kite_graph()]))
            name="named"
        elif k==7:
            # Cayley: Z_a x Z_b with 2-5 generators (closed under inverse)
            a=rng.randint(2,8); b=rng.randint(2,8)
            elts=[(i,j) for i in range(a) for j in range(b)]
            mul=lambda e,s:((e[0]+s[0])%a,(e[1]+s[1])%b)
            s1=(1,0); s2=(0,1)
            S=[s1,((-1)%a,0),s2,(0,(-1)%b)]
            if rng.random()<0.5: 
                extra=(rng.randrange(a),rng.randrange(b))
                if (2*extra[0])%a==0 and (2*extra[1])%b==0: S.append(extra)
            g=cayley(elts,mul,S)
            g=[[w for w in r] for r in g]
            name=f"cay{a}x{b}"
        elif k==8:
            # K_{a,a}, complete, stars, paths, cycles, small degenerate
            c=rng.randrange(6)
            if c==0: g=nxl(nx.complete_graph(rng.randint(1,6))); name="K"
            elif c==1: g=nxl(nx.complete_bipartite_graph(rng.randint(1,5),rng.randint(1,5))); name="Kab"
            elif c==2: g=nxl(nx.star_graph(rng.randint(1,5))); name="star"
            elif c==3: g=nxl(nx.path_graph(rng.randint(1,30))); name="path"
            elif c==4: g=nxl(nx.cycle_graph(rng.randint(3,30))); name="cycle"
            else: g=[[] for _ in range(rng.randint(0,8))]; name="empty"
        elif k==9:
            # disconnected unions of copies of small things
            parts=[]
            for _ in range(rng.randint(2,6)):
                t=rng.randrange(4)
                if t==0: parts.append(nxl(nx.cycle_graph(rng.randint(3,8))))
                elif t==1: parts.append(tree_matching(2,rng.randint(1,3),rng))
                elif t==2: parts.append(nxl(nx.petersen_graph()))
                else: parts.append(nxl(nx.complete_graph(rng.randint(1,5))))
            if rng.random()<0.5: parts.append(rng.choice(parts))
            rng.shuffle(parts)
            g=union(*parts); name="union"
        elif k==10:
            # graph with random vertex colors
            n=2*rng.randint(2,25); d=rng.choice([3,4,5])
            if d>=n or (n*d)%2: continue
            g=nxl(nx.random_regular_graph(d,n,seed=rng.randrange(1<<30)))
            col=[rng.randrange(rng.choice([2,3,5])) for _ in range(n)]
            name=f"regc{d}-{n}"
        elif k==11:
            # coloured tree-matching
            b=rng.choice([2,3,4]); dep=rng.randint(1,3)
            if b**dep>64: continue
            g=tree_matching(b,dep,rng)
            col=[rng.randrange(2) for _ in range(len(g))]
            name="tmc"
        elif k==12:
            # line graph of cubic graph (degree 4)
            n=2*rng.randint(2,12)
            G=nx.random_regular_graph(3,n,seed=rng.randrange(1<<30))
            g=nxl(nx.line_graph(G)); name="linecub"
        elif k==13:
            # hypercube-like: Q_d, d<=5, with some hanging tails
            d=rng.randint(2,5)
            g=nxl(nx.hypercube_graph(d)); name=f"Q{d}"
        elif k==14:
            # path / cycle powers: circulant degree <= 5
            n=rng.randint(6,40)
            ks=rng.sample(range(1,n//2+1),rng.randint(1,2))
            if len(ks)==2 and n%2==0 and n//2 in ks and len(ks)*2-1>5: continue
            g=nxl(nx.circulant_graph(n,ks)); name=f"circ{n}"
        elif k==15:
            # twin-heavy: blow-ups of paths with twin classes of 2..4
            L=rng.randint(2,8); sz=[rng.randint(1,3) for _ in range(L)]
            G=nx.Graph(); layers=[]; c=0
            for s in sz:
                layers.append(list(range(c,c+s))); c+=s
            G.add_nodes_from(range(c))
            ok=True
            for a,b in zip(layers,layers[1:]):
                for u in a:
                    for v in b: G.add_edge(u,v)
            g=[sorted(G[v]) for v in range(c)]
            if max(map(len,g),default=0)>5: continue
            name="blowup"
        elif k==16:
            # random tree with degree <=5
            n=rng.randint(2,50)
            G=nx.Graph(); G.add_nodes_from(range(n))
            deg=[0]*n
            for v in range(1,n):
                while True:
                    u=rng.randrange(v)
                    if deg[u]<5:
                        G.add_edge(u,v); deg[u]+=1; deg[v]+=1; break
            g=[sorted(G[v]) for v in range(n)]; name="tree"
        elif k==17:
            # lift of K4 or K33 by Z_m x Z_2 (solvable), with pendants
            base=rng.choice([list(nx.complete_graph(4).edges()), list(nx.complete_bipartite_graph(3,3).edges())])
            nb=max(max(e) for e in base)+1
            m=rng.randint(2,8)
            g=add_pendants(voltage_lift(base,nb,m,rng),rng,0.3); name="liftp"
        else:
            # random graph max degree 5 (sparse)
            n=rng.randint(2,40); p=rng.random()*0.2
            G=nx.gnp_random_graph(n,p,seed=rng.randrange(1<<30))
            for v in list(G):
                while G.degree(v)>5:
                    G.remove_edge(v,rng.choice(list(G[v])))
            g=[sorted(G[v]) for v in range(n)]; name="gnp"
        if len(g) and max(map(len,g),default=0)>5:
            continue
        yield name,g,col

rng=random.Random(int(sys.argv[1]) if len(sys.argv)>1 else 1)
limit=float(sys.argv[2]) if len(sys.argv)>2 else 500
t0=time.time()
stats=Counter(); count=0; forms={} ; bad=0
ncerts={}
tally=Counter()
mx={}
for name,g,col in gen_instances(rng):
    if time.time()-t0>limit: break
    if len(g)>200: continue
    st=Counter()
    f=canonical_form_lists(g,col,stats=st)
    count+=1
    fam=name.split('-')[0]
    tally[fam]+=1
    stats['canon_ir']+=st['canon_ir']; stats['fallback']+=st['canon_luks_fallback']
    for k in ('canon_luks_nodes','canon_luks_max_degree'):
        pass
    if st['canon_ir'] or st['canon_luks_fallback']:
        print("BAD COUNTER",name,len(g),dict(st),flush=True); bad+=1
    for _ in range(3):
        h,c2,p=relabel(g,col,rng)
        st2=Counter()
        f2=canonical_form_lists(h,c2,stats=st2)
        if f2!=f:
            print("WRONG DIFF",name,len(g),g,col,flush=True); bad+=1; break
    # layers=bfs and guarantee modes agree on decision
    for kw in ({"layers":"bfs"},{"guarantee":True}):
        fa=canonical_form_lists(g,col,**kw); h,c2,p=relabel(g,col,rng); fb=canonical_form_lists(h,c2,**kw)
        if fa!=fb:
            print("WRONG DIFF mode",kw,name,len(g),g,col,flush=True); bad+=1
    # against nauty: form classes must match certificate classes
    c=nauty_cert(g,col)
    # compare by cert over the isomorphism: same cert => same form
    key=(len(g),c, None if col is None else tuple(sorted(Counter(col).items())))
    if key in ncerts:
        if ncerts[key]!=f:
            print("WRONG vs nauty: same cert different form",name,len(g),flush=True); bad+=1
    else:
        # two different graphs with same form?
        ncerts[key]=f
    if f in forms and forms[f]!=key:
        print("WRONG vs nauty: same form different cert",name,len(g),flush=True); bad+=1
    forms[f]=key
print("done",count,"graphs; distinct forms",len(forms),"bad",bad,dict(stats),time.time()-t0)
print(tally)
