#!/usr/bin/env python3
# drive.py: writes conf.c input files for the experiment batches (one process, nice).
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen
root='/tmp/claude-1000/-home-bepis-math/117a2777-2472-4276-845a-e0dfeb712755/scratchpad/r4-sources/w32-spence-data'

def paley_list(qmax):
    return [q for q in range(5, qmax+1, 4) if gen.prime_power(q)]

def write_paley(out, qmax, qmin=5):
    for q in paley_list(qmax):
        if q < qmin: continue
        A = gen.paley(q)
        F = gen.GF(q); log = F.logtable()
        g = next(x for x, k in log.items() if k == 1)
        gen.write_graph(out, f"paley{q}", A, [0], [1, g])

def write_spence(out, n, limit=None, seed=1):
    p, nv = gen.spence_files(root)[n]
    graphs = list(gen.parse_spence(p, nv))
    if limit and len(graphs) > limit:
        random.Random(seed).shuffle(graphs); graphs = graphs[:limit]
    for i, A in enumerate(graphs):
        order, orbits, gens_ = gen.nauty_info(A)
        reps = sorted(set(orbits))
        gen.write_graph(out, f"sp{n}_{i}|aut={order}|orbits={len(reps)}", A, reps)

def write_peisert(out):
    for q in [9, 49, 81, 121, 361]:
        A = gen.peisert(q)
        order, orbits, gens_ = gen.nauty_info(A)
        reps = sorted(set(orbits))
        gen.write_graph(out, f"peisert{q}|aut={order}", A, reps)

def write_lines(out, q, nsamples=3, seed=2):
    rng = random.Random(seed)
    for i in range(nsamples):
        L = rng.sample(range(q+1), (q+1)//2)
        A = gen.peisert_type_lines(q, L)
        assert gen.is_conference(A)
        order, orbits, gens_ = gen.nauty_info(A)
        reps = sorted(set(orbits))
        gen.write_graph(out, f"lines{q}_{i}|aut={order}", A, reps)

def write_turyn(out, base_name, V, levels, maxn=7000):
    for L, A in gen.turyn_family(V, levels):
        n = len(A)
        if n > maxn: return
        if n <= 200:
            assert gen.is_conference(A)
        order, orbits, gens_ = gen.nauty_info(A)
        reps = sorted(set(orbits))
        gen.write_graph(out, f"turyn_{base_name}_L{L}|aut={order}|orbits={len(reps)}", A, reps)

def main():
    kind = sys.argv[1]; out = sys.stdout
    if kind == 'paley': write_paley(out, int(sys.argv[2]), int(sys.argv[3]) if len(sys.argv) > 3 else 5)
    elif kind == 'spence': write_spence(out, int(sys.argv[2]), int(sys.argv[3]) if len(sys.argv) > 3 else None)
    elif kind == 'peisert': write_peisert(out)
    elif kind == 'turyn':
        spec = sys.argv[2]
        if spec.startswith('skew'): V = gen.paley_skew(int(spec[4:]))
        else: V = gen.seidel_of_adj(gen.paley(int(spec)))
        write_turyn(out, spec, V, int(sys.argv[3]))
    elif kind == 'lines': write_lines(out, int(sys.argv[2]), int(sys.argv[3]) if len(sys.argv) > 3 else 3)

if __name__ == '__main__':
    main()
