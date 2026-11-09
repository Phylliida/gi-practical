"""Exact minimum 1-WL depth on Spence's lists and all two-graph descendants; see depth_spence_lib.py."""
import sys, time, collections, argparse
sys.path.insert(0, '.')
from rt_common import *
from depth_spence_lib import min_depth

def run(name, graphs, out):
    tally = collections.Counter(); t = time.time(); deep = []
    for i, A in enumerate(graphs):
        assert is_conference_graph(A)
        k, S = min_depth(A)
        tally[k] += 1
        if k != 2: deep.append((i, k, S))
        if (i + 1) % 500 == 0:
            print(f'  [{name}] {i+1} done, tally {dict(tally)}, {time.time()-t:.0f}s', flush=True)
    print(f'{name}: {len(graphs)} graphs, exact MIN distribution {dict(tally)}; depth!=2: {deep[:20]}{"..." if len(deep)>20 else ""}; {time.time()-t:.0f}s', flush=True)
    return tally, deep

def main():
    ap = argparse.ArgumentParser(); ap.add_argument('which', nargs='+'); args = ap.parse_args()
    files = {'25': (25, '25-12-5-6'), '29': (29, '29-14-6-7'), '37': (37, '37-18-8-9.bz2'),
             'T26': (25, 'conf2graph.26'), 'T30': (29, 'conf2graph.30'), 'T38': (37, 'conf2graph.38'),
             'T42': (41, 'conf2graph.42'), 'T46': (45, 'conf2graph.46'), 'T50': (49, 'conf2graph.50')}
    for w in args.which:
        if w.startswith('D'):                                  # all descendants of a two-graph list
            n, f = files[w[1:]]
            base = parse_rows(SPENCE + '/' + f, n)
            graphs = [d for A in base for d in descendants(A)]
            run(f'descendants of {f} (n={n}, {len(base)} two-graph reps, {len(graphs)} descendant labellings)', graphs, sys.stdout)
        else:
            n, f = files[w]
            run(f'list {f} (n={n})', parse_rows(SPENCE + '/' + f, n), sys.stdout)

main()
