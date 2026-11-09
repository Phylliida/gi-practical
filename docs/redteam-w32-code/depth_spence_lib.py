"""Exact minimum 1-WL depth on every graph of Spence's lists and on all descendants of his
two-graph lists.  Every pair is tried (early exit at the first discrete pair); if none is
discrete, every triple, etc.  No orbit reductions, no hashing."""
import sys, itertools, time, collections, argparse
sys.path.insert(0, '.')
from rt_common import *

def min_depth(A, kmax=4):
    n = len(A)
    for k in range(1, kmax + 1):
        for S in itertools.combinations(range(n), k):
            if is_discrete(A, S):
                return k, S
    return None, None

