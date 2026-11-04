"""Exactness tests against brute force on small graphs. Run: python3 -m pytest -q tests"""
import itertools
import os
import random
import sys

import pytest

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.setrecursionlimit(100000)

from gi import graph_iso, Solver
from gi.group import PermGroup


def rand_graph(n, p, rng):
    A = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < p:
                A[i][j] = A[j][i] = 1
    return A


def relabel(A, s):
    n = len(A)
    B = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            B[s[i]][s[j]] = A[i][j]
    return B


def brute(A, B):
    n = len(A)
    return [s for s in itertools.permutations(range(n))
            if all(B[s[i]][s[j]] == A[i][j] for i in range(n) for j in range(n))]


CONFIGS = [dict(certificates=False, enum_limit=1), dict(certificates=True, enum_limit=1, kappa=3)]


@pytest.mark.parametrize("cfg", CONFIGS, ids=["nocert", "cert3"])
def test_random_small(cfg):
    rng = random.Random(1)
    for _ in range(60):
        n = rng.randint(1, 6)
        A = rand_graph(n, rng.choice([0.3, 0.5, 0.7]), rng)
        if rng.random() < 0.5:
            s = list(range(n))
            rng.shuffle(s)
            B = relabel(A, s)
        else:
            B = rand_graph(n, 0.5, rng)
        res = graph_iso(A, B, solver=Solver(**cfg))
        isos, auts = brute(A, B), brute(A, A)
        assert (res is None) == (not isos)
        if res is not None:
            sigma, gens = res
            assert all(B[sigma[i]][sigma[j]] == A[i][j] for i in range(n) for j in range(n))
            assert all(A[g[i]][g[j]] == A[i][j] for g in gens for i in range(n) for j in range(n))
            assert PermGroup(n, gens).order() == len(auts)


def test_directed():
    rng = random.Random(2)
    for _ in range(30):
        n = rng.randint(2, 5)
        A = [[int(i != j and rng.random() < 0.4) for j in range(n)] for i in range(n)]
        s = list(range(n))
        rng.shuffle(s)
        B = relabel(A, s)
        res = graph_iso(A, B, solver=Solver(enum_limit=1, certificates=False))
        assert res is not None
        assert PermGroup(n, res[1]).order() == len(brute(A, A))
