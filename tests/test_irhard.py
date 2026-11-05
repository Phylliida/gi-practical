"""The IR-hard constructions of bench/irhard.py: the claimed answers (by the
multipede lemma and the CFI theorem) against the default pipeline graph_iso,
which shares no code with gi/bounded.py, and the bounded pipeline on them.
Run: python3 -m pytest -q tests"""
import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.setrecursionlimit(100000)

import pytest

from bench import irhard as H
from gi import Solver, graph_iso
from gi.bounded import bounded_iso_lists


def dense(nbr):
    n = len(nbr)
    A = [[0] * n for _ in range(n)]
    for u in range(n):
        for v in nbr[u]:
            A[u][v] = 1
    return A


def verify(I, res):
    n = len(I["X"])
    sigma, gens = res
    EY = {(u, v) for u in range(n) for v in I["Y"][u]}
    assert all((sigma[u], sigma[v]) in EY for u in range(n) for v in I["X"][u])
    EX = {(u, v) for u in range(n) for v in I["X"][u]}
    for g in gens:
        assert all((g[u], g[v]) in EX for u in range(n) for v in I["X"][u])


@pytest.mark.parametrize("fam,k", [("ns", 3), ("ns", 4), ("nsr", 4), ("nst", 3), ("nss", 3),
                                   ("cfix", 8), ("cfix", 10), ("mzgen", 2)])
def test_claims_against_default_pipeline(fam, k):
    rng = random.Random(100 + k)
    for I in H.FAMILIES[fam](k, rng):
        ref = graph_iso(dense(I["X"]), dense(I["Y"]), solver=Solver(certificates=False))
        if I["claim"] is not None:
            assert (ref is not None) == I["claim"], I["name"]
        S = Solver(cameron_no_enum=True, certificates=False)
        res = bounded_iso_lists(I["X"], I["Y"], solver=S)
        assert (res is None) == (ref is None), I["name"]
        if res is not None:
            verify(I, res)
            from gi.group import PermGroup
            n = len(I["X"])
            assert PermGroup(n, res[1]).order() == PermGroup(n, ref[1]).order()
            if I["aut"] is not None:
                assert PermGroup(n, res[1]).order() == I["aut"]


def test_ns_lemma_conditions():
    rng = random.Random(1)
    for k in (3, 5, 8):
        for _ in range(3):
            rows, nw = H.ns_base(k, rng)
            bad = H.check_ns_lemma(rows, nw)
            if not bad:
                assert len(rows) == 4 * k and nw == 3 * k
                # the twist candidate is outside the column space
                cs, _ = H.col_space(rows, nw)
                assert len(cs) == nw


def test_f2_helpers():
    basis = H.echelon([0b011, 0b110, 0b101])
    assert len(basis) == 2                       # 011 + 110 = 101
    assert H._reduce(basis, 0b101) == 0 and H._reduce(basis, 0b001) != 0


def test_multipede_shapes():
    rng = random.Random(2)
    rows, nw = H.ns_base(4, rng)
    X = H.multipede(rows, nw, [0] * len(rows))
    assert len(X) == 2 * nw + 4 * len(rows)
    assert sorted(set(map(len, X))) == [3, 8]
    Xs = H.bypass(X, 2 * nw)
    assert len(Xs) == 4 * len(rows)


def test_miyazaki_generator_matches_bliss_files():
    path = os.path.join(H.MZ_DIR, "bliss-mz", "x", "mz")
    if not os.path.isdir(path):
        pytest.skip("bliss Miyazaki files not present")
    for k in range(2, 51, 2):
        E = set()
        for line in open(os.path.join(path, f"mz-{k}")):
            t = line.split()
            if t and t[0] == "e":
                E.add(tuple(sorted((int(t[1]), int(t[2])))))
        assert E == {tuple(sorted(e)) for e in H.miyazaki_edges(k)}
