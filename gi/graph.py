"""Graph isomorphism through string isomorphism (the paper's Algorithm 1):
positions are ordered vertex pairs, colored by diagonal status and adjacency,
and the allowed relabelings are the vertex permutations acting on both
coordinates."""
import math

from .perm import sym_gens
from .group import PermGroup
from .solver import Solver


def pair_coloring(adj, vcolors=None):
    n = len(adj)
    vc = vcolors or [0] * n
    return tuple(2 + vc[i] if i == j else int(bool(adj[i][j]))
                 for i in range(n) for j in range(n))


def sym_on_pairs(n):
    gens = []
    for g in sym_gens(n, range(n)):
        gens.append(tuple(g[i] * n + g[j] for i in range(n) for j in range(n)))
    # (only the identity fixes every diagonal position)
    return PermGroup(n * n, gens, order=math.factorial(n),
                     ambient_base=[i * (n + 1) for i in range(n)])


def graph_iso(X, Y, solver=None, vcolors_x=None, vcolors_y=None):
    """X, Y: adjacency matrices (lists of 0/1 rows; directed graphs allowed).
    Returns None if not isomorphic, else (sigma, aut_gens): sigma[i] is the
    image of vertex i (an isomorphism X -> Y) and aut_gens generate Aut(X)."""
    n = len(X)
    if len(Y) != n:
        return None
    if n == 0:
        return (), []
    solver = solver or Solver()
    x = pair_coloring(X, vcolors_x)
    y = pair_coloring(Y, vcolors_y)
    ans = solver.solve(sym_on_pairs(n), range(n * n), x, y)
    if ans is None:
        return None

    def vertex_perm(g):
        return tuple(g[i * n + i] // n for i in range(n))

    gens = list(dict.fromkeys(vertex_perm(g) for g in ans.gens))
    gens = [g for g in gens if g != tuple(range(n))]
    return vertex_perm(ans.rep), gens
