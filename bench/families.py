"""Benchmark instances with known answers.

Each instance is (name, tier, X, Y, expect_iso, expect_aut_order) where X, Y
are adjacency matrices. expect_aut_order may be None (then it is checked
against networkx when that is affordable).
"""
import itertools
import random

import networkx as nx


def adj(G):
    nodes = sorted(G.nodes(), key=repr)
    idx = {v: i for i, v in enumerate(nodes)}
    n = len(nodes)
    A = [[0] * n for _ in range(n)]
    for u, v in G.edges():
        if u != v:
            A[idx[u]][idx[v]] = A[idx[v]][idx[u]] = 1
    return A


def relabel(A, s):
    n = len(A)
    B = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            B[s[i]][s[j]] = A[i][j]
    return B


def shuffled(A, rng):
    s = list(range(len(A)))
    rng.shuffle(s)
    return relabel(A, s)


def paley(q):
    sq = {(i * i) % q for i in range(1, q)}
    G = nx.Graph()
    G.add_nodes_from(range(q))
    G.add_edges_from((i, j) for i in range(q) for j in range(i + 1, q) if (j - i) % q in sq)
    return G


def rook(m):
    return nx.cartesian_product(nx.complete_graph(m), nx.complete_graph(m))


def shrikhande():
    G = nx.Graph()
    V = [(a, b) for a in range(4) for b in range(4)]
    G.add_nodes_from(V)
    D = [(0, 1), (0, 3), (1, 0), (3, 0), (1, 1), (3, 3)]
    for (a, b) in V:
        for (da, db) in D:
            G.add_edge((a, b), ((a + da) % 4, (b + db) % 4))
    return G


def triangular(m):
    return nx.line_graph(nx.complete_graph(m))


def johnson(m, k):
    V = list(itertools.combinations(range(m), k))
    G = nx.Graph()
    G.add_nodes_from(V)
    G.add_edges_from((a, b) for a, b in itertools.combinations(V, 2)
                     if len(set(a) & set(b)) == k - 1)
    return G


def kneser(m, k):
    V = list(itertools.combinations(range(m), k))
    G = nx.Graph()
    G.add_nodes_from(V)
    G.add_edges_from((a, b) for a, b in itertools.combinations(V, 2) if not set(a) & set(b))
    return G


def cfi(base, twist=False):
    """Cai-Furer-Immerman graph over a connected base graph. With twist=True,
    one edge is twisted; the two graphs are non-isomorphic."""
    G = nx.Graph()
    edges = sorted(tuple(sorted(e)) for e in base.edges())
    for v in base.nodes():
        inc = [e for e in edges if v in e]
        for bits in itertools.product((0, 1), repeat=len(inc)):
            if sum(bits) % 2 == 0:
                m = ("m", v, bits)
                G.add_node(m)
                for e, bit in zip(inc, bits):
                    G.add_edge(m, ("a", v, e, bit))
        for e in inc:
            G.add_node(("a", v, e, 0))
            G.add_node(("a", v, e, 1))
    for idx, (u, v) in enumerate(edges):
        e = (u, v)
        t = 1 if (twist and idx == 0) else 0
        for b in (0, 1):
            G.add_edge(("a", u, e, b), ("a", v, e, b ^ t))
    return G


def instances(seed=0):
    rng = random.Random(seed)
    out = []

    def iso(name, tier, G, aut=None):
        A = adj(G)
        out.append((name, tier, A, shuffled(A, rng), True, aut))

    def noniso(name, tier, G, H):
        # every non-isomorphism label is verified independently
        assert not nx.is_isomorphic(G, H), name
        out.append((name, tier, adj(G), shuffled(adj(H), rng), False, None))

    # tiny: n <= 8
    iso("C6", "tiny", nx.cycle_graph(6), 12)
    iso("K4", "tiny", nx.complete_graph(4), 24)
    iso("Q3", "tiny", nx.hypercube_graph(3), 48)
    iso("rand8", "tiny", nx.gnp_random_graph(8, 0.5, seed=1))
    noniso("C8-vs-2C4", "tiny", nx.cycle_graph(8),
           nx.disjoint_union(nx.cycle_graph(4), nx.cycle_graph(4)))
    noniso("rand8-pair", "tiny", nx.gnp_random_graph(8, 0.5, seed=2),
           nx.gnm_random_graph(8, nx.gnp_random_graph(8, 0.5, seed=2).number_of_edges(), seed=3))
    # small: n <= 12
    iso("Petersen", "small", nx.petersen_graph(), 120)
    iso("C12", "small", nx.cycle_graph(12), 24)
    iso("K44", "small", nx.complete_bipartite_graph(4, 4), 1152)
    iso("T5", "small", triangular(5), 120)
    iso("Paley13", "small", paley(13), 78)
    iso("rand12", "small", nx.gnp_random_graph(12, 0.5, seed=4))
    iso("3reg12", "small", nx.random_regular_graph(3, 12, seed=5))
    noniso("3reg12-pair", "small", nx.random_regular_graph(3, 12, seed=5),
           nx.random_regular_graph(3, 12, seed=7))
    # medium: n <= 20
    iso("rook4", "medium", rook(4), 1152)
    iso("Shrikhande", "medium", shrikhande(), 192)
    noniso("rook4-vs-Shrikhande", "medium", rook(4), shrikhande())
    iso("Q4", "medium", nx.hypercube_graph(4), 384)
    iso("Paley17", "medium", paley(17), 136)
    iso("T6", "medium", triangular(6), 720)
    iso("rand20", "medium", nx.gnp_random_graph(20, 0.5, seed=7))
    iso("3reg20", "medium", nx.random_regular_graph(3, 20, seed=8))
    iso("Kneser(6,2)", "medium", kneser(6, 2), 720)
    # hard: CFI graphs and larger strongly regular graphs
    iso("T8", "hard", triangular(8), 40320)
    iso("Paley29", "hard", paley(29), 406)
    iso("J(7,3)", "hard", johnson(7, 3), 5040)
    iso("CFI(K4)", "hard", cfi(nx.complete_graph(4)))
    noniso("CFI(K4)-twist", "hard", cfi(nx.complete_graph(4)), cfi(nx.complete_graph(4), True))
    iso("rand40", "hard", nx.gnp_random_graph(40, 0.5, seed=9))
    return out
