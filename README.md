# gi-practical

A minimal Python implementation of the graph-isomorphism algorithm of
Hajiaghayi and JafariRaviz, *Deterministic n^O(log n) Graph Isomorphism
Algorithm via Inherited Decompositions* (arXiv:2611.01399). The goal is to make
it practical step by step, while keeping every answer exact.

## Interface

```python
from gi import graph_iso, Solver
res = graph_iso(X, Y)            # X, Y: adjacency matrices (lists of 0/1 rows)
if res is not None:
    sigma, aut_gens = res        # isomorphism X -> Y and generators of Aut(X)
```

`Solver(kappa=3, enum_limit=500, certificates=True, max_enum=100000, cert_refine=True)`; `solver.stats` counts the
recursive operations of the last run.

## Layout

* `gi/perm.py`: permutations as tuples. Right action: `mul(p, q)` means first `p`, then `q`, and
  `act(x, g)` relabels a coloring.
* `gi/group.py`: deterministic Schreier–Sims (`PermGroup`), orbits, Atkinson block systems, the
  stacked block hierarchy, action homomorphisms with lifting and kernels (`ActionHom`), and
  recognition of the Johnson action on 2-sets.
* `gi/solver.py`: string isomorphism `Iso_G(x, y)`, which is the paper's recursion.
* `gi/graph.py`: the graph wrapper (paper Algorithm 1). Positions are the ordered vertex pairs and
  the group is Sym(n) acting on both coordinates.
* `tests/`: exactness tests against brute force.
* `bench/`: benchmark families with known answers, and a runner that verifies every answer.

## What follows the paper

| Paper | Code |
|---|---|
| Alg. 1, graph to colored positions | `graph.graph_iso` |
| Alg. 5 `Solve` (faithful action on the active domain) | `Solver.solve` |
| Alg. 5 `Continue`: orbit chain rule, largest orbit first (Sec. 3.1) | `Solver.cont` |
| Primitive-quotient dispatcher: enumerate small quotients | `Solver.transitive`, `enum_cosets` |
| Giant on blocks, Johnson action → labels | `Solver.transitive`, `group.johnson_labels` |
| Giant step on Sym(q) directly (Young subgroups of Sym(q)); parity-restricted path for Alt(q) | `Solver.giant`, `lift_and_continue` |
| One-/two-label support map of the positions (Cor. "physical support thresholds") | `Solver.label_projection` |
| Alg. 3 `LocalCertificate` with windows, affected and visible orbits | `Solver.local_certificate` |
| `CheckNewWindow`: cosets of ker φ_T, then solve on the window | `Solver.check_new_window` |
| Large-symmetry branch (full certificates map onto Alt(q)) | `Solver.giant_step` |
| `LiftAndContinue`, `CombineExact` | `Solver.lift_and_continue`, `solver.combine` |

## Branching economy (exact; not in the paper)

* **No Sym→Alt normalization.** The paper's two normalization cosets doubled every giant step.
  `giant_step` works on phi(G) = Sym(q) directly; `lift_and_continue` lifts Young subgroups of
  Sym(q), and the large-symmetry branch adds the odd coset of ker(phi) when needed.
* **Automorphism pruning** (`individualize`, `coset_union`). Branches B(g) = {isos with
  label 0 ↦ g} satisfy B(g)·b = B(g^phi(b)) for b in Aut(y). Once one isomorphism sigma is known,
  every found automorphism a of x gives b = sigma⁻¹ a sigma, and branches in the orbit of an
  explored one are skipped. The proof that the output still generates all of Aut(x) is in the
  docstrings.
* **Memo and one-mode** (`cont`). Aut_G(x) is memoized by (generators of G, x). All branches of a
  giant step share their x side, so after Aut of the x-vs-x branch is known, every branch only
  needs one isomorphism. In one-mode, branches are pruned by the known Aut(x) (one
  representative per orbit).
* **Certificates** are computed only when the labels are uniform after projection refinement,
  only for x (that is all the large-symmetry branch and pruning need), and are cached.
  `cert_refine=True` also refines labels by certificate signatures of x and y.

## What is simplified (exactness is kept, running time is not)

1. **Aggregation.** The paper compares ordered test tuples in lockstep, applies Babai's Design
   Lemma and coherent configurations, and stops Split-or-Johnson at the *first rectangle*,
   solving that bipartite graph exactly. Here, the certificate signatures and the colors pulled
   back through the support map are refined on the labels with WL-style refinement. Labels are
   then individualized one at a time. Branching is over all images of the individualized label.
2. **No row/column step** (Alg. 4) and no phase, hierarchy-cap or hereditary-budget bookkeeping.
   The bookkeeping only matters for the running-time proof.
3. **Product actions and Johnson actions on k-sets with k ≥ 3** are handled by enumerating the
   quotient. Beyond `max_enum` they raise `Unsupported`.
4. **Small constants.** κ = 3 by default (the paper uses κ = 64), and groups of order up to
   `enum_limit` are enumerated directly.

## Benchmark protocol

```sh
python3 -m pytest -q tests                                   # must pass
python3 bench/run.py --tiers tiny,small --timeout 60 --label NAME
python3 bench/run.py --tiers medium --timeout 120 --label NAME --solver-args '{"certificates": false}'
```

`bench/run.py` checks every answer. It verifies the isomorphism, verifies that each generator is
an automorphism, and checks that the order of the generated group (computed with sympy) equals
the known |Aut|. A wrong answer is a failure regardless of speed. Results go to
`bench/results/NAME.json`.
