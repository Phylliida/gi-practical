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

`graph_iso(X, Y, solver=None, vcolors_x=None, vcolors_y=None, refine="2wl", staged=True, ir=3,
ir_min=6, ir_max="auto", ir_budget=2.0)`: adjacency entries may be edge colors, graphs may be
directed and have loops. The keyword arguments control the front end (below); `ir=0` hands every
stage to the recursion.

## Layout

* `gi/perm.py`: permutations as tuples. Right action: `mul(p, q)` means first `p`, then `q`, and
  `act(x, g)` relabels a coloring.
* `gi/group.py`: deterministic Schreier–Sims (`PermGroup`), orbits, Atkinson block systems, the
  stacked block hierarchy, action homomorphisms with lifting and kernels (`ActionHom`), and
  recognition of the Johnson action on 2-sets.
* `gi/solver.py`: string isomorphism `Iso_G(x, y)`, which is the paper's recursion.
* `gi/refine.py`: joint canonical color refinement of two graphs (1-WL and 2-WL), with colors named
  by one content-based rule for both graphs.
* `gi/graph.py`: the graph wrapper (paper Algorithm 1). Positions are the ordered vertex pairs and
  the group acts on both coordinates. Front end: refinement, then a staged orbit chain over
  vertex-class factors with refinement between stages, and optional bounded-depth
  individualization (see below).
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

## Front end (graph level)

1. **Joint 2-WL.** X and Y are refined together (coherent closure of the pair coloring). Every
   new color contains the old one, and names are ranks in the sorted union of both graphs'
   signatures. So isomorphisms map refined colors onto refined colors, and adjacency is a function
   of the refined pair color. Different histograms mean the graphs are not isomorphic. The group
   becomes the product of Sym(C) over the refined vertex classes C.
2. **Staged orbit chain** (`staged=True`). The state is `Iso(X, Y) = Iso_G(x, y) * rho` with
   `G = F_1 x ... x F_k` over disjoint vertex sets (each F_i is the full Sym or a solved group).
   The loop re-refines with the G-orbits as vertex labels, which is exact because G fixes its own
   orbits. It shrinks the Sym factors to the refined classes, then gives one stage to
   `Solver.solve`: the induced block of one factor, or the cross block of two factors. The answer
   replaces those factors (orbit-chain rule). Results that are products of symmetric groups, or
   direct products of two parts, are split again. When all blocks are clean, the answer is G.
3. **Individualization policy** (`ir`, `ir_min`, `ir_max`, `ir_budget`; `graph.Policy`). A stage
   on a Sym factor of size at least `ir_min` (with a non-uniform induced coloring) can be replaced
   by branching on the image of one vertex. The first `ir` levels always branch. Levels up to
   `ir_max` (default `max(ir, ceil(log2 n))`) first give the stage to the recursion with a time
   budget of `ir_budget` times the mean refinement time of this graph (one branch costs at least
   one refinement); if the recursion does not finish, its work is discarded and the stage
   branches. No trial is made when `100 (|P|/n)^3 > ir_budget` (building the group of Sym(P) on
   |P|^2 positions costs about |P|^3 sifts and cannot be interrupted), and after one timeout at a
   given (depth, factor size), later stages with the same (depth, size) branch at once. Both choices are exact (an aborted call leaves only finished,
   exact memo entries behind), so the policy only affects speed and which generators are
   returned. Depth O(log n) costs at most a factor n^O(log n), so the n^O(log n) bound is kept.
4. **Orbit pruning.** Automorphisms: Aut_{G_v}(x) (the branch of v against itself) plus one
   element taking v to each point of its orbit, skipping points already in the orbit of the
   generators found. Every search for a single isomorphism (the test whether u is in the orbit
   of v, and the final x→y search) branches on the *preimage* u of the y-side vertex instead,
   `Iso_G(x, y) = ∪_u t_u Iso_{G_v}(x^(t_u), y)`, and one u per orbit of the known automorphisms
   suffices; the next level gets `t_u Stab(u) t_u`. For non-isomorphic pairs, where every branch
   fails, this is most of the cost (CFI(3reg8)-twist: 153 branches before, 11 now).
5. **Fast 2-WL.** The multiset of a pair is summarized by `sum_k U[C(i,k)] V[C(k,j)]` for fixed
   random tables, computed for a whole row as one big-integer sum over packed rows. Any fixed
   function of the multiset is a canonical refinement, so exactness does not depend on the
   tables (a coincidence would only coarsen a round; `wl2_reference` keeps the definition and a
   test checks equal partitions). Hashed 1-WL rounds (O(n^2) each) run first; when they make
   the vertex colors discrete, no 2-WL round is needed. Each graph is refined on its own and cached (the same side
   recurs across individualization branches); the shared naming is replaced by a direct check
   that the input color is one function of the refined color on both sides.
6. **Chunked stages.** A stage with more than `CHUNK` (2000) positions is solved in chunks of
   orbits of its group, one after the other (orbit-chain rule), each chunk together with the
   diagonal of the stage's vertices (so the group acts faithfully); orbits where x and y share
   one constant color are skipped. The recursion then permutes a chunk instead of all positions
   (CFI(3reg20)-twist, n = 200: 156s → 1.4s). Stage groups are built with a diagonal base, their
   known order and an ambient base.

No change to `solver.py` is needed: each stage calls `Solver.solve` on a group that is built
directly on the stage's positions.

## Benchmark protocol

```sh
python3 -m pytest -q tests                                   # must pass
python3 bench/run.py --tiers tiny,small --timeout 60 --label NAME
python3 bench/run.py --tiers medium --timeout 120 --label NAME --solver-args '{"certificates": false}'
```

`bench/reference.py` times networkx VF2 (decision only) and, if importable, pynauty on the same
instances (`python3 -m venv .venv && .venv/bin/pip install pynauty networkx sympy`, then run it
with `.venv/bin/python`); `bench/nauty_check.py` cross-checks graph_iso against nauty on graphs
outside the families.

`--graph-args '{"ir": 0}'` passes keyword arguments to `graph_iso` (for example, to measure the
recursion without individualization). `bench/run.py` checks every answer. It verifies the isomorphism, verifies that each generator is
an automorphism, and checks that the order of the generated group (computed with sympy) equals
the known |Aut|. A wrong answer is a failure regardless of speed. Results go to
`bench/results/NAME.json`.

## Reference comparison (r2, machine under load ~35)

Seconds per instance, `certificates=False`; VF2 is `nx.is_isomorphic` (decision only, no
automorphism group), pynauty compares certificates and reports |Aut|.

| tier | ours (total) | VF2 | pynauty |
|---|---|---|---|
| large (18) | 6.0 (max 1.1) | iso pairs ≤ 0.3; non-iso 2-WL-equivalent pairs 2.4–111 | ≤ 0.003 |
| xl (9) | 19.4 (max 3.5) | ≤ 2.3, but CFI(3reg14)-twist 104, 3reg200 69 | ≤ 0.08 |

So the exact pure-Python solver is about 1000× slower than nauty, faster than VF2 on non-isomorphic
CFI/strongly-regular pairs and random regular graphs, and slower than VF2 on isomorphic symmetric
pairs (where VF2 finds one match quickly and computes no group).

