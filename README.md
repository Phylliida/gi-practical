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

`Solver(kappa=3, enum_limit=500, certificates=True, max_enum=100000, cert_refine=True, recognize=True,
product_hint=True, scheme=True)`;
`solver.stats` counts the recursive operations of the last run.

`graph_iso(X, Y, solver=None, vcolors_x=None, vcolors_y=None, refine="2wl", staged=True, ir=3,
ir_min=6)`: adjacency entries may be edge colors, graphs may be directed and have loops. The
keyword arguments control the front end (below); `ir=0` hands every stage to the recursion.

## Layout

* `gi/perm.py`: permutations as tuples. Right action: `mul(p, q)` means first `p`, then `q`, and
  `act(x, g)` relabels a coloring.
* `gi/group.py`: deterministic Schreier–Sims (`PermGroup`), orbits, Atkinson block systems, the
  stacked block hierarchy, action homomorphisms with lifting and kernels (`ActionHom`), and
  verified recognition of Johnson actions on k-sets and of product actions (see below).
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
| Giant on blocks, Johnson action on k-sets → labels (Maróti, r = 1) | `Solver.transitive`, `group.johnson_structure` |
| Product action (Maróti, r ≥ 2) → product refinement over ≤ r! coordinate cosets | `Solver.transitive`, `group.product_action` |
| Johnson outcome (Split-or-Johnson): Johnson/Hamming color class on the labels | `Solver.scheme_step`, `group.johnson_embedding` |
| Giant step on Sym(q) directly (Young subgroups of Sym(q)); parity-restricted path for Alt(q) | `Solver.giant`, `lift_and_continue` |
| One-/two-label support map of the positions (Cor. "physical support thresholds") | `Solver.label_projection` |
| Alg. 3 `LocalCertificate` with windows, affected and visible orbits | `Solver.local_certificate` |
| `CheckNewWindow`: cosets of ker φ_T, then solve on the window | `Solver.check_new_window` |
| Large-symmetry branch (full certificates map onto Alt(q)) | `Solver.giant_step` |
| `LiftAndContinue`, `CombineExact` | `Solver.lift_and_continue`, `solver.combine` |

## Recognition of large primitive quotients

By Maróti's form of Cameron's theorem, a large primitive group lies in Sym(m) wr Sym(r) in the
product action on r-tuples of k-subsets and contains Alt(m)^r. `Solver.transitive` dispatches the
primitive quotient P (degree d) as follows: natural giant (order d! or d!/2) → GiantStep; small
(order ≤ `enum_limit`, or d < 5) → enumerate; Johnson action (r = 1, k ≥ 2) → GiantStep on the m
recovered labels; product action (r ≥ 2) → **product refinement**: the union over the ≤ r! cosets
of the coordinate-preserving subgroup, which is imprimitive, so the recursion continues on a finer
hierarchy (its next quotient is the action on the fibers of one coordinate, as in the paper's
inherited tower); Sym(m) or Alt(m) in any other action (for example on the k|k bisections, which
are Cameron-small but have order (2k)!) → GiantStep on m labels; anything else → enumerate. If x
is invariant under G, the answer is G (or empty) at once. The dispatch decision depends only on G
and is cached (with its homomorphism objects) by G's generators.

The structure is guessed from one orbital graph of P and then **verified**, so a wrong guess can
only lead to `None` (and enumeration):

* `group.johnson_structure`: in the Johnson graph J(m, k) (the suborbit |A ∩ B| = k − 1), the
  (k−1)-sets are the maximal cliques of size m − k + 1 (one side of the common neighbourhood of
  an edge); repeating this down to 1-sets gives the m stars {k-sets ∋ i}. Verified: every
  generator permutes the stars (so the induced map is a homomorphism), and its image has order
  m! or m!/2.
* `group.product_action`: in a Cartesian product of r graphs, two neighbours of a point differ
  from it in the same coordinate iff they are adjacent or have ≥ 3 common neighbours; this gives
  lines, and coordinates are propagated along squares. Verified: every generator maps lines to
  lines and coordinate classes to coordinate classes (so the induced map to Sym(r) is a
  homomorphism), and each class partitions the points into lines of size D = d^(1/r).
* `group.giant_labels`: a transposition (a 3-cycle for Alt(m)) is found among powers of
  pseudo-random elements (fixed seed); its conjugacy class must have C(m, 2) members (C(m, 3)
  subgroups), and the conjugation action on it, a homomorphism, is a Johnson action on 2-sets
  (3-sets), which `johnson_structure` recognizes and verifies.

**Johnson and Hamming structure on the labels** (`Solver.scheme_step`, `scheme=True`). In graph
problems the Johnson structure usually lives in the label coloring, not in the group: for J(7,3)
with `ir=0` the group is Sym(35) and the projected pair coloring of the 35 labels is the distance
coloring of J(7,3). Before a GiantStep on q labels (natural, Johnson or abstract giant), if a color
class of x's two-label projection is exactly a Johnson graph J(m, k) (m ≥ 2k ≥ 4) or a Hamming graph
H(r, D) (D ≥ 2, so hypercubes too) on all q labels (`group.johnson_embedding`,
`group.hamming_embedding`, both verified edge by edge), its embedding is unique up to the graph's automorphism group A (Sym(m), with
complementation when m = 2k; Sym(D) wr Sym(r)). Every isomorphism maps x's class graph onto y's,
so Sym(q) is replaced by the preimage of A (embedded via x) and one coset representative that maps
x's embedding onto y's (with parity handled when phi(G) = Alt(q)). This is Babai's "Johnson"
outcome of Split-or-Johnson; stats `scheme_johnson`, `scheme_hamming`.

`Solver(recognize=False)` restores the old dispatcher (only 2-set Johnson actions, the rest
enumerated). Stats: `johnson_k<k>`, `giant_abstract`, `product_refine`, `product_cosets`,
`product_hint`, `unrecognized_primitive`, `enum_large_primitive`, `invariant`.

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
3. **Other primitive quotients.** Natural giants, Johnson actions on k-sets (any k ≥ 2), product
   actions and Sym(m)/Alt(m) in other actions are recognized (above); any other large primitive
   quotient is enumerated, and beyond `max_enum` it raises `Unsupported`.
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
3. **Bounded individualization** (`ir`, `ir_min`). A stage on a Sym factor of size at least
   `ir_min` can be replaced by branching on the image of one vertex, for up to `ir` levels.
   Automorphisms use orbit pruning, and isomorphisms need only one successful branch. A constant
   depth costs at most a factor n^ir, so the n^O(log n) bound is kept.

No change to `solver.py` is needed: each stage calls `Solver.solve` on a group that is built
directly on the stage's positions.

## Benchmark protocol

```sh
python3 -m pytest -q tests                                   # must pass
python3 bench/run.py --tiers tiny,small --timeout 60 --label NAME
python3 bench/run.py --tiers medium --timeout 120 --label NAME --solver-args '{"certificates": false}'
```

`--graph-args '{"ir": 0}'` passes keyword arguments to `graph_iso` (for example, to measure the
recursion without individualization). `bench/run.py` checks every answer. It verifies the isomorphism, verifies that each generator is
an automorphism, and checks that the order of the generated group (computed with sympy) equals
the known |Aut|. A wrong answer is a failure regardless of speed. Results go to
`bench/results/NAME.json`.
