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

`Solver(kappa=3, enum_limit=500, certificates=True, max_enum=100000, cert_refine=True, young=True,
young_min=5, young_wl=1, young_pick="small", giant_wl=2, recognize=True, product_hint=True,
scheme=True)`; `solver.stats` counts the recursive operations of the last run. The `young*` options
control the Young-label step and `giant_wl` the giant step's pair refinement (see "Aggregation over
the whole instance" below); `recognize`, `product_hint` and `scheme` control the dispatcher's
recognition of Johnson and product actions and the Johnson/Hamming label-structure step.

`graph_iso(X, Y, solver=None, vcolors_x=None, vcolors_y=None, refine="2wl", staged=True, ir=3,
ir_min=6, ir_max="auto", ir_budget=2.0)`: adjacency entries may be edge colors, graphs may be
directed and have loops. The keyword arguments control the front end (below); `ir=0` hands every
stage to the recursion.

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
| One-/two-label support map of the positions (Cor. "physical support thresholds") | `Solver.label_projection`, `Solver.young_root` |
| Aggregation into a coherent configuration on the labels (stable pair refinement) | `Solver.young_step`, `wl2_joint`, `Solver.label_refine` |
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

## Aggregation over the whole instance (exact; `Solver.young_step`)

The orbit chain solves one orbit at a time, so a giant step only sees the colors on its own orbit:
after a label is individualized, the information in the other orbits (on a graph stage: the rows
of the individualized vertex, the cross blocks) never reaches the labels. The Young-label step
runs in `_cont` on intransitive groups, before the orbit chain:

* **Labels** (`young_root`, once per root group G0): the G0-orbits O with |O| >= 3 on which G0
  acts as the full product of the Sym(O) (checked by the order of the restriction; orbits are
  taken greedily, smallest first). On a graph stage these are the diagonal positions, so the
  labels are the vertex classes. The support of a position is the set of labels fixed by its
  stabilizer, as in `label_projection`, computed from Schreier generators on a transversal.
  It depends on G0 alone and is G0-equivariant, so it is valid in every subgroup.
* **Refinement** (`young_refine`). Each label gets the colors (G0-orbit, x[w]) of the positions w
  with support (a,), and each pair gets those with support (a, b). The class index goes on the
  diagonal. x and y are refined jointly with content-based names, by 1-WL with pair colors
  (`young_wl=1`) or by 2-WL, the coherent closure (`young_wl=2`). Every g in Iso_H(x, y) maps the
  x coloring onto the y coloring.
* **Continue.** If the label partition splits, LiftAndContinue runs under
  H' = psi0^-1(Young(refined)). The class-matching map lies in Young(partition) = psi0(H), so
  tau is in H. If x is H-invariant, the answer is H or empty. Otherwise one label of the smallest
  class of size >= `young_min` whose positions still carry information is individualized, with
  the same pruning, memo and one-mode as the giant step (`branch_labels`). The step falls back to
  the orbit chain when no such class exists (for example, on the 2- and 4-point classes of CFI
  graphs).
* **Economy** (all exact). Young preimages are cached per partition, so branches share their
  group and the memo applies. Each branch's stable refinement is handed to its child, with the
  labels of y renamed by phi(tau). The child's own refinement would give the same partition,
  because its initial coloring lies between the branch's marked coloring and that stable
  coloring. Branch refinements restart from the node's stable coloring plus the mark.
  Generators are reduced through a faithful label action.

`young_wl=1` is the default. On isomorphic instances it gives the same branch counts as 2-WL, at
3-5x less solver time. 2-WL refutes the non-isomorphic Chang and Latin-square pairs with 0
branches (1-WL needs 38 and 138). The transitive giant step also refines two-label pair
colorings by 2-WL (`giant_wl=2`, alternated with the certificate hypergraph). The 1-WL label
refinement (`refine_labels`) encodes each label's pair multiset as a sorted tuple of integers
`code(p[a][b], p[b][a]) * K + c[b]` (one code table for both instances), built with C-level
map/sort; the partitions are those of the literal multisets.

## What is simplified (exactness is kept, running time is not)

1. **Aggregation.** The paper compares ordered test tuples in lockstep and applies Babai's Design
   Lemma. It stops Split-or-Johnson at the *first rectangle* and solves that bipartite graph
   exactly. Here the colors pulled back through the support map, over the whole instance (above),
   and the certificate signatures are refined on the labels with WL-style refinement. Labels are
   then individualized one at a time, branching over all images of the individualized label. The
   first rectangle is not implemented. After the Young step, branching is no longer the
   bottleneck (7-39 branches on the large tier with `ir=0`), and a rectangle such as points x
   lines of PG(2, 5) minus a point keeps most of the symmetry, so solving it needs the same
   individualizations.
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
3. **Individualization policy** (`ir`, `ir_min`, `ir_max`, `ir_budget`; `graph.Policy`). A stage
   on a Sym factor of size at least `ir_min` (with a non-uniform induced coloring) can be replaced
   by branching on the image of one vertex. The first `ir` levels always branch. Levels up to
   `ir_max` (default `max(ir, ceil(log2 n))`) first give the stage to the recursion with a
   **work budget** of `ir_budget` refinements of this graph (one branch costs at least one
   refinement); if the recursion does not finish, its work is discarded and the stage
   branches. Work is counted, not timed: each call of `Solver.solve`/`Solver.cont` in the trial
   costs the degree of its group, and a refinement counts as `WORK_PER_REFINEMENT * n^2`
   (1.5 n^2, calibrated so that the budget matches the old wall-clock one). So the output
   (σ and the generators) does not depend on the machine or its load; the old timed budget
   changed the output of 7 of the 56 benchmark instances under simulated preemption. No trial is
   made when `100 (|P|/n)^3 > ir_budget` (trials on all sizes made the benchmark 18% slower),
   and after one aborted trial at a given (depth, factor size), later stages with the same
   (depth, size) branch at once. Both choices are exact (an aborted call leaves only finished,
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
   test checks equal partitions). Hashed 1-WL rounds (O(n^2) each) run before every 2-WL round
   (folded into the pairs); once they make the vertex colors discrete, no further 2-WL round is
   needed. Each step is implied by 2-WL, so the stable partition is unchanged; on random
   3-regular graphs 1-WL is stuck at first but splits the vertices after one 2-WL round
   (3reg200: 1 round instead of 4). Each graph is refined on its own and cached (the same side
   recurs across individualization branches); the shared naming is replaced by a direct check
   that the input color is one function of the refined color on both sides.
6. **Chunked stages.** A stage with more than `CHUNK` (2000) positions is solved in chunks of
   orbits of its group, one after the other (orbit-chain rule), each chunk together with the
   diagonal of the stage's vertices (so the group acts faithfully); orbits where x and y share
   one constant color are skipped. The recursion then permutes a chunk instead of all positions
   (CFI(3reg20)-twist, n = 200: 156s → 1.4s).
7. **Explicit stage groups.** A stage whose factors are all symmetric groups gets its chain
   written down instead of built by Schreier–Sims (`graph.sym_product_group`,
   `PermGroup.from_bsgs`): base = the diagonal positions (v, v), classes with ≥ 3 points first;
   the transversal of the level of v maps (w, w) to the transposition (v w) acting on the pairs,
   made on first use (`group.LazyTransversal`); strong generators = a transposition and a cycle of
   the remaining points of each class. The Young-label step's labels are then a base prefix, so its
   restriction map reuses the chain (`RestrictionHom`), and its Young preimages are written down
   too (`group.young_preimage`: views of the same transpositions, plus one product per cycle).
   Schreier–Sims for Sym(62) on its 3844 pairs took seconds and could not be interrupted. Solved
   factors still use Schreier–Sims with a diagonal base, their known order and an ambient base.

No change to `solver.py` is needed: each stage calls `Solver.solve` on a group that is built
directly on the stage's positions.

## Round 3 results (r3-practical)

`certificates=False`, seconds per tier; `bench/results/r3-practical-{full,ir0}{-before,}.json`
(before = c3fd001). The machine's load varied between 3 and 36 during these runs, so single
timings are noisy; the paired column runs the old and the new code back to back on each instance.

| tier | full before | full after | ir=0 before | ir=0 after | ir=0 paired (old → new, load ~35) |
|---|---|---|---|---|---|
| hard (6) | 0.3 | 0.3 | 1.0 | 0.6 | |
| large (18) | 3.9 | 3.8 | 49.7 | 46.9 | |
| xl (9) | 11.6 | 10.5 | 270.4 | 121.3 | PG(2,7) 220 → 46, Paley101 24 → 1.0, Kneser(10,3) 53 → 3.5, rook10 51 → 14 |
| all | 16.0 | 14.8 | 321.2 | 168.8 | |

At low load, ir=0: PG(2,7) 112s → 18s, Paley101 16s → 0.65s, PG(2,5) 2.9s → 0.5s. The full
hybrid individualizes before stages get large, so it gains little from explicit chains;
3reg200 0.94s → 0.17s comes from the interleaved 1-WL. Determinism: the final code returned the
same σ and generators on all 56 instances in a run at load 33 and in one at load 9 (239 trials
finished, none aborted, in both); the old timed policy changed 7 of 56 outputs under simulated
preemption.

Remaining hotspots. Full hybrid on xl: 2-WL rounds (`_wl2_keys`, about 45%; big-integer
arithmetic, about n^2 additions and one product per row color, near the floor for this
representation), then the stage loop (`pick_stage`/`clean` about 10%, rechecking every factor
pair after each stage). ir=0: when the Young classes fall below `young_min` the orbit chain runs
on degree-n^2 Young groups, and `RestrictionHom`/`image_group`/`reduce_gens` there are
Schreier–Sims again (Q7: 55 of 80s). `young_min=2` makes Q7 2.7s and rook10 2.6s, but PG(2,7)
then times out, so this needs those restrictions written down, not a different threshold.

## Benchmark protocol

```sh
python3 -m pytest -q tests                                   # must pass
python3 bench/run.py --tiers tiny,small --timeout 60 --label NAME
python3 bench/run.py --tiers large,xl --only "J(8,3)|PG(2,5)"     # names may contain commas
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

