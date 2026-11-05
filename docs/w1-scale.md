# w1-scale: scaling the bounded-degree pipeline, and graphs where it beats nauty

Data: bench/results/irhard-w1-*.json (`bench/irhard.py table --label w1-ns` etc.). All runs used
one process at a time, `nice -n 19`, and timeouts; the machine was otherwise lightly loaded
(load about 1.5–3). Across all of them, no answer was wrong.

## 1. What changed in `gi/`

All changes keep every answer exact. `python3 -m pytest -q tests` passes.

### 1.1 Rooted 1-WL colors (`gi/bounded.py: rooted_colors`)

Each rooted graph (X, (u0, u1)) is colored by 1-WL with u0 and u1 individualized. Colors are
named canonically: a color is the index of its signature (old color, sorted neighbour colors) in a
dict shared by every rooted graph of one `bounded_iso` call. Any rooted isomorphism maps colors
onto equal colors (induction on rounds; isomorphic graphs stop after the same round), so the
colors can be added without changing the set of rooted isomorphisms.

### 1.2 Layers by color classes (`class_plan`, `layers="class"`)

Luks's layers are BFS distance layers. The proof of his step uses only two facts: every rooted
isomorphism maps layers onto layers, and the step sees the edges from the new layer to earlier
ones (through up-sets) and the edges inside it. Any sequence of unions of color classes
satisfies both, if the sequence is fixed by color names. Z is then layered by X's sequence of
names. Up-sets become "neighbours in earlier layers", and the lifting argument in the module
docstring carries over word for word.

`class_plan` chooses the order greedily, breaking every tie by color name:

* All classes whose vertices have pairwise distinct up-sets go into the next layer. They add no
  symmetry, because a vertex is fixed by its up-set.
* Otherwise the next layer is one class. Classes with a twin block of 3 or more vertices come
  last. Among the rest, a twin pair with an empty up-set is preferred: it adds a direct Z_2
  factor. A twin pair with a nonempty up-set comes next, and it may be moved by G''. Remaining
  ties go to fewer twin pairs, then to more placed vertices at distance 2.

With BFS layers, CFI-type graphs give twin pairs whose up-sets G'' swaps, and these produce
transient D_8 sections. With this order, every layer group on the CFI and multipede families
stays elementary abelian.

### 1.3 Elementary abelian layers by linear algebra (`gi/ea2.py`, `_Chain.step_ea`)

While G_r is an elementary abelian 2-group with an independent basis g_1..g_k, a layer step uses
no Schreier–Sims and no `Solver.solve`:

* Phase 1 (string isomorphism of G_r on the orbits of up-sets) runs orbit by orbit. On an orbit
  O, G acts regularly through G/K_O. A BFS labels each point by a vector in F_2^k. K_O is spanned
  by the Schreier vectors. The solutions on O form an affine subspace c_O + U_O, where U_O is K_O
  plus the differences of the valid images of the base point. Its annihilator gives linear
  equations. All equations together are solved by Gaussian elimination on int bitmasks: the
  solution set is a0 + N, and N is Aut_G(x) in coordinates.
* Phase 2: H = rho(G'') ⋉ prod Sym(twin class ∩ color) is elementary abelian exactly when every
  color block of a twin class has at most 2 vertices and G'' fixes each twin class that holds a
  pair. This is checked. Then H = G''⁺ × Z_2^t. The inner-edge string problem is solved the same
  way, and G_{r+1} is the solution space. Its basis is independent by construction, because
  null-space vectors over an independent basis are independent.
* If the check fails, the layer falls back to the permutation-group path (`_step_perm`, the old
  code). A later G_{r+1} that is again elementary abelian (generators are commuting involutions;
  PermGroup's accepted generators are irredundant, hence a basis) returns to the fast path.

### 1.4 Edge invariants by bit-parallel balls

The oriented-edge invariant (end colors plus the multiset of (d(u, w), d(v, w), color of w)) was
computed by n BFS runs and a Counter over n vertices per edge, which is O(n·|E|) Python
operations. It now comes from balls as int bitmasks: ball_{t+1}(v) = ball_t(v) | ⋃ ball_t(w) over
the neighbours w. A count is the popcount of a sphere intersection. This is the same invariant.

### 1.5 `bounded_iso_lists`

`bounded_iso_lists(nx, ny, ...)` takes neighbour lists, so no O(n²) matrices are needed. This
matters at n ≥ 2000.

Options (all exact; for tests and ablation): `rooted_wl`, `layers="class"|"bfs"`, `ea`.
`rooted_wl=False, ea=False` is the previous pipeline.

### 1.6 Speedups: before and after

The two code versions were timed back to back on the same instances: `bounded_iso` of commit
cc58dee against the final code, one process, `nice`. Times are in seconds and cover Aut(X) plus
the isomorphism or refutation.

| instance | n | before | after | speedup |
|---|---|---|---|---|
| CFI(3reg20) / twist | 200 | 0.24 / 0.23 | 0.066 / 0.052 | 3.6–4.4× |
| CFI(3reg40) / twist | 400 | 0.87 / 0.86 | 0.17 / 0.16 | 5.2–5.4× |
| CFI(3reg60) / twist | 600 | 2.66 / 2.61 | 1.17 / 1.10 | 2.3–2.4× |
| CFI(3reg80) / twist | 800 | 10.5 / 11.0 | 0.50 / 0.51 | 21× |
| NS multipede ns16 / twist | 352 | 41.5 / 63.1 | 0.11 / 0.13 | 390–470× |
| ns24, ns32 (iso and twist) | 528, 704 | > 300 | 0.22, 0.33 | > 900× |
| colored 3-XOR multipede (r3) / non-iso | 264 | 1.87 / 2.06 | 0.078 / 0.071 | 24–29× |
| colored 3-XOR multipede / non-iso | 440 | 5.46 / 8.68 | 0.11 / 0.15 | 50–57× |
| random 3-regular / other | 400 | 0.82 / 0.77 | 0.081 / 0.059 | 10–13× |
| random 4-regular / other | 400 | 5.10 / 2.86 | 0.082 / 0.059 | 48–62× |
| hypercube Q6, Q8 | 64, 256 | 0.035, 0.43 | 0.026, 0.14 | 1.3×, 3.1× |

CFI(3reg80) was 2.5× slower than dense nauty (10.8 s against 4.4 s); it is now 8× faster. Most
of the gain on CFI and the multipedes comes from the elementary abelian path: no Schreier–Sims at
all. The groups are also smaller under the class order. On CFI(3reg80), max log2|G_r| is 40,
which is log2|Aut| itself, against 79 with BFS layers. On ns up to n = 3168 it is at most 21. On random
regular graphs it comes from the cheaper invariants and the rooted refinement, which makes the
coloring discrete, so the groups are trivial. The CFI(3reg60) instance is slower than
CFI(3reg80). Its chain has more layers on the permutation path. The run is deterministic, so this
is a property of the instance, not noise.

Hypercubes were the one regression in development: class layers made Q8 take more than 200 s.
`class_plan` now gives up (returns BFS layers) as soon as it would add a twin block of ≥ 3
vertices.

## 2. Hard instances for IR solvers (`bench/irhard.py`)

The sources are Neuen and Schweitzer, *An exponential lower bound for individualization-refinement
algorithms for graph isomorphism* (STOC 2018, arXiv:1705.03283), and *Benchmark graphs for
practical graph isomorphism* (ESA 2017, arXiv:1705.03686). The STOC construction (CFI gadgets on a
random bipartite expander with large r) proves 2^Ω(n) search trees for every IR algorithm whose
refinement is no stronger than k-WL. It is impractical, though: the gadgets have 2^(r−1) middle
vertices with r ≥ r_0. The ESA paper gives the practical version, which we build:

* G_k is the 2k-cycle with its k diagonals.
* B(G_k, σ) has V = V(G_k) × {0, 1} and W = E(G_k). Here (v, 0) ~ e iff v ∈ e, and (v, 1) ~ e iff
  v ∈ σ(e), for a random permutation σ of E(G_k).
* R(B, r) is the multipede. It has feet a(w), b(w) for w ∈ W, and for each v ∈ V a CFI gadget X_3
  on its three feet pairs with parity r_v (4 middle vertices).

| family | NS name | vertices | max degree | pairs | how the answer is known |
|---|---|---|---|---|---|
| `ns` | z2 | 22k | 8 | R(B, 0) vs relabeled R(B, A x) (iso); vs relabeled R(B, e_v), e_v ∉ col(A) (non-iso) | lemma below, at every size; \|Aut\| = 1 |
| `nsr` | r2 | 18k | 8 | B* = a row basis of A (square, invertible), so all parities are isomorphic; iso pairs only | lemma; \|Aut\| = 1 |
| `nss` | s2 | 16k | ≤ 21 | feet bypassed (their neighbourhoods made cliques) | iso by construction; non-iso and \|Aut\| from nauty when it finishes |
| `nst` | t2 ("shrunken multipedes") | 12k | ≤ 21 | both reductions | iso by construction; \|Aut\| from nauty |
| `cfix` | – | 10b | 3 | CFI over a random cubic graph: 2 twists (iso), 1 twist (non-iso) | Cai–Fürer–Immerman |
| `mzgen`, `mz`, `mzaug`, `mzaug2` | Miyazaki | 20k (mz) | 3 (mz) | relabeled (iso); one twisted base edge (non-iso) | iso by construction; non-iso and \|Aut\| from nauty (Traces solves these at once) |

**Lemma** (NS17 Lemma 2.3, extended from automorphisms to isomorphisms). Suppose B = (V, W, E)
satisfies four conditions: (1) |N(v)| = 3 for every v ∈ V; (2) A_B has full column rank over F_2;
(3) B is rigid; (4) no two distinct w1, w2 ∈ W have N²(w1) = N²(w2). Then R(B, r) is rigid, and
R(B, r) ≅ R(B, r') iff r + r' lies in the column space of A.

*Proof.* Feet have even degree and middles have degree 3, so an isomorphism ψ maps feet to feet.
N²(a(w)) = N²(b(w)) = F(N²_B(w)), so by (4) ψ maps foot pairs to foot pairs, and hence gadgets to
gadgets. The induced bijection is an automorphism of B, which is the identity by (3). Let x_w = 1
iff ψ swaps a(w) and b(w). The CFI gadget lemma says a gadget of parity r_v maps onto one of
parity r'_v swapping the pairs X iff |X| ≡ r_v + r'_v (mod 2). So A x = r + r'. Conversely, every
such x defines an isomorphism.

`check_ns_lemma` verifies the four conditions for every generated base. Conditions (1), (2) and
(4) are checked directly; (2) uses Gaussian elimination. Condition (3) is checked twice: by our
exact solver on B (7k vertices) and by dreadnaut. A base that fails is redrawn. So for `ns` and
`nsr` both answers and |Aut| = 1 are theorems at every size, including sizes where nauty does not
finish.

`mzgen` is our generator for Miyazaki's graphs. It is a chain of 2k odd CFI (Fürer) gadgets of 10
vertices. Blocks 2i−1 and 2i are joined by one outer pair (a single base edge), blocks 2i and 2i+1
by two pairs (a double base edge), and the first and last blocks carry a loop. For every k = 2..50
it reproduces the edge set of the bliss benchmark file mz-k exactly (tests/test_irhard.py, when the
files are present). The augmented variants are read from the bliss files (n ≤ 1200).

## 3. Headline: Neuen–Schweitzer multipedes (`ns`), where we beat nauty and Traces

Setup:

* **Pipelines.** Ours is `bounded_iso_lists` with `Solver(cameron_no_enum=True,
  certificates=False)`, pure Python. Its time covers Aut(X) plus an isomorphism or a refutation.
* **nauty.** dreadnaut from nauty 2.9.1 (nixpkgs), in three modes: dense nauty (`Ad`), sparse
  nauty (`As`) and Traces (`At`). The task is the standard IR isomorphism test: canonical forms of
  X and Y, then a comparison. The time is the sum of the two reported cpu times.
* **Runs.** One process at a time, `nice -n 19`, a 600 s timeout per mode and instance. Once a mode
  times out, larger sizes of the same kind are skipped and shown as `>600`.
* **Instances.** Seed 0. Data: bench/results/irhard-w1-ns.json.
* **Checks.** Every one of our answers was verified: the decision against the lemma, σ on every
  edge, every generator, and |⟨gens⟩| = |Aut| = 1. Wherever a nauty mode finished, its verdict
  agreed with the lemma and it reported grpsize = 1.

| n | ours iso | ours non-iso | dense nauty | sparse nauty | Traces | log2 max\|G_r\| |
|---|---|---|---|---|---|---|
| 352 | 0.13 | 0.17 | 0.19 / 0.19 | 0.02 / 0.04 | 0.01 / 0.00 | 3 |
| 704 | 0.31 | 0.32 | 2.8 / 2.9 | 0.12 / 0.12 | 0.05 / 0.05 | 5 |
| 1056 | 0.43 | 0.53 | 14.7 / 17.3 | 0.41 / 0.38 | 1.9 / 1.9 | 7 |
| 1408 | 0.57 | 0.70 | 204 / 223 | 4.8 / 5.7 | >600 / >600 | 10 |
| 1760 | 0.64 | 0.89 | >600 | 7.5 / 6.9 | >600 | 10 |
| 2112 | 1.02 | 1.13 | >600 | 67.8 / 68.7 | >600 | 12 |
| 2464 | 1.41 | 1.40 | >600 | >600 / >600 | >600 | 15 |
| 2816 | 1.51 | 1.70 | >600 | >600 | >600 | 20 |
| 3168 | 1.61 | 2.11 | >600 | >600 | >600 | 21 |

(nauty cells: iso / non-iso pair, in seconds.)

**Fits** (`bench/irhard.py fit --label w1-ns --floor 0.1`):

| mode | sizes | polynomial fit (R²) | exponential fit (R²) |
|---|---|---|---|
| ours | 352–3168 | n^1.17 (0.98), non-iso n^1.15 (0.99) | – |
| dense nauty | 352–1408 | n^4.8 (0.96) | 2^(9.3 n/1000) (0.99): doubles every ~110 vertices |
| sparse nauty | 704–2112 | n^5.6 (0.95) | 2^(6.4 n/1000) (0.97): doubles every ~155 vertices |
| Traces | 352–1056, then > 600 s at 1408 | – | – |

**Crossovers** (measured, not extrapolated):

* Dense nauty: ours is faster from n = 352, the smallest size run (0.13 s vs 0.19 s).
* Traces: ours is faster between n = 704 and 1056 (0.43 s vs 1.9 s at 1056). Traces gives up
  (more than 600 s) at 1408.
* Sparse nauty: the two are level at n = 1056 (0.43 s vs 0.41 s, iso; 0.53 s vs 0.38 s, non-iso).
  Ours is ahead at every larger size: 8× at 1408, 10× at 1760, 65× at 2112. At 2464 sparse nauty
  does not finish in 600 s and ours takes 1.4 s, so the ratio exceeds 400.
* The fitted curves agree: ours stays below sparse nauty for all n ≥ 934–1047, below dense nauty
  for all n ≥ 338.

### 3.1 Why the n = 2464 result is solid

The instance is `ns112`: R(B(G_112, σ)) with seed 0, n = 2464, 5376 edges, 672 feet of degree 8
and 1792 middles of degree 3. The pair is X against a relabeled R(B, A x) (isomorphic), and X
against a relabeled R(B, e_v) with e_v ∉ col(A) (not isomorphic).

1. **The answer is a theorem, not a nauty output.** `irhard.py audit --size 112` re-derives the
   base: |V| = 448, |W| = 336, rank A = 336. All four lemma conditions hold. B's rigidity is
   checked by our solver and by dreadnaut, and B is small and easy. So the iso/non-iso answers
   and |Aut| = 1 follow from the lemma in §2.
2. **Our answer was fully verified.** On the iso pair, σ is a bijection that maps all 10752
   oriented edges of X onto edges of Y, with equal edge counts. We return 0 automorphism
   generators, and |⟨∅⟩| = 1 = |Aut| from the lemma. On the non-iso pair we answer
   "not isomorphic", as the lemma requires. Times are 1.38–1.41 s
   (bench/results/irhard-w1-ns112-audit.txt).
3. **Growth curves for both solvers.** See the table above: ours grows like n^1.2, nauty
   exponentially. Tree sizes on X alone (`irhard.py nodes`, bench/results/irhard-w1-ns-nodes.jsonl):

   | n | sparse nauty: nodes / depth / cpu | dense nauty: nodes / depth / cpu | Traces: nodes / cpu |
   |---|---|---|---|
   | 352 | 569 / 6 / 0.01 s | 313 / 5 / 0.09 s | 256 / 0.01 s |
   | 704 | 3 241 / 8 / 0.06 s | 3 041 / 9 / 1.7 s | 512 / 0.02 s |
   | 1056 | 7 913 / 11 / 0.20 s | 7 377 / 10 / 9.2 s | 768 / 0.95 s |
   | 1408 | 123 849 / 14 / 3.4 s | 107 441 / 13 / 163 s | > 200 s |
   | 1760 | 58 593 / 13 / 2.3 s | > 200 s | – |
   | 2112 | 918 985 / 17 / 41 s | – | – |
   | 2464 | **10 225 361 / 21 / 530 s** | – | **> 600 s** |

   Every leaf of nauty's tree is "bad": the graphs are rigid, so nothing can be pruned by
   automorphisms. The depth (individualizations before the partition is discrete) grows
   linearly, which is NS's mechanism. Instances vary, as NS also report: the 1760 instance is
   easier than the 1408 one.
4. **Sparse nauty and Traces fail too.** On the pair, all three modes exceed 600 s at n = 2464.
   On X alone, sparse nauty needs 530 s, so canonizing X and Y takes about 1060 s, against 1.4 s
   for ours (about 750×). Traces does not finish on X alone in 600 s; it already failed at 1408,
   and the machine has about 1 TB of RAM, so memory is not the cause. Dense nauty failed from
   1760 on.
5. **The timeout is not a setup artifact.**
   * Nauty receives the same graph: dreadnaut reads our input and types it back (`t`), and the
     edge set is identical to ours (10752 oriented edges). Parsing takes 0.01 s.
   * The same harness and format solve every smaller member in every mode with the right verdict
     and grpsize = 1: 352–2112 for sparse nauty, 352–1408 for dense nauty, 352–1056 for Traces.
   * Given the full 10-minute cap, sparse nauty does finish on X, after 10.2 million nodes. The
     pair runs only count time, so the earlier timeout was simply the cost of two such runs.

### 3.2 Other seeds (robustness)

There are two more random σ per size: seeds 1 and 2, with 200 s timeouts. Data:
bench/results/irhard-w1-ns-s{1,2}.json. Each cell gives iso / non-iso times in seconds.

| n | ours (s1) | sparse nauty (s1) | Traces (s1) | ours (s2) | sparse nauty (s2) | Traces (s2) |
|---|---|---|---|---|---|---|
| 1056 | 0.49 / 0.50 | 0.30 / 0.49 | 0.35 / 0.34 | 0.43 / 0.49 | 0.50 / 0.53 | 2.0 / 2.0 |
| 1408 | 0.69 / 0.67 | 0.52 / 1.02 | 2.6 / 2.6 | 0.49 / 0.68 | 4.1 / 4.3 | 21 / 21 |
| 1760 | 0.86 / 0.91 | 9.5 / 8.3 | > 200 | 0.84 / 0.89 | 25 / 18 | > 200 |
| 2112 | 0.77 / 1.12 | 139 / 165 | > 200 | 1.12 / 1.21 | 184 / 195 | > 200 |

The crossover with sparse nauty moves with σ, as NS17 also observed. It lies between 1056 and
1408 for seeds 0 and 2, and between 1408 and 1760 for seed 1. From n = 1760 on, ours wins on all
three seeds, by 10–30×. At 2112 it wins by 60–180×, and at 2464 by more than 400× (seed 0).
Our own times hardly vary with σ (0.77–1.21 s at 2112).

## 4. The other families: where we win and where we lose

Times are in seconds; each cell gives iso / non-iso; the timeout is 200 s. The
answers for nss, nst, cfix and mz are from the construction (iso pairs) or from nauty (non-iso
pairs and |Aut|), and all of ours were verified against them.

**Shrunken multipedes `nst`** (NS's t2, 12k vertices; iso pairs only):

| n | ours | dense nauty | sparse nauty | Traces |
|---|---|---|---|---|
| 288 | 0.22 | 0.06 | 0.02 | 0.16 |
| 384 | 0.25 | 0.23 | 0.02 | > 200 |
| 576 | 0.68 | 2.5 | 0.33 | > 200 |
| 768 | 4.5 | > 200 | 78.9 | > 200 |

Traces fails from n = 384, dense nauty from 768. Sparse nauty is faster up to 576 and 18× slower
at 768. Here ours grows faster than on ns. log2|G_r| reaches 28 at n = 768, because the bypassed
graphs have no feet, so twin pairs with nonempty up-sets appear, and 12 layers fall back to the
permutation path. Even so, it is far below nauty's growth.

**CFI over random cubic graphs `cfix`** (|Aut| = 2^(b/2+1)):

| n | ours | dense nauty | sparse nauty | Traces |
|---|---|---|---|---|
| 400 | 0.19 / 0.19 | 0.25 / 0.24 | 0.09 / 0.12 | 0.00 / 0.00 |
| 800 | 0.49 / 0.47 | 3.0 / 3.1 | 1.4 / 1.3 | 0.01 / 0.01 |
| 1600 | 1.7 / 1.6 | 43 / 42 | 17 / 26 | 0.02 / 0.02 |
| 3200 | 8.5 / 7.7 | > 200 | 69 / 109 | 0.06 / 0.06 |

We beat dense nauty from n ≈ 400 and sparse nauty from n ≈ 800, by 8–14× at 3200. Here every
mode grows polynomially. The fits are: ours n^1.75 (R² 0.99), dense nauty n^3.7, sparse nauty
n^3.2–3.4. **Traces is far ahead
at every size:** 0.06 s at 3200, more than 100× faster than ours. CFI graphs have huge
automorphism groups, and Traces' automorphism pruning keeps its search tiny.

**Miyazaki graphs `mzgen`** (our generator, identical to the bliss files for k ≤ 50):

| n | ours | dense nauty | sparse nauty | Traces |
|---|---|---|---|---|
| 1000 | 3.7 / 3.6 | 5.9 / 5.9 | 1.8 / 3.0 | 0.00 |
| 2000 | 17 / 17 | 76 / 78 | 22 / 15 | 0.01 |
| 3000 | 45 / 43 | > 200 | > 200 | 0.02 |

Ours beats dense nauty at all sizes from n ≈ 1000, and sparse nauty around 2000–3000. Traces
solves them at once, as Miyazaki and NS17 report. Ours fits n^2.10 (R² 0.998), dense nauty n^3.1–3.5, sparse nauty n^3.1–3.6. The groups are
large:
|Aut| = 2^(n/10 + 1), and log2|G_r| reaches 301.

**Default pipeline (`graph_iso`) on ns:** 0.08, 0.53, 1.3, 12.6 and 26.6 s for n = 88, 176, 264,
352, 528 (iso). That fits n^3.4 (R² 0.96), and 100–200× slower than the new bounded pipeline at 352–528.
Its 2-WL front end is Θ(n³) per refinement, so it was not run further.

## 5. Summary and confidence

* **Regime where we beat nauty and Traces.** These are rigid, bounded-degree multipede graphs from
  Neuen–Schweitzer's construction (`ns`, NS's z2), with answers known by a lemma checked at every
  size. Ours is faster than dense nauty from n ≈ 350 and faster than Traces from n ≈ 1000 (Traces
  fails at 1408–1760). Against sparse nauty the crossover is n ≈ 1056–1760, depending on σ.
  Beyond 1760 ours wins on every instance measured. At n = 2464 all three modes exceed 600 s; on
  the graph alone, sparse nauty needs 530 s per canonical form, against 1.4 s for our complete
  answer. The NS shrunken multipedes (nst) show the same picture from n = 768.
* **Confidence.** High that the gap widens: nauty's tree is exponential (10^7 nodes at 2464,
  depth 21, all bad leaves), while ours grows like n^1.2 up to 3168. The fits favour exponential
  over polynomial for nauty (R² 0.97–0.99 against 0.95–0.96). The exact rate of sparse nauty is
  uncertain to within a factor of about 2 in the doubling distance (σ-dependent).
* **Where we lose.** Traces is far faster on CFI over random cubic graphs and on Miyazaki graphs,
  where large automorphism groups let it prune. Sparse nauty is faster on all families below
  n ≈ 1000. Our pipeline is pure Python. It is exact everywhere, and the polynomial guarantee is
  Luks's.
* **What the multipede win rests on.** The rooted 1-WL coloring followed by the class order turns
  each rooted test into a few hundred linear-algebra steps over F_2 with tiny groups (log2|G_r| ≤ 21).
  This is the group-theoretic advantage NS17 point to ("bounded color class size ... polynomial by
  group-theoretic techniques"). An IR solver instead has to search a tree whose depth grows
  linearly.

## 6. Reproduce

```sh
PY=../r2-hybrid/.venv/bin/python        # dreadnaut: nixpkgs nauty 2.9.1 (DREADNAUT=... to override)
nice $PY bench/irhard.py run --family ns --sizes 16,32,48,64,80,96,112,128,144 \
     --modes new,dnd,dns,dnt --timeout 600 --label w1-ns
$PY bench/irhard.py table --label w1-ns;  $PY bench/irhard.py fit --label w1-ns --floor 0.1
nice $PY bench/irhard.py audit --size 112          # §3.1, items 1, 2 and 5
nice $PY bench/irhard.py nodes --sizes 16,32,48,64,80,96 --algs As,At,Ad --timeout 200
python3 -m pytest -q tests                          # 341 passed, 19 skipped
```
