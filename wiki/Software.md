# Software: architecture, pipelines, kernel, correctness checks

An exact graph-isomorphism and canonical-labeling solver, written in Python with an optional C kernel. "Exact" means every answer is
correct or the run fails or times out; heuristics affect only speed.

[Home](Home.md) · [Benchmarks](Benchmarks.md) · [Reproduce](Reproduce.md) · Interface reference: [README](../README.md)

**Current as of master `1368fb6`,** including the merged `w22-speed` and `w23-speed2`.

## Module map

| File | Role |
|---|---|
| [gi/perm.py](../gi/perm.py) | permutations as tuples. Right action: `mul(p, q)` is first p, then q |
| [gi/group.py](../gi/group.py) | deterministic Schreier–Sims (`PermGroup`), orbits, Atkinson block systems, stacked block hierarchy, `ActionHom`, verified recognition of Johnson and product actions; since w22 a chain cache front keyed by generator ids, shared trivial levels and incremental level scans |
| [gi/solver.py](../gi/solver.py) | string isomorphism `Iso_G(x, y)`, the paper's recursion: `Solver` |
| [gi/graph.py](../gi/graph.py) | graph wrapper (paper Algorithm 1): positions are ordered vertex pairs; front end: refinement, staged orbit chain, optional individualization; `choose_pipeline`; `StageMemo` and `pick_stage_tracked` (w22) |
| [gi/refine.py](../gi/refine.py) | joint canonical colour refinement (1-WL and 2-WL), with names from one content-based rule for both graphs |
| [gi/wl.py](../gi/wl.py) | canonical worklist 1-WL, O(m log n) per run, on neighbour lists |
| [gi/bounded.py](../gi/bounded.py) | Luks's reduction: bounded degree to string isomorphism, layer by layer from an edge |
| [gi/ea2.py](../gi/ea2.py) | elementary abelian 2-groups by a basis; SI and least-image canonization by Gaussian elimination on bitmasks; `SparseEA` for sparse generators |
| [gi/canon.py](../gi/canon.py) | canonical labeling of bounded-degree graphs; verified-automorphism probe `_probe_automorphism` and `_LazyGroup` (w23) |
| [gi/_ckernel.c](../gi/_ckernel.c), [gi/kernel.py](../gi/kernel.py) | optional compiled kernel and loader |
| [build_ckernel.py](../build_ckernel.py) | builds the kernel, including an ASan/UBSan mode |

## Pipelines and when each runs

`graph_iso(X, Y)` defaults to `method="auto"`, which picks a pipeline by cheap deterministic features (`gi.graph.choose_pipeline`):

| Pipeline | Used when | What it is |
|---|---|---|
| **bounded** | maximum degree ≤ 8 or n > 256, and the input is a simple graph | Luks's reduction, layered by colour classes, F₂ linear algebra while layer groups are elementary abelian, `Solver.solve` otherwise |
| **hybrid** | otherwise; also for explicit front-end options, directed or looped or edge-coloured inputs | joint 2-WL, staged orbit chain, individualization policy, then the recursion |
| **fallback** | a bounded run exceeds its work budget (100·n² units charged by `Solver.solve/cont` and Schreier–Sims, at most 3n rooted tests; since the w22 merge a Schreier–Sims level scan charges len(T)·len(news)·n/32, only for the generators actually scanned; [overnight log](../docs/overnight-log.md)) | restarts in the hybrid pipeline; work is discarded, only finished memo entries remain |
| recursion only | `graph_iso(..., ir=0)` | every stage goes to the recursion; used to measure the paper's part alone |

Which pipeline ran is in `solver.stats` (`pipeline_bounded`, `pipeline_hybrid`, `pipeline_fallback`). Work is counted, not timed, so output does not depend on machine load.
Dispatch thresholds came from measuring both pipelines on the tiers and the hardness families ([w14-solver](../docs/w14-solver.md)).

`canonical_form` and `canonical_labeling` always use [gi/canon.py](../gi/canon.py), for simple undirected graphs with vertex colours.

### The hybrid front end ([graph.py](../gi/graph.py))

1. **Joint 2-WL** of X and Y (coherent closure of the pair colouring), by a fast summary hash; 1-WL passes interleaved (hashing is exact: a collision only coarsens a round).
2. **Staged orbit chain.** State Iso(X,Y) = Iso_G(x,y)·ρ with G a product of factors over disjoint vertex sets. Re-refine, shrink Sym factors, solve one stage, repeat.
3. **Individualization policy** (`ir`, `ir_min`, `ir_max`, `ir_budget`). The first `ir` levels (default 3) always branch; levels up to `ir_max` first give the stage to the recursion under a counted budget of `ir_budget` refinements. Exact.
4. **Orbit pruning**, including branching on preimages in one-isomorphism searches.
5. **Chunked stages** (over 2000 positions) and **explicit chains** for stages with Sym factors, avoiding Schreier–Sims.
6. **Stage-loop verdict memo** (w22). `graph.StageMemo` keeps each block's verdict across one `staged_iso` loop, and `pick_stage_tracked` makes the checks of `pick_stage` in the same order. `pick_stage` is unchanged and remains the reference. Where the loop ends is decided by an uncached `pick_stage`, so the memo can only change speed, not an answer. `GI_STAGE_CHECK=1` audits every scan and raises on a disagreement ([w22-speed](../docs/w22-speed.md) §1).

### The recursion ([solver.py](../gi/solver.py))

Solve / Continue with the orbit chain; primitive-quotient dispatcher (natural giant → GiantStep; small → enumerate; Johnson → GiantStep on recovered labels; product action → product refinement; abstract Sym/Alt → GiantStep on labels; else enumerate). The recognized structure is always verified.
Exact additions not in the paper: no Sym→Alt normalization, automorphism pruning, memo and one-mode, certificates only when labels are uniform, a Young-label step that aggregates over the whole instance. See [README](../README.md) for the option list; dispatcher modification (M) is `cameron_no_enum=True`.

#### What follows the paper and what does not

| Paper | Code |
|---|---|
| Alg. 1 (graph to positions) | `graph.graph_iso` |
| Alg. 5 Solve, Continue with orbit chain | `Solver.solve`, `Solver.cont` |
| Primitive-quotient dispatcher | `Solver.transitive`, `enum_cosets` |
| Johnson, product actions | recognized in `gi.group`, verified |
| Johnson outcome of Split-or-Johnson | `Solver.scheme_step` |
| Local certificates (Alg. 3), CheckNewWindow | `Solver.local_certificate`, `check_new_window` (off by default in benchmarks) |
| Large-symmetry branch | `Solver.giant_step` |
| LiftAndContinue, CombineExact | `Solver.lift_and_continue`, `solver.combine` |

**Simplified, exact but without the running-time guarantee:** aggregation is WL-style refinement of label colourings, and labels are individualized one at a time (no Design Lemma, no first rectangle); no row/column step; no phase, hierarchy-cap or hereditary-budget bookkeeping; κ = 3 by default (paper κ = 64), small quotients enumerated up to `enum_limit`; other large primitive quotients raise `Unsupported` beyond `max_enum`.

**Default practice.** In round 1 the paper's local certificates cost about 10–60× and never reduced branching, so benchmarks run with `certificates=False`. On the tiers, the 2-WL front end and bounded individualization do most of the work; the recursion is an exact backstop. On non-isomorphic CFI at `ir=0` the recursion was 14× faster than the hybrid.

### The bounded pipeline ([bounded.py](../gi/bounded.py))

For connected X, Y and an oriented root edge, Luks's step extends G_r = Aut_f(X_r) one layer at a time through two string problems: up-sets under G_r; twin classes and inner edges under ρ(G″) ⋉ ∏ Sym(twin classes). Groups stay in Γ̂_{d−1}. The module docstring contains the exactness argument. Later improvements, all exact:

* **rooted 1-WL** with the root edge individualized, canonical names;
* **class layers** (`class_plan`): colour-class order that keeps groups elementary abelian on CFI-type graphs, with BFS fallback when a twin block of ≥ 3 appears;
* **elementary abelian layers** by Gaussian elimination over F₂ on bitmasks, no Schreier–Sims;
* **sparse generators** and worklist 1-WL (w14);
* **staged root classes** and **discrete rooted certificates**;
* **compiled closures, edge-orbit absorb and vertex maps** (w23), preserving the BFS orders the isomorphism tests depend on.

### Canonical labeling

[gi/canon.py](../gi/canon.py) is the canonical version of Luks's reduction (Babai–Luks 1983). Components sorted by form; least rooted form over a canonical class of edges; per layer two string canonizations. Layer canonizers: invariant strings (no work), elementary abelian least image (`EAAction.canon`), `ir_canon` for phase-2 layers that are coloured-graph problems, and `perm_canon`, a least-image search over a stabilizer chain with automorphism pruning, for the rest.

**Automorphism probe and lazy layer groups (w23).** Before a root edge is computed, a parallel individualization-refinement descent from the best root and from that edge proposes a bijection. It counts only if it is verified to be a color-preserving automorphism, so the probe cannot change the form. The probe is capped at 64 refinements and 3 failures per graph and tried only when |K| ≥ 16. `_perm_H` returns a `_LazyGroup`, so a layer's group H gets a stabilizer chain only if its string is not invariant. Reasons and data: [w23-speed2](../docs/w23-speed2.md) §1, §4.

**No polynomial guarantee.** `perm_canon` and `ir_canon` are exponential in the worst case; the probe does not change this; no adversarial family was tried. Theorem A or BL83's canonical Luks recursion would be the polynomial replacement; neither is implemented ([w9-canontool](../docs/w9-canontool.md) §4, [w14-solver](../docs/w14-solver.md)).

## The compiled kernel

[gi/_ckernel.c](../gi/_ckernel.c) compiles hot primitives. Python stays the reference and every output is identical with the kernel on or off; unusual input is declined before any state changes.

| Added by | Primitives |
|---|---|
| w16 | `wl2_single`, `wl2_check`, `mul`, `inv`, `act`, `maps`, `sift`, `sifts_to_id`, `make_fast_plan`, `orbits` |
| w22 | `clean`, `action_on_pairs`, `refine_labels_pairs` |
| w23 | `wl_refine`, `class_plan`, `balls_new/step`, `orbit_table/absorb`, `closure_dense`, `closure_sparse`, `ea_compose`, `ea_who_add/remove`, `ea_canon`, `check_lists`, `bfs_dist`, `is_automorphism` |

* A stale build is ignored with a warning (SHA-256 of the source). `GI_NO_CKERNEL=1` disables it. `GI_REQUIRE_CKERNEL=1` makes absence a test failure.
* Invalid input falls back to the Python path, so errors match.
* Effect. Measured at w16: default hybrid 2.0–2.4×, `ir=0` 1.5×; bounded and canonical then only 1.00–1.15×. w23 compiled those paths. Current numbers are in [Benchmarks](Benchmarks.md#canonical-forms-and-bounded-isomorphism). Upper bounds for further compilation were estimated in [w16-ckernel](../docs/w16-ckernel.md) §6, before w23.

## Correctness checks

**Tests** ([tests/](../tests/)). On master after the w22 and w23 merges, `python3 -m pytest -q tests` reports **2679 passed with the kernel on and 1910 passed with `GI_NO_CKERNEL=1`** ([overnight log](../docs/overnight-log.md)). Earlier counts were against different trees: 487 at w9, 553 with the kernel, 954 at w14, 1039 collected at `b1a2d03`, 1453 passed at w22 and 1779 at w23 (kernel on). New in w22 and w23: [tests/test_stage_memo.py](../tests/test_stage_memo.py), pinned to `method="hybrid"` because auto dispatch sends small graphs elsewhere, and [tests/test_w23.py](../tests/test_w23.py). Checks are against brute force on small graphs (exhaustive for n ≤ 5 in `test_canon.py`), VF2, hand-known orders, and mutation tests in a few places (for instance six plausible breakages of the pruning).

**Run-time verification of benchmarks.** `bench/run.py` checks each answer edge by edge, each generator is an automorphism, and the order of the generated group (by sympy, independently of `gi`) equals the known |Aut|. A wrong answer is a failure regardless of speed. `bench/irhard.py` and `bench/canon.py` also verify σ, generators and |Aut| (0 errors were recorded in any run, including for nauty modes where they finished). Non-isomorphism labels in [bench/families.py](../bench/families.py) are verified by networkx or justified by a theorem at the call site, after the [3reg12 incident](Corrections.md#benchmarks-and-software).

**Ground truth at scale.** For Neuen–Schweitzer multipedes, `iso`/`non-iso` and |Aut| = 1 come from a lemma (NS17 Lemma 2.3 extended to isomorphisms), with its four conditions checked per instance (`bench/irhard.py audit`).

**Memory safety.** The kernel passed the whole suite under ASan + UBSan (`python3 build_ckernel.py --asan`) with no report, and a leak smoke test, at w16. At w23 the suite was run the same way, and it found one real report during the work (a zero-length `memcpy` from a null pointer), since fixed ([w23-speed2](../docs/w23-speed2.md) §5).

**Limits of these checks.** They test instances. They do not prove exactness of the code; the arguments are in docstrings and memos.
