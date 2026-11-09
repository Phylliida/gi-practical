# w23-speed2: compiling the bounded and canonical paths, and why hypercubes were slow

Before = commit 04de436, after = branch w23-speed2. Both were run on the same machine under `nice`, one
heavy process at a time. `bench/w23.py` alternates the two trees in fresh processes and keeps the minimum
of the repeats (3 rounds with the kernel, 2 without). The machine's load ranged from 3 to 31 during the runs.
The kernel stays optional, and Python stays the reference and the fallback.

**Short version.** Paired canonical forms (both graphs of a pair) got 1.7–8.4× faster (2.2–8.4× at the largest
size of each family), and `bounded_iso` 1.1–2.5× faster, with no slowdown with the kernel on. Forms, labellings and `bounded_iso` results are
byte-identical to the base commit on every instance. Only the generator *lists* of highly symmetric graphs
change (same groups). Traces is still ahead on every family except multipedes. The gaps are about 7× on CFI,
about 23× on Miyazaki, 14–29× on Q12 and 3–6× on 3-regular graphs (Traces' clock resolves 0.01 s).

## 1. Why hypercubes were slow

Q12, one canonical form, base commit, 2.2 s. (The `absorb` share is from cProfile, the others from timers around
each section; the Schreier–Sims row is part of the rooted runs, so the rows do not add up.)

| where | share | what it is |
|---|---|---|
| `absorb` in `canon_connected` | about 44% | a union-find over all 49 152 oriented edges, once per generator, through Python dicts |
| three full rooted runs | about 36% | each rebuilds the S₁₁ chain and every layer group from scratch |
| `_truncated_profiles` | about 14% | 13 bit-parallel ball rounds on Python big ints, then tallies of 49 152 tuples |
| Schreier–Sims for H at each layer | about 8% | a stabilizer chain nobody reads (next row) |
| `perm_canon` | 0% | never called (0 nodes) |
| `ir_canon` | about 3% | 3 layers, 693 nodes |

So the cause was neither `perm_canon` nor the layering (11 BFS layers). In 60 of the 66 string canonizations the
string is invariant under the group, so no search happens at all. The time went to group bookkeeping that
is never used, to redoing the same work once per root, and to Python-level loops over K. The fixes are
algorithmic first:

* **Automorphism probe** (`_probe_automorphism`). Before a root edge is computed, a parallel
  individualization-refinement descent from the best root and from that edge proposes a bijection. It counts only
  if it is verified to be a color-preserving automorphism. Q12 goes from 3 roots to 1 root and 2 probes. The probe
  is capped at 64 refinements and 3 failures per graph, and is tried only when |K| ≥ 16.
* **No unused chains.** `_perm_H` returns a `_LazyGroup`. H's stabilizer chain is built only if a layer's string
  is not invariant. Its generator list equals what `PermGroup` keeps: the rank-wise extensions of U1, and
  the Sym generators of the first block of each U1-orbit of positions. The others are conjugate under the
  extensions, hence redundant. A test checks equality against `PermGroup` during canonization.
* **One action table per layer.** The closure of the positions, the invariance test, the rank-wise extension and
  the block checks used to recompute the same images up to three times.
* **Compiled edge orbits and balls.** `orbit_absorb` and `balls_step`. The stage-1 keys are recomputed only when
  the vertex partition changes. The loop over K stops once K is one orbit.

Q12 went from 4.83 to 0.57 s per pair. What remains is about 26% the rooted run, 21% root class and 13% probes,
at Python speed. Traces finds the group with a few refinement paths in C.

## 2. What was compiled

All of it is in one delimited block of `gi/_ckernel.c`. Unusual input is declined before any state changes.

| primitive | reference | used by |
|---|---|---|
| `wl_refine` | `wl.refine` | every rooted coloring, `ir_canon`, the probe |
| `class_plan` | `bounded.class_plan` | layer plans |
| `balls_new/step` | `_truncated_profiles` | root class |
| `orbit_table/absorb` | `absorb` (`canon`, `bounded`) | edge orbits |
| `closure_dense`, `closure_sparse` | `_closure_*`, the closures of `layer1_ea/layer2_ea` | positions and their action (`kind & 2` keeps BFS order) |
| `ea_compose`, `ea_who_add/remove` | `ea2.compose`, `SparseEA` index | restriction of the layer groups |
| `ea_canon` | `EAAction.canon` | word-parallel F₂ elimination, same bases |
| `check_lists`, `bfs_dist`, `is_automorphism` | `_check_lists`, `_bfs_dist`, the probe's check | input check, root class, probe |

The F₂ solver turned out not to dominate. `ea_canon` is worth 3–8% on Miyazaki and multipedes. On multipedes the cost was
`SparseEA.restrict` (composing generators with supports of about 600 points), which `ea_compose` and the index
primitives took from 1.6 s of a 3.8 s profile to about 0.25 s.

## 3. Paired results

Seconds. canon = both canonical forms of a pair, biso = `bounded_iso_lists` with Aut. Traces and sparse nauty (`dnt`,
`dns`, dreadnaut 2.9.1, cpu time at 0.01 s resolution, timeout 120 s) come from `bench/canon.py` on the final code.

| instance | n | canon before | canon after | ratio | biso before | biso after | ratio | Traces | sparse nauty |
|---|---|---|---|---|---|---|---|---|---|
| CFIx80 | 800 | 0.206 | 0.076 | 2.7 | 0.101 | 0.056 | 1.8 | 0.01 | 1.37 |
| CFIx320 | 3200 | 1.396 | 0.431 | 3.2 | 0.591 | 0.361 | 1.6 | 0.06 | 72.9 |
| mz50 | 1000 | 0.262 | 0.095 | 2.8 | 0.125 | 0.082 | 1.5 | 0 | 1.82 |
| mz150 | 3000 | 1.836 | 0.465 | 3.9 | 0.552 | 0.352 | 1.6 | 0.02 | >120 |
| Q8 | 256 | 0.135 | 0.020 | 6.7 | 0.074 | 0.060 | 1.2 | 0 | 0 |
| Q10 | 1024 | 0.743 | 0.113 | 6.6 | 0.416 | 0.259 | 1.6 | 0 | 0 |
| Q11 | 2048 | 2.019 | 0.256 | 7.9 | 1.018 | 0.664 | 1.5 | 0.02 | 0.02 |
| Q12 | 4096 | 4.834 | 0.574 | 8.4 | 2.715 | 1.819 | 1.5 | 0.04 | 0.03 |
| 3reg1000 | 1000 | 0.062 | 0.023 | 2.7 | 0.056 | 0.034 | 1.7 | 0 | 0.34 |
| 3reg4000 | 4000 | 0.252 | 0.114 | 2.2 | 0.281 | 0.113 | 2.5 | 0.04 | 13.1 |
| 4reg4000 | 4000 | 0.284 | 0.132 | 2.2 | 0.314 | 0.146 | 2.1 | | |
| ns16 | 352 | 0.080 | 0.031 | 2.6 | 0.068 | 0.035 | 2.0 | 0.01 | 0.02 |
| ns64 | 1408 | 0.419 | 0.171 | 2.5 | 0.290 | 0.147 | 2.0 | >120 | 4.90 |
| ns112 | 2464 | 0.833 | 0.335 | 2.5 | 0.631 | 0.340 | 1.9 | >120 | >120 |
| ns256 | 5632 | 3.633 | 1.433 | 2.5 | 2.137 | 1.027 | 2.1 | >120 | >120 |
| nst64 | 768 | 2.575 | 1.089 | 2.4 | 2.225 | 1.706 | 1.3 | | |

Traces and sparse nauty were not run past the first timeout (`bench/canon.py` skips larger sizes after one), so
`>120` above n = 1408 (Traces) and n = 2464 (sparse nauty) means that. The non-isomorphic twins of each pair
are in `bench/results/w23-paired.json` and match these timings. Data: `bench/results/w23-paired.json`,
`w23-paired-nock.json`, `canon-w23-{cfix,cube,mzgen,reg3,ns}.json`.

**Multipedes.** The result stands and improves: n = 5632 in 1.43 s (both forms), while Traces and nauty time out.

**Without the kernel** (pure Python, same algorithmic changes), canon before → after: Q12 5.12 → 2.42, CFI n = 3200
1.39 → 0.83, Miyazaki n = 3000 1.82 → 0.95, 3-regular n = 4000 0.248 → 0.226, ns256 3.65 → 3.07. Over the 42 rows
canon is 1.0–2.1× and biso 0.90–1.29×.

**Canonical forms on the benchmark tiers** (56 instances, `bench/families.py`): total 2.29 → 0.57 s, forms identical,
every decision correct; PG(2,5) exceeds the 25 s limit of this check in both versions. The probe saves roots across
all the symmetric families (rook10 0.72 → 0.16 s, Kneser(10,3) 0.24 → 0.04 s, Paley101 0.11 → 0.02 s); no instance taking
over 10 ms got slower by more than 15%.

**Slowdowns.** With the kernel on, none: the smallest ratios are 1.7 (canon) and 1.12 (biso). Without the kernel (Python only),
four of the 84 cells are below 1: biso ns16 0.069 → 0.077 s (0.90×), biso ns160-twist 0.98×, biso Q8 0.99×, canon ns32 0.995×.
The difference on ns16 is 8 ms; I did not isolate its cause.

## 4. Exactness

* Compiled primitives mirror their references step by step, including cell naming in `wl_refine`, `class_plan`'s tie
  breaking, the BFS orders the isomorphism tests depend on and the F₂ basis choices. `tests/test_w23.py` compares each
  with its reference on random input, in addition to digests of whole pipelines in both modes.
* **Digests.** Canonical form, labelling and `bounded_iso` result are equal to the base commit on all 51 paired rows
  with the kernel on and all 42 with it off. Generator lists differ on hypercubes in the paired rows (Q6–Q12), because a probe contributes
  its automorphism in place of the equal-key one; `bench/canon.py` verifies each generator and the group order.
* The probe cannot change the form: it only skips an edge that a *verified* automorphism maps from the best root, and such
  an edge has the same rooted form. Aut is still generated: every edge of the least orbit is reached from the best root by
  automorphisms that were found, either the equal-key ones or the verified probes.
* `_LazyGroup` carries H's exact order and generators; the chain is built as soon as a non-invariant string needs it.

## 5. Tests and correctness runners

`python3 -m pytest -q tests`: 1779 passed, 19 skipped with the kernel (`GI_REQUIRE_CKERNEL=1`); 1020 passed, 778 skipped with
`GI_NO_CKERNEL=1` (the extra skips are the C-versus-Python comparisons).

* `tests/test_w23.py`: randomized equivalence of every new primitive against its reference, unusual input declined with
  no state changed, `_LazyGroup` generators equal to `PermGroup`'s during canonization, the probe's soundness, canonical forms
  under relabelling, |Aut| of hypercubes, and whole-pipeline digests with the kernel on and off.
* **Sanitizers.** The whole suite passes with the kernel built `--asan` (ASan + UBSan, no recovery, libasan preloaded,
  `PYTHONMALLOC=malloc`): 1779 passed, 19 skipped. It found one real report during the work (a zero-length `memcpy` from a null pointer
  for an empty up-set), now fixed.
* **On and off.** Labellings, generators, forms and `bounded_iso` results of the final code are identical with the kernel on and off
  on 42 benchmark instances.
* **Correctness runners** (files unchanged). `bench/run.py` through xl: 56/56 correct with the kernel on (3.9 s) and off (8.8 s),
  including sympy's |Aut| check. `bench/canon.py` on cfix, cube, mzgen, reg3 and ns: no WRONG. `bench/irhard.py audit --size 112`: the
  lemma answers, σ on every edge and |Aut| verified.

## 6. Where we still lose

* Traces wins every family except multipedes from n = 1408 up (it also wins ns16 and ns32), and sparse nauty wins hypercubes. What is left
  is mostly Python per layer: `RootedCanon.step` (the largest single item on CFI and Miyazaki, 40–60%), `_Rooted` construction and the
  root class.
* `ir_canon` and `perm_canon` remain exponential in the worst case. The probe does not change this.
* Non-elementary-abelian groups on long graphs stay in dense tuples, at O(layers · generators · n). A cycle of 1000 hubs with
  two leaves each (n = 3000) takes 17 s per graph; the base commit needed over 140 s. A sparse representation of those groups
  is the next algorithmic step.
* `bounded_iso` on hypercubes (1.8 s at Q12) is dominated by Schreier–Sims inside `_step_perm`, which is w22's area.

## 7. Reproduce

```sh
python3 build_ckernel.py
git archive 04de436 | tar -x -C /some/dir && (cd /some/dir && python3 build_ckernel.py)
nice python3 bench/w23.py run --base /some/dir --label paired --rounds 3
nice python3 bench/w23.py run --base /some/dir --label paired-nock --rounds 2 --no-ck --only cube,cfix,mzgen,reg3,ns
python3 bench/w23.py table --label paired
nice python3 bench/canon.py run --family cube --sizes 6,8,9,10,11,12 --modes canon,biso,dnt,dns --timeout 120 --label X
python3 -m pytest -q tests && GI_NO_CKERNEL=1 python3 -m pytest -q tests
```
