# w22-speed: an incremental stage loop and cheaper Schreier–Sims

Outputs are identical to the base commit (1d3dacd): over the 112 tier/mode cells below, every σ, every
generator list and every `solver.stats` digest matches, in every round. The default hybrid is 1.5–1.6×
faster on the large and xl tiers, and `ir=0` is about 1.5× faster. Tiers of a few milliseconds are flat.
Numbers are for commit 03b4452 (later commits change only tests and docs), on one machine (64 cores, load
2–5, `nice -n 19`).

## 1. The stage loop

`pick_stage` rechecked every factor pair after every stage: 15–70 `clean` calls per stage, 18–38% of the
instance time. Yet about 90% of iterations do not refine, and between refinements `y` only changes as
`pull_back(y, π)`.

`graph.StageMemo` keeps the verdict of each block across one `staged_iso` loop, and `pick_stage_tracked`
makes the checks of `pick_stage` in the same order, taking unchanged verdicts from the memo. `pick_stage`
itself is unchanged and stays the reference.

**The invariant.** Whenever the tracked scan runs, every stored verdict of two current factor objects
equals what `pick_stage` would compute now. A verdict is a function of `x` and `y` on the block and of the
factors' `(P, gens)` only, and:

* (a) `x` and `y` are only ever rebound, never mutated. `x` changes only at a refinement, which clears the
  memo; `y` changes at a refinement or as `pull_back(y, π)`, and π is reported to `moved()`.
* (b) `pull_back(y, π)[i][j] = y[π i][π j]`, so an entry whose indices π fixes does not change. Every
  factor holding a moved vertex gets a new serial, and verdicts are keyed by serials. If π moves a fixed
  vertex (the loop never does), everything is cleared.
* (c) A factor object is never mutated and is held alive while its `id()` is a key. Classes that did not
  split keep their factor object through `align`, so their verdicts survive.
* (d) `fixed` only grows and its vertices never move. A check against the fixed vertices is a conjunction
  over them, so a verdict for `fixed[:m]` extends by checking the new vertices only, and a dirty one stays
  dirty.

**Soundness does not rest on the invariant.** A wrong "dirty" only causes a redundant exact stage. "fail"
is only returned from a direct comparison. A wrong "clean" could only matter where the loop ends, and that
is decided by an uncached `pick_stage`, so the memo cannot change an answer (it would only change speed).
That one full rescan per loop costs about 0.3% of the xl time.

**Debug mode.** `GI_STAGE_CHECK=1` (module flag `STAGE_CHECK`) runs `StageMemo.audit` after every scan: the
full rescan must return the same stage, and every stored verdict is recomputed. A disagreement raises.

Also in the loop: identity `pull_back`s are skipped (77% of them on CFI), and `align` reads the diagonals
once instead of once per class.

## 2. New kernel functions

`clean`, `action_on_pairs` (the generators of a stage on its positions, which `solve_on` built in Python,
16–22% of the full-hybrid time), and `refine_labels_pairs` (`solver.refine_labels` without hypergraphs).
All follow the kernel's contract: only the shapes the solver produces are handled, anything else returns
`None` and the Python body runs, so invalid input gets the reference's result or exception. The Python code
stays the reference. `refine_labels_pairs` assigns the pair codes in the reference's order of first
appearance, because the numeric codes decide the final names.

## 3. Schreier–Sims and chains

* **Chain cache front** (`_CHAIN_IDS`). A key by value costs generators × degree to hash. Repeated groups
  usually arrive as the same tuple objects, so `(n, ids of the generators, base)` is tried first. An id is
  only compared while its object is alive: each id-key is stored with a tuple holding its generators, and
  it leaves the table when the chain is evicted. Aliases are charged to the cache size.
* **Shared trivial levels.** A prescribed base of thousands of points allocated five containers per level,
  nearly all of which stay trivial. `{b: idn}` is now shared by (degree, point), and `_par` and `_ok` are
  shared or lazy. Level dicts are only ever replaced, never written to, except `_ok`, which is created when
  a level needs it.
* **Incremental level scans.** `_schreier` visited 2.8M pairs for 338k pieces of real work on the large
  tier. A level whose transversal is unchanged since its last *complete* scan only needs the generators
  appended since: every older pair is verified against the same `u`, `v`, and stays verified because
  `<S[i+1]>` only grows. `_orbit` keeps its old dicts when a rebuild is identical, so that this shows by
  identity. 75% of the pair visits go.
* Per-level Python generators replaced by C-level `map`/`bisect` (`_store`, `image_order`, the image
  levels), and `solve` builds `xs`/`ys` with `itemgetter`.
* `refine_labels`: 6.2 s → 0.6 s of the cProfile time of the large tier with `ir=0`.

## 4. Tests

`python3 -m pytest -q tests`: **1453 passed, 19 skipped** with the kernel (`GI_REQUIRE_CKERNEL=1`), **1379
passed, 93 skipped** with `GI_NO_CKERNEL=1`. The checks in `bench/run.py` and `bench/families.py` are
unchanged.

`tests/test_stage_memo.py` adds: tracked against full scans on random states, and on whole tiers with the
audit on; that the audit does detect stale verdicts; a loop-level test that a refinement forgets verdicts
(a clean block turned dirty); fault injection (a tracked scan that always says "clean" leaves every output
unchanged, and spurious dirty stages stay exact); C against Python on random and invalid inputs; the chain
cache under id reuse and eviction, against fresh construction; and chains against the unoptimized reference
`tests/_ref_group.py` (element order included). `tests/test_group.py`, which already compares against that
reference, covers the scan skip.

**Debug sweep.** `GI_STAGE_CHECK=1 python3 bench/run.py` (the sympy check of |Aut| included), results in
`bench/results/w22-audit-*.json`:

| run | result |
|---|---|
| hybrid, tiers through xl, `certificates=False` | 56/56 correct, no audit failure |
| `ir=0`, through xl, `certificates=False` | 56/56 |
| hybrid, through xl, `GI_NO_CKERNEL=1` | 56/56 |
| hybrid, through large, default `Solver()` | 47/47 |
| `ir=0`, through large, default `Solver()` | 47/47 |

**Mutation checks of the tests** (each mutant in a throwaway copy, against `tests/test_stage_memo.py` and
`tests/test_group.py`). Caught: an alias not holding its generators; eviction leaving id-keys behind;
`moved()` doing nothing; no memo clear at a refinement; no final rescan; the fixed-vertex prefix not
extended; new fixed rows left unchecked; a write to the shared `_NO_PAR`; the skip ignoring whether `T`
changed; `_orbit` keeping changed dicts; a wrong Schreier edge index; a level marked as scanned before its
scan finished; a self-evicting alias; `_cont` reordering the cached orbit list. One mutant is equivalent and
survives: dropping `queue == list(oT)` from `_orbit`, since identical tree edges fix the BFS order (the
check is defensive). Three mutants (the self-evicting alias, the missing clear at a refinement, the
reordered orbit list) first escaped; the deterministic tests for them were written because of that.

Two of these were real bugs while this branch was written, which is why those tests exist: an alias id-key
whose generators the chain did not hold (a recycled id gave an unrelated group a false hit, caught only by
the `order` guard), and a chain evicting itself during its own alias registration (a `KeyError`). Both were
in the id-keyed front of the chain cache; neither reached a commit.

## 5. Paired timings

`bench/paired.py` runs two checkouts in fresh processes, alternating (before, after, then after, before),
over 3 rounds, keeps the minimum per instance of solver time alone, and compares the digest of the output
and of `solver.stats`. Data: `bench/results/paired-w22-final.json`. `certificates=False`, as in
docs/w16-ckernel.md; both sides have the compiled kernel.

| workload | before (s) | after (s) | speedup |
|---|---|---|---|
| tiny, small, medium (hybrid) | 0.063 | 0.060 | 1.05 |
| hard (hybrid) | 0.153 | 0.113 | 1.36 |
| large (hybrid) | 1.541 | 1.009 | 1.53 |
| xl (hybrid) | 4.848 | 3.065 | 1.58 |
| tiny, small, medium (`ir=0`) | 0.113 | 0.081 | 1.40 |
| hard (`ir=0`) | 0.366 | 0.282 | 1.30 |
| large (`ir=0`) | 19.232 | 12.985 | 1.48 |
| xl (`ir=0`) | 54.994 | 37.469 | 1.47 |

xl hybrid per instance: CFI(3reg14)-twist 2.04×, CFI(3reg14) 1.90×, Q7 1.60×, rook10 1.44×, Kneser(10,3)
1.41×, the rest within ±5% (PG(2,7) 0.96×, a small loss). xl `ir=0`: PG(2,7) 2.22×, rook10 1.37×, CFI
1.26–1.28×, Kneser(10,3) 1.21×, Q7 1.20×, Paley101 1.18×.

## 6. What dominates next

* **Hybrid (xl, wall clock).** The recursion is 30%; the stage overhead around it (group construction,
  chunking and orbit bookkeeping in `solve_stage`) about 25%; refinement 10%; the tracked scan 9%, mostly
  the first scan after each refinement, which cannot reuse verdicts; `new_factors` 5%.
* **`ir=0`.** `_orbit` and `_schreier` remain (dict operations on transversals and tree edges, which the
  kernel's marshalling helps little), then `mul`, `orbits_shared`, and `_trivial_levels` at new degrees.
  Q7 is 22 of the 37 s of xl with `ir=0`. It needs fewer groups rather than cheaper ones: as noted in the
  README, its Young classes fall below `young_min` and the orbit chain runs on degree-n² groups.
* bounded-degree and canonical paths were not touched; they wait for w14-solver.
