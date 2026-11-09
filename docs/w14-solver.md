# w14-solver: profile-driven speedups of the bounded and canonical pipelines, and pipeline dispatch

Measured on the families where we lost to Traces and nauty. Before = commit d6db110, after = this
branch, both run back to back on the same machine under `nice`, one benchmark at a time; dreadnaut
2.9.1. Short single-core jobs (a few seconds of pytest, git) ran alongside some runs, and the machine
(64 cores) had a load of about 2-4 from other work. One seed per size.
Data: `bench/results/canon-w14-*.json` (`-base` = before, `-new` = after, `-nauty-*` = the three
dreadnaut modes), `bench/results/w14-tiers-{base,new}.json`.

## 1. What the profiles showed and what changed

Everything below is exact; every answer was checked as in `bench/` (§4).

* **Dense generators per layer (the main cost on CFI, Miyazaki, multipedes).** Every elementary
  abelian (EA) layer step in `gi/bounded.py` and `gi/canon.py` carried the group as dense permutation
  tuples: O(k·n) per layer for k generators, even when a layer touches two points. New: `gi/ea2.py:
  SparseEA`, generators as dicts of moved points with a point → generators index. A layer step now
  costs the generators that move its points, and generators are extended in place to new layers
  (images of old points never change, so older layer data stays valid). No O(n) copy per layer; the
  coset representative and its inverse are updated on supports. `EAAction` runs on the active
  generators only; the others act trivially on the positions.
* **Hopcroft-style 1-WL (`gi/wl.py`).** Worklist partition refinement replaces round-based rooted
  1-WL, O(m log n) instead of O(rounds·m), and rooted runs start from the stable coloring with only
  the individualized cells on the worklist. Every decision depends only on sizes, counts and colors,
  so the names are a function of the rooted isomorphism type.
* **Staged root selection (`root_class`).** The O(diam·|E|) edge invariants on all oriented edges
  (16 s of a 31 s profiled run on Miyazaki n=2000) are replaced by stages: 1-WL color pair; sphere-size profiles, stopped
  at the radius where a class of ≤ 8 edges appears; then the old invariant, skipped when the class
  is too large. Every isomorphism respects these classes; `iso` selects the same keys in Y.
* **Discrete rooted certificates (`discrete_cert`).** A root whose rooted refinement is discrete
  needs no chain: compare a certificate of the rooted graph (exact: colors are a function of the
  rooted isomorphism type). On a rigid random Latin square pair (n = 64) the profiled run went from
  27 s to 6.4 s; what remains is one refinement per root. Under dispatch most such rigid inputs go to the
  hybrid pipeline anyway, so this mainly helps rigid graphs of low degree or above n = 256.
* **`ir_canon`.** Phase-2 layers where H = U1 × ∏Sym(blocks), U1 moving no block, are a colored
  graph problem; solved by individualization-refinement instead of `perm_canon`. On Q11 `perm_canon`
  took 0.9 s of a 3.3 s profiled run (84k search nodes); it is no longer called on Q10 and Q11.
* **Smaller items.** `class_plan` keeps its neighbourhood counts incrementally; the orbits of the
  root class stop being updated once they are one orbit; repeated `is_ea2` checks are avoided.
* **Dispatch (`graph_iso(method="auto")`, the new default).** Deterministic: bounded when
  maxdeg ≤ 8 or n > 256, hybrid otherwise; explicit front-end options select hybrid. A bounded run
  with a work budget (100·n² units charged by `Solver.solve/cont` and Schreier–Sims, `gi.group.WORK`; at
  most 3n rooted tests) falls back to the hybrid pipeline. Which pipeline ran is in `solver.stats`
  (`pipeline_bounded`, `pipeline_hybrid`, `pipeline_fallback`). The thresholds come from measuring both
  pipelines on the tiers and on `bench/hardness.py` (bounded is 2–100× faster on low-degree/CFI/multipede
  families; hybrid wins on rigid dense graphs and designs, where bounded runs out of budget).

Not done: the solvable-layer extension of `ea2` (candidate 1). The profiles did not point to it:
`luks_ea_fallback` was 0–3 per run where I looked (nst, CFI over 4-regular bases, Q8, jgad), and
`perm_canon` stays small on the natural families (nst n = 768: 88 calls, 528 nodes; CFI(4reg): about
80 nodes). Only the constructed Johnson gadgets reach tens of thousands of nodes (jgad12: 98k). No time
went into building inputs that attack `perm_canon`. So layers with non-EA groups still go through
`Solver.solve`/`perm_canon`, and **`gi.canon` still has no polynomial guarantee at d ≤ 5**.

## 2. Why it is exact

* **WL (gi/wl.py).** Standard coarsest equitable partition (tested against round-based refinement
  and for canonical naming under relabelling). Hopcroft's "all but the largest" argument with counts
  is the difference-of-counts identity. Individualized cells are split from a stable coloring, so
  only the new singletons must be queued.
* **SparseEA.** The group elements are unchanged; only their representation is. Extension in place
  adds images of new points. A retired dict stays valid for its old points. The EA linear algebra is
  unchanged, restricted to active generators (others fix every position).
* **root_class.** Each stage key is an isomorphism invariant, including the truncation radius and
  the stage-2 skip rule, which depend only on class sizes, n and the profiles. `iso` compares class
  sizes and uses the same keys.
* **Certificates.** The certificate lists the root colors, the input color of each discrete cell
  and all edges by cell name; with discrete colorings, equality is an isomorphism of the rooted graphs,
  and inequality excludes one because the names are a function of the rooted isomorphism type. A
  mixed discrete/non-discrete pair is not isomorphic.
* **ir_canon.** Canonical labelling of the inner-edge graph under ∏Sym(blocks), a colored graph with
  fixed label classes: the search depends only on the isomorphism type, the least leaf is taken, and
  the same induction as in `perm_canon` (every least leaf is an automorphic image of a visited one)
  gives generators of the whole automorphism group. It is used only when U1 fixes every position
  holding a block, a property of the group as a set (principle P1 of the write-up).
* **Dispatch.** Both pipelines are exact; the budget only chooses which one finishes. Over-budget
  runs discard their work (only finished memo entries remain), and the counters are not clocks, so
  the pipeline used does not depend on the machine.

## 3. Results (paired before/after, nauty and Traces)

Before/after columns come from the same back-to-back runs. Traces and nauty columns are canonical
forms of a pair (cpu time, 0.01 s clock, so 0 means under 0.01 s and ratios against small cells are rough;
timeout 120 s, `>120` after a timeout at that size). The biso columns solve a different task (isomorphism plus
Aut, no canonical form). Twisted/non-isomorphic pairs are omitted here; they are in the JSON, and ours
match the isomorphic timings.

**CFI over random cubic graphs (cfix), isomorphic pairs** (seconds; canon = both canonical forms; biso = bounded_iso_lists with Aut)

| instance | n | canon before | canon after | biso before | biso after | Traces | sparse nauty | dense nauty |
|---|---|---|---|---|---|---|---|---|
| CFIx20 | 200 | 0.058 | 0.034 | 0.061 | 0.02 | 0 | 0 | 0.02 |
| CFIx40 | 400 | 0.18 | 0.085 | 0.156 | 0.042 | 0 | 0.12 | 0.24 |
| CFIx80 | 800 | 0.615 | 0.21 | 0.47 | 0.101 | 0.01 | 1.38 | 2.96 |
| CFIx160 | 1600 | 2.41 | 0.501 | 1.61 | 0.241 | 0.02 | 16.2 | 42 |
| CFIx320 | 3200 | 13.5 | 1.41 | 8.52 | 0.636 | 0.06 | 71.3 | >120 |

**Hypercubes** (seconds; canon = both canonical forms; biso = bounded_iso_lists with Aut)

| instance | n | canon before | canon after | biso before | biso after | Traces | sparse nauty | dense nauty |
|---|---|---|---|---|---|---|---|---|
| Q6 | 64 | 0.042 | 0.028 | 0.025 | 0.021 | 0 | 0 | 0 |
| Q8 | 256 | 0.223 | 0.126 | 0.129 | 0.092 | 0 | 0 | 0 |
| Q9 | 512 | 0.685 | 0.366 | 0.319 | 0.211 | 0 | 0 | 0.02 |
| Q10 | 1024 | 1.73 | 0.766 | 0.796 | 0.51 | 0 | 0 | 0.1 |
| Q11 | 2048 | 4.62 | 2.1 | 2.08 | 1.26 | 0.02 | 0.03 | 0.78 |
| Q12 | 4096 | 24.3 | 5.04 | 6.18 | 3.6 | 0.02 | 0.03 | 6.48 |

**Miyazaki graphs (mzgen), isomorphic pairs** (seconds; canon = both canonical forms; biso = bounded_iso_lists with Aut)

| instance | n | canon before | canon after | biso before | biso after | Traces | sparse nauty | dense nauty |
|---|---|---|---|---|---|---|---|---|
| mz25 | 500 | 1.08 | 0.131 | 0.848 | 0.06 | 0 | 0.15 | 0.53 |
| mz50 | 1000 | 3.98 | 0.271 | 3.66 | 0.124 | 0 | 1.89 | 5.89 |
| mz100 | 2000 | 19.5 | 0.804 | 17 | 0.31 | 0.01 | 22.8 | 78.1 |
| mz150 | 3000 | 66.5 | 1.86 | 44.7 | 0.557 | 0.02 | >120 | >120 |

**Random 3-regular graphs** (seconds; canon = both canonical forms; biso = bounded_iso_lists with Aut)

| instance | n | canon before | canon after | biso before | biso after | Traces | sparse nauty | dense nauty |
|---|---|---|---|---|---|---|---|---|
| 3reg200 | 200 | 0.012 | 0.009 | 0.035 | 0.009 | 0 | 0.01 | 0.04 |
| 3reg1000 | 1000 | 0.071 | 0.053 | 0.211 | 0.057 | 0 | 0.34 | 4.5 |
| 3reg4000 | 4000 | 0.455 | 0.256 | 1.31 | 0.264 | 0.02 | 12.9 | >120 |

**Neuen-Schweitzer multipedes (ns), isomorphic pairs** (seconds; canon = both canonical forms; biso = bounded_iso_lists with Aut)

| instance | n | canon before | canon after | biso before | biso after | Traces | sparse nauty | dense nauty |
|---|---|---|---|---|---|---|---|---|
| ns16 | 352 | 0.111 | 0.081 | 0.105 | 0.079 | 0.01 | 0.02 | 0.19 |
| ns32 | 704 | 0.246 | 0.153 | 0.26 | 0.124 | 0.05 | 0.12 | 2.94 |
| ns64 | 1408 | 0.595 | 0.414 | 0.565 | 0.294 | >120 | 4.84 | >120 |
| ns112 | 2464 | 1.24 | 0.825 | 1.42 | 0.662 | >120 | >120 | >120 |
| ns160 | 3520 | 2.12 | 1.65 | 2.49 | 1.2 | >120 | >120 | >120 |
| ns256 | 5632 | 4.2 | 3.63 | 3.79 | 2.14 | >120 | >120 | >120 |

**Shrunken multipedes (nst)** (seconds; canon = both canonical forms; biso = bounded_iso_lists with Aut)

| instance | n | canon before | canon after | biso before | biso after | Traces | sparse nauty | dense nauty |
|---|---|---|---|---|---|---|---|---|
| nst16 | 192 | 0.245 | 0.246 | 0.157 | 0.143 | 0.02 | 0 | 0 |
| nst32 | 384 | 0.781 | 0.732 | 0.233 | 0.306 | >120 | 0.02 | 0.23 |
| nst64 | 768 | 2.39 | 2.69 | 4.43 | 2.51 | >120 | 79.5 | >120 |

Random 4-regular graphs: canon before/after 0.40 → 0.28 s, biso 1.2 → 0.31 s at n = 4000. `nsr` (reduced
multipedes): canon 0.78 → 0.62 s, biso 0.70 → 0.23 s at n = 1152.

**Multipede claim.** The headline survives and improves: at n = 2464 sparse nauty, dense nauty and
Traces all exceed the 120 s limit here (sparse nauty 530 s in docs/w1-scale.md), and ours takes 0.66 s
(isomorphism with Aut) and 0.83 s (both canonical forms); `irhard.py audit --size 112` re-verified the
lemma-known answers, |Aut| = 1 and every edge of σ.

**Tiers (bench/run.py, tiny..xl, 50 instances, all answers checked):** 14.6 s → 8.8 s, 50/50 correct.
Dispatch: 31 bounded, 19 hybrid (2 of them fallbacks, PG(2,5) and PG(2,7)). Largest slowdowns: PG(2,5) 0.46 → 0.55 s
and PG(2,7) 1.77 → 2.06 s (the aborted bounded run), and rand12 1 → 2 ms. Dispatch also leaves time on the table:
degree above 8 at n ≤ 256 goes to hybrid even where the bounded pipeline was faster when measured alone (rook10
2.0 s against 0.2 s, Kneser(10,3) 1.4 s against 0.8 s).

**Dispatch on hardness families** (39 instances, `method="auto"` vs the old `graph_iso`; the two decisions
agree on every instance, σ was not re-verified in this run):
total 63.8 → 50.6 s. Large gains on CFI over grids/K5 and multipedes (e.g. CFI(grid3x5) 5.9 → 0.07 s). Budget
overhead is at most 0.3 s (PG(2,7)); STS13-pair 0.01 → 0.09 s, STS15-pair 0.03 → 0.14 s are the largest
relative slowdowns.

### Remaining losses

* Traces is faster on every non-multipede family: CFI n = 3200: 0.06 s vs 0.64 s (biso), 1.41 s
  (canon), about 10–23×; Q11: 0.02 vs 2.1 s canon, about 100×, and Q12 0.02 vs 5.0 s, about 250×; Miyazaki
  n = 3000: 0.02 vs 0.56/1.86 s, about 30–90×; random 3-regular n = 4000: 0.02 vs 0.26 s, about 13×.
* Sparse nauty beats us on all hypercubes (Q12: 0.03 s vs 5 s) and at the small end of some other
  families: CFI at n = 200, nst at n ≤ 384 (the sizes measured), ns up to n = 704 (level there for biso).
* **Slowdowns against before.** nst n = 768 canon 2.39 → 2.69 s (0.9×), nst n = 384 biso 0.233 → 0.306 s
  (0.8×). At n = 768 the layer count changed (548 → 587); the likely cause is that the color names changed and
  `class_plan` breaks ties by name, but this was not isolated. Dispatch fallbacks, listed above.
* `perm_canon` and `ir_canon` remain exponential in the worst case; no adversarial family was tried.

## 4. Tests

`python3 -m pytest -q tests` (Python 3.12): 954 passed, 19 skipped (was 487 passed, 19 skipped).
`tests/test_w14.py` adds, against brute force or VF2: worklist 1-WL vs round-based refinement and
canonical naming under relabelling; SparseEA products/restrict/index; `ir_canon` forms and full Aut
against enumeration of permutations; root-class invariance (classes map under relabelling, `keys` selects
them in the other graph); dispatch on random graphs in all three methods against VF2 with |Aut|; the
budget fallback path; colored and disconnected graphs; non-simple inputs going to hybrid; discrete
certificates. Every benchmark answer is verified as before (`bench/canon.py` checks, `bench/run.py`
with sympy orders). A one-off stress (not committed: base and new code on 195 graphs × 2 seeds of random,
structured, CFI and multipede instances, with perturbed pairs and VF2 where n ≤ 26) found no disagreement in
decisions or |Aut|.

## 5. Reproduce

```sh
PY=../r2-hybrid/.venv/bin/python
nice $PY bench/canon.py run --family cfix --sizes 20,40,80,160,320 --modes canon,biso,dnt,dns,dnd --timeout 200 --label X
nice $PY bench/canon.py run --family mzgen --sizes 25,50,100,150 --modes canon,biso,dnt,dns --timeout 200 --label X   # new: mzgen in bench/canon.py
nice $PY bench/canon.py run --family cube --sizes 6,8,9,10,11,12 --modes canon,biso --label X
nice $PY bench/run.py --tiers tiny,small,medium,large,xl --timeout 120 --label X
nice $PY bench/irhard.py audit --size 112
python3 -m pytest -q tests
```
