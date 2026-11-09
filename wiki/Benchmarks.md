# Benchmarks

Tables, caveats, and where the solver wins or loses. Later numbers supersede earlier ones. Raw data is in [bench/results/](../bench/results/). To rerun, see [Reproduce](Reproduce.md).

[Home](Home.md) · [Software](Software.md)

**Current as of master `b819c8d`** (no file under `gi/`, `bench/` or `tests/` has changed since `1368fb6`), which includes the merged `w22-speed` and `w23-speed2`. Tables headed "current" hold the latest numbers. Older numbers remain only where they show progress, under a heading or column that says so; do not cite those as current.

## Read these caveats first

* **Clocks differ.** Ours is Python wall time. Nauty and Traces via dreadnaut report C CPU time at 0.01 s resolution, so entries of 0 mean under 0.01 s and ratios against small cells are rough. pynauty runs in a subprocess.
* **One machine** (64 cores, shared; load between about 1.5 and 36 depending on the run; the memo for each table states it), `nice -n 19`, one benchmark process at a time. Many memos note the load; single timings are noisy (±30% in r4, about 1.5× in `hardness`). Paired runs alternate old and new code on each instance.
* **Seeds.** Headline tables use seed 0, one random instance per size. Multipede robustness was checked on seeds 1 and 2. Sizes after a first timeout were skipped, not measured, and shown as `>T`.
* **Timeouts differ between tables** (60 s to 600 s).
* **Task differs.** Our `biso` columns solve isomorphism plus Aut; canonical `canon` columns compute both canonical forms of a pair; dreadnaut columns are canonical-form runs. Our times from w16 on use the compiled kernel unless stated; earlier tables are pure Python.
* **Options.** Nauty and Traces were run with defaults, without invariants. They may do better with other options.
* **Kernel.** Since w23 the kernel also covers the hot code of the bounded and canonical paths, so those timings now depend on it (no-kernel numbers are [below](#canonical-forms-and-bounded-isomorphism)). Before w23 it barely affected them (1.00–1.15×, [w16-ckernel](../docs/w16-ckernel.md)).

## Progression on the benchmark tiers

The tiers are `tiny` (n ≤ 8), `small` (n ≤ 12), `medium` (n ≤ 20), `hard`, `large` (n ≤ 70) and `xl` (n ≤ 200): 56 instances in total ([bench/families.py](../bench/families.py)). Every answer is verified.

**Current (master after the w22 and w23 merges):** `bench/run.py` through `xl`, 56/56 correct in 3.3 s ([overnight log](../docs/overnight-log.md); the log does not state the kernel mode. Before the merge, w23 measured 3.9 s with the kernel and 8.8 s without, [w23-speed2](../docs/w23-speed2.md) §5). `bench/irhard.py audit` also ran after the merge.

**History.** Each row is the number at that stage, and all but the last are superseded. `bench/run.py` totals and paired solver-only times are not the same clock, so compare within a row.

| Stage | Result | Source |
|---|---|---|
| Baseline, no certificates | 14 of 29 with the mislabeled pair counted correct (13 ok, 1 wrong label, 15 timeouts in the raw file) | `baseline-nocert.json` |
| Round 1 merged | 29/29 in 4.4 s | `r1-merged-.json` |
| Round 1 on `large` | 18/18 in about 155 s | project notes |
| Round 2 merged, full hybrid | 56/56 in 16.2 s; `large` 154 s → 6.0 s, `xl` 387 s → 19.4 s | `r2-merged-full.json`, `r2-hybrid-*` |
| Round 2, recursion only (`ir=0`) | 33/33 in 322 s | `r2-merged-ir0.json` |
| Round 3 | full 16.0 s → 14.8 s; `ir=0` 321.2 s → 168.8 s | [README](../README.md) |
| w14 (dispatch), tiny…xl excluding `hard` (50 instances) | 14.6 s → 8.8 s, 50/50 correct | [w14-solver](../docs/w14-solver.md) |
| w16 kernel, per tier | `large` 3.69 s → 1.56 s; `xl` 10.29 s → 4.90 s (paired, solver only) | [w16-ckernel](../docs/w16-ckernel.md) |
| w16 verification, kernel on | 56/56 correct | `w16-verify-on.json` |
| w22 paired, hybrid, `certificates=False` (solver only) | `large` 1.541 s → 1.009 s; `xl` 4.848 s → 3.065 s (1.58×); tiers of a few ms flat | [w22-speed](../docs/w22-speed.md) §5 |
| w22 paired, `ir=0` (solver only) | `large` 19.2 s → 13.0 s; `xl` 55.0 s → 37.5 s (1.47×) | same |
| w23 verification, before merging | 56/56 in 3.9 s (kernel on), 8.8 s (off) | [w23-speed2](../docs/w23-speed2.md) §5 |
| Master after the w22 and w23 merges | 56/56 in 3.3 s | [overnight log](../docs/overnight-log.md) |

The r2 comparison with references (load about 35): our exact solver is about 1000× slower than nauty, faster than VF2 on non-isomorphic CFI/strongly-regular pairs and random regular graphs, and slower than VF2 on isomorphic symmetric pairs ([README](../README.md)).

**Where the recursion matters.** With individualization on, the recursion barely ran on the early tiers. Comparing `ir=0` and full shows when group theory beats refinement: the recursion beat the hybrid 14× on the non-isomorphic CFI pair in r1, and on CFI(4reg) in r3.

**The stage loop (w22).** Outputs are identical to the base over all 112 tier/mode cells (every σ, generator list and `solver.stats` digest). Per instance on `xl` hybrid: CFI(3reg14)-twist 2.04×, CFI(3reg14) 1.90×, Q7 1.60×, rook10 1.44×, Kneser(10,3) 1.41×, the rest within ±5% (PG(2,7) 0.96×, a small loss). What dominates next is in [w22-speed](../docs/w22-speed.md) §6.

## Headline: Neuen–Schweitzer multipedes (`ns`)

Rigid multipedes R(B(G_k, σ)), n = 22k vertices, degrees 8 and 3, built to give IR solvers exponential search trees. Answers and |Aut| = 1 follow from a lemma checked per instance. Seed 0.

**Current** (w23, kernel on; [w23-speed2](../docs/w23-speed2.md) §3). canon = both canonical forms of a pair, biso = `bounded_iso_lists` with Aut, seconds. Traces and sparse nauty use a 120 s timeout and were not run past the first timeout, so `>120` above n = 1408 (Traces) and n = 2464 (sparse nauty) means a timeout at a smaller size.

| n | canon | biso | Traces | sparse nauty |
|---|---|---|---|---|
| 352 | 0.031 | 0.035 | 0.01 | 0.02 |
| 1408 | 0.171 | 0.147 | >120 | 4.90 |
| 2464 | 0.335 | 0.340 | >120 | >120 |
| 5632 | 1.433 | 1.027 | >120 | >120 |

**Historical: w1, 600 s timeout.** The "ours" columns are the w1 code and are superseded by the table above. The competitor columns stand: w1 and w9 are the only runs with a timeout as long as 600 s. Times in seconds, iso/non-iso where given ([w1-scale](../docs/w1-scale.md) §3; `irhard-w1-ns.json`).

| n | ours iso (w1) | ours non-iso (w1) | dense nauty | sparse nauty | Traces |
|---|---|---|---|---|---|
| 352 | 0.13 | 0.17 | 0.19 | 0.02 / 0.04 | 0.01 / 0.00 |
| 704 | 0.31 | 0.32 | 2.8 / 2.9 | 0.12 | 0.05 |
| 1056 | 0.43 | 0.53 | 14.7 / 17.3 | 0.41 / 0.38 | 1.9 |
| 1408 | 0.57 | 0.70 | 204 / 223 | 4.8 / 5.7 | >600 |
| 1760 | 0.64 | 0.89 | >600 | 7.5 / 6.9 | >600 |
| 2112 | 1.02 | 1.13 | >600 | 67.8 / 68.7 | >600 |
| 2464 | 1.41 | 1.40 | >600 | >600 | >600 |
| 2816 | 1.51 | 1.70 | >600 | >600 | >600 |
| 3168 | 1.61 | 2.11 | >600 | >600 | >600 |

Fits on the w1 data: ours n^1.17 (R² 0.98); dense nauty 2^(9.3n/1000), sparse nauty 2^(6.4n/1000) (R² 0.97–0.99). Crossovers measured then: dense nauty from the smallest size; Traces between 704 and 1056; sparse nauty about 1056–1760 depending on σ (on seeds 1 and 2 it moves). From n = 1760 on ours won on all three seeds, 10–30×.

On the graph X alone at n = 2464, sparse nauty needs 530 s, 10.2 million nodes, depth 21; every leaf is bad because the graphs are rigid. Ours is now 0.340 s (biso) and 0.335 s (both forms) ([w23-speed2](../docs/w23-speed2.md) §3); at w14 it was 0.66 s and 0.83 s ([w14-solver](../docs/w14-solver.md)).

**What the win rests on:** rooted 1-WL and the class order turn each rooted test into linear algebra over F₂ with tiny groups. This is the group-theoretic advantage Neuen–Schweitzer point to, and it is a Luks-style advantage, not an HJ-specific one. It does not touch HJ's analysis.

## Canonical forms and bounded isomorphism

**Current** (w23, kernel on; [w23-speed2](../docs/w23-speed2.md) §3; data `bench/results/w23-paired.json`, `canon-w23-*.json`). Seconds; minimum over 3 paired rounds. canon = both canonical forms of a pair, biso = `bounded_iso_lists` with Aut. Traces and sparse nauty are dreadnaut 2.9.1, CPU time at 0.01 s resolution, 120 s timeout; "not run" means `bench/canon.py` did not include the family. The last column is the base commit `04de436`, kept to show progress.

| Family | Instance | n | canon | biso | Traces | sparse nauty | canon at `04de436` (older) |
|---|---|---|---|---|---|---|---|
| CFI | CFIx80 | 800 | 0.076 | 0.056 | 0.01 | 1.37 | 0.206 |
| CFI | CFIx320 | 3200 | 0.431 | 0.361 | 0.06 | 72.9 | 1.396 |
| Miyazaki | mz50 | 1000 | 0.095 | 0.082 | 0 | 1.82 | 0.262 |
| Miyazaki | mz150 | 3000 | 0.465 | 0.352 | 0.02 | >120 | 1.836 |
| hypercube | Q8 | 256 | 0.020 | 0.060 | 0 | 0 | 0.135 |
| hypercube | Q10 | 1024 | 0.113 | 0.259 | 0 | 0 | 0.743 |
| hypercube | Q11 | 2048 | 0.256 | 0.664 | 0.02 | 0.02 | 2.019 |
| hypercube | Q12 | 4096 | 0.574 | 1.819 | 0.04 | 0.03 | 4.834 |
| 3-regular | 3reg1000 | 1000 | 0.023 | 0.034 | 0 | 0.34 | 0.062 |
| 3-regular | 3reg4000 | 4000 | 0.114 | 0.113 | 0.04 | 13.1 | 0.252 |
| 4-regular | 4reg4000 | 4000 | 0.132 | 0.146 | not run | not run | 0.284 |
| `nst` | nst64 | 768 | 1.089 | 1.706 | not run | not run | 2.575 |

Forms, labellings and `bounded_iso` results equal the base on all 51 paired rows with the kernel on and all 42 with it off; only generator lists of highly symmetric graphs change (same groups; [w23-speed2](../docs/w23-speed2.md) §4). Across the paired rows, canon is 1.7–8.4× faster (2.2–8.4× at the largest size of each family) and biso 1.1–2.5×.

Dense nauty was not rerun for w23. At w14 it took 42 s on CFIx160 (n = 1600), 78.1 s on mz100 (n = 2000), 0.78 s on Q11 and 6.48 s on Q12, and timed out at 120 s on ns112, ns160, ns256, nst64, CFIx320, mz150 and 3reg4000 ([w14-solver](../docs/w14-solver.md) §3).

**Without the kernel** (pure Python, same algorithmic changes), canon before → after: Q12 5.12 → 2.42, CFI n = 3200 1.39 → 0.83, Miyazaki n = 3000 1.82 → 0.95, 3-regular n = 4000 0.248 → 0.226, ns256 3.65 → 3.07. Over 42 rows canon is 1.0–2.1× and biso 0.90–1.29×.

**On the benchmark tiers** (56 instances, `bench/families.py`): canonical forms total 2.29 → 0.57 s, forms identical, every decision correct. PG(2,5) exceeds the 25 s limit of this check in both versions.

**Why hypercubes were slow** ([w23-speed2](../docs/w23-speed2.md) §1): not `perm_canon` (0 nodes) and not the layering. Q12 spent about 44% in a union-find over all 49 152 oriented edges, and about 36% in three full rooted runs that rebuilt the same groups. The verified-automorphism probe and the compiled edge-orbit union-find took Q12 from 4.83 to 0.57 s per pair.

**Historical progression** of canon (both forms, seconds). Each column is superseded by the one to its right. "Before w14" is the w9 code; it comes from the [overnight log](../docs/overnight-log.md) w14 entry, and for ns256 from [w9-canontool](../docs/w9-canontool.md) §3.1.

| Instance | n | before w14 | after w14 | before w23 (`04de436`) | after w23 |
|---|---|---|---|---|---|
| CFIx320 | 3200 | 13.5 | 1.41 | 1.396 | 0.431 |
| mz150 | 3000 | 66.5 | 1.86 | 1.836 | 0.465 |
| Q12 | 4096 | not in the log | 5.04 | 4.834 | 0.574 |
| 3reg4000 | 4000 | 0.46 | 0.256 | 0.252 | 0.114 |
| ns112 | 2464 | 1.24 | 0.825 | 0.833 | 0.335 |
| ns256 | 5632 | 4.23 | 3.63 | 3.633 | 1.433 |

## Where we win and where we lose

**We win** against all three nauty modes on rigid `ns` multipedes from n ≈ 1100 (w1's measured crossover, which moves with σ for sparse nauty; in w23, Traces wins at n = 352 and 704 and times out at n = 1408, with no size between). We win on `nst` at n = 768 (ours 1.09 s for both forms in w23; Traces and dense nauty > 120 s, sparse nauty 79.5 s, last measured at w14). We beat sparse nauty on CFI and Miyazaki at larger sizes (CFIx320 0.43 s against 72.9 s; mz150 0.47 s against > 120 s, w23). We beat dense nauty from small sizes on `ns` (w1).

**We lose**, by the latest measurements ([w23-speed2](../docs/w23-speed2.md) §3, §6):

* **Traces is ahead on every family except multipedes**: about 7× on CFI (n = 3200: 0.06 s against 0.43 s for both forms), about 23× on Miyazaki, 14–29× on Q12, 3–6× on 3-regular graphs. Traces' clock resolves 0.01 s, so these ratios are rough. It also wins `ns` at n = 352 and 704. (Historical: at w14 the gaps were CFI 10–23×, Miyazaki 30–90×, Q12 about 250×, 3-regular about 13×.)
* **Sparse nauty** beats us on all hypercubes (Q12: 0.03 s against 0.574 s for both forms) and at n = 352 on `ns` (0.02 s against 0.031 s), and roughly ties at CFI n = 200 (0.01 s against 0.012–0.016 s, at the limit of its clock; `bench/results/canon-w23-cfix.json`). `nst` n ≤ 384 was last measured at w14, where sparse nauty won. At `ns` n = 704 we now win (0.071 s against 0.11 s; `canon-w23-ns.json`), a change since w14.
* **Dense nauty and pynauty** beat us on hypercubes and the smallest instances of other families (last measured at w14; not rerun for w23).
* **Remaining cost** is mostly Python per layer: `RootedCanon.step` (40–60% on CFI and Miyazaki), `_Rooted` construction and the root class ([w23-speed2](../docs/w23-speed2.md) §6). `bounded_iso` on hypercubes (1.8 s at Q12) is dominated by Schreier–Sims inside `_step_perm`.
* **Non-elementary-abelian groups on long graphs** stay in dense tuples: a cycle of 1000 hubs with two leaves each (n = 3000) takes 17 s per graph (the base commit needed over 140 s).
* **Slowdowns in w23:** with the kernel on, none (smallest ratios 1.7 canon, 1.12 biso). Without it, four of the 84 cells are below 1: biso ns16 0.90× (a difference of 8 ms, cause not isolated), biso ns160-twist 0.98×, biso Q8 0.99×, canon ns32 0.995×. Historical, w14: `nst` n = 768 canon 2.39 → 2.69 s and dispatch fallbacks on PG(2,5) and PG(2,7).
* **No polynomial guarantee** for the canonical pipeline. `ir_canon` and `perm_canon` remain exponential in the worst case; the probe does not change this.

**Compiled kernel.** w16 (paired on/off, no change in answers; [w16-ckernel](../docs/w16-ckernel.md) §5): tiers 2.0–2.37×; `ir=0` large 1.52×; xl per instance PG(2,7) 9.4×, Paley101 7.9×, 3reg200 4.7×; bounded and canonical 1.00–1.15× at that time (historical; those paths were compiled in w23). The gain from the kernel after w23, read from the kernel-on table and the no-kernel list above: CFI n = 3200 canon 0.83 → 0.43 s, Q12 2.42 → 0.57 s, ns256 3.07 → 1.43 s.

## Hardness study

Measured with the round 3 code ([hardness.md](../docs/hardness.md), not rerun since): parametrized families with known answers, n ≤ 300, against pynauty; 632 rows, 415 verified solver runs, 19 timeouts, 0 wrong. Exponential growth was rejected for every family except PG(2,q) at `ir=0`; polynomial and n^{c log n} cannot be separated on this range by R² alone, so the trend of the local exponent is used.

* In full mode, growth is about n³ to n^3.6 on rigid structures, against n^3.4–4.0 for nauty, at a constant 40–300×.
* The one superpolynomial signature is PG(2,q) at `ir=0`, label depth linear in q from one heuristic. `young_pick="large"` makes it constant; not the default.
* Remaining `ir=0` cost is Θ(n⁴) group bookkeeping per node, not branching.
* The n^{O(log n)} terms of HJ's analysis never dominate at this scale.

## Other families

[bounded-degree.md](../docs/bounded-degree.md) covers the first bounded pipeline against nauty (CFI, random regular, hypercubes, multipedes, Johnson gadgets). Its numbers are superseded by w1, w14 and w23 for the bounded path, but the observation stands that dense nauty fits close to n³ on CFI(3-reg), and that bounded loses to the default pipeline on random regular graphs.

| Topic | File |
|---|---|
| CFI, random cubic, Miyazaki, nst tables | [w1-scale](../docs/w1-scale.md) §4 |
| canonical forms vs isomorphism | [w9-canontool](../docs/w9-canontool.md) §3.2 |
| dispatch on hardness families (39 instances; total 63.8 → 50.6 s; historical, w14) | [w14-solver](../docs/w14-solver.md) §3 |
| paired kernel on/off and before/after tables with data files | [w22-speed](../docs/w22-speed.md) §5, [w23-speed2](../docs/w23-speed2.md) §3 |
