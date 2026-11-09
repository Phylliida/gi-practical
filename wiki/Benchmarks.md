# Benchmarks

Tables, caveats, and where the solver wins or loses. Later numbers supersede earlier ones. Raw data is in [bench/results/](../bench/results/). To rerun, see [Reproduce](Reproduce.md).

[Home](Home.md) · [Software](Software.md)

**In progress as of master `b1a2d03`:** `w22-speed` (`624be06`) changes the hybrid stage loop and has its own paired benchmark; it is not reflected here. `w23-speed2` (`4742c66`) compiles the bounded and canonical hot paths and is not merged, so the bounded and canonical timings below do not include it.

## Read these caveats first

* **Clocks differ.** Ours is Python wall time. Nauty and Traces via dreadnaut report C CPU time at 0.01 s resolution, so entries of 0 mean under 0.01 s and ratios against small cells are rough. pynauty runs in a subprocess.
* **One machine** (64 cores, shared; load between about 1.5 and 36 depending on the run; the memo for each table states it), `nice -n 19`, one benchmark process at a time. Many memos note the load; single timings are noisy (±30% in r4, about 1.5× in `hardness`). Paired runs alternate old and new code on each instance.
* **Seeds.** Headline tables use seed 0, one random instance per size. Multipede robustness was checked on seeds 1 and 2. Sizes after a first timeout were skipped, not measured, and shown as `>T`.
* **Timeouts differ between tables** (60 s to 600 s).
* **Task differs.** Our `biso` columns solve isomorphism plus Aut; canonical `canon` columns compute both canonical forms of a pair; dreadnaut columns are canonical-form runs. Ours are pure Python unless stated.
* **Options.** Nauty and Traces were run with defaults, without invariants. They may do better with other options.
* **Pure Python.** The kernel does not affect bounded or canonical timings much.

## Progression on the benchmark tiers

The tiers are `tiny` (n ≤ 8), `small` (n ≤ 12), `medium` (n ≤ 20), `hard`, `large` (n ≤ 70) and `xl` (n ≤ 200): 56 instances in total ([bench/families.py](../bench/families.py)). Every answer is verified.

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

The r2 comparison with references (load about 35): our exact solver is about 1000× slower than nauty, faster than VF2 on non-isomorphic CFI/strongly-regular pairs and random regular graphs, and slower than VF2 on isomorphic symmetric pairs ([README](../README.md)).

**Where the recursion matters.** With individualization on, the recursion barely ran on the early tiers. Comparing `ir=0` and full shows when group theory beats refinement: the recursion beat the hybrid 14× on the non-isomorphic CFI pair in r1, and on CFI(4reg) in r3.

## Headline: Neuen–Schweitzer multipedes (`ns`)

Rigid multipedes R(B(G_k, σ)), n = 22k vertices, degrees 8 and 3, built to give IR solvers exponential search trees. Answers and |Aut| = 1 follow from a lemma checked per instance. Seed 0; 600 s timeout per mode and instance. Times in seconds, iso/non-iso where given ([w1-scale](../docs/w1-scale.md) §3; `irhard-w1-ns.json`).

| n | ours iso | ours non-iso | dense nauty | sparse nauty | Traces |
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

Fits: ours n^1.17 (R² 0.98); dense nauty 2^(9.3n/1000), sparse nauty 2^(6.4n/1000) (R² 0.97–0.99). Crossovers measured: dense nauty from the smallest size; Traces between 704 and 1056; sparse nauty about 1056–1760 depending on σ (on seeds 1 and 2 it moves). From n = 1760 on ours wins on all three seeds, 10–30×.

On the graph X alone at n = 2464, sparse nauty needs 530 s, 10.2 million nodes, depth 21; every leaf is bad because the graphs are rigid. After w14, ours is 0.66 s (biso) and 0.83 s (both forms) ([w14-solver](../docs/w14-solver.md)).

**What the win rests on:** rooted 1-WL and the class order turn each rooted test into linear algebra over F₂ with tiny groups. This is the group-theoretic advantage Neuen–Schweitzer point to, and it is a Luks-style advantage, not an HJ-specific one. It does not touch HJ's analysis.

## Canonical forms (w9, then w14)

Both forms of a pair, seconds; `ns` at seed 0, up to n = 5632 ([w9-canontool](../docs/w9-canontool.md) §3.1). After w14 (`canon` after, biso after) ([w14-solver](../docs/w14-solver.md) §3):

| Family | Instance | n | canon | biso | Traces | sparse nauty | dense nauty |
|---|---|---|---|---|---|---|---|
| `ns` | ns112 | 2464 | 0.825 | 0.662 | >120 | >120 | >120 |
| `ns` | ns160 | 3520 | 1.65 | 1.2 | >120 | >120 | >120 |
| `ns` | ns256 | 5632 | 3.63 | 2.14 | >120 | >120 | >120 |
| `nst` | nst64 | 768 | 2.69 | 2.51 | >120 | 79.5 | >120 |
| CFI | CFIx160 | 1600 | 0.501 | 0.241 | 0.02 | 16.2 | 42 |
| CFI | CFIx320 | 3200 | 1.41 | 0.636 | 0.06 | 71.3 | >120 |
| Miyazaki | mz100 | 2000 | 0.804 | 0.31 | 0.01 | 22.8 | 78.1 |
| Miyazaki | mz150 | 3000 | 1.86 | 0.557 | 0.02 | >120 | >120 |
| hypercube | Q11 | 2048 | 2.1 | 1.26 | 0.02 | 0.03 | 0.78 |
| hypercube | Q12 | 4096 | 5.04 | 3.6 | 0.02 | 0.03 | 6.48 |
| 3-regular | 3reg4000 | 4000 | 0.256 | 0.264 | 0.02 | 12.9 | >120 |

Timeouts in this table are 120 s (a 600 s timeout applies in the w1/w9 tables).

## Where we win and where we lose

**We win** against all three nauty modes on rigid `ns` multipedes from n ≈ 1100, on `nst` at n = 768, and on Miyazaki and CFI against the nauty modes at larger sizes. We beat dense nauty from small sizes on `ns`.

**We lose**, by the latest measurements ([w14-solver](../docs/w14-solver.md) §3):

* **Traces is faster on every non-multipede family**: CFI n = 3200: 0.06 s vs 0.64 s (biso) and 1.41 s (canon), about 10–23×; Q11 about 100×, Q12 about 250×; Miyazaki n = 3000 about 30–90×; 3-regular n = 4000 about 13×.
* **Sparse nauty** beats us on all hypercubes and at small sizes: CFI n = 200, `nst` n ≤ 384, `ns` up to n = 704.
* **Dense nauty and pynauty** beat us on hypercubes and the smallest instances of other families.
* **Slowdowns against before w14**: `nst` n = 768 canon 2.39 → 2.69 s; dispatch fallbacks PG(2,5) and PG(2,7).
* **No polynomial guarantee** for the canonical pipeline.

**Compiled kernel** (paired, no change in answers; [w16-ckernel](../docs/w16-ckernel.md) §5): tiers 2.0–2.37×; `ir=0` large 1.52×; bounded and canonical 1.00–1.15×. xl per instance: PG(2,7) 9.4×, Paley101 7.9×, 3reg200 4.7×.

## Hardness study

[hardness.md](../docs/hardness.md): parametrized families with known answers, n ≤ 300, against pynauty; 632 rows, 415 verified solver runs, 19 timeouts, 0 wrong. Exponential growth was rejected for every family except PG(2,q) at `ir=0`; polynomial and n^{c log n} cannot be separated on this range by R² alone, so the trend of the local exponent is used.

* In full mode, growth is about n³ to n^3.6 on rigid structures, against n^3.4–4.0 for nauty, at a constant 40–300×.
* The one superpolynomial signature is PG(2,q) at `ir=0`, label depth linear in q from one heuristic. `young_pick="large"` makes it constant; not the default.
* Remaining `ir=0` cost is Θ(n⁴) group bookkeeping per node, not branching.
* The n^{O(log n)} terms of HJ's analysis never dominate at this scale.

## Other families

[bounded-degree.md](../docs/bounded-degree.md) covers the first bounded pipeline against nauty (CFI, random regular, hypercubes, multipedes, Johnson gadgets). Its numbers are superseded by w1 and w14 for the bounded path, but the observation stands that dense nauty fits close to n³ on CFI(3-reg), and that bounded loses to the default pipeline on random regular graphs.

| Topic | File |
|---|---|
| CFI, random cubic, Miyazaki, nst tables | [w1-scale](../docs/w1-scale.md) §4 |
| canonical forms vs isomorphism | [w9-canontool](../docs/w9-canontool.md) §3.2 |
| dispatch on hardness families (39 instances; total 63.8 → 50.6 s) | [w14-solver](../docs/w14-solver.md) §3 |
