# w16-ckernel: an optional compiled kernel

`gi/_ckernel.c` is a small CPython extension for the hottest primitives. The pure-Python code stays
as the fallback and the reference, and every output is identical with the kernel on or off. All
numbers below are for commit 94b42be, on one machine (64 cores, load 3–5, `nice -n 19`).

**Short version.** The default hybrid is 2.0–2.4× faster and `ir=0` is 1.5× faster. The
bounded-degree pipeline and the canonical forms, which are the families where Traces is far ahead,
barely move (1.00–1.15×), because their hot code is in `gi/bounded.py`, `gi/canon.py` and
`gi/ea2.py`, which this branch was not allowed to edit (w14-solver is changing them). The kernel
does not close the gap to Traces on 3-regular graphs, CFI graphs or hypercubes.

## 1. What is compiled, and why

Shares are from cProfile on the pure-Python code (cumulative, except where marked self). cProfile
inflates Python-heavy code, so they are a guide for choosing targets, not a prediction.

| workload | where the time goes |
|---|---|
| full hybrid: hard / large / xl | `refine.wl2` 48% / 52% / 45%; `mul` + `inv` about 4%; `PermGroup` construction 14% (xl) |
| `ir=0`, large tier | `mul` 8.4%, `inv` 7.7%, `_sifts_to_id` 12.6%, `_make_fast_plan` 8.9%, `orbits` 6.5% |
| `bounded_iso_lists`: ns / cfix / reg3 / Q9 | `edge_invariants` 48% / 36% / 75% / 43% (not editable here) |
| `canonical_labeling_lists`: ns / cfix | `canon.step` + `class_plan` 64%; `canon.step` + `absorb` 75% (not editable here) |

Compiled, in order of measured value:

| primitive | Python | what it does |
|---|---|---|
| `wl2_single(P, tables)` | `refine.wl2_single` | the whole 1-WL and 2-WL loop on int arrays |
| `wl2_check` | end of `refine.wl2` | one function from refined to input colors, equal histograms |
| `mul`, `inv`, `act`, `maps` | `gi/perm.py` | tuple operations; call sites unchanged |
| `sift`, `sifts_to_id`, `make_fast_plan` | `PermGroup` methods | the sifting inner loops |
| `orbits` | `PermGroup.orbits` | orbit computation |

`wl2_single` computes the same keys as `_wl2_keys`: `s(i, j) = sum_k U[C(i, k)] V[C(k, j)]`, with
the same tables, called with the same arguments in the same order. The reference's integers are
below 2^128 (the tables are sized for that), so arithmetic mod 2^128 gives the same values; the
1-WL sums are below 2^63. Ranks are computed in C by hashing the distinct keys and sorting them.

Not compiled, by measurement. `_schreier` and `_orbit` have self shares of 2–6% and identity-based
caches; `PermGroup.__init__` is mostly per-level allocation (5 containers per base point), which C
would not make much cheaper. `refine_labels` is 19% of `ir=0` only.

## 2. Design

* **Reference semantics by construction.** The fast path accepts only what the solver produces
  (exact tuples or lists of exact ints in range). Anything else (lists where a tuple is expected,
  bools, negative or out-of-range entries, huge ints) is not handled in C: `mul`, `inv`, `act` and
  `maps` call the registered Python function, and the rest return `None`, so the Python method body
  runs. Invalid input therefore gets the reference's result or exception. No state changes before
  that decision.
* **Marshalling.** Tuples go in and out. Permutation results reuse a table of int objects instead of
  boxing. At small degree there is no loss: `mul` at n = 2 goes from 303 ns to 91 ns. `mul` is 3.3×
  at small degree and 4.6× at n = 1000; `inv` and `act` are 5–17×; `maps` 4.5–8×.
* **A loaded kernel is always the current one.** `build_ckernel.py` embeds the SHA-256 of the
  source, and `gi/kernel.py` ignores a mismatching module with a `RuntimeWarning`. A wrong-ABI
  interpreter (checked with the system's Python 3.13) cannot see the 3.12 module and uses Python.
* **Timeouts still work.** `wl2_single` calls `PyErr_CheckSignals` every round, so bench SIGALRM
  timeouts still fire.
* Also tried: `target_clones("avx2")` on the column additions. It gained 10% on `wl2_single` and
  about 0.4% end to end, so it was removed.

## 3. Build

```sh
python3 build_ckernel.py            # needs only gcc on PATH (or $CC)
python3 build_ckernel.py --clean    # remove it
GI_NO_CKERNEL=1 python3 ...         # run without it
```

Headers and the extension suffix come from the interpreter that runs the script, not from
`python3-config` on PATH, which on this machine belongs to Python 3.13. On this NixOS machine the
system gcc 14.3 is enough and nothing new is downloaded. If `gcc` is not on PATH, use
`nix shell nixpkgs#gcc -c python3 build_ckernel.py`, and check `df` first if that would fetch
anything. The build writes only `gi/_ckernel*.so`, which is git-ignored.

## 4. Tests

`python3 -m pytest -q tests`: 553 passed, 19 skipped with the kernel; 489 passed, 83 skipped with
`GI_NO_CKERNEL=1` (the extra skips are the 64 tests comparing C against Python directly).
`GI_REQUIRE_CKERNEL=1` makes a missing kernel a failure instead of a skip.

`tests/test_ckernel.py`:

* randomized equivalence of each primitive against its reference, at degrees 0, 1, small, 2000 and
  200 000; invalid input (result or exception equal to the reference's); the `maps` early-exit
  order; reference counts on success and part-way failure;
* `wl2_single` on random, structured and near-discrete matrices and negative names, with the same
  sequence of table requests as the reference;
* whole pipelines in a subprocess per mode: `graph_iso` (`ir` default and 0) with stats,
  `refine_graphs`, `bounded_iso_lists`, `canonical_labeling_lists`, and `PermGroup` chains (base,
  strong generators, transversals with insertion order, orbits) must give equal digests.

`tests/test_refine.py::test_wl2_interleaved_1wl` counts rounds of the Python path by patching
`_wl2_keys`, so it now pins that path with `_ck = None`.

**Memory safety.** The kernel built with `python3 build_ckernel.py --asan` (ASan + UBSan, no
recovery; the module is confirmed instrumented), with `libasan` preloaded and `PYTHONMALLOC=malloc`,
passed the whole suite (133 + 420 tests) with no report. This instruments the kernel only, not
CPython. A leak smoke test (22 000 passes over every primitive, including the error paths) showed no
RSS growth.

**Correctness runners, both modes.** `bench/run.py` through xl (56/56 correct, including sympy's
check of |Aut|); `bench/irhard.py` on ns and cfix (`new`); `bench/canon.py` on ns, cfix, reg3 and
cube (`canon`). All `ok`. These files were not changed.

## 5. Paired timings

`bench/ckernel.py` alternates off and on in fresh processes (off, on, on, off), keeps the minimum
per instance over 2 rounds per mode, and times the solver alone. (`bench/run.py`'s times include
its sympy verification.) Every output digest was identical between the modes. Data:
`bench/results/ckernel-w16-*.json`.

| workload | off (s) | on (s) | speedup |
|---|---|---|---|
| tiers tiny / small / medium | 0.007 / 0.030 / 0.098 | 0.004 / 0.013 / 0.046 | 2.0 / 2.3 / 2.1 |
| tier hard (6) | 0.338 | 0.154 | 2.20 |
| tier large (18) | 3.689 | 1.556 | 2.37 |
| tier xl (9) | 10.290 | 4.904 | 2.10 |
| tier large, `ir=0` | 29.42 | 19.37 | 1.52 |
| multipedes ns, n = 352–3168: iso test | 8.39 | 8.40 | 1.00 |
| ns: both canonical forms | 7.88 | 7.84 | 1.00 |
| CFI, n = 200–3200: iso test | 20.40 | 20.26 | 1.01 |
| CFI: both canonical forms | 32.17 | 31.87 | 1.01 |
| 3-regular, n = 500–4000: iso test | 3.92 | 3.94 | 1.00 |
| 3-regular: both canonical forms | 1.488 | 1.457 | 1.02 |
| hypercubes Q6–Q11: iso test | 3.40 | 2.96 | 1.15 |
| hypercubes: both canonical forms | 7.51 | 6.82 | 1.10 |

xl per instance: PG(2,7) 9.4×, Paley101 7.9×, 3reg200 4.7×, rand200 2.5×, CFI(3reg14) 2.1×,
Q7 1.8×, rook10 1.7×, Kneser(10,3) 1.7×, CFI(3reg14)-twist 1.4×. `wl2_single` alone on these seven
xl graphs: 330 ms → 20 ms, about 16×.

nauty/Traces were not re-run: on the families of docs/w9-canontool.md §3.4 the times moved by at
most 15%, so the gaps there are essentially unchanged.

## 6. What remains Python

* **Full hybrid (xl, with the kernel, cProfile).** Most of the rest is the `gi/graph.py` stage loop
  (`clean` 16%, `solve_stage`, `pull_back`, `solve_on`, `pick_stage`, `align`, together about 39%
  self), and `PermGroup` construction. `wl2_single` is now 3%.
* **`ir=0`.** `PermGroup.__init__` allocation, `refine_labels`, `_schreier`, `_orbit`, `lift`.
* **Bounded degree and canonical forms: nearly all of it.** This is where the kernel would need to
  go next. The upper bound (Amdahl, from the cProfile shares above) for compiling `edge_invariants`
  is about 1.9× on ns, 1.6× on CFI and 4× on 3-regular; for `canon.step` + `absorb` about 4× on CFI
  canonical forms. These functions were deliberately not patched at run time from outside: a
  monkey-patch would silently override whatever w14-solver changes in them. They should be compiled
  after that branch is merged, the same way: a C fast path, the Python body as reference.
