# w36-lean: can the `n^{O(log d)}` bound be machine-checked?

Branch `w36-lean`, 2026-11-09. New Lean under `lean/DegreeD/` (imports the built development at
`~/math/GraphIsomorphismLog2`; that tree was not modified). Scope: Theorem R\* of
`docs/verify-theorem-R.md` (conditional bound, GI of max degree `d` in `n^{O(log d)}`).

**Status.** The abstract analysis and the key regrouping (H2) are machine-checked, no `sorry`, axioms
`propext, Classical.choice, Quot.sound` only. The real-run theorem is proved conditional on two local
facts about Γ̂_d-runs. The dispatcher (M′), Γ̂_d closure, and everything at the machine level are not done.

## 1. Scoping

**Q1. Is the potential induction abstract enough? Is `x` hard-wired?** It is hard-wired in three places
only: `PotentialState.Φ/W`, the columns `Row.drop`, `Row.mult`, and the root bound. The induction itself
needs just (a) `Φ ≥ 0` and the toll is paid by `(s+2)^D`; (b) `M·exp(-ΔΦ) ≤ 1/(8J)` per class; (c) the
child relation of each row gives `ΔΦ`. `x` is used only to pay `N^a` via `eq_main_phase_active`. So
the generalization is clean, and `Row`, `Row.Child`, `Row.Valid`, `OrbitChild`, `ChargingConstants` all carry over
unchanged. Done: `AbstractCharging` (general potential) and `Φ_Λ` (weight `Λ : ℕ → ℝ`, `Λ = x` is HJ,
`Λ = const` is R\*).

**Q2. Which charging fields change?** Only the multiplicity column (`class_mult` → family form
`class_fam`) and the potential. The existing `Script`/`Exec`/`callBranches` are not touched: the
regrouping is a labelling of the per-call branches by families, with fibers of total size `≤ s`,
expressed as `AbstractCharging.class_families`. The multiplicities on real scripts:
`9 q^{2κ}` families (`aggregate_branch_fam`, §2). Note the type-split in the memo is unnecessary in
Lean: the two classes filter leaves by size at `θs`, and `ChargedCall.types` handles each leaf.

**Q3. New statements needed.** `Γ̂_d` as an inductive on composition series (mirroring
`GI.Cited.CompositionProducts`), its closure, "simple section of `S_d` embeds in `S_d`", and the bound
`q ≤ d` for an `Alt(q)` label set; a modified `DispatchStep` (the constructor `.enumeration` currently
carries `Q.Small P.a`, the order test (M′ replaces it)); GNS 3.13 and BCP Lemma 2.2 and the BLS/GNS 4.4 recognition as new
literature statements (the `Workspace/Cited` axiom pattern); clipped caps `Q_d` as an analysis-only function
of the state (done: `CapUpdate.Qd_drop`); the bound `E_N = N^{O(1)}` for `q ≤ λ` (no row terminal); and at the machine level, Luks's reduction
and the (M′) program.

**Q4. Size.** See §3.

## 2. What was formalized (`lean/DegreeD/`, 3,342 lines)

Compile: `cd ~/math/GraphIsomorphismLog2 && nix shell nixpkgs#elan -c lake env lean --root=$ROOT -o $OLEAN $FILE`
with `$ROOT=.../lean`; each file depends on the previous oleans via `LEAN_PATH`. Importing the build
makes each file compile in 5–30 s.

| file | lines | content |
|---|---|---|
| `Induction.lean` | 376 | `AbstractCharging`: Lemma 7.1 for an arbitrary potential `Φ`, claimed drops, node toll `τ`, and **family grouping** of branches. `cost_le`, `wf`. |
| `TableLambda.lean` | 828 | `Φ_Λ` for a weight `Λ : ℕ → ℝ`; `Row'.dropL/multL`; `child_ΦL_le` (each row of HJ's `Row.Child`), `multL_mul_exp_neg_dropL_le` (the charging inequality, no `N` in the statement); `PhaseTree.HypL` (`PhaseCore` + `class_fam`); `HypL.cost_le`; `root_potentialL`; `fresh_phase_boundL`; `recurrenceL` (constant independent of `Λ`); `abstract_R_star`; `tollL`, `poly_toll_le_tollL`, `hj_toll_le_tollL`. |
| `HJInstance.lean` | 404 | `Hyp.toHypL`, `lem_main_phase_bound_of_general` (HJ's Lemma 7.1 as the instance `Λ = x`); `real_runs_core`, `real_runs_hypL_x`; `example_hypL` (explicit 2-level tree, every row, `N = 2^{10t} → ∞`, `Λ` constant). |
| `RStarColumns.lean` | 239 | Numeric facts: `family_le_multL`, `product_count_le_multL`, `gns_count_le_multL` (GNS 3.13(1)), `small_cameron_count_le_multL`, `continuation_count_le_multL` for `Λ = log(8 max(d,6))`. |
| `ListFam.lean` | 344 | Combinatorics of "families": append, flatten, singletons, and the **layer merge** across updates. |
| `ScriptFamilies.lean` | 482 | (H2) on the real scripts: `Script.contSizes`; `win_card` (windows are disjoint); `endpoint_fam`, `certPhase_fam`, `compareScript_fam`, `comparePhase_fam`; `Aggregation.script_fam` (`≤ 9 q^{2κ}` families); `Exec.contSizes_eq`; `aggregate_branch_fam`. |
| `RealRuns.lean` | 669 | `runKind_class_fam`; `phaseTreeOn` (real tree restricted to a child-closed `Good`); `phaseTreeOn_hypL`, `real_runs_cost_le` (the real-run Lemma 7.1 at `Λ = lam d`, conditional); `good_le_N_conditions` (hypotheses hold for `d ≥ N`, `Good := s ≤ N`); `CapUpdate.Qd_drop` (clipped caps). |

Main statements (all `#print axioms` = the three standard axioms):

* `AbstractCharging.cost_le`. If a phase tree satisfies the abstract charging conditions (with families)
  then `cost v ≤ K (s+2)^D exp(Φ v)`.
* `PhaseTree.HypL.cost_le`. `HypL C Λ N K T` ⇒ every node costs ≤ `K (s+2)^D exp(Φ_Λ)`, and the tree terminates. The constants `C` are HJ's, unchanged: the Λ-table is checked to fit `multL` with HJ's constants (`a* = a/γ`). No `N` occurs in the column.
* `abstract_R_star`. For absolute `C' , base`: every `F ≥ 0`, `Λ ≥ log 48`, if `F ≤ B₀` below base and each phase size is provided by a `HypL` tree with toll `tollL` and `RootBoundsL` roots, then `F N ≤ exp(C' Λ log(N+2))`. The constant does not depend on `Λ`.
* `GI.Algorithm.aggregate_branch_fam`. The `Continue` calls of every actual aggregation round
  (certificate, comparison, items) fall into `≤ 9 q^{2κ}` families with total size `≤ s`. Unconditional. **This is (H2) machine-checked on the real scripts.** The Lean windows are read straight from `increment`/`win`: `win_card`.
* `GI.Algorithm.phaseTreeOn_hypL`. For any set `Good` of real vertices closed under children, satisfying `Run.VertexBound` (`q ≤ max(d,6)` at giant steps, dispatcher cosets `≤ multL`), the restricted real phase tree satisfies `HypL` at `Λ = lam d`. `real_runs_cost_le`: every `Good` vertex costs `≤ K (s+2)^D exp(Φ_Λ)`.
* `lem_main_phase_bound_of_general`. HJ's Lemma 7.1 re-derived from the general theorem.

**Non-vacuity, checked.** (1) `Hyp.toHypL`: HJ's real runs (via the existing `phaseTree_hyp`) satisfy
`HypL` at `Λ = x` (`real_runs_hypL_x`), so the hypothesis class is inhabited by the actual algorithm.
(2) `real_runs_core`: every field except the multiplicity column holds for real runs at any `Λ`.
(3) `example_hypL`: an explicit tree with all six rows satisfies `HypL` for every `t` (`N = 2^{10t}`) with
`Λ` fixed. (4) `good_le_N_conditions`: for `d ≥ N`, the full restricted real-run hypotheses hold with `Good := s ≤ N`.
(5) Constants: `hab`, `2κ + log 9/log 48 ≤ a*`, holds with HJ's `a = 36001`, `γ = 9/10`, `κ = 64`: `a* = 40001 ≥ 129`.

**Honest gaps in `phaseTreeOn_hypL`.** (a) In the regime `d < N` nothing yet shows `Good` runs exist with
(i) and (ii); that is Γ̂_d closure and (M′). (b) The tree's `Q` is HJ's unclipped cap moment; the root bound needs the
clipped `Q_d` (`RootBoundsL.Q_le`). `CapUpdate.Qd_drop` proves the only row where the cap moment *must* drop; the others need re-proving
for `hierQd`. So the real-run tree with `Q_d` plus `RootBoundsL` is ~200–500 further lines. (c) The toll `K` is left open (`leaf_cost`,
`toll`). In the regime `d ≤ N^α` it needs `E_N = N^{O(1)}`, i.e. `q ≤ λ` and no row terminal/rectangles.

## 3. Remaining work, with sizes

| part | size (lines of Lean) | difficulty |
|---|---|---|
| Thread clipped caps `Q_d` through the real tree, `RootBoundsL` | 200–500 | small |
| `Γ̂_d` definition, closure (subgroup/quotient/extension), `q ≤ d` for `Alt(q)` labels | 500–1,500 | moderate, routine group theory |
| Closure under each `Run` constructor; `Good` nonempty on Γ̂_d runs | 300–800 | moderate |
| (M′) dispatcher: new `DispatchStep` cases, GNS 3.13 and BCP as `Cited` axioms, exhaustiveness (`dispatch_cases`), product `k ≥ 2` refinement counts | 1,500–4,000 | moderate |
| `run_exists` for (M′) | 500–2,000 | moderate |
| `E_N = N^{O(1)}`: `¬RowCase` when `q ≤ d ≤ N^α`, `NodeBound` shape for the toll | 1,000–3,000 | moderate |
| **Stage-1 Theorem R\*** (Run-level, cost hypotheses like HJ's `thm_main_graph_stage1`) total | **≈ 5k–12k** | weeks of focused work |
| Machine-level (M′) program, Kantor–Luks socle and BLS as algorithm axioms | 5k–15k | large |
| Budget shape `expLogSq` → `exp(c Λ log X)` through `Assembly`/`Impl` (28 files, ~300 uses) | 5k–20k | large, mostly mechanical |
| Luks / Babai–Luks reduction GI(max deg `d`) → Γ̂_d-string, verified in `Lang` | 10k–30k | large |
| **Stage-2 machine theorem** (the program and cost at machine level) total | **≈ 30k–150k** | a project at the scale of a large part of the existing 300k-line `Impl` |

**Verdict.** The analysis is formalizable, and the (H2) regrouping, the riskiest claim of Theorem R\*, is now done. Stage-1
R\* is a realistic target (5k–12k lines). The machine-level program for degree-`d` GI is, as the ask suspected, a much larger project
and out of reach for now.

