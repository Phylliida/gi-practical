# w43-lean-statement: a graph theorem that means something

Branch `w43-lean-statement`. New file `lean/DegreeD/Luks/Statement.lean`; edits to `Luks/{Graph,Final,Components}.lean`.
No `sorry`. Nothing under `~/math/GraphIsomorphismLog2` was modified.

**The defect.** `graphIso_final` (w42) quantified the script `∃ s` after `X, Y`, and `Script.done a` carries any
value built classically. So `done {iso set}` with zero calls satisfied it with `C = 0`
(`docs/vacuity-graphIso-final.lean.txt`).

**Status.** Fixed. The new theorem is about a named script and its behaviour against every oracle. The
trivial witness provably fails. One residual weakness remains and is stated precisely in §3.

## 1. The new statement

```lean
theorem GI.DegreeD.Luks.graphIso_reduction
    (hcite : GI.Cited.TransitiveAffected) (hK : GI.Cited.KaryCoherentRefinement)
    (h6 : GI.Cited.SixTransitiveContainsAlt) (hDL : GI.Cited.DesignLemma)
    (hAut : GI.Cited.AutCardLeSq) (hLie : GI.Cited.SimpleValuationDegree) :
    ∃ (P : Params) (C : ℝ), 0 ≤ C ∧ ∀ (n d : ℕ) (X Y : SimpleGraph (Fin n))
      (hX : ∀ v, Nat.card (X.neighborSet v) ≤ d) (hY : ∀ v, Nat.card (Y.neighborSet v) ≤ d),
      IsLuksReduction hX hY (luksScript hX hY) ∧
      ∃ e : M.Exec P (luksScript hX hY) (isoSet X Y),
        e.total (fun _ => (1 : ℝ)) ≤ Real.exp (C * (Real.log (d + 2) * Real.log (n + 2)))

structure IsLuksReduction (hX hY) (s : Script (Set (Perm (Fin n)))) : Prop where
  readOff : ∀ o : Oracle, s.evalWith o = luksOff hX hY o
  layered : s.AllCalls (LuksQuery X Y (min d n))
  calls   : s.CallsExact fun {_ _} m T => m = .solve ∧ GammaHat d T.G ∧ (T.size : ℝ) ≤ 3 * (n : ℝ) ^ 4
  numCalls : s.numCalls ≤ n ^ 5
  exact   : s.evalExact = isoSet X Y
```

`graphIso_reduction_general` is the form from `Stage1Conclusion P w`, any weight `w`.

Definitions (all in `Statement.lean` unless noted):

* `Oracle := ∀ Ω C, Mode → State Ω C → Set (Perm Ω)`; `Script.evalWith o` runs a script against `o`.
  `Oracle.exact` gives `evalExact` (`evalWith_exact`); `Oracle.null` answers `∅`.
* `Script.AllCalls p`: every call on **every** branch of answers satisfies `p` (unlike `CallsExact`, the exact branch only).
* `LuksQuery X Y q`: the query is `layerState (mkLG c.toSimpleGraph …) (mkLG c'.toSimpleGraph …) A τ r`, for connected
  components `c` of `X`, `c'` of `Y`.
* `luksScript hX hY` (`Components.lean`): the named script, `graphScript` with `q = min d n`.
* `luksOff hX hY o` = `graphOff o …` (`compOff`, `anyOff`, `connOff`, `candOff`, `rootedOff`, `layerLoop`): the output as an
  explicit term in the oracle: the layer loop threads `(A, τ)` through `readStep X Y r τ (o (layerState X Y A τ r))`, and the
  output is `{g | ∀ c, ∃ p, restr X g c ∈ liftMap '' …}`. `luksScript_evalWith` proves `(luksScript hX hY).evalWith o = luksOff hX hY o`.

What `readOff` says: the script is a fixed function of the answers, on right and wrong answers alike. This is the
formal content of "computed from the answers".

`luksScript` no longer has a branch that returns a value without asking. The old `anyScript` had
`Script.done {iso set}` for one-vertex graphs; it now runs the layer loop from a degenerate root `u = v` (`RootImg`,
`connScript_spec` with `huv : v = u ∨ X.Adj u v`). So for `n ≥ 1` every component pair goes through the oracle.

## 2. The trivial witness fails (kernel-checked)

```lean
theorem luksOff_null (hn : 1 ≤ n) : luksOff hX hY Oracle.null = ∅
theorem not_isLuksReduction_done (hn : 1 ≤ n) (e : X ≃g Y) :
    ¬ IsLuksReduction hX hY (Script.done (isoSet X Y))
theorem not_isLuksReduction_useless (hn : 1 ≤ n) (e : X ≃g Y) (m) (S) (k)
    (hk : ∀ A, (k A).evalWith Oracle.null = isoSet X Y) :
    ¬ IsLuksReduction hX hY (Script.ask m S k)
theorem luksScript_answers_matter (hn : 1 ≤ n) (e : X ≃g Y) :
    (luksScript hX hY).evalWith Oracle.null ≠ (luksScript hX hY).evalExact
```

The first says that with all answers empty the read-off is empty. So a script that ignores its answers, with or
without useless queries, fails `readOff` at `Oracle.null`. `n = 0` is excluded because there the graph is unique, the iso set is a singleton
and the reduction has nothing to ask: `done` is correct there.

A *filter* script (ask something, then return the iso set if the answer is nonempty and `∅` otherwise) is **not** excluded by the
null oracle alone. `readOff` quantifies over every `o`, which is what should exclude it, but I have not proved
that for an arbitrary filter script (Lean's kernel-checked statements are the ones above). In the theorem itself this does not arise: the script is the
named `luksScript`, so no script is quantified.

## 3. The residual weakness (precise)

`readOff`, `layered`, `calls`, `exact` constrain the script's input–output behaviour against all oracles, not the cost of
what it computes between calls. In Lean a `Script`, and `luksOff`, are classical terms. So:

1. **The definition has to be read.** `luksOff`, `layerState`, `readStep`, `extf`, `mkLG` are named definitions; that they
   do no hidden work is a reader's check. The kernel certifies the properties, not their "explicitness". The definitions are short, and a reachability
   check confirms none of them mentions the answer: computing the transitive set of constants used by the *definitions*
   `luksOff`, `luksScript`, `layerState`, `readStep`, `mkLG`, none reaches `SimpleGraph.Iso`, `IsIso`, `isoSet`, `State.answer` or
   `Script.evalExact` (positive control: the shape of the old branch, `done {f | ∃ e : X ≃g Y, …}`, reaches `SimpleGraph.Iso`).
   This check can miss an inlined copy of the definition of isomorphism; it is evidence, not proof.
2. **Classical picks remain**: the root edge (`h.choose`), the slot numbering (`exists_nb`, in `mkLG`), the representative element of a
   nonempty answer (`Set.Nonempty.some`), and `Subgroup.closure {b | …}` in `readStep` (a set-builder quantifying over `Perm V`; a program must compute generators).
   Each is determined by data the script legitimately reads, and is a place where a program would do polynomial work; none is priced in `e.total`.
3. **`GammaHat` and the size bound hold along the exact answers only** (`calls`); on wrong answers `A` can be any subgroup. `layered` does hold on all branches.
4. **`w` is not time, and there is no program** (unchanged from w42). `e.total (fun _ => 1)` counts nodes of the recursion; this is
   the Stage-2 gap.

So: `graphIso_reduction` proves that the named reduction reads its answers and is exact. It does not (and in a classical
metatheory without a machine model cannot) prove that the reduction's bookkeeping is efficient. To go further needs a deep
embedding of the read-off in a cost-carrying language, which is the machine-level work estimated in `docs/w36-lean.md`.

## 4. Audit of the rest of `lean/DegreeD/`

`∃ Script`: only the four renamed theorems (§5). `∃ e : M.Exec` occurs elsewhere only for a **given** script
(`exec_of_calls`, `M.Exec.exists_exact`).

* `degreeD_stage1` (`M/Main.lean`): `∀` runs. Fine.
* `degreeD_stage1_full`, `_of_giant`, `_cited`, `_axioms`, `exists_run_solve`: `∃ r : Run … S.answer`, with `∀ r` for the cost bound. Not the
  defect: `Run` is an inductive of the algorithm's cases, its index `A` is forced by `Run.exact` to be `S.answer` (unconditional), and any
  cheaper run is still covered by the `∀`.
* **Can a run "just return" the answer on a large instance? No.** The only constructor of `M.Run` with neither a child run nor a script is
  `direct`, which needs `S.size ≤ P.N₀`, a constant fixed before `n`. The families indexed by cosets (`dispatch`, `normalize`, `aggregate`'s `overs`) could only be empty if the cosets failed to
  cover, which their interface fields (`cover`, `Branches.Covers`) exclude for a nonempty group, except that an aggregation may cover an empty answer. `M.Exec` is structural over its script: its leaf is `done a` on
  `Script.done a`. In every case the value is forced by `Run.exact` and `Exec.exact`, which hold unconditionally (`luksScript_exec_value`: every run of `luksScript`, however obtained, returns the iso set).
* **One related point, not a defect in a stated theorem.** Inside `Run.aggregate`, `I : Aggregation` is classical interface data, and
  `AuxItem.script` has `done` leaves carrying `(σ, E₀)` from that data (`.overcoset`, in HJ's `Workspace/Algorithm/AuxItems.lean`). They are constrained by `Aggregation`'s
  fields and `Branches.Covers`, and the cost bound is universal over runs, so no statement becomes trivially true. But "the run is the algorithm" is a claim about those
  interfaces, as w41/w42 already said (`Supply` data, `Structural` recognition).

## 5. The old theorems

Renamed, with a warning docstring: `graphIso_connected_weak`, `graphIso_connected_final_weak` (`Final.lean`), `graphIso_general_weak`,
`graphIso_final_weak` (`Components.lean`). The last two are now one-line consequences of `luksScript_spec`/`luksScript_exec`.

## 6. Axioms

```
#print axioms graphIso_reduction          : propext, Classical.choice, Quot.sound, GI.DegreeD.M.bcp, GI.DegreeD.M.gnsPrimitive
#print axioms graphIso_reduction_general  : propext, Classical.choice, Quot.sound
#print axioms not_isLuksReduction_done    : propext, Classical.choice, Quot.sound
#print axioms not_isLuksReduction_useless : propext, Classical.choice, Quot.sound
#print axioms luksOff_null                : propext, Classical.choice, Quot.sound
#print axioms luksScript_answers_matter   : propext, Classical.choice, Quot.sound
#print axioms luksScript_exec_value       : propext, Classical.choice, Quot.sound
#print axioms graphIso_final_weak         : propext, Classical.choice, Quot.sound, GI.DegreeD.M.bcp, GI.DegreeD.M.gnsPrimitive
```

Same trusted base as w42: the six cited statements are hypotheses, and `bcp`, `gnsPrimitive` are the two axioms of `M/Axioms.lean`.

## 7. Compile

As in `docs/w36-lean.md`, one file at a time under `nice`, into a scratch olean directory. Compile order: the w42 order, then `Luks.Statement`. 4–8 s per file for the changed files.
