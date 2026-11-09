import DegreeD.ListFam
import Workspace.Algorithm.PhaseTree

/-!
# The regrouping (H2) on the real scripts of an aggregation round

HJ charge the local-certificate and comparison calls of an aggregation round with multiplicity
`N^a`: the scripts make up to `2 binom(q,κ) s κ!` and `4 q^{2κ} s` `Continue` calls. Theorem R*
needs instead that these calls fall into `q^{O(κ)}` *families*, the calls of one family having
total domain size at most the parent's. This file proves it, on the actual scripts
(`GI.Algorithm.endpointScriptLift`, `certPhase`, `comparePhase`, `Aggregation.script`), along the
exact answers.

* `Script.contSizes`: the domain sizes of the `Continue` calls of a script, along the exact
  answers (the same order as `Exec.calls`).
* `endpoint_fam`: the endpoint script of Algorithm 2 for one string and one test has at most
  `|Alt(T)|` families: take the `j`-th coset representative in every update. The windows `V_t` of
  different updates are disjoint (`inc_disjoint_win`), so each family has total size `≤ s`.
* `compareScript_fam`: a lockstep comparison has `1` family.
* `certPhase_fam`, `comparePhase_fam`: `2 binom(q,κ) κ!` and `(2q^κ)²` families.
* `Aggregation.script_fam`: all calls of a round are in `≤ 9 q^{2κ}` families.
* `exec_contSizes`: the Continue calls of a script run, with sizes, are `s.contSizes`.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.Endpoint GI.LocalGroups GI.LocalCertificates
open scoped Pointwise
open GI.DegreeD

namespace Script

variable {α β : Type}

/-- The domain sizes of the `Continue` calls of a script, along the exact answers, in order. -/
noncomputable def contSizes : Script α → List ℕ
  | done _ => []
  | ask m S k => (if m = .cont then [S.size] else []) ++ (k S.answer).contSizes

theorem contSizes_bind : ∀ (s : Script α) (f : α → Script β),
    (s.bind f).contSizes = s.contSizes ++ (f s.evalExact).contSizes
  | .done _, f => by simp [bind, contSizes, evalExact]
  | .ask m S k, f => by
    simp only [bind, contSizes, evalExact]
    rw [contSizes_bind (k _) f, List.append_assoc]

theorem contSizes_seqList : ∀ (l : List (Script α)),
    (seqList l).contSizes = (l.map contSizes).flatten
  | [] => rfl
  | s :: ss => by
    simp only [seqList, contSizes_bind, List.map_cons, List.flatten_cons, contSizes_seqList ss]
    simp [contSizes]

theorem contSizes_length (s : Script α) : s.contSizes.length = s.numCont := by
  induction s with
  | done a => rfl
  | ask m S k ih =>
    simp only [contSizes, numCont, List.length_append]
    rw [ih]
    split_ifs <;> simp

/-- A `Continue` call with result post-processing: its one size. -/
theorem contSizes_call_bind {Ω' C' : Type} (S : State Ω' C') (f : Set (Perm Ω') → Script β) :
    ((call .cont S).bind f).contSizes = S.size :: (f S.answer).contSizes := by
  simp [call, bind, contSizes]

theorem contSizes_call {Ω' C' : Type} (m : Mode) (S : State Ω' C')
    (f : Set (Perm Ω') → Script β) (hm : m ≠ .cont) :
    ((call m S).bind f).contSizes = (f S.answer).contSizes := by
  simp [call, bind, contSizes, hm]

end Script

variable {P : Params}

/-! ### Sizes of `Continue` calls are at most the domain size -/

theorem Script.contSizes_le_of_calls {Ω C : Type} [Finite Ω] {S : State Ω C} {α : Type}
    (s : Script α) (hs : s.CallsExact (AggCall P S)) : ∀ x ∈ s.contSizes, x ≤ S.size := by
  induction s with
  | done a => simp [Script.contSizes]
  | ask m T k ih =>
    intro x hx
    simp only [Script.contSizes] at hx
    obtain ⟨hcall, hk⟩ := hs
    rcases List.mem_append.1 hx with hx | hx
    · split_ifs at hx with hm
      · rw [List.mem_singleton] at hx
        subst hx
        rcases hcall with ⟨hm', -⟩ | ⟨-, hΩ, hch⟩
        · rw [hm] at hm'; cases hm'
        · subst hΩ
          exact size_le_of_subset hch.sub
      · simp at hx
    · exact ih _ hk x hx

/-! ### Windows of the endpoint procedure -/

section Windows

variable {V : Type} [DecidableEq V] [Fintype V] {Q : Type} [Group Q] {P' : Subgroup (Perm V)}
  (phi : P' →* Q) {C : Type}

theorem increment_disjoint (A : Subgroup (Perm V)) (W : Finset V) :
    Disjoint (increment phi A W) W := by
  classical
  rw [Finset.disjoint_left]
  intro v hv hW
  unfold increment at hv
  split_ifs at hv with h1 h2 h3
  all_goals first
    | exact absurd hv (by simp)
    | exact ((mem_affectedSet phi).1 hv).1 hW
    | exact ((mem_extraSet phi).1 hv).1 hW

theorem inc_disjoint_win (x : V → C) (t : ℕ) : Disjoint (inc phi x t) (win phi x t) :=
  increment_disjoint phi _ _

/-- `|W_t| = Σ_{i<t} |V_i|`. -/
theorem win_card (x : V → C) (t : ℕ) :
    (win phi x t).card = ∑ i ∈ Finset.range t, (inc phi x i).card := by
  induction t with
  | zero => simp [win_zero]
  | succ t ih =>
    rw [Finset.sum_range_succ, win_succ, Finset.card_union_of_disjoint (inc_disjoint_win phi x t).symm,
      ih]

/-- The sizes of all windows of the endpoint procedure add up to at most `|V|`. -/
theorem sum_inc_card_le (x : V → C) (t : ℕ) :
    ∑ i ∈ Finset.range t, (inc phi x i).card ≤ Fintype.card V := by
  rw [← win_card]; exact Finset.card_le_univ _

end Windows

/-! ### One endpoint script -/

section Endpoint

variable {Ω C C₀ : Type} [DecidableEq Ω] (S : State Ω C) [Fintype S.dom] {Q : Type} [Group Q]
  [Finite Q] (R : CosetRepFn S.dom) {P' : Subgroup (Perm S.dom)}

/-- The size of a lifted window call is the size of its window. -/
theorem size_windowCall (N : Subgroup (Perm S.dom)) (V : Finset S.dom)
    (hV : GI.Algorithm.Invariant N (V : Set S.dom)) (x : S.dom → C₀) (τ : Perm S.dom) :
    (windowCall S N V hV x τ).size = V.card := by
  simp only [windowCall, State.size, State.queryChild_dom]
  rw [Nat.card_coe_set_eq, Set.ncard_image_of_injective _ Subtype.val_injective,
    Set.ncard_coe_finset]

/-- The Continue calls of `CheckNewWindow` all have the size of the window. -/
theorem contSizes_checkNewWindowLift (A N : Subgroup (Perm S.dom)) (W : Finset S.dom)
    (x : S.dom → C₀) :
    ∃ r, r ≤ (R.reps A N).length ∧
      (checkNewWindowLift S R A N W x).contSizes = List.replicate r W.card := by
  classical
  unfold checkNewWindowLift
  split_ifs with hW
  · refine ⟨(R.reps A N).length, le_rfl, ?_⟩
    rw [Script.contSizes_bind, Script.contSizes_seqList, List.map_map]
    simp only [Script.contSizes, List.append_nil]
    have hs : ∀ τ : Perm S.dom, (Function.comp Script.contSizes
          (fun τ : Perm S.dom => (Script.call .cont (windowCall S N W hW x τ)).bind
            fun B => Script.done (τ • restrictAns S B))) τ = [W.card] := by
      intro τ
      show ((Script.call .cont (windowCall S N W hW x τ)).bind
            fun B => Script.done (τ • restrictAns S B)).contSizes = [W.card]
      rw [Script.contSizes_call_bind, size_windowCall]
      simp [Script.contSizes]
    rw [List.map_congr_left (fun τ _ => hs τ)]
    induction (R.reps A N) with
    | nil => rfl
    | cons a l ih => simp [List.flatten_cons, List.replicate_succ, ih]
  · exact ⟨0, Nat.zero_le _, by simp [Script.contSizes]⟩

/-- **One endpoint script, in layers.** The Continue calls of the endpoint script after `t`
updates are, for each update `i`, at most `|Q|` copies of the window size `|V_i|`. -/
theorem endpoint_contSizes (phi : P' →* Q) (hP : P' ≤ S.domGroup) (x : S.dom → C₀) (t : ℕ) :
    ∃ r : ℕ → ℕ, (∀ i, r i ≤ Nat.card Q) ∧
      (endpointScriptLift S R phi x t).contSizes =
        (List.range t).flatMap fun i => List.replicate (r i) (inc phi x i).card := by
  classical
  induction t with
  | zero => exact ⟨fun _ => 0, fun _ => Nat.zero_le _, by simp [endpointScriptLift, Script.contSizes]⟩
  | succ t ih =>
    obtain ⟨r, hr, hL⟩ := ih
    have hstep : ∃ m, m ≤ Nat.card Q ∧
        (if increment phi (stage phi x t).1 (stage phi x t).2 = ∅ then
          Script.done (stage phi x t) else
          (checkNewWindowLift S R (stage phi x t).1 (kernelIn phi (stage phi x t).1)
            (increment phi (stage phi x t).1 (stage phi x t).2) x).bind
            fun B => Script.done (Subgroup.closure B, (stage phi x t).2 ∪
              increment phi (stage phi x t).1 (stage phi x t).2)).contSizes =
          List.replicate m (inc phi x t).card := by
      split_ifs with hinc
      · exact ⟨0, Nat.zero_le _, by simp [Script.contSizes]⟩
      · obtain ⟨m, hm, hc⟩ := contSizes_checkNewWindowLift S R (stage phi x t).1
          (kernelIn phi (stage phi x t).1)
          (increment phi (stage phi x t).1 (stage phi x t).2) x
        refine ⟨m, hm.trans ((R.length_le _ _).trans (kernelIn_index_le phi (grp_le phi x t))), ?_⟩
        rw [Script.contSizes_bind, hc]
        simp [Script.contSizes, inc, grp, win]
    obtain ⟨m, hm, hx⟩ := hstep
    refine ⟨fun i => if i = t then m else r i, fun i => by
      dsimp only; split_ifs; exacts [hm, hr i], ?_⟩
    rw [endpointScriptLift, Script.contSizes_bind, endpointScriptLift_evalExact S R phi hP, hL,
      List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, if_true]
    congr 1
    apply List.flatMap_congr
    intro i hi
    rw [if_neg (by have := List.mem_range.1 hi; omega)]

/-- **The endpoint script has `|Q|` families.** -/
theorem endpoint_fam (phi : P' →* Q) (hP : P' ≤ S.domGroup) (x : S.dom → C₀) (t : ℕ) :
    ListFam (endpointScriptLift S R phi x t).contSizes (Nat.card Q) (Fintype.card S.dom) := by
  classical
  obtain ⟨r, hr, hL⟩ := endpoint_contSizes S R phi hP x t
  rw [hL]
  exact (ListFam.layers t (Nat.card Q) r (fun i => (inc phi x i).card) hr).mono_B
    (sum_inc_card_le phi x t)

end Endpoint

/-! ### The certificate phase -/

section CertPhase

variable {Ω C : Type} [DecidableEq Ω] (S : State Ω C) [Fintype S.dom] {q : ℕ}
  (πd : S.domGroup →* alternatingGroup (Fin q)) (κ : ℕ) (O : TestSetOrder q κ)
  (R : CosetRepFn S.dom)

/-- **The certificate phase has `binom(q,κ) · 2 κ!` families**: one per triple
`(test set, string, coset representative index)`. -/
theorem certPhase_fam (x y : S.dom → C) :
    ListFam (certPhase S πd κ O R x y).contSizes (q.choose κ * (2 * κ.factorial))
      (Fintype.card S.dom) := by
  classical
  unfold certPhase
  rw [Script.contSizes_seqList, List.map_map]
  have hone : ∀ l ∈ O.sets.map (Script.contSizes ∘ fun T : Finset (Fin q) =>
      (endpointScriptLift S R (phiT S.domGroup πd T) x (Fintype.card S.dom)).bind fun a =>
        (endpointScriptLift S R (phiT S.domGroup πd T) y (Fintype.card S.dom)).bind fun b =>
          Script.done (a, b)),
      ListFam l (2 * κ.factorial) (Fintype.card S.dom) := by
    intro l hl
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hl
    have hTc : T.card = κ := (O.mem T).1 hT
    have hQ : Nat.card (alternatingGroup T) ≤ κ.factorial := by
      calc Nat.card (alternatingGroup T) ≤ Nat.card (Perm T) :=
            Nat.card_le_card_of_injective _ Subtype.val_injective
        _ = κ.factorial := by rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_coe, hTc]
    have h1 := endpoint_fam S R (phiT S.domGroup πd T) Pgrp_le x (Fintype.card S.dom)
    have h2 := endpoint_fam S R (phiT S.domGroup πd T) Pgrp_le y (Fintype.card S.dom)
    have h3 : ListFam ((endpointScriptLift S R (phiT S.domGroup πd T) x (Fintype.card S.dom)).contSizes ++
        (endpointScriptLift S R (phiT S.domGroup πd T) y (Fintype.card S.dom)).contSizes)
        (2 * κ.factorial) (Fintype.card S.dom) :=
      (h1.append h2).mono (by omega)
    simp only [Function.comp, Script.contSizes_bind, Script.contSizes, List.append_nil]
    exact h3
  have h := ListFam.flatten hone
  rw [List.length_map, O.length_eq] at h
  exact h

end CertPhase

/-! ### The comparison phase -/

section ComparePhase

variable {Ω C C₀ : Type} [DecidableEq Ω] (S : State Ω C) [Fintype S.dom] {q k : ℕ}
  (πd : S.domGroup →* alternatingGroup (Fin q)) (Pk : PickFn S.dom)

theorem size_compareCall (N : Subgroup (Perm S.dom)) (V : Finset S.dom)
    (hV : GI.Algorithm.Invariant N (V : Set S.dom)) (x y : S.dom → C₀) (g₀ : Perm S.dom) :
    (compareCall S N V hV x y g₀).size = V.card := by
  simp only [compareCall, State.size, State.queryChild_dom]
  rw [Nat.card_coe_set_eq, Set.ncard_image_of_injective _ Subtype.val_injective,
    Set.ncard_coe_finset]

/-- A lockstep update has one call on the new window. -/
theorem contSizes_lockstepStepLift (j : ℕ) (x y : S.dom → C₀) (t : Fin k → Fin q)
    (g₀ : Perm S.dom) :
    (lockstepStepLift S πd j x y t g₀).contSizes =
      [(inc (phiT S.domGroup πd (tset t)) x j).card] := by
  simp only [lockstepStepLift, Script.contSizes_call_bind, Script.contSizes, size_compareCall]

/-- The lockstep run, in layers: each update `i` makes at most one call, of size `|V_i|`. -/
theorem compareLoop_contSizes (x y : S.dom → C₀) (t t' : Fin k → Fin q) (j : ℕ) :
    ∃ r : ℕ → ℕ, (∀ i, r i ≤ 1) ∧
      (compareLoop S πd Pk x y t t' j).contSizes =
        (List.range j).flatMap fun i =>
          List.replicate (r i) (inc (phiT S.domGroup πd (tset t)) x i).card := by
  classical
  induction j with
  | zero => exact ⟨fun _ => 0, fun _ => Nat.zero_le _, by simp [compareLoop, Script.contSizes]⟩
  | succ j ih =>
    obtain ⟨r, hr, hL⟩ := ih
    obtain ⟨m, hm, hx⟩ : ∃ m, m ≤ 1 ∧
        ((match (compareLoop S πd Pk x y t t' j).evalExact with
          | none => Script.done none
          | some g₀ => (lockstepStepLift S πd j x y t g₀).bind fun B =>
              Script.done (Pk.pick B)) : Script (Option (Perm S.dom))).contSizes =
          List.replicate m (inc (phiT S.domGroup πd (tset t)) x j).card := by
      split
      · exact ⟨0, Nat.zero_le _, by simp [Script.contSizes]⟩
      · refine ⟨1, le_rfl, ?_⟩
        rw [Script.contSizes_bind, contSizes_lockstepStepLift]
        simp [Script.contSizes]
    refine ⟨fun i => if i = j then m else r i, fun i => by
      dsimp only; split_ifs; exacts [hm, hr i], ?_⟩
    rw [compareLoop, Script.contSizes_bind, hL, List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, if_true]
    congr 1
    apply List.flatMap_congr
    intro i hi
    rw [if_neg (by have := List.mem_range.1 hi; omega)]

/-- **A lockstep comparison has one family.** -/
theorem compareScript_fam (x y : S.dom → C₀) (t t' : Fin k → Fin q) :
    ListFam (compareScript S πd Pk x y t t').contSizes 1 (Fintype.card S.dom) := by
  classical
  obtain ⟨r, hr, hL⟩ := compareLoop_contSizes S πd Pk x y t t' (Fintype.card S.dom)
  rw [compareScript, Script.contSizes_bind, hL]
  simp only [Script.contSizes, List.append_nil]
  exact (ListFam.layers _ 1 r _ hr).mono_B (sum_inc_card_le _ x _)

variable (κ : ℕ) (O : TestTupleOrder q κ)

/-- **The comparison phase has `(2 q^κ)²` families**, one per pair of test tuples. -/
theorem comparePhase_fam (x y : S.dom → C) :
    ListFam (comparePhase S πd κ O Pk x y).contSizes (4 * q ^ (2 * κ)) (Fintype.card S.dom) := by
  classical
  rw [comparePhase, Script.contSizes_seqList]
  set L := O.tuples
  have h1 : ∀ l ∈ (L.flatMap fun a => L.map fun b =>
      compareScript S πd Pk (strOf S x y a.1) (strOf S x y b.1) a.2 b.2).map Script.contSizes,
      ListFam l 1 (Fintype.card S.dom) := by
    intro l hl
    obtain ⟨sc, hsc, rfl⟩ := List.mem_map.1 hl
    obtain ⟨a, -, hb⟩ := List.mem_flatMap.1 hsc
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hb
    exact compareScript_fam S πd Pk _ _ _ _
  have h := ListFam.flatten h1
  rw [List.length_map, List.length_flatMap] at h
  simp only [List.length_map, List.map_const', List.sum_replicate, smul_eq_mul, mul_one] at h
  refine h.mono ?_
  have hL : L.length ≤ 2 * q ^ κ := by
    rw [O.length_eq]; have := card_embedding_le (q := q) κ; omega
  calc L.length * L.length ≤ (2 * q ^ κ) * (2 * q ^ κ) := Nat.mul_le_mul hL hL
    _ = 4 * q ^ (2 * κ) := by ring

end ComparePhase

/-! ### All calls of an aggregation round -/

section Agg

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S} (I : Aggregation P S L)

/-- **The regrouping (H2) for a whole aggregation round**: the `Continue` calls of the round's
script fall into at most `9 q^{2κ}` families, each with total size at most `s = |dom|`:
`2 binom(q,κ) κ!` certificate families (test set, string, coset index), `4 q^{2κ}` comparison
families, and at most `3 q^{κ+1}` item calls (each its own family). -/
theorem Aggregation.script_fam : ListFam I.script.contSizes (9 * L.q ^ (2 * P.κ)) S.size := by
  haveI := I.fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq Ω := Classical.decEq _
  have hs : Fintype.card S.dom = S.size := by
    rw [State.size, Nat.card_eq_fintype_card]
  have h1 : ListFam I.certScript.contSizes (L.q.choose P.κ * (2 * P.κ.factorial)) S.size := by
    have h := certPhase_fam S I.πd P.κ I.sets I.reps (dstr S S.x) (dstr S S.y)
    rw [hs] at h
    exact h
  have h2 : ListFam I.compScript.contSizes (4 * L.q ^ (2 * P.κ)) S.size := by
    have h := comparePhase_fam S I.πd I.pick P.κ I.tests (dstr S S.x) (dstr S S.y)
    rw [hs] at h
    exact h
  have hcalls : I.itemsScript.CallsExact (AggCall P S) :=
    Script.callsExact_bind _ _ (Script.callsExact_seqList _ fun s hs => by
        obtain ⟨b, -, rfl⟩ := List.mem_map.1 hs
        exact (I.items b).calls (I.items_valid b)) trivial
  have h3 : ListFam I.itemsScript.contSizes I.itemsScript.contSizes.length S.size :=
    ListFam.singletons (Script.contSizes_le_of_calls _ hcalls)
  have hitems : I.itemsScript.contSizes.length ≤ 3 * L.q ^ (P.κ + 1) := by
    rw [Script.contSizes_length]
    exact I.itemsScript_numCont_le
  have hcont : I.script.contSizes =
      I.certScript.contSizes ++ (I.compScript.contSizes ++ I.itemsScript.contSizes) := by
    rw [Aggregation.script, Script.contSizes_bind, Script.contSizes_bind]
  rw [hcont]
  refine ((h1.append (h2.append h3)).mono ?_)
  -- arithmetic
  have hq2 : 2 ≤ L.q := I.q_two
  have hκ5 : 5 ≤ P.κ := I.κ_five
  have hq1 : 1 ≤ L.q := by omega
  have hdesc : L.q.choose P.κ * P.κ.factorial ≤ L.q ^ P.κ := by
    have := Nat.descFactorial_le_pow L.q P.κ
    rw [Nat.descFactorial_eq_factorial_mul_choose] at this
    linarith
  have hA : L.q ^ P.κ ≤ L.q ^ (2 * P.κ) := Nat.pow_le_pow_right hq1 (by omega)
  have hC : L.q ^ (P.κ + 1) ≤ L.q ^ (2 * P.κ) := Nat.pow_le_pow_right hq1 (by omega)
  have h4 : L.q.choose P.κ * (2 * P.κ.factorial) ≤ 2 * L.q ^ P.κ := by nlinarith
  omega

end Agg

/-! ### From script sizes to exec calls -/

/-- **The Continue calls of a script run, with their sizes, are `Script.contSizes`.** -/
theorem Exec.contSizes_eq {α : Type} {s : Script α} {a : α} (e : Exec P s a) :
    (e.calls.filter fun nd => decide (nd.m = .cont)).map (fun nd => nd.S.size) = s.contSizes := by
  refine Exec.rec (motive_1 := fun _ {_ _} _ _ _ _ => True)
    (motive_2 := fun s _ e =>
      (e.calls.filter fun nd => decide (nd.m = .cont)).map (fun nd => nd.S.size) = s.contSizes)
    (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    ?done ?ask e
  case done =>
    intro α a
    simp [Exec.calls, Script.contSizes]
  case ask =>
    intro α Ω' C' m S k A a r e' _ ih
    have hA : A = S.answer := r.exact
    subst hA
    change (((⟨m, Ω', C', S, none, S.answer, r⟩ : Node P) :: e'.calls).filter _).map _ = _
    rw [List.filter_cons]
    simp only [Script.contSizes]
    by_cases hm : m = .cont
    · subst hm
      simp only [decide_true, if_true, List.map_cons, List.singleton_append]
      exact congrArg _ ih
    · simp only [decide_eq_true_eq, if_neg hm, List.nil_append]
      exact ih

/-! ### Families of the branches of an aggregation round -/

open Classical in
/-- **The families of the branches of a round.** The branch sums (`Σ_{u ∈ b} s_u`) of the
inherited calls of an aggregation round are grouped into `9 q^{2κ}` families, each with total
size at most `s = |dom|`, for each of the two classes (`aff = true`: domain `≤ θs`;
`aff = false`: the rest). -/
theorem aggregate_branch_fam {Ω C : Type} [Finite Ω] {S : State Ω C} {L : GiantLabels S}
    (I : Aggregation P S L) {b : Branches Ω} (e : Exec P I.script b) (θs : ℝ) (aff : Bool) :
    ListFam ((callBranches θs aff e).map fun b => (b.map fun u => (u.leaf.state P.κ).s).sum)
      (9 * L.q ^ (2 * P.κ)) S.size := by
  have hfin : ∀ nd ∈ e.calls, nd.m = .cont → Finite nd.Ω := by
    intro nd hnd hm
    have hcall := (Exec.calls_spec e _ I.calls).1 nd hnd
    rcases hcall with ⟨hm', -⟩ | ⟨-, hΩ, -⟩
    · rw [hm] at hm'; cases hm'
    · rw [hΩ]; infer_instance
  refine ListFam.mono_entries (I.script_fam) ?_ ?_
  · simp [callBranches, ← Exec.contSizes_eq e]
  · intro i hi
    have hlen : ((e.calls.filter fun nd => decide (nd.m = .cont))).length =
        (callBranches θs aff e).length := by
      simp [callBranches]
    have hi' : i < (e.calls.filter fun nd => decide (nd.m = .cont)).length := by
      simpa [callBranches] using hi
    have hnd := (List.mem_filter.1 (List.getElem_mem hi'))
    set nd := (e.calls.filter fun nd => decide (nd.m = .cont))[i]'hi' with hndef
    -- the entry on the left is a branch sum of `nd`, the entry on the right its size
    have hL : ((callBranches θs aff e).map fun b =>
        (b.map fun u => (u.leaf.state P.κ).s).sum)[i]'hi =
        ((nd.run.forest.filter fun ℓ => decide (((Nat.card ℓ.dom : ℕ) : ℝ) ≤ θs) = aff).map
          fun ℓ => Nat.card ℓ.dom).sum := by
      simp only [callBranches, List.getElem_map]
      simp [List.map_map, Function.comp_def, Leaf.toP, Leaf.state]
      rfl
    have hR : I.script.contSizes[i]'(by
        simpa [← Exec.contSizes_eq e] using hi') = nd.S.size := by
      simp only [← Exec.contSizes_eq e, List.getElem_map]
      rfl
    rw [hL, hR]
    have hndm : nd.m = .cont := by simpa using hnd.2
    haveI := hfin nd hnd.1 hndm
    have hspec := (forest_spec nd.run).2.2 this
    refine le_trans ?_ hspec
    exact List.Sublist.sum_le_sum ((List.filter_sublist).map _) (fun _ _ => Nat.zero_le _)

end GI.Algorithm
