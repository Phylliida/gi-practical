import DegreeD.M.Existence
import DegreeD.M.Final
import Workspace.Paper.MainTheoremCarrier
import Workspace.Assembly.AggParams

/-!
# `Supply P D` for all `D`, from HJ's Stage-1 data

`M.Supply P D` (`DegreeD/M/Existence.lean`) is HJ's `Supply` with one extra clause: the
fresh `Solve` calls of an aggregation round are on groups in `Γ̂_D` (`cls`). This file checks
this clause on HJ's own aggregation rounds: the only fresh `Solve` query of a round is the
configuration query `cfgQuery` (`pairState` on `Sym(C)`, `C ⊆ [q]`), which is in `Γ̂_D` when
`q ≤ D` (`pairState_class`); every other query of a round (certificates, comparisons, rectangle
queries, halving) is a `Continue` call. Then HJ's giant-step data `GiantSupply P` gives `M.Supply P D`
for every `D ≥ 6` (`Supply.ofGiant`), so the run existence of `degreeD_stage1_full` is
unconditional, modulo the cited inputs that HJ's giant-step data takes.
-/

namespace GI.DegreeD.M

open Equiv Equiv.Perm GI.Algorithm GI.Paper GI.CoherentEntrance GI.Rectangle GI.PairRefinement
open scoped Pointwise

variable {P : Params} {Ω C : Type} {D : ℕ}

section Items

variable {S : State Ω C} {L : GiantLabels S}

/-- The fresh `Solve` queries of an item are on `Γ̂_D` groups. -/
def itemClass (D : ℕ) : AuxItem P S L → Prop
  | .query Qs _ => ∀ Q ∈ Qs, Q.mode = .solve → GammaHat D Q.T.G
  | _ => True

/-- The script of an item in the class asks only class `Solve` queries. -/
theorem itemClass_calls (I : AuxItem P S L) (h : itemClass D I) :
    I.script.CallsExact fun {_ _} m T => m = .solve → GammaHat D T.G := by
  cases I with
  | none => trivial
  | overcoset => trivial
  | query Qs E₀ =>
    refine Script.callsExact_bind _ _ (Script.callsExact_seqList _ fun s hs => ?_) trivial
    obtain ⟨Q, hQ, rfl⟩ := List.mem_map.1 hs
    exact ⟨h Q hQ, trivial⟩
  | halving H =>
    show H.script.CallsExact _
    simp [Halving.script, Script.CallsExact]

theorem objItem_class {Z : Type*} [MulAction (Perm (Fin L.q)) Z] (zX zY : Z) :
    itemClass D (objItem zX zY : AuxItem P S L) := by
  classical
  unfold objItem
  split_ifs <;> exact trivial

theorem invItem_class {Z : Type*} [MulAction (Perm (Fin L.q)) Z] {ℓ : ℕ}
    (F : Canon L.q P.κ ℓ → Z) (X Y : Canon L.q P.κ ℓ) :
    itemClass D (invItem F X Y : AuxItem P S L) := by
  classical
  unfold invItem
  split_ifs <;> exact trivial

/-- The configuration query of Algorithm `alg:auxiliary` is on `Sym(C)`, `C ⊆ [q]`. -/
theorem cfgItem_class (hq : L.q ≤ D) (X Y : PairCfg L.q) :
    itemClass D (cfgItem X Y : AuxItem P S L) := by
  classical
  unfold cfgItem
  split_ifs with hc
  · intro Q hQ _
    simp only [List.mem_singleton] at hQ
    subst hQ
    refine pairState_class (D := D) ?_ _ _
    calc X.fiber.card ≤ Fintype.card (Fin L.q) := Finset.card_le_univ _
      _ = L.q := Fintype.card_fin _
      _ ≤ D := hq
  · exact trivial

/-- A rectangle oracle whose queries are `Continue` calls. -/
def RectOracleCont (O : RectOracle P S L) : Prop :=
  ∀ W R M N a₀, ∀ Q ∈ O.queries W R M N a₀, Q.mode = .cont

theorem ofReps_cont [Finite Ω]
    (rep : ∀ W R : Finset (Fin L.q), RectConds P S L W R → RectRep P S L W R) :
    RectOracleCont (RectOracle.ofReps rep) := by
  classical
  intro W R M N a₀ Q hQ
  simp only [RectOracle.ofReps] at hQ
  split_ifs at hQ with h
  · simp only [RectRep.queries, List.mem_cons] at hQ
    rcases hQ with rfl | hQ
    · rfl
    · simp only [Option.mem_toList, Option.map_eq_some_iff] at hQ
      obtain ⟨t, -, rfl⟩ := hQ
      rfl
  · simp at hQ

theorem rectItem_class {O : RectOracle P S L} (hO : RectOracleCont O) (ch : SojChoice)
    (X Y : PairCfg L.q) (y₀ : Fin L.q) (i₀ : Fin X.fiber.card)
    (cert : RectangleCertificate X.coloring false i₀ etaB) :
    itemClass D (rectItem O ch X Y y₀ i₀ cert) := by
  classical
  unfold rectItem
  simp only []
  split_ifs with hs
  · intro Q hQ hm
    have := hO _ _ _ _ _ Q hQ
    rw [this] at hm
    cases hm
  · exact trivial

theorem sojItem_class {O : RectOracle P S L} (hO : RectOracleCont O) (ch : SojChoice)
    (X Y : PairCfg L.q) (x₀ y₀ : Fin L.q) :
    itemClass D (sojItem O ch X Y x₀ y₀) := by
  classical
  unfold sojItem
  split_ifs with hx h1 h2 h3 h4
  · exact objItem_class _ _
  · exact rectItem_class hO ch X Y y₀ _ _
  · exact trivial
  · exact objItem_class _ _
  · exact trivial
  · exact trivial

theorem cfgOutItem_class {O : RectOracle P S L} (hO : RectOracleCont O) (ch : SojChoice)
    (hq : L.q ≤ D) (oX oY : CfgOut L.q) : itemClass D (cfgOutItem O ch oX oY) := by
  classical
  cases oX with
  | part zX =>
    cases oY with
    | part zY => exact objItem_class _ _
    | pair _ _ => exact trivial
    | none => exact trivial
  | pair X x₀ =>
    cases oY with
    | part _ => exact trivial
    | pair Y y₀ =>
      show itemClass D (if (L.q : ℝ) ≤ (S.N : ℝ) ^ P.α then cfgItem X Y else sojItem O ch X Y x₀ y₀)
      split_ifs
      · exact cfgItem_class hq X Y
      · exact sojItem_class hO ch X Y x₀ y₀
    | none => exact trivial
  | none => cases oY <;> exact trivial

theorem plan_class [Finite Ω] (πd : S.domGroup →* alternatingGroup (Fin L.q))
    (hv : HalvingChoice S L) {ℓ : ℕ} (cfg : Canon L.q P.κ ℓ → Canon L.q P.κ ℓ → AuxItem P S L)
    (hcfg : ∀ X Y, itemClass D (cfg X Y)) (fin : Finite Ω) (X Y : Canon L.q P.κ ℓ) :
    itemClass D (plan (P := P) fin πd hv cfg X Y) := by
  unfold plan
  split
  · exact invItem_class _ _ _
  · unfold halvingItem
    split_ifs <;> exact trivial
  · exact hcfg _ _
  · exact hcfg _ _

/-- **The fresh `Solve` calls of an aggregation round are on `Γ̂_D` groups.** -/
theorem Aggregation.calls_class [Finite Ω] (I : Aggregation P S L) (hq : L.q ≤ D) :
    I.script.CallsExact fun {_ _} m T => m = .solve → GammaHat D T.G := by
  classical
  letI : Fintype S.dom := Fintype.ofFinite _
  have hcont : ∀ {α : Type} {s : Script α}, s.CallsExact (fun m _ => m = .cont) →
      s.CallsExact fun {_ _} m T => m = .solve → GammaHat D T.G :=
    fun h => h.mono fun _ _ hm hs => by rw [hm] at hs; cases hs
  refine Script.callsExact_bind _ _ (hcont ?_)
    (Script.callsExact_bind _ _ (hcont ?_)
      (Script.callsExact_bind _ _ (Script.callsExact_seqList _ fun s hs => ?_) trivial))
  · exact certPhase_cont S I.πd P.κ I.sets I.reps _ _
  · exact comparePhase_cont S I.πd P.κ I.tests I.pick _ _
  · obtain ⟨b, -, rfl⟩ := List.mem_map.1 hs
    refine itemClass_calls (I.items b) ?_
    refine plan_class (P := P) I.πd I.halv I.cfg (fun X Y => ?_) I.fin _ _
    exact cfgOutItem_class (ofReps_cont I.rep) I.soj hq _ _

end Items

/-! ### Supply -/

/-- **`Supply P D` from HJ's giant-step data**, for every `D ≥ 6`. Unlike `Run`, the giant step
of the recursion does not depend on the class `Γ̂_D` except for the requirement on
the fresh calls, which `Aggregation.calls_class` checks: `q ≤ D` by `labels_q_le`. -/
noncomputable def Supply.ofGiant (hP : P.Terminating) (hγ : 0 ≤ P.γ) (Gs : GiantSupply P) {D : ℕ}
    (hD : 6 ≤ D) : Supply P D where
  cont S hinv hN _ htr hs _ := contData hP hγ S hinv hN htr hs
  giant S hinv hN hsN htr hs L hq hg :=
    have hqD : L.q ≤ D := by
      have := labels_q_le hg L
      rwa [max_eq_left hD] at this
    match Gs.giant S hinv hN hsN htr hs L hq with
    | .terminal hrow I => .terminal hrow I
    | .columns hrow I hinv => .columns hrow I hinv
    | .aggregate hnot I hsel hcon fin =>
      .aggregate hnot I hsel hcon fin (Aggregation.calls_class I hqD)

/-- **The Stage-1 degree-`d` theorem, with `Supply` discharged.** With HJ's giant-step data
`Gs` (`GI.Algorithm.GiantSupply P`), the conclusions of `degreeD_stage1_full` hold for every
`d`: every `Γ̂_d` state has a run with exact answer and root bounds, and every run with root
bounds costs at most `exp(C' log(s+2) log(8 max(d,6)))`. -/
theorem degreeD_stage1_of_giant (hP : P.Terminating) (hAut : GI.Cited.AutCardLeSq)
    (hLie : GI.Cited.SimpleValuationDegree) (hκ : 64 ≤ P.κ) {cc : ChargingConstants}
    (hc : Compat P cc) (hαγ : 2 * P.α ≤ P.γ) (hbase : AboveBase P cc)
    (h4 : ∀ n : ℕ, P.N₀ < n → (4 : ℝ) ≤ (n : ℝ) ^ ((1 - P.γ) / 2))
    (hab : ((2 * P.κ : ℕ) : ℝ) + Real.log (9 : ℕ) / Real.log 48 ≤ cc.aStar)
    {c₁ c₂ : ℝ} (hBCP : BCP) (hGNS : GNSPrimitive c₁ c₂) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hcc : c₁ / Real.log 2 + c₂ / Real.log 48 ≤ cc.a + cc.aStar / Real.log 2)
    (hq : (Real.log P.q₀.factorial / Real.log 48 + 1) / Real.log 17 ≤
      cc.a + cc.aStar / Real.log 2)
    {w : Node P → ℝ} {cw af : ℝ} (hw : NodeBoundD w cw af) (hcw : 0 ≤ cw) (haf : 0 ≤ af)
    (ha : af + 1 ≤ cc.a) (hγ : 0 ≤ P.γ) (Gs : GiantSupply P) :
    ∃ cσ C' : ℝ, 0 ≤ cσ ∧ ∀ (d : ℕ) {Ω C : Type} [Finite Ω] (S : State Ω C),
      GammaHat d S.G →
      (∃ r : Run P .solve S none S.answer, r.RootsOK cσ (max d 6)) ∧
      ∀ {A : Set (Perm Ω)} (r : Run P .solve S none A), r.RootsOK cσ (max d 6) →
        (A = {g | g ∈ S.G ∧ ∀ v ∈ S.dom, S.y (g v) = S.x v} ∧
          (A = ∅ ∨ ∃ t ∈ S.G, A = t • (autGroup S.G S.dom S.dom_inv S.x : Set (Perm Ω)))) ∧
        r.total w ≤ Real.exp (C' * (lam d * Real.log ((S.size : ℝ) + 2))) :=
  degreeD_stage1_full hP hAut hLie hκ hc hαγ hbase h4 hab hBCP hGNS hc₁ hc₂ hcc hq hw hcw haf ha
    (fun _ => Supply.ofGiant hP hγ Gs (le_max_right _ _))

/-- HJ's aggregation data, from the parameter conditions and the cited results. -/
noncomputable def giantSupplyOfCited {P : Params} (hA : P.Aggregates) (hT : P.RowThreshold)
    (hcite : GI.Cited.TransitiveAffected) (hK : GI.Cited.KaryCoherentRefinement)
    (h6 : GI.Cited.SixTransitiveContainsAlt) (hD : GI.Cited.DesignLemma) : GiantSupply P :=
  GiantSupply.ofAggregate hcite hT (AggSupply.ofCited hA hK h6 hD)

/-- **The run-existence half of the Stage-1 theorem, for every `d`**: from the cited results of
HJ's aggregation (`TransitiveAffected`, `KaryCoherentRefinement`, `SixTransitiveContainsAlt`,
`DesignLemma`) and Theorem A.9 (`AutCardLeSq`, `SimpleValuationDegree`), with the parameter conditions of
HJ's aggregation round. `degreeD_stage1_of_giant` with `giantSupplyOfCited`. -/
theorem degreeD_stage1_cited (hcite : GI.Cited.TransitiveAffected)
    (hK : GI.Cited.KaryCoherentRefinement) (h6 : GI.Cited.SixTransitiveContainsAlt)
    (hDL : GI.Cited.DesignLemma) (hAut : GI.Cited.AutCardLeSq)
    (hLie : GI.Cited.SimpleValuationDegree)
    (hP : P.Terminating) (hA : P.Aggregates) (hT : P.RowThreshold) (hκ : 64 ≤ P.κ)
    {cc : ChargingConstants}
    (hc : Compat P cc) (hαγ : 2 * P.α ≤ P.γ) (hbase : AboveBase P cc)
    (h4 : ∀ n : ℕ, P.N₀ < n → (4 : ℝ) ≤ (n : ℝ) ^ ((1 - P.γ) / 2))
    (hab : ((2 * P.κ : ℕ) : ℝ) + Real.log (9 : ℕ) / Real.log 48 ≤ cc.aStar)
    {c₁ c₂ : ℝ} (hBCP : BCP) (hGNS : GNSPrimitive c₁ c₂) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hcc : c₁ / Real.log 2 + c₂ / Real.log 48 ≤ cc.a + cc.aStar / Real.log 2)
    (hq : (Real.log P.q₀.factorial / Real.log 48 + 1) / Real.log 17 ≤
      cc.a + cc.aStar / Real.log 2)
    {w : Node P → ℝ} {cw af : ℝ} (hw : NodeBoundD w cw af) (hcw : 0 ≤ cw) (haf : 0 ≤ af)
    (ha : af + 1 ≤ cc.a) (hγ : 0 ≤ P.γ) :
    ∃ cσ C' : ℝ, 0 ≤ cσ ∧ ∀ (d : ℕ) {Ω C : Type} [Finite Ω] (S : State Ω C),
      GammaHat d S.G →
      (∃ r : Run P .solve S none S.answer, r.RootsOK cσ (max d 6)) ∧
      ∀ {A : Set (Perm Ω)} (r : Run P .solve S none A), r.RootsOK cσ (max d 6) →
        (A = {g | g ∈ S.G ∧ ∀ v ∈ S.dom, S.y (g v) = S.x v} ∧
          (A = ∅ ∨ ∃ t ∈ S.G, A = t • (autGroup S.G S.dom S.dom_inv S.x : Set (Perm Ω)))) ∧
        r.total w ≤ Real.exp (C' * (lam d * Real.log ((S.size : ℝ) + 2))) :=
  degreeD_stage1_of_giant hP hAut hLie hκ hc hαγ hbase h4 hab hBCP hGNS hc₁ hc₂ hcc hq hw hcw haf ha
    hγ (giantSupplyOfCited hA hT hcite hK h6 hDL)

/-! ### The parameter conditions -/

/-- **Parameters satisfying every condition**: every numeric hypothesis of `degreeD_stage1`,
`Params.Aggregates` and `Params.RowThreshold` (from the cited `TransitiveAffected`, as
`GI.Assembly.P₀_aggregates`), for any size of the GNS constants. -/
theorem params_full (hcite : GI.Cited.TransitiveAffected) (c₁ c₂ : ℝ) :
    ∃ (P : Params) (cc : ChargingConstants),
      P.Terminating ∧ 64 ≤ P.κ ∧ Compat P cc ∧ 2 * P.α ≤ P.γ ∧ AboveBase P cc ∧
      (∀ n : ℕ, P.N₀ < n → (4 : ℝ) ≤ (n : ℝ) ^ ((1 - P.γ) / 2)) ∧
      (((2 * P.κ : ℕ) : ℝ) + Real.log (9 : ℕ) / Real.log 48 ≤ cc.aStar) ∧
      (Real.log P.q₀.factorial / Real.log 48 + 1) / Real.log 17 ≤
        cc.a + cc.aStar / Real.log 2 ∧
      c₁ / Real.log 2 + c₂ / Real.log 48 ≤ cc.a + cc.aStar / Real.log 2 ∧
      P.Aggregates ∧ P.RowThreshold ∧ 0 ≤ P.γ ∧ P.a = cc.a - 1 ∧ 198 ≤ cc.a := by
  obtain ⟨P, cc, h1, h2, h3, h4, h5, h6, h7, h8, h9, hN, hα, hγ, hκ, hθ, hβ, hq₀, ha⟩ :=
    params_exist_ge (max (c₁ / Real.log 2 + c₂ / Real.log 48) 198) GI.Assembly.P₀.N₀
  have hmax1 := le_max_left (c₁ / Real.log 2 + c₂ / Real.log 48) 198
  have hmax2 := le_max_right (c₁ / Real.log 2 + c₂ / Real.log 48) 198
  have h2' : 0 < Real.log 2 := ChargingConstants.log_two_pos'
  have hstar : 0 ≤ cc.aStar / Real.log 2 := by
    have := cc.aStar_nonneg
    positivity
  have hα₀ : P.α = GI.Assembly.P₀.α := hα
  refine ⟨P, cc, h1, h2, h3, h4, h5, h6, h7, h8, by linarith, ?_, ?_, ?_, ha, by linarith⟩
  · exact
      { β_cfg := by rw [hβ]; norm_num
        θ_half := by rw [hθ]; norm_num
        θκ := by rw [hθ, hκ]; norm_num
        κ_five := by rw [hκ]; norm_num
        q₀_cert := by rw [hκ, hq₀]; norm_num
        q₀_cfg := by rw [hq₀, a12Threshold_eq]
        a_cert := by rw [hκ, ha]; push_cast; linarith
        cases := fun N hN' => by
          rw [hα₀]
          exact GI.Assembly.P₀_supportCases hcite N (lt_of_le_of_lt hN hN') }
  · intro N hN'
    rw [hα₀]
    exact GI.Assembly.P₀_rowThreshold N (lt_of_le_of_lt hN hN')
  · rw [hγ]; norm_num

end GI.DegreeD.M
