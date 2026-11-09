import DegreeD.M.Existence
import DegreeD.M.Axioms
import DegreeD.M.ParamsExample

/-!
# The Stage-1 degree-`d` theorem, assembled

`degreeD_stage1` (`DegreeD/M/Main.lean`) is the cost bound for every run with root bounds on a
`Γ̂_d` state. `degreeD_stage1_full` adds the existence of such a run, for `Γ̂_d` states, given
the subroutine data `Supply`; `degreeD_stage1_axioms` is the form with the cited results of the
degree-`d` analysis as axioms.
-/

namespace GI.DegreeD.M

open Equiv Equiv.Perm GI.Algorithm GI.Paper
open scoped Pointwise

variable {P : Params}

/-- **The Stage-1 degree-`d` theorem with run existence.** Under the hypotheses of
`degreeD_stage1` and Theorem A.9 (the cited inputs of `σ = O(log s)`), for `Γ̂_d` states there is a run of
`Solve` with exact answer and root bounds (given the subroutine data), and every run with root bounds
costs at most `exp(C' log(s+2) log(8 max(d,6)))`, with `C'` absolute. -/
theorem degreeD_stage1_full (hP : P.Terminating) (hAut : GI.Cited.AutCardLeSq)
    (hLie : GI.Cited.SimpleValuationDegree) (hκ : 64 ≤ P.κ) {cc : ChargingConstants}
    (hc : Compat P cc) (hαγ : 2 * P.α ≤ P.γ) (hbase : AboveBase P cc)
    (h4 : ∀ n : ℕ, P.N₀ < n → (4 : ℝ) ≤ (n : ℝ) ^ ((1 - P.γ) / 2))
    (hab : ((2 * P.κ : ℕ) : ℝ) + Real.log (9 : ℕ) / Real.log 48 ≤ cc.aStar)
    {c₁ c₂ : ℝ} (hBCP : BCP) (hGNS : GNSPrimitive c₁ c₂) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hcc : c₁ / Real.log 2 + c₂ / Real.log 48 ≤ cc.a + cc.aStar / Real.log 2)
    (hq : (Real.log P.q₀.factorial / Real.log 48 + 1) / Real.log 17 ≤
      cc.a + cc.aStar / Real.log 2)
    {w : Node P → ℝ} {cw af : ℝ} (hw : NodeBoundD w cw af) (hcw : 0 ≤ cw) (haf : 0 ≤ af)
    (ha : af + 1 ≤ cc.a) (Su : ∀ d, Supply P (max d 6)) :
    ∃ cσ C' : ℝ, 0 ≤ cσ ∧ ∀ (d : ℕ) {Ω C : Type} [Finite Ω] (S : State Ω C),
      GammaHat d S.G →
      (∃ r : Run P .solve S none S.answer, r.RootsOK cσ (max d 6)) ∧
      ∀ {A : Set (Perm Ω)} (r : Run P .solve S none A), r.RootsOK cσ (max d 6) →
        (A = {g | g ∈ S.G ∧ ∀ v ∈ S.dom, S.y (g v) = S.x v} ∧
          (A = ∅ ∨ ∃ t ∈ S.G, A = t • (autGroup S.G S.dom S.dom_inv S.x : Set (Perm Ω)))) ∧
        r.total w ≤ Real.exp (C' * (lam d * Real.log ((S.size : ℝ) + 2))) := by
  obtain ⟨cσ, hcσ, hσ⟩ := GI.Paper.sigma_le_log hAut hLie
  have hσ' := hσ P.κ hκ
  obtain ⟨C', hC'⟩ := degreeD_stage1 hP hc hαγ hbase h4 hab hBCP hGNS hc₁ hc₂ hcc hq hcσ hw hcw haf ha
  refine ⟨cσ, C', hcσ, fun d Ω C _ S hg => ⟨?_, fun r hr => hC' d S r hg hr⟩⟩
  have hgD : GammaHat (max d 6) S.G := hg.mono (le_max_left _ _)
  exact exists_run_solve hP hσ' hcσ (Su d) S hgD

/-- **The Stage-1 degree-`d` theorem, with the cited results as axioms** (`bcp`, `gnsPrimitive`):
there are absolute constants `c₁, c₂` such that the conclusion of `degreeD_stage1_full` holds for
all parameters with `c₁ / log 2 + c₂ / log 48 ≤ cc.a + cc.aStar / log 2`. -/
theorem degreeD_stage1_axioms : ∃ c₁ c₂ : ℝ, 0 ≤ c₁ ∧ 0 ≤ c₂ ∧
    ∀ {P : Params} (_ : P.Terminating) (_ : GI.Cited.AutCardLeSq)
      (_ : GI.Cited.SimpleValuationDegree) (_ : 64 ≤ P.κ) {cc : ChargingConstants}
      (_ : Compat P cc) (_ : 2 * P.α ≤ P.γ) (_ : AboveBase P cc)
      (_ : ∀ n : ℕ, P.N₀ < n → (4 : ℝ) ≤ (n : ℝ) ^ ((1 - P.γ) / 2))
      (_ : ((2 * P.κ : ℕ) : ℝ) + Real.log (9 : ℕ) / Real.log 48 ≤ cc.aStar)
      (_ : c₁ / Real.log 2 + c₂ / Real.log 48 ≤ cc.a + cc.aStar / Real.log 2)
      (_ : (Real.log P.q₀.factorial / Real.log 48 + 1) / Real.log 17 ≤
        cc.a + cc.aStar / Real.log 2)
      {w : Node P → ℝ} {cw af : ℝ} (_ : NodeBoundD w cw af) (_ : 0 ≤ cw) (_ : 0 ≤ af)
      (_ : af + 1 ≤ cc.a) (_ : ∀ d, Supply P (max d 6)),
    ∃ cσ C' : ℝ, 0 ≤ cσ ∧ ∀ (d : ℕ) {Ω C : Type} [Finite Ω] (S : State Ω C),
      GammaHat d S.G →
      (∃ r : Run P .solve S none S.answer, r.RootsOK cσ (max d 6)) ∧
      ∀ {A : Set (Perm Ω)} (r : Run P .solve S none A), r.RootsOK cσ (max d 6) →
        (A = {g | g ∈ S.G ∧ ∀ v ∈ S.dom, S.y (g v) = S.x v} ∧
          (A = ∅ ∨ ∃ t ∈ S.G, A = t • (autGroup S.G S.dom S.dom_inv S.x : Set (Perm Ω)))) ∧
        r.total w ≤ Real.exp (C' * (lam d * Real.log ((S.size : ℝ) + 2))) := by
  obtain ⟨c₁, c₂, h₁, h₂, hG⟩ := gnsPrimitive
  exact ⟨c₁, c₂, h₁, h₂, fun hP hAut hLie hκ _ hc hαγ hbase h4 hab hcc hq _ _ _ hw hcw haf ha Su =>
    degreeD_stage1_full hP hAut hLie hκ hc hαγ hbase h4 hab bcp hG h₁ h₂ hcc hq hw hcw haf ha Su⟩

end GI.DegreeD.M
