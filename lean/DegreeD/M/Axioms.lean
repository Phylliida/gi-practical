import DegreeD.M.Main

/-!
# The cited results as axioms

The pattern of `Workspace/Axioms/`: each cited result has its statement and justification as a
`def` with a docstring in `DegreeD/M/Cited.lean`, and is added here as an `axiom`, so that
`#print axioms` shows exactly which cited results a theorem depends on.

`GNSPrimitive` has constants: `gnsPrimitive` states only their existence (GNS Theorem 3.13: "for
some absolute constants `c₁, c₂`").
-/

namespace GI.DegreeD.M

/-- Babai–Cameron–Pálfy, Lemma 2.2 (as quoted by GNS, Lemma 2.2), for groups in `Γ̂_d`. -/
axiom bcp : BCP

/-- Grohe–Neuen–Schweitzer, Theorem 3.13, with option 2 in the product form established by its
proof (`DegreeD/M/Cited.lean`). -/
axiom gnsPrimitive : ∃ c₁ c₂ : ℝ, 0 ≤ c₁ ∧ 0 ≤ c₂ ∧ GNSPrimitive c₁ c₂

open Equiv Equiv.Perm GI.Algorithm GI.Paper
open scoped Pointwise

/-- **The Stage-1 degree-`d` theorem, with the cited results as axioms.** There are absolute
constants `c₁, c₂` such that for parameters `P`, charging constants `cc` compatible with `P` and
with `c₁ / log 2 + c₂ / log 48 ≤ a + a* / log 2`, the conclusion of `degreeD_stage1` holds. -/
theorem degreeD_stage1_ax : ∃ c₁ c₂ : ℝ, 0 ≤ c₁ ∧ 0 ≤ c₂ ∧
    ∀ {P : Params} {cc : ChargingConstants} {w : Node P → ℝ} {cw af cσ : ℝ}
      (_ : P.Terminating) (_ : Compat P cc) (_ : 2 * P.α ≤ P.γ) (_ : AboveBase P cc)
      (_ : ∀ n : ℕ, P.N₀ < n → (4 : ℝ) ≤ (n : ℝ) ^ ((1 - P.γ) / 2))
      (_ : ((2 * P.κ : ℕ) : ℝ) + Real.log (9 : ℕ) / Real.log 48 ≤ cc.aStar)
      (_ : c₁ / Real.log 2 + c₂ / Real.log 48 ≤ cc.a + cc.aStar / Real.log 2)
      (_ : (Real.log P.q₀.factorial / Real.log 48 + 1) / Real.log 17 ≤
        cc.a + cc.aStar / Real.log 2)
      (_ : 0 ≤ cσ) (_ : NodeBoundD w cw af) (_ : 0 ≤ cw) (_ : 0 ≤ af) (_ : af + 1 ≤ cc.a),
      ∃ C' : ℝ, ∀ (d : ℕ) {Ω C : Type} [Finite Ω] (S : State Ω C) {A : Set (Perm Ω)}
        (r : Run P .solve S none A), GammaHat d S.G → r.RootsOK cσ (max d 6) →
        (A = {g | g ∈ S.G ∧ ∀ v ∈ S.dom, S.y (g v) = S.x v} ∧
          (A = ∅ ∨ ∃ t ∈ S.G, A = t • (autGroup S.G S.dom S.dom_inv S.x : Set (Perm Ω)))) ∧
        r.total w ≤ Real.exp (C' * (GI.DegreeD.lam d * Real.log ((S.size : ℝ) + 2))) := by
  obtain ⟨c₁, c₂, h₁, h₂, hG⟩ := gnsPrimitive
  exact ⟨c₁, c₂, h₁, h₂, fun hP hc hαγ hbase h4 hab hcc hq hcσ hw hcw haf ha =>
    degreeD_stage1 hP hc hαγ hbase h4 hab bcp hG h₁ h₂ hcc hq hcσ hw hcw haf ha⟩

end GI.DegreeD.M
