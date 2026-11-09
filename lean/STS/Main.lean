import STS.Forward
import STS.Backward
import Mathlib.Algebra.Order.Group.Nat

/-!
# T2: the proofs of the two claims of `STS/Statement.lean`
-/

namespace STS

theorem card_point (d : ℕ) : Fintype.card (Point d) = 2 ^ (d + 3) - 1 := by
  have h1 : Fintype.card {z : Z // z ≠ 0} = 7 := by decide
  have h2 : Fintype.card {c : V d // c ≠ 0} = 2 ^ d - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    simp [ZMod.card]
  rw [Fintype.card_sum, Fintype.card_prod, h1, h2, Fintype.card_fin, pow_add]
  have : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  generalize 2 ^ d = m at this ⊢
  norm_num
  omega

/-- **T2, part 1**: `X_χ` is a Steiner triple system on `2^(d+3) - 1` points. -/
theorem t2_sts : T2_sts := by
  intro d χ
  refine ⟨?_, card_point d⟩
  rw [X_eq_blocksOf]
  exact isSTS_blocksOf (isSQ_third χ)

/-- **T2, part 2**: for non-constant `χ, χ'`, `X_χ ≅ X_χ'` iff `χ' ∘ A = χ` for some `A ∈ GL(V)`. -/
theorem t2_iso : T2_iso := by
  intro d χ χ' hχ hχ'
  exact ⟨linearlyEquivalent_of_isomorphic hχ hχ', isomorphic_of_linearlyEquivalent⟩

end STS

#print axioms STS.t2_sts
#print axioms STS.t2_iso
#print axioms STS.induced_linear
