import STS.Main
import Mathlib.Data.Fin.VecNotation

/-!
# Non-vacuity checks for `STS/Statement.lean`

Concrete colourings at `d = 2` and `d = 3`:
* the hypotheses `NonConstant` are satisfiable;
* `X χ` is a Steiner triple system on 31 points, with blocks of each of the three kinds, and the
  colour really changes the blocks (a colour-0 block is absent from a colour-1 fibre);
* a pair where both sides of `T2_iso` are true, and pairs where both sides are false, the right-hand
  side decided directly (not through the theorem).  One false pair has equal weight, so the
  isomorphism is excluded only by the linear structure.
-/

namespace STS.Sanity

/-! ## `d = 2` -/

def e₀ : V 2 := ![1, 0]
def e₁ : V 2 := ![0, 1]

/-- indicator of `e₀` -/
def χ₁ : V 2 → Bool := fun c => decide (c = e₀)
/-- indicator of `e₁` -/
def χ₂ : V 2 → Bool := fun c => decide (c = e₁)
/-- on `V ∖ 0`: true at `e₁` and `e₀ + e₁` (weight 2) -/
def χ₃ : V 2 → Bool := fun c => !decide (c = e₀)

theorem nc₁ : NonConstant χ₁ := ⟨e₀, e₁, by decide, by decide, by decide⟩
theorem nc₂ : NonConstant χ₂ := ⟨e₀, e₁, by decide, by decide, by decide⟩
theorem nc₃ : NonConstant χ₃ := ⟨e₀, e₁, by decide, by decide, by decide⟩

/-- The point count, computed directly. -/
example : Fintype.card (Point 2) = 31 := by decide

example : IsSTS (X χ₁) ∧ Fintype.card (Point 2) = 2 ^ (2 + 3) - 1 := t2_sts 2 χ₁

def z (k : Z) (h : k ≠ 0 := by decide) : {z : Z // z ≠ 0} := ⟨k, h⟩
def v (c : V 2) (h : c ≠ 0 := by decide) : {c : V 2 // c ≠ 0} := ⟨c, h⟩

/-- A block of kind (i). -/
example : ({.inl (z 1), .inl (z 2), .inl (z 3)} : Finset (Point 2)) ∈ X χ₁ :=
  Or.inl ⟨z 1, z 2, z 3, by decide, rfl⟩

/-- A block of kind (ii) in the colour-1 fibre over `e₀`: `{0,5} ∈ F¹_1`. -/
theorem blk₁ : ({.inl (z 1), .inr (v e₀, 0), .inr (v e₀, 5)} : Finset (Point 2)) ∈ X χ₁ :=
  Or.inr (Or.inl ⟨z 1, v e₀, 0, 5, by decide, rfl⟩)

/-- A block of kind (ii) in the colour-0 fibre over `e₁`: `{0,1} ∈ F⁰_1`. -/
example : ({.inl (z 1), .inr (v e₁, 0), .inr (v e₁, 1)} : Finset (Point 2)) ∈ X χ₁ :=
  Or.inr (Or.inl ⟨z 1, v e₁, 0, 1, by decide, rfl⟩)

/-- ... but the same colour-0 triple over the colour-1 fibre `e₀` is *not* a block. -/
example : ({.inl (z 1), .inr (v e₀, 0), .inr (v e₀, 1)} : Finset (Point 2)) ∉ X χ₁ := by
  intro h
  obtain ⟨-, huniq⟩ := (t2_sts 2 χ₁).1
  obtain ⟨B, -, hB⟩ := huniq (.inl (z 1)) (.inr (v e₀, 0)) Sum.inl_ne_inr
  have e1 := hB _ ⟨blk₁, by simp, by simp⟩
  have e2 := hB _ ⟨h, by simp, by simp⟩
  have : (.inr (v e₀, 1) : Point 2) ∈ ({.inl (z 1), .inr (v e₀, 0), .inr (v e₀, 5)} :
      Finset (Point 2)) := by rw [e1, ← e2]; simp
  simp [v] at this

/-- A block of kind (iii) over the line `{e₀, e₁, e₀ + e₁}`. -/
example : ({.inr (v e₀, 3), .inr (v e₁, 6), .inr (v (e₀ + e₁), 3 ^^^ 6)} : Finset (Point 2)) ∈
    X χ₁ :=
  Or.inr (Or.inr ⟨v e₀, v e₁, v (e₀ + e₁), 3, 6, by decide, rfl⟩)

/-! ### Both sides true: `χ₁, χ₂` (swap the coordinates) -/

/-- `(v₀, v₁) ↦ (v₁, v₀)` -/
def swapL : V 2 →ₗ[ZMod 2] V 2 where
  toFun c := ![c 1, c 0]
  map_add' a b := by funext i; fin_cases i <;> simp
  map_smul' r a := by funext i; fin_cases i <;> simp

theorem swapL_injective : Function.Injective swapL := by
  intro a b h
  have : ∀ a b : V 2, swapL a = swapL b → a = b := by decide
  exact this a b h

noncomputable def swapA : V 2 ≃ₗ[ZMod 2] V 2 :=
  LinearEquiv.ofBijective swapL ⟨swapL_injective, Finite.injective_iff_surjective.1 swapL_injective⟩

theorem lin₁₂ : LinearlyEquivalent χ₁ χ₂ := by
  refine ⟨swapA, fun c hc => ?_⟩
  show χ₂ (swapL c) = χ₁ c
  revert c; decide

example : Isomorphic (X χ₁) (X χ₂) ∧ LinearlyEquivalent χ₁ χ₂ :=
  ⟨(t2_iso 2 χ₁ χ₂ nc₁ nc₂).2 lin₁₂, lin₁₂⟩

/-! ### Both sides false: `χ₁, χ₃` (weights 1 and 2) -/

theorem not_lin₁₃ : ¬ LinearlyEquivalent χ₁ χ₃ := by
  rintro ⟨A, hA⟩
  -- the only nonzero `c` with `χ₃ c = false` is `e₀`
  have only : ∀ c : V 2, c ≠ 0 → χ₃ c = false → c = e₀ := by decide
  have h1 := only _ (A.map_ne_zero_iff.2 (by decide)) (hA e₁ (by decide))
  have h2 := only _ (A.map_ne_zero_iff.2 (by decide)) (hA (e₀ + e₁) (by decide))
  have := A.injective (h1.trans h2.symm)
  revert this; decide

example : ¬ Isomorphic (X χ₁) (X χ₃) ∧ ¬ LinearlyEquivalent χ₁ χ₃ :=
  ⟨fun h => not_lin₁₃ ((t2_iso 2 χ₁ χ₃ nc₁ nc₃).1 h), not_lin₁₃⟩

/-! ## `d = 3`: equal weights -/

def f₀ : V 3 := ![1, 0, 0]
def f₁ : V 3 := ![0, 1, 0]
def f₂ : V 3 := ![0, 0, 1]

/-- indicator of a line `{f₀, f₁, f₀ + f₁}` -/
def χL : V 3 → Bool := fun c => decide (c = f₀ ∨ c = f₁ ∨ c = f₀ + f₁)
/-- indicator of a basis `{f₀, f₁, f₂}` -/
def χB : V 3 → Bool := fun c => decide (c = f₀ ∨ c = f₁ ∨ c = f₂)
/-- indicator of another basis `{f₀, f₀ + f₁, f₀ + f₁ + f₂}` -/
def χB' : V 3 → Bool := fun c => decide (c = f₀ ∨ c = f₀ + f₁ ∨ c = f₀ + f₁ + f₂)

theorem ncL : NonConstant χL := ⟨f₀, f₂, by decide, by decide, by decide⟩
theorem ncB : NonConstant χB := ⟨f₀, f₀ + f₁, by decide, by decide, by decide⟩
theorem ncB' : NonConstant χB' := ⟨f₀, f₁, by decide, by decide, by decide⟩

/-- Both sides false although both colourings have weight 3. -/
theorem not_linLB : ¬ LinearlyEquivalent χL χB := by
  rintro ⟨A, hA⟩
  have inB : ∀ c : V 3, χB c = true → c = f₀ ∨ c = f₁ ∨ c = f₂ := by decide
  have h0 := inB _ ((hA f₀ (by decide)).trans (by decide))
  have h1 := inB _ ((hA f₁ (by decide)).trans (by decide))
  have h2 := inB _ ((hA (f₀ + f₁) (by decide)).trans (by decide))
  have hne : A f₀ ≠ A f₁ := A.injective.ne (by decide)
  rw [map_add] at h2
  -- the sum of two distinct basis vectors is not a basis vector
  have key : ∀ u w : V 3, (u = f₀ ∨ u = f₁ ∨ u = f₂) → (w = f₀ ∨ w = f₁ ∨ w = f₂) → u ≠ w →
      ¬ (u + w = f₀ ∨ u + w = f₁ ∨ u + w = f₂) := by decide
  exact key _ _ h0 h1 hne h2

example : ¬ Isomorphic (X χL) (X χB) ∧ ¬ LinearlyEquivalent χL χB :=
  ⟨fun h => not_linLB ((t2_iso 3 χL χB ncL ncB).1 h), not_linLB⟩

/-- `v ↦ (v₀ + v₁ + v₂, v₁ + v₂, v₂)`, sending `f₀, f₁, f₂` to `f₀, f₀ + f₁, f₀ + f₁ + f₂`. -/
def triA : V 3 →ₗ[ZMod 2] V 3 where
  toFun c := ![c 0 + c 1 + c 2, c 1 + c 2, c 2]
  map_add' a b := by
    funext i; fin_cases i <;> simp <;> ring
  map_smul' r a := by
    funext i; fin_cases i <;> simp <;> ring

theorem triA_injective : Function.Injective triA := by
  intro a b h
  have : ∀ a b : V 3, triA a = triA b → a = b := by decide
  exact this a b h

noncomputable def triE : V 3 ≃ₗ[ZMod 2] V 3 :=
  LinearEquiv.ofBijective triA ⟨triA_injective, Finite.injective_iff_surjective.1 triA_injective⟩

/-- Both sides true, by a non-permutation matrix. -/
theorem linBB' : LinearlyEquivalent χB χB' := by
  refine ⟨triE, fun c hc => ?_⟩
  show χB' (triA c) = χB c
  revert c; decide

example : Isomorphic (X χB) (X χB') ∧ LinearlyEquivalent χB χB' :=
  ⟨(t2_iso 3 χB χB' ncB ncB').2 linBB', linBB'⟩

end STS.Sanity

#print axioms STS.Sanity.not_linLB
#print axioms STS.Sanity.linBB'
#print axioms STS.Sanity.not_lin₁₃
#print axioms STS.Sanity.lin₁₂
