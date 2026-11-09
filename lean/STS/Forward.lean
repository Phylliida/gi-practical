import STS.Third

/-!
# (⇐): a linear equivalence lifts to an isomorphism

`z ↦ z`, `(c, a) ↦ (A c, a)`, as in the memo.
-/

namespace STS

variable {d : ℕ}

/-- The lift of `A` to points. -/
def liftPt (A : V d ≃ₗ[ZMod 2] V d) : Point d → Point d
  | .inl z => .inl z
  | .inr (c, a) => .inr (⟨A c.1, A.map_ne_zero_iff.2 c.2⟩, a)

theorem liftPt_symm (A : V d ≃ₗ[ZMod 2] V d) (p : Point d) : liftPt A.symm (liftPt A p) = p := by
  rcases p with z | ⟨c, a⟩
  · rfl
  · simp [liftPt]

/-- The lift of `A` as a bijection. -/
def liftEquiv (A : V d ≃ₗ[ZMod 2] V d) : Point d ≃ Point d where
  toFun := liftPt A
  invFun := liftPt A.symm
  left_inv := liftPt_symm A
  right_inv p := by simpa using liftPt_symm A.symm p

theorem liftPt_commute {χ χ' : V d → Bool} (A : V d ≃ₗ[ZMod 2] V d)
    (hA : ∀ c : V d, c ≠ 0 → χ' (A c) = χ c) :
    ∀ x y, x ≠ y → liftPt A (third χ x y) = third χ' (liftPt A x) (liftPt A y) := by
  rintro (z | ⟨c, a⟩) (w | ⟨c', b⟩) hxy
  · have h : z ≠ w := fun e => hxy (e ▸ rfl)
    rw [third_inl_inl χ h]; exact (third_inl_inl χ' h).symm
  · simp only [liftPt, third_inl_inr, hA c'.1 c'.2]
  · simp only [liftPt, third_inr_inl, hA c.1 c.2]
  · by_cases h : c = c'
    · subst h
      have hab : a ≠ b := fun e => hxy (e ▸ rfl)
      simp only [liftPt, third_inr_inr_same _ _ hab, hA c.1 c.2]
    · have h' : (⟨A c.1, A.map_ne_zero_iff.2 c.2⟩ : Vn d) ≠ ⟨A c'.1, A.map_ne_zero_iff.2 c'.2⟩ :=
        fun e => h (Subtype.ext (A.injective (congrArg Subtype.val e)))
      simp only [liftPt, third_inr_inr_ne _ h, third_inr_inr_ne _ h']
      congr 2
      exact Subtype.ext (map_add A _ _)

/-- **(⇐)** -/
theorem isomorphic_of_linearlyEquivalent {χ χ' : V d → Bool} (h : LinearlyEquivalent χ χ') :
    Isomorphic (X χ) (X χ') := by
  obtain ⟨A, hA⟩ := h
  rw [X_eq_blocksOf, X_eq_blocksOf]
  exact isomorphic_of_commute (liftEquiv A) (liftPt_commute A hA)

end STS
