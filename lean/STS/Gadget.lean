import STS.Statement

/-!
# Finite facts about `Z = Fin 8` (xor) and the gadget `F⁰, F¹`

All by `decide` over `Fin 8`.
-/

namespace STS

instance instDecInFactor : ∀ (col : Bool) (z a b : Z), Decidable (InFactor col z a b)
  | false, z, a, b => inferInstanceAs (Decidable (b = a ^^^ z))
  | true, z, a, b => inferInstanceAs (Decidable ((a, b) ∈ F1 z ∨ (b, a) ∈ F1 z))

/-! ## xor on `Fin 8` -/

theorem xor_assoc' (a b c : Z) : a ^^^ b ^^^ c = a ^^^ (b ^^^ c) := by
  revert a b c; decide

theorem xor_comm' (a b : Z) : a ^^^ b = b ^^^ a := by
  revert a b; decide

theorem xor_self' (a : Z) : a ^^^ a = 0 := by
  revert a; decide

theorem xor_zero' (a : Z) : a ^^^ 0 = a := by
  revert a; decide

theorem zero_xor' (a : Z) : 0 ^^^ a = a := by
  revert a; decide

theorem xor_eq_zero_iff (a b : Z) : a ^^^ b = 0 ↔ a = b := by
  revert a b; decide

theorem xor_cancel_left (a b : Z) : a ^^^ (a ^^^ b) = b := by
  revert a b; decide

theorem xor_cancel_right (a b : Z) : a ^^^ b ^^^ b = a := by
  revert a b; decide

theorem xor_three (a b : Z) : a ^^^ b ^^^ (a ^^^ b) = 0 := by
  revert a b; decide

theorem xor_solve (a b c : Z) (h : a ^^^ b ^^^ c = 0) : c = a ^^^ b := by
  revert a b c; decide

theorem xor_ne_self (a b : Z) (hb : b ≠ 0) : a ^^^ b ≠ a := by
  revert a b; decide

/-! ## The factors -/

/-- Each `F^col_z` (`z ≠ 0`) is a perfect matching: existence of the partner. -/
theorem inFactor_exists (col : Bool) (z : Z) (hz : z ≠ 0) (a : Z) : ∃ b, InFactor col z a b := by
  cases col
  · exact ⟨a ^^^ z, rfl⟩
  · revert z a; decide

/-- Uniqueness of the partner. -/
theorem inFactor_unique (col : Bool) (z a b b' : Z) (h : InFactor col z a b)
    (h' : InFactor col z a b') : b = b' := by
  cases col
  · exact h.trans h'.symm
  · revert z a b b'; decide

theorem inFactor_symm (col : Bool) (z a b : Z) (h : InFactor col z a b) : InFactor col z b a := by
  cases col
  · change a = b ^^^ z; change b = a ^^^ z at h; subst h; exact (xor_cancel_right a z).symm
  · exact h.symm

theorem inFactor_ne (col : Bool) (z a b : Z) (hz : z ≠ 0) (h : InFactor col z a b) : a ≠ b := by
  cases col
  · change b = a ^^^ z at h; subst h; exact (xor_ne_self a z hz).symm
  · revert z a b; decide

/-- `(F^col_z)_{z ≠ 0}` covers every pair: it is a 1-factorization. -/
theorem inFactor_cover (col : Bool) (a b : Z) (hab : a ≠ b) : ∃ z, z ≠ 0 ∧ InFactor col z a b := by
  cases col
  · refine ⟨a ^^^ b, ?_, ?_⟩
    · rwa [Ne, xor_eq_zero_iff]
    · exact (xor_cancel_left a b).symm
  · revert a b; decide

/-- ... and each pair lies in only one factor. -/
theorem inFactor_label_unique (col : Bool) (z z' a b : Z) (h : InFactor col z a b)
    (h' : InFactor col z' a b) : z = z' := by
  cases col
  · change b = a ^^^ z at h; change b = a ^^^ z' at h'
    have := h.symm.trans h'
    have := congrArg (a ^^^ ·) this
    simpa [← xor_assoc', xor_self', zero_xor'] using this
  · revert z z' a b; decide

/-! ## The two properties (a), (b) of the memo, in the form the proof uses -/

/-- Property (b) of the memo, used as: an additive `μ : Z → 𝔽₂` with `μ z + μ a + μ b = 0` for
every `{a,b} ∈ F¹_z` vanishes. -/
theorem F1_span (μ : Z → ZMod 2) (hμ : ∀ a b, μ (a ^^^ b) = μ a + μ b)
    (h : ∀ z a b, InFactor true z a b → μ z + μ a + μ b = 0) : ∀ a, μ a = 0 := by
  have h0 : μ 0 = 0 := by
    have := hμ 0 0
    have e : (0 : Z) ^^^ 0 = 0 := rfl
    rw [e] at this
    have key : ∀ x : ZMod 2, x = x + x → x = 0 := by decide
    exact key _ this
  have h3 : μ 3 = μ 1 + μ 2 := hμ 1 2
  have h5 : μ 5 = μ 1 + μ 4 := hμ 1 4
  have h6 : μ 6 = μ 2 + μ 4 := hμ 2 4
  have h7 : μ 7 = μ 3 + μ 4 := hμ 3 4
  have t1 := h 1 0 5 (by decide)
  have t2 := h 1 1 2 (by decide)
  have t3 := h 2 1 6 (by decide)
  rw [h0] at t1
  rw [h5] at t1
  rw [h6] at t3
  have key : ∀ m1 m2 m4 : ZMod 2, m1 + 0 + (m1 + m4) = 0 → m1 + m1 + m2 = 0 →
      m2 + m1 + (m2 + m4) = 0 → m1 = 0 ∧ m2 = 0 ∧ m4 = 0 := by decide
  obtain ⟨e1, e2, e4⟩ := key _ _ _ t1 t2 t3
  intro a
  have cases8 : ∀ a : Z, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 := by
    decide
  rcases cases8 a with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact e1
  · exact e2
  · rw [h3, e1, e2]; rfl
  · exact e4
  · rw [h5, e1, e4]; rfl
  · rw [h6, e2, e4]; rfl
  · rw [h7, h3, e1, e2, e4]; rfl

/-- Property (a) of the memo, in the form used: in `F¹` the composite of the matchings `F¹_{w₂}`
then `F¹_{w₁}` is not the matching `F¹_{w₁+w₂}` (whereas for `F⁰` it always is). -/
theorem F1_not_PG : ∃ w₁ w₂ a b c : Z, w₁ ≠ 0 ∧ w₂ ≠ 0 ∧ w₁ ≠ w₂ ∧ InFactor true w₂ a b ∧
    InFactor true w₁ b c ∧ ¬ InFactor true (w₁ ^^^ w₂) a c := by
  decide

end STS
