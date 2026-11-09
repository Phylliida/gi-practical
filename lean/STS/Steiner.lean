import STS.Statement
import Mathlib.Data.Finset.Card

/-!
# Steiner quasigroups versus block systems

A "third point" operation `t` with the Steiner quasigroup laws on distinct pairs gives the block
system `blocksOf t = {{x, y, t x y} | x ≠ y}`, which is a Steiner triple system; a bijection is an
isomorphism of such block systems iff it commutes with `t`.
-/

namespace STS

variable {P P' : Type*} [DecidableEq P] [DecidableEq P']

/-- Steiner quasigroup laws for `t`, required only on distinct pairs. -/
structure IsSQ (t : P → P → P) : Prop where
  ne_left : ∀ x y, x ≠ y → t x y ≠ x
  ne_right : ∀ x y, x ≠ y → t x y ≠ y
  comm : ∀ x y, x ≠ y → t x y = t y x
  cancel : ∀ x y, x ≠ y → t x (t x y) = y

/-- The blocks `{x, y, t x y}`. -/
def blocksOf (t : P → P → P) : Set (Finset P) := {B | ∃ x y, x ≠ y ∧ B = {x, y, t x y}}

variable {t : P → P → P} {t' : P' → P' → P'}

omit [DecidableEq P] in
theorem IsSQ.cancel' (h : IsSQ t) (x y : P) (hxy : x ≠ y) : t (t x y) y = x := by
  have h1 := h.ne_right x y hxy
  rw [h.comm _ _ h1, h.comm x y hxy, h.cancel y x (Ne.symm hxy)]

set_option linter.unusedTactic false in
/-- If `x ≠ y` lie in the block `{x₀, y₀, t x₀ y₀}`, so does `t x y`. -/
theorem IsSQ.third_mem (h : IsSQ t) {x₀ y₀ x y : P} (h₀ : x₀ ≠ y₀) (hxy : x ≠ y)
    (hx : x ∈ ({x₀, y₀, t x₀ y₀} : Finset P)) (hy : y ∈ ({x₀, y₀, t x₀ y₀} : Finset P)) :
    t x y ∈ ({x₀, y₀, t x₀ y₀} : Finset P) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hxy
    | (simp; done)
    | (rw [h.comm _ _ hxy]; simp; done)
    | (rw [h.cancel _ _ h₀]; simp; done)
    | (rw [h.comm _ _ hxy, h.cancel _ _ h₀]; simp; done)
    | (rw [h.comm _ _ h₀, h.cancel _ _ (Ne.symm h₀)]; simp; done)
    | (rw [h.cancel' _ _ h₀]; simp; done)

theorem IsSQ.card_eq (h : IsSQ t) {x y : P} (hxy : x ≠ y) : ({x, y, t x y} : Finset P).card = 3 :=
  Finset.card_eq_three.2 ⟨x, y, t x y, hxy, (h.ne_left x y hxy).symm, (h.ne_right x y hxy).symm,
    rfl⟩

/-- The block through two distinct points of a block `{x₀, y₀, t x₀ y₀}` is that block. -/
theorem IsSQ.block_eq (h : IsSQ t) {x₀ y₀ x y : P} (h₀ : x₀ ≠ y₀) (hxy : x ≠ y)
    (hx : x ∈ ({x₀, y₀, t x₀ y₀} : Finset P)) (hy : y ∈ ({x₀, y₀, t x₀ y₀} : Finset P)) :
    ({x₀, y₀, t x₀ y₀} : Finset P) = {x, y, t x y} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact h.third_mem h₀ hxy hx hy
  · rw [h.card_eq h₀, h.card_eq hxy]

theorem isSTS_blocksOf (h : IsSQ t) : IsSTS (blocksOf t) := by
  refine ⟨?_, ?_⟩
  · rintro B ⟨x, y, hxy, rfl⟩; exact h.card_eq hxy
  · intro x y hxy
    refine ⟨{x, y, t x y}, ⟨⟨x, y, hxy, rfl⟩, by simp, by simp⟩, ?_⟩
    rintro B ⟨⟨x₀, y₀, h₀, rfl⟩, hx, hy⟩
    exact h.block_eq h₀ hxy hx hy

/-- A bijection commuting with the third-point operations is an isomorphism of block systems. -/
theorem isomorphic_of_commute (e : P ≃ P') (he : ∀ x y, x ≠ y → e (t x y) = t' (e x) (e y)) :
    Isomorphic (blocksOf t) (blocksOf t') := by
  refine ⟨e, fun B => ⟨?_, ?_⟩⟩
  · rintro ⟨x, y, hxy, rfl⟩
    refine ⟨e x, e y, e.injective.ne hxy, ?_⟩
    simp [Finset.image_insert, he x y hxy]
  · rintro ⟨x', y', hxy', hB⟩
    refine ⟨e.symm x', e.symm y', e.symm.injective.ne hxy', ?_⟩
    apply Finset.image_injective e.injective
    rw [hB]
    have := he (e.symm x') (e.symm y') (e.symm.injective.ne hxy')
    simp only [Equiv.apply_symm_apply] at this
    simp [Finset.image_insert, this]

/-- An isomorphism of block systems commutes with the third-point operations. -/
theorem commute_of_iso (h : IsSQ t) (h' : IsSQ t') (e : P ≃ P')
    (he : ∀ B : Finset P, B ∈ blocksOf t ↔ B.image e ∈ blocksOf t') :
    ∀ x y, x ≠ y → e (t x y) = t' (e x) (e y) := by
  intro x y hxy
  have hB : ({x, y, t x y} : Finset P).image e ∈ blocksOf t' := (he _).1 ⟨x, y, hxy, rfl⟩
  have hexy : e x ≠ e y := e.injective.ne hxy
  obtain ⟨x₀, y₀, h₀, hB'⟩ := hB
  have hmem : ∀ p ∈ ({x, y, t x y} : Finset P), e p ∈ ({x₀, y₀, t' x₀ y₀} : Finset P') := by
    intro p hp; rw [← hB']; exact Finset.mem_image_of_mem e hp
  have heq := h'.block_eq h₀ hexy (hmem x (by simp)) (hmem y (by simp))
  have h3 := hmem (t x y) (by simp)
  rw [heq] at h3
  simp only [Finset.mem_insert, Finset.mem_singleton] at h3
  rcases h3 with h3 | h3 | h3
  · exact absurd (e.injective h3) (h.ne_left x y hxy)
  · exact absurd (e.injective h3) (h.ne_right x y hxy)
  · exact h3

omit [DecidableEq P] [DecidableEq P'] in
/-- If `e` commutes with the third-point operations, so does `e.symm`. -/
theorem commute_symm (e : P ≃ P') (he : ∀ x y, x ≠ y → e (t x y) = t' (e x) (e y)) :
    ∀ x y, x ≠ y → e.symm (t' x y) = t (e.symm x) (e.symm y) := by
  intro x y hxy
  apply e.injective
  rw [he _ _ (e.symm.injective.ne hxy)]
  simp

end STS
