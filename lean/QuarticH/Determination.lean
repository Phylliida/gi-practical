import QuarticH.Basic

/-! Part 1: a good tuple determines the linear map. -/

namespace QuarticH

open Module

variable {d : ℕ}

/-- If every functional in a spanning set of `V*` vanishes at `x`, then `x = 0`. -/
theorem eq_zero_of_span_top {S : Set (Module.Dual (ZMod 2) (V d))}
    (hS : Submodule.span (ZMod 2) S = ⊤) {x : V d} (hx : ∀ φ ∈ S, φ x = 0) : x = 0 := by
  refine (Module.forall_dual_apply_eq_zero_iff (ZMod 2) x).1 fun φ => ?_
  have hle : Submodule.span (ZMod 2) S ≤ LinearMap.ker (Module.Dual.eval (ZMod 2) (V d) x) := by
    rw [Submodule.span_le]
    intro ψ hψ
    simp [hx ψ hψ]
  have := hle (hS ▸ Submodule.mem_top : φ ∈ Submodule.span (ZMod 2) S)
  simpa using this

theorem compLinearMap_vec (τ' : AltForm4 d) (M : V d →ₗ[ZMod 2] V d) (a b c x : V d) :
    τ'.compLinearMap M ![a, b, c, x] = τ' ![M a, M b, M c, M x] := by
  rw [AlternatingMap.compLinearMap_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem determination_proof : Determination := by
  intro d m b τ τ' u bv M₁ M₂ hgood h₁ h₂ hu hb
  have hval : ∀ M : V d →ₗ[ZMod 2] V d, τ = τ'.compLinearMap M →
      ∀ a b c x, τ ![a, b, c, x] = τ' ![M a, M b, M c, M x] := by
    intro M hM a b c x
    rw [hM, compLinearMap_vec]
  have hinj : Function.Injective M₁ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply eq_zero_of_span_top hgood
    rintro φ ⟨j, k, i, -, rfl⟩
    rw [contr3_apply, hval M₁ h₁, hx]
    exact τ'.map_coord_zero 3 rfl
  have hsurj := LinearMap.injective_iff_surjective.1 hinj
  refine LinearMap.ext fun x => ?_
  obtain ⟨z, hz⟩ := hsurj (M₁ x - M₂ x)
  have hz0 : z = 0 := by
    apply eq_zero_of_span_top hgood
    rintro φ ⟨j, k, i, -, rfl⟩
    rw [contr3_apply, hval M₁ h₁, hz, ← contr3_apply, map_sub, contr3_apply, contr3_apply,
      ← hval M₁ h₁, hu j, hu k, hb i, ← hval M₂ h₂, sub_self]
  rw [hz0, map_zero] at hz
  exact sub_eq_zero.1 hz.symm

end QuarticH
