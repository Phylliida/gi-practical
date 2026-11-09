import STS.Chars
import Mathlib.Algebra.Module.ZMod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# (⇒): an isomorphism induces a linear equivalence

Let `φ` commute with the third-point operations of `X_χ` and `X_χ'` (`χ, χ'` non-constant).
Characters are pulled back along `φ`, so by `char_classify` `φ` maps `Z ∖ 0` to itself and fibres
to fibres; the induced map `A` on fibre indices is additive (lines of `PG(V)` go to lines) and
bijective.  Finally colours are preserved: a colour-0 fibre `S ∪ C_c` is `PG(3,2)`-like (the
matchings compose additively), a colour-1 fibre is not (`F1_not_PG`).
-/

namespace STS

variable {d : ℕ}

/-- `φ` commutes with the third-point operations. -/
def Commutes (χ χ' : V d → Bool) (φ : Point d ≃ Point d) : Prop :=
  ∀ x y, x ≠ y → φ (third χ x y) = third χ' (φ x) (φ y)

section OneSided

variable {χ χ' : V d → Bool} (hχ : NonConstant χ) {φ : Point d ≃ Point d} (hφ : Commutes χ χ' φ)
include hφ

theorem isChar_comp {f : Point d → ZMod 2} (hf : IsChar (third χ') f) :
    IsChar (third χ) (f ∘ φ) := by
  intro x y hxy
  simp only [Function.comp, hφ x y hxy]
  exact hf _ _ (φ.injective.ne hxy)

include hχ

theorem fibre_const (c : Vn d) (a b : Z) :
    fibreOf (φ (.inr (c, a))) = fibreOf (φ (.inr (c, b))) := by
  funext i
  exact (char_classify hχ (isChar_comp hφ (isChar_coord χ' i))).2 c a b

theorem map_inl (z : Zn) : ∃ w, φ (.inl z) = .inl w := by
  have h0 : fibreOf (φ (.inl z)) = 0 := by
    funext i
    exact (char_classify hχ (isChar_comp hφ (isChar_coord χ' i))).1 z
  rcases h : φ (.inl z) with w | ⟨c, a⟩
  · exact ⟨w, rfl⟩
  · rw [h] at h0; exact absurd h0 c.2

end OneSided

theorem Commutes.symm {χ χ' : V d → Bool} {φ : Point d ≃ Point d} (hφ : Commutes χ χ' φ) :
    Commutes χ' χ φ.symm :=
  commute_symm φ hφ

section TwoSided

variable {χ χ' : V d → Bool} (hχ : NonConstant χ) (hχ' : NonConstant χ')
  {φ : Point d ≃ Point d} (hφ : Commutes χ χ' φ)
include hχ hχ' hφ

omit hχ in
theorem map_inr (c : Vn d) (a : Z) : ∃ q, φ (.inr (c, a)) = .inr q := by
  rcases h : φ (.inr (c, a)) with w | q
  · obtain ⟨u, hu⟩ := map_inl hχ' hφ.symm w
    rw [← h, Equiv.symm_apply_apply] at hu
    exact absurd hu Sum.inr_ne_inl
  · exact ⟨q, rfl⟩

omit hχ in
/-- Fibres go to distinct fibres. -/
theorem fibre_inj {c c' : Vn d} {a b : Z}
    (h : fibreOf (φ (.inr (c, a))) = fibreOf (φ (.inr (c', b)))) : c = c' := by
  obtain ⟨⟨e, a'⟩, ha⟩ := map_inr hχ' hφ c a
  obtain ⟨⟨e', b'⟩, hb⟩ := map_inr hχ' hφ c' b
  rw [ha, hb] at h
  simp only [fibreOf] at h
  have hee : e = e' := Subtype.ext h
  subst hee
  have := fibre_const hχ' hφ.symm e a' b'
  rw [← ha, ← hb, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this
  exact Subtype.ext this

end TwoSided

/-- The map induced on `V` (extended by `0 ↦ 0`). -/
noncomputable def inducedMap (φ : Point d ≃ Point d) (v : V d) : V d :=
  if h : v = 0 then 0 else fibreOf (φ (.inr (⟨v, h⟩, 0)))

section Induced

variable {χ χ' : V d → Bool} (hχ : NonConstant χ) (hχ' : NonConstant χ')
  {φ : Point d ≃ Point d} (hφ : Commutes χ χ' φ)
include hχ hφ

omit hχ' in
theorem inducedMap_fibre (c : Vn d) (a : Z) : fibreOf (φ (.inr (c, a))) = inducedMap φ c.1 := by
  simp only [inducedMap, c.2, dite_false]
  exact fibre_const hχ hφ c a 0

include hχ'

theorem inducedMap_ne_zero (c : Vn d) : inducedMap φ c.1 ≠ 0 := by
  rw [← inducedMap_fibre hχ hφ c 0]
  obtain ⟨q, hq⟩ := map_inr hχ' hφ c 0
  rw [hq]; exact q.1.2

theorem inducedMap_eq_iff (c c' : Vn d) : inducedMap φ c.1 = inducedMap φ c'.1 ↔ c = c' := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  rw [← inducedMap_fibre hχ hφ c 0, ← inducedMap_fibre hχ hφ c' 0] at h
  exact fibre_inj hχ' hφ h

theorem inducedMap_injective : Function.Injective (inducedMap φ) := by
  intro u v h
  by_cases hu : u = 0 <;> by_cases hv : v = 0
  · rw [hu, hv]
  · exfalso; rw [hu] at h
    exact inducedMap_ne_zero hχ hχ' hφ ⟨v, hv⟩ (by simpa [inducedMap] using h.symm)
  · exfalso; rw [hv] at h
    exact inducedMap_ne_zero hχ hχ' hφ ⟨u, hu⟩ (by simpa [inducedMap] using h)
  · exact congrArg Subtype.val ((inducedMap_eq_iff hχ hχ' hφ ⟨u, hu⟩ ⟨v, hv⟩).1 h)

theorem inducedMap_add (u v : V d) : inducedMap φ (u + v) = inducedMap φ u + inducedMap φ v := by
  by_cases hu : u = 0
  · subst hu; simp [inducedMap]
  by_cases hv : v = 0
  · subst hv; simp [inducedMap]
  by_cases huv : u = v
  · subst huv; rw [V.add_self, V.add_self]; simp [inducedMap]
  -- a line `{u, v, u + v}` of `PG(V)`
  set c : Vn d := ⟨u, hu⟩
  set c' : Vn d := ⟨v, hv⟩
  have hcc' : c ≠ c' := fun e => huv (congrArg Subtype.val e)
  have key := hφ (.inr (c, 0)) (.inr (c', 0)) (fun e => hcc' (congrArg Prod.fst (Sum.inr.inj e)))
  rw [third_inr_inr_ne χ hcc'] at key
  obtain ⟨⟨e, a'⟩, ha⟩ := map_inr hχ' hφ c 0
  obtain ⟨⟨e', b'⟩, hb⟩ := map_inr hχ' hφ c' 0
  have hee' : e ≠ e' := by
    intro hee; apply hcc'
    apply fibre_inj hχ' hφ (a := 0) (b := 0)
    rw [ha, hb]; simp [fibreOf, hee]
  rw [ha, hb, third_inr_inr_ne χ' hee'] at key
  have h1 := inducedMap_fibre hχ hφ (vadd c c' hcc') (0 ^^^ 0)
  have h2 := inducedMap_fibre hχ hφ c 0
  have h3 := inducedMap_fibre hχ hφ c' 0
  rw [key] at h1; rw [ha] at h2; rw [hb] at h3
  simp only [fibreOf, vadd] at h1 h2 h3
  rw [← h1, ← h2, ← h3]

/-- The induced linear equivalence. -/
noncomputable def inducedEquiv : V d ≃ₗ[ZMod 2] V d :=
  LinearEquiv.ofBijective
    ((AddMonoidHom.mk' (inducedMap φ) (inducedMap_add hχ hχ' hφ)).toZModLinearMap 2)
    ⟨inducedMap_injective hχ hχ' hφ,
      Finite.injective_iff_surjective.1 (inducedMap_injective hχ hχ' hφ)⟩

theorem inducedEquiv_apply (v : V d) : inducedEquiv hχ hχ' hφ v = inducedMap φ v := rfl

end Induced

/-! ## Colours -/

theorem xor_swap (a u v : Z) : a ^^^ v ^^^ u = a ^^^ (u ^^^ v) := by revert a u v; decide

/-- If `ψ` maps `Z ∖ 0` into itself and the fibre over `c'` into the fibre over `c`, a colour-1
fibre cannot go to a colour-0 fibre. -/
theorem colour_true {σ τ : V d → Bool} {ψ : Point d ≃ Point d} (hψ : Commutes σ τ ψ)
    (hinl : ∀ z, ∃ w, ψ (.inl z) = .inl w) {c' c : Vn d}
    (hfib : ∀ a, ∃ a', ψ (.inr (c', a)) = .inr (c, a')) (hc' : σ c'.1 = true) : τ c.1 = true := by
  by_contra hc
  have hc0 : τ c.1 = false := by simpa using hc
  obtain ⟨w₁, w₂, a, b, e, hw₁, hw₂, hw, h2, h1, hnot⟩ := F1_not_PG
  set W₁ : Zn := ⟨w₁, hw₁⟩
  set W₂ : Zn := ⟨w₂, hw₂⟩
  have hW : W₁ ≠ W₂ := fun h => hw (congrArg Subtype.val h)
  obtain ⟨U₁, hU₁⟩ := hinl W₁
  obtain ⟨U₂, hU₂⟩ := hinl W₂
  have hU : U₁ ≠ U₂ := by
    intro h; apply hW; apply Sum.inl_injective; apply ψ.injective; rw [hU₁, hU₂, h]
  obtain ⟨a₁, ha₁⟩ := hfib a
  -- the path `a → b → e` through the matchings `W₂`, `W₁` in the colour-1 fibre
  have s2 : third σ (.inl W₂) (.inr (c', a)) = .inr (c', b) := by
    rw [third_inl_inr, hc', ← eq_partner (col := true) (z := W₂) h2]
  have s1 : third σ (.inl W₁) (.inr (c', b)) = .inr (c', e) := by
    rw [third_inl_inr, hc', ← eq_partner (col := true) (z := W₁) h1]
  have s12 := third_inl_inl σ hW
  -- their images in the colour-0 fibre
  have t2 := hψ _ _ (Sum.inl_ne_inr (a := W₂) (b := (c', a)))
  rw [s2, hU₂, ha₁, third_inl_inr, hc0, partner_false] at t2
  have t1 := hψ _ _ (Sum.inl_ne_inr (a := W₁) (b := (c', b)))
  rw [s1, hU₁, t2, third_inl_inr, hc0, partner_false] at t1
  have t12 := hψ _ _ (fun h => hW (Sum.inl_injective h) : (Sum.inl W₁ : Point d) ≠ .inl W₂)
  rw [s12, hU₁, hU₂, third_inl_inl τ hU] at t12
  have t3 := hψ _ _ (Sum.inl_ne_inr (a := zxor W₁ W₂ hW) (b := (c', a)))
  rw [t12, ha₁, third_inl_inr σ, third_inl_inr τ, hc0, partner_false] at t3
  -- in the colour-0 fibre the two images coincide
  have heq : ψ (.inr (c', e)) = ψ (.inr (c', partner (σ c'.1) (zxor W₁ W₂ hW) a)) := by
    rw [t1, t3]; simp only [zxor]; rw [xor_swap]
  have := congrArg Prod.snd (Sum.inr.inj (ψ.injective heq))
  simp only at this
  apply hnot
  rw [this, hc']
  exact partner_spec true (zxor W₁ W₂ hW) a

/-! ## Assembly -/

/-- **(⇒), with the map**: every isomorphism `φ : X_χ ≅ X_χ'` (non-constant `χ, χ'`) maps
`Z ∖ 0` to itself and each fibre `{c} × Z` into the fibre over `A c`, for a linear equivalence `A`
with `χ' ∘ A = χ`. -/
theorem induced_linear {χ χ' : V d → Bool} (hχ : NonConstant χ) (hχ' : NonConstant χ')
    (φ : Point d ≃ Point d) (hφB : ∀ B : Finset (Point d), B ∈ X χ ↔ B.image φ ∈ X χ') :
    ∃ A : V d ≃ₗ[ZMod 2] V d, (∀ c : V d, c ≠ 0 → χ' (A c) = χ c) ∧
      (∀ z, ∃ w, φ (.inl z) = .inl w) ∧
      (∀ (c : Vn d) (a : Z), ∃ a', φ (.inr (c, a)) = .inr (⟨A c.1, A.map_ne_zero_iff.2 c.2⟩, a')) := by
  rw [X_eq_blocksOf, X_eq_blocksOf] at hφB
  have hφ : Commutes χ χ' φ := commute_of_iso (isSQ_third χ) (isSQ_third χ') φ hφB
  set A := inducedEquiv hχ hχ' hφ
  -- fibre over `c` goes to the fibre over `A c`
  have hfib : ∀ (c : Vn d) (a : Z), ∃ a', φ (.inr (c, a)) = .inr (⟨A c.1, A.map_ne_zero_iff.2 c.2⟩, a') := by
    intro c a
    obtain ⟨⟨e, a'⟩, ha⟩ := map_inr hχ' hφ c a
    refine ⟨a', ?_⟩
    rw [ha]
    have := inducedMap_fibre hχ hφ c a
    rw [ha] at this
    congr 2
    exact Subtype.ext this
  -- and back
  have hfib' : ∀ (c : Vn d) (a : Z), ∃ a',
      φ.symm (.inr (⟨A c.1, A.map_ne_zero_iff.2 c.2⟩, a)) = .inr (c, a') := by
    intro c a
    obtain ⟨⟨e, a'⟩, ha⟩ := map_inr hχ hφ.symm ⟨A c.1, A.map_ne_zero_iff.2 c.2⟩ a
    refine ⟨a', ?_⟩
    rw [ha]
    obtain ⟨a'', ha''⟩ := hfib e a'
    have hφe : φ (.inr (e, a')) = .inr (⟨A c.1, A.map_ne_zero_iff.2 c.2⟩, a) := by
      rw [← ha, Equiv.apply_symm_apply]
    rw [hφe] at ha''
    have hv := congrArg Subtype.val (congrArg Prod.fst (Sum.inr.inj ha''))
    simp only at hv
    have : e = c := Subtype.ext (A.injective hv.symm)
    rw [this]
  refine ⟨A, fun c hc => ?_, map_inl hχ hφ, hfib⟩
  apply Bool.eq_iff_iff.2
  constructor
  · intro h
    exact colour_true hφ.symm (map_inl hχ' hφ.symm) (c := ⟨c, hc⟩) (hfib' ⟨c, hc⟩) h
  · intro h
    exact colour_true hφ (map_inl hχ hφ) (c' := ⟨c, hc⟩) (hfib ⟨c, hc⟩) h

/-- **(⇒)** -/
theorem linearlyEquivalent_of_isomorphic {χ χ' : V d → Bool} (hχ : NonConstant χ)
    (hχ' : NonConstant χ') (h : Isomorphic (X χ) (X χ')) : LinearlyEquivalent χ χ' := by
  obtain ⟨φ, hφB⟩ := h
  obtain ⟨A, hA, -⟩ := induced_linear hχ hχ' φ hφB
  exact ⟨A, hA⟩

end STS
