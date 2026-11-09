import STS.Third

/-!
# `𝔽₂`-characters of `X_χ`

A character is `f : P → 𝔽₂` with `f x + f y + f w = 0` on every block `{x, y, w}`.
For non-constant `χ`, every character of `X_χ` vanishes on `Z ∖ 0` and is constant on each fibre
`{c} × Z` (memo §6, proof of (⇒)); the coordinate functions of the fibre index are characters.
-/

namespace STS

variable {d : ℕ}

/-- Characters of a Steiner quasigroup. -/
def IsChar {P : Type*} (t : P → P → P) (f : P → ZMod 2) : Prop :=
  ∀ x y, x ≠ y → f x + f y + f (t x y) = 0

/-- The fibre index of a point (`0` on `Z ∖ 0`). -/
def fibreOf : Point d → V d
  | .inl _ => 0
  | .inr (c, _) => c.1

theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by revert x; decide

theorem isChar_coord (χ : V d → Bool) (i : Fin d) : IsChar (third χ) (fun p => fibreOf p i) := by
  rintro (z | ⟨c, a⟩) (w | ⟨c', b⟩) hxy
  · have h : z ≠ w := fun e => hxy (e ▸ rfl)
    rw [third_inl_inl χ h]; rfl
  · rw [third_inl_inr]; simp only [fibreOf, Pi.zero_apply, zero_add, zmod2_add_self]
  · rw [third_inr_inl]; simp only [fibreOf, Pi.zero_apply, add_zero, zmod2_add_self]
  · by_cases h : c = c'
    · subst h
      have hab : a ≠ b := fun e => hxy (e ▸ rfl)
      rw [third_inr_inr_same χ c hab]
      simp only [fibreOf, Pi.zero_apply, add_zero, zmod2_add_self]
    · rw [third_inr_inr_ne χ h]
      simp only [fibreOf, vadd, Pi.add_apply]
      generalize c.1 i = p; generalize c'.1 i = q; revert p q; decide

theorem not_inFactor_zero (a b : Z) : ¬ InFactor true 0 a b := by revert a b; decide

/-- **Characters of `X_χ`** for non-constant `χ`. -/
theorem char_classify {χ : V d → Bool} (hχ : NonConstant χ) {f : Point d → ZMod 2}
    (hf : IsChar (third χ) f) :
    (∀ z, f (.inl z) = 0) ∧ ∀ (c : Vn d) (a b : Z), f (.inr (c, a)) = f (.inr (c, b)) := by
  -- a fibre of each colour
  obtain ⟨c0, c1, h0, h1⟩ : ∃ c0 c1 : Vn d, χ c0.1 = false ∧ χ c1.1 = true := by
    obtain ⟨u, v, hu, hv, huv⟩ := hχ
    cases hu' : χ u <;> cases hv' : χ v <;> rw [hu', hv'] at huv
    · exact absurd rfl huv
    · exact ⟨⟨u, hu⟩, ⟨v, hv⟩, hu', hv'⟩
    · exact ⟨⟨v, hv⟩, ⟨u, hu⟩, hv', hu'⟩
    · exact absurd rfl huv
  set g : Vn d → Z → ZMod 2 := fun c a => f (.inr (c, a)) with hg
  -- lines of PG(V)
  have line : ∀ (c c' : Vn d) (h : c ≠ c') (a b : Z),
      g c a + g c' b + g (vadd c c' h) (a ^^^ b) = 0 := by
    intro c c' h a b
    have := hf (.inr (c, a)) (.inr (c', b)) (fun e => h (congrArg Prod.fst (Sum.inr.inj e)))
    rwa [third_inr_inr_ne χ h] at this
  -- the linear part `g c a + g c 0` does not depend on the fibre
  have step : ∀ (c c' : Vn d) (h : c ≠ c') (a : Z),
      g c a + g c 0 = g (vadd c c' h) a + g (vadd c c' h) 0 := by
    intro c c' h a
    have e1 := line c c' h a 0
    have e2 := line c c' h 0 0
    rw [xor_zero'] at e1 e2
    revert e1 e2
    generalize g c a = p; generalize g c' 0 = q; generalize g (vadd c c' h) a = r
    generalize g c 0 = s; generalize g (vadd c c' h) 0 = u
    revert p q r s u; decide
  have indep : ∀ (c c' : Vn d) (a : Z), g c a + g c 0 = g c' a + g c' 0 := by
    intro c c' a
    by_cases h : c = c'
    · rw [h]
    · rw [step c c' h a, step c' c (Ne.symm h) a]
      have : vadd c' c (Ne.symm h) = vadd c c' h := Subtype.ext (add_comm _ _)
      rw [this]
  set μ : Z → ZMod 2 := fun a => g c0 a + g c0 0 with hμdef
  have hμ : ∀ (c : Vn d) (a : Z), g c a + g c 0 = μ a := fun c a => indep c c0 a
  -- `μ` is additive
  have hc01 : c0 ≠ c1 := by rintro rfl; rw [h0] at h1; exact absurd h1 (by decide)
  have add : ∀ a b, μ (a ^^^ b) = μ a + μ b := by
    intro a b
    have e1 := line c0 c1 hc01 a b
    have e2 := line c0 c1 hc01 0 0
    rw [xor_zero'] at e2
    have e3 := hμ c1 b
    have e4 := hμ (vadd c0 c1 hc01) (a ^^^ b)
    show μ (a ^^^ b) = g c0 a + g c0 0 + μ b
    revert e1 e2 e3 e4
    generalize g c0 a = p1; generalize g c0 0 = p0; generalize g c1 b = q1
    generalize g c1 0 = q0; generalize g (vadd c0 c1 hc01) (a ^^^ b) = r1
    generalize g (vadd c0 c1 hc01) 0 = r0; generalize μ (a ^^^ b) = m; generalize μ b = mb
    revert p1 p0 q1 q0 r1 r0 m mb; decide
  -- a colour-0 fibre: `f` on `Z ∖ 0` equals `μ`
  have hl : ∀ z : Zn, f (.inl z) = μ z.1 := by
    intro z
    have := hf (.inl z) (.inr (c0, 0)) Sum.inl_ne_inr
    rw [third_inl_inr, h0, partner_false, zero_xor'] at this
    change f (.inl z) + g c0 0 + g c0 z.1 = 0 at this
    show f (.inl z) = g c0 z.1 + g c0 0
    revert this
    generalize f (.inl z) = p; generalize g c0 z.1 = q; generalize g c0 0 = r
    change p + r + q = 0 → p = q + r
    revert p q r; decide
  -- a colour-1 fibre and property (b): `μ = 0`
  have hμ0 : ∀ a, μ a = 0 := by
    apply F1_span μ add
    intro z a b hab
    by_cases hz : z = 0
    · subst hz; exact absurd hab (not_inFactor_zero a b)
    have := hf (.inl ⟨z, hz⟩) (.inr (c1, a)) Sum.inl_ne_inr
    rw [third_inl_inr, h1, ← eq_partner (col := true) (z := ⟨z, hz⟩) hab, hl] at this
    change μ z + g c1 a + g c1 b = 0 at this
    have ea := hμ c1 a
    have eb := hμ c1 b
    revert this ea eb
    generalize μ z = m; generalize g c1 a = p; generalize g c1 b = q; generalize g c1 0 = r
    generalize μ a = ma; generalize μ b = mb
    change m + p + q = 0 → p + r = ma → q + r = mb → m + ma + mb = 0
    revert m p q r ma mb; decide
  refine ⟨fun z => (hl z).trans (hμ0 z.1), fun c a b => ?_⟩
  have ea := (hμ c a).trans (hμ0 a)
  have eb := (hμ c b).trans (hμ0 b)
  change g c a = g c b
  revert ea eb
  generalize g c a = p; generalize g c b = q; generalize g c 0 = r
  revert p q r; decide

end STS
