import DegreeD.M.PhaseTree
import DegreeD.M.Cited
import DegreeD.RStarColumns

/-!
# The dispatcher counts for `Γ̂_d` groups

A dispatcher vertex has at most `Row'.multL` cosets, when the group of the state lies in `Γ̂_d`.
This is the analysis of `(M′)` (`docs/verify-theorem-R.md` §4.3, `docs/redteam-theorem-R.md` §1.3):

* enumeration of a non-structural quotient: GNS 3.13 (`GNSPrimitive`) bounds `|ρ(G)|`, by its
  first option, or by its second option with `m ≤ q₀` (a structural quotient with `m > q₀` is
  excluded by the guard), with the BCP bound (`BCP`) on the top group;
* product refinement: the number of cosets is the order of the top group `K ≤ S_r`, which is in
  `Γ̂_d`, so BCP gives `|K| ≤ d̃^{r-1}`.
-/

namespace GI.DegreeD.M

open Equiv Equiv.Perm GI.Algorithm GI.Paper
open scoped Pointwise

variable {Ω C : Type}

section Numeric

/-- `m ≤ binom(m, k)` for `1 ≤ k`, `2k ≤ m`. -/
theorem le_choose_of {m k : ℕ} (h1 : 1 ≤ k) (h2 : 2 * k ≤ m) : m ≤ m.choose k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk : k = 0
    · subst hk; simp
    have hk1 : 1 ≤ k := by omega
    have ih' := ih hk1 (by omega)
    have h := Nat.choose_succ_right_eq m k
    have hle : k + 1 ≤ m - k := by omega
    have hpos : 0 < k + 1 := by omega
    have : m.choose k * (k + 1) ≤ m.choose (k + 1) * (k + 1) := by
      rw [h]
      exact Nat.mul_le_mul_left _ hle
    have hmono := Nat.le_of_mul_le_mul_right this hpos
    omega

/-- `2^s ≤ s^4` for `2 ≤ s ≤ 16`. -/
theorem two_pow_le_pow_four {s : ℕ} (h2 : 2 ≤ s) (h16 : s ≤ 16) : 2 ^ s ≤ s ^ 4 := by
  interval_cases s <;> norm_num

/-- `s ≥ 17` when `s ≥ 2` and `4 log₂ s < s`. -/
theorem seventeen_le {s : ℕ} (h2 : 2 ≤ s) (h : 4 * Real.logb 2 s < s) : 17 ≤ s := by
  by_contra hlt
  have h16 : s ≤ 16 := by omega
  have hs0 : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hpow : (2 : ℝ) ^ (s : ℕ) ≤ (s : ℝ) ^ (4 : ℕ) := by
    exact_mod_cast two_pow_le_pow_four h2 h16
  have hle : (s : ℝ) ≤ Real.logb 2 ((s : ℝ) ^ (4 : ℕ)) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
    rw [Real.rpow_natCast]
    exact hpow
  rw [Real.logb_pow] at hle
  simp only [Nat.cast_ofNat] at hle
  linarith

end Numeric

/-! ### The order of a product action -/

/-- `|G| ≤ |K| (m!)^r` for a group in a product action, where `K` is the image in `S_r`
(`coordHom`). -/
theorem Product.card_le_of_top {n m k r : ℕ} (e : Fin n ≃ (Fin r → Product.KSet m k))
    (G : Subgroup (Perm (Fin n))) (hG : ∀ g ∈ G, ∃ σ h, Product.IsProd e g σ h)
    (hb : 2 ≤ m.choose k) :
    Nat.card G ≤ Nat.card (Product.coordHom e G hG hb).range * m.factorial ^ r := by
  classical
  have hmul := Subgroup.card_mul_index (Product.coordHom e G hG hb).ker
  rw [Subgroup.index_ker] at hmul
  rw [← hmul, mul_comm]
  apply Nat.mul_le_mul_left
  -- the kernel maps injectively to `(Fin r → Sym(m))`
  have hker : ∀ g : (Product.coordHom e G hG hb).ker, ∃ h, Product.IsProd e g.1.1 1 h :=
    fun g => (Product.coordHom_eq_one_iff e G hG hb g.1).1 g.2
  let F : (Product.coordHom e G hG hb).ker → (Fin r → Perm (Fin m)) := fun g => (hker g).choose
  have hF : Function.Injective F := by
    intro g₁ g₂ hg
    have h1 := (hker g₁).choose_spec
    have h2 := (hker g₂).choose_spec
    apply Subtype.ext
    apply Subtype.ext
    ext x
    have e1 := h1 x
    have e2 := h2 x
    have hFe : (hker g₁).choose = (hker g₂).choose := hg
    rw [hFe] at e1
    exact congrArg Fin.val (e.injective (e1.trans e2.symm))
  have hcard := Nat.card_le_card_of_injective F hF
  have hfin : Nat.card (Fin r → Perm (Fin m)) = m.factorial ^ r := by
    rw [Nat.card_fun, Nat.card_fin, Nat.card_perm, Nat.card_fin]
  rwa [hfin] at hcard

section Counts

variable {P : Params} {S : State Ω C}

/-- `S.G ∈ Γ̂_d` passes to `ρ(G)` for a primitive quotient. -/
theorem PrimitiveQuotient.gammaHat_range [Finite Ω] {d d' : ℕ} (hS : GammaHat d S.G)
    (hd : d ≤ d') (Q : PrimitiveQuotient S) : GammaHat d' Q.ρ.range :=
  (GammaHat.range Q.ρ hS).mono hd

/-- **The enumeration count of `(M′)` for a `Γ̂_d` group.** -/
theorem enumeration_card_le [Finite Ω] {cc : ChargingConstants} {c₁ c₂ : ℝ}
    (hBCP : BCP) (hGNS : GNSPrimitive c₁ c₂) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hcc : c₁ / Real.log 2 + c₂ / Real.log 48 ≤ cc.a + cc.aStar / Real.log 2)
    (hq : (Real.log P.q₀.factorial / Real.log 48 + 1) / Real.log 17 ≤
      cc.a + cc.aStar / Real.log 2)
    {d : ℕ} (hS : GammaHat d S.G) (Q : PrimitiveQuotient S) (hns : ¬ Structural P Q) :
    ((Nat.card Q.ρ.range : ℕ) : ℝ) ≤ Row'.multL cc (lam d) (.enumeration Q.d) := by
  classical
  set D := max d 6 with hD
  have hD6 : 6 ≤ D := le_max_right _ _
  have hG : GammaHat D Q.ρ.range := PrimitiveQuotient.gammaHat_range hS (le_max_left _ _) Q
  rcases hGNS D Q.d hD6 Q.two_le Q.ρ.range Q.primitive hG with h1 | ⟨m, k, r, e, hform, hmD, h2km, hlog⟩
  · -- option 1 of GNS 3.13
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hc : c₁ / Real.log 2 + c₂ / Real.log 48 ≤ cc.a + cc.aStar / Real.log 2 := hcc
    have hexp : c₁ * Real.logb 2 D + c₂ = c₁ / Real.log 2 * Real.log (max d 6 : ℕ) + c₂ := by
      rw [Real.logb]
      push_cast [hD]
      field_simp
    calc ((Nat.card Q.ρ.range : ℕ) : ℝ) ≤ (Q.d : ℝ) ^ (c₁ * Real.logb 2 D + c₂) := h1
      _ = (Q.d : ℝ) ^ (c₁ / Real.log 2 * Real.log (max d 6 : ℕ) + c₂) := by rw [hexp]
      _ ≤ _ := gns_count_le_multL cc Q.two_le (div_nonneg hc₁ hl2.le) hc₂ hc
  · -- option 2: the guard excludes `m > q₀`
    have hPS : Q.ProductStructure m k r e := hform
    have hm : m ≤ P.q₀ := by
      by_contra hgt
      exact hns ⟨m, k, r, e, hPS, h2km, by omega, hlog⟩
    have hdk := Q.card_kset_pow e
    have hb : 2 ≤ m.choose k := Q.two_le_choose e
    have hr : 1 ≤ r := by
      by_contra h0
      have h0' : r = 0 := by omega
      rw [h0', pow_zero] at hdk
      have := Q.two_le
      omega
    have hk1 : 1 ≤ k := by
      by_contra h0
      have : k = 0 := by omega
      subst this
      simp at hb
    have hs17 : 17 ≤ m.choose k := by
      have hmle : m ≤ m.choose k := le_choose_of hk1 h2km
      apply seventeen_le hb
      have : (m : ℝ) ≤ m.choose k := by exact_mod_cast hmle
      linarith
    have hd' : (17 : ℝ) ^ r ≤ Q.d := by
      rw [hdk]
      exact_mod_cast Nat.pow_le_pow_left hs17 r
    -- the top group
    let f := Product.coordHom e Q.ρ.range hPS.1 hb
    have hKG : GammaHat D f.range := GammaHat.range f hG
    have hK : Nat.card f.range ≤ D ^ (r - 1) := hBCP D hD6 r f.range hKG
    have hcard : Nat.card Q.ρ.range ≤ D ^ (r - 1) * P.q₀.factorial ^ r := by
      calc Nat.card Q.ρ.range ≤ Nat.card f.range * m.factorial ^ r :=
            Product.card_le_of_top e Q.ρ.range hPS.1 hb
        _ ≤ D ^ (r - 1) * P.q₀.factorial ^ r :=
            Nat.mul_le_mul hK (Nat.pow_le_pow_left (Nat.factorial_le hm) r)
    have hQ1 : (1 : ℝ) ≤ (P.q₀.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    have hbound := small_cameron_count_le_multL (C := cc) (d := d) (d' := Q.d) (k := r)
      (Q := (P.q₀.factorial : ℝ)) hQ1 hr hd' hq
    have hstep : ((Nat.card Q.ρ.range : ℕ) : ℝ) ≤ (P.q₀.factorial : ℝ) ^ r * (((max d 6 : ℕ) : ℝ) + 1) ^ (r - 1) := by
      have h1 : ((Nat.card Q.ρ.range : ℕ) : ℝ) ≤ (D : ℝ) ^ (r - 1) * (P.q₀.factorial : ℝ) ^ r := by
        exact_mod_cast hcard
      have h2 : (D : ℝ) ^ (r - 1) ≤ ((max d 6 : ℕ) + 1 : ℝ) ^ (r - 1) := by
        apply pow_le_pow_left₀ (by positivity)
        have : (D : ℝ) = (max d 6 : ℕ) := by rw [hD]
        rw [this]; linarith
      calc ((Nat.card Q.ρ.range : ℕ) : ℝ) ≤ (D : ℝ) ^ (r - 1) * (P.q₀.factorial : ℝ) ^ r := h1
        _ ≤ ((max d 6 : ℕ) + 1 : ℝ) ^ (r - 1) * (P.q₀.factorial : ℝ) ^ r := by gcongr
        _ = _ := by ring
    exact hstep.trans hbound

/-- **The product count of `(M′)` for a `Γ̂_d` group**: at most `2^r (d̃+1)^{r-1}` cosets. -/
theorem product_index_le [Finite Ω] {cc : ChargingConstants} (hBCP : BCP) {d : ℕ}
    (hS : GammaHat d S.G) (Q : PrimitiveQuotient S) (c : Q.ProductChoice) :
    (((Q.productRed P c).K.subgroupOf S.G).index : ℝ) ≤ Row'.multL cc (lam d) (.product c.r) := by
  set D := max d 6 with hD
  have hD6 : 6 ≤ D := le_max_right _ _
  have hSD : GammaHat D S.G := hS.mono (le_max_left _ _)
  have hb : 2 ≤ c.m.choose c.k := Q.two_le_choose c.e
  let f : S.G →* Perm (Fin c.r) :=
    (Product.coordHom c.e Q.ρ.range c.hS.1 hb).comp Q.ρ.rangeRestrict
  have hidx : ((Q.productRed P c).K.subgroupOf S.G) = f.ker := by
    ext g
    simp [PrimitiveQuotient.productRed, PrimitiveQuotient.product,
      CitedInstances.Reduction.ofProduct, PrimitiveQuotient.coordinateGroup, Subgroup.mem_subgroupOf,
      f]
  have hcard : ((Q.productRed P c).K.subgroupOf S.G).index = Nat.card f.range := by
    rw [hidx, Subgroup.index_ker]
  have hK : Nat.card f.range ≤ D ^ (c.r - 1) := hBCP D hD6 c.r f.range (GammaHat.range f hSD)
  have h2 : (2 : ℝ) ≤ (D : ℝ) := by
    have : (6 : ℝ) ≤ D := by exact_mod_cast hD6
    linarith
  have hbound := product_count_le_multL (C := cc) (d := d) (k := c.r) c.hr
  have hstep : ((Nat.card f.range : ℕ) : ℝ) ≤ (2 : ℝ) ^ c.r * (((max d 6 : ℕ) : ℝ) + 1) ^ (c.r - 1) := by
    have h3 : ((Nat.card f.range : ℕ) : ℝ) ≤ (D : ℝ) ^ (c.r - 1) := by exact_mod_cast hK
    have h4 : (D : ℝ) ^ (c.r - 1) ≤ (((max d 6 : ℕ) : ℝ) + 1) ^ (c.r - 1) := by
      apply pow_le_pow_left₀ (by positivity)
      have : (D : ℝ) = (max d 6 : ℕ) := by rw [hD]
      rw [this]; linarith
    calc ((Nat.card f.range : ℕ) : ℝ) ≤ (((max d 6 : ℕ) : ℝ) + 1) ^ (c.r - 1) := h3.trans h4
      _ ≤ 2 ^ c.r * (((max d 6 : ℕ) : ℝ) + 1) ^ (c.r - 1) := by
          have : (0 : ℝ) ≤ (((max d 6 : ℕ) : ℝ) + 1) ^ (c.r - 1) := by positivity
          have h1le : (1 : ℝ) ≤ 2 ^ c.r := one_le_pow₀ (by norm_num)
          nlinarith
  rw [hcard]
  exact hstep.trans hbound

/-- **Every dispatcher vertex of `(M′)` on a `Γ̂_d` state has at most `multL` cosets.** -/
theorem DispatchStep.n_le_multL {cc : ChargingConstants} {c₁ c₂ : ℝ}
    (hBCP : BCP) (hGNS : GNSPrimitive c₁ c₂) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hcc : c₁ / Real.log 2 + c₂ / Real.log 48 ≤ cc.a + cc.aStar / Real.log 2)
    (hq : (Real.log P.q₀.factorial / Real.log 48 + 1) / Real.log 17 ≤
      cc.a + cc.aStar / Real.log 2)
    {d : ℕ} (hS : GammaHat d S.G) (I : DispatchStep P S) :
    (I.n : ℝ) ≤ Row'.multL cc (lam d) (kindRow I.kind) := by
  cases I with
  | enumeration Q fin htr hns reps hkeep =>
    haveI := fin
    have h := enumeration_card_le (P := P) hBCP hGNS hc₁ hc₂ hcc hq hS Q hns.1
    have hidx : (DispatchStep.enumeration Q fin htr hns reps hkeep).n = Nat.card Q.ρ.range := by
      show (Q.kernel.subgroupOf S.G).index = _
      rw [Q.kernel_subgroupOf, Subgroup.index_ker]
    rw [hidx]
    exact h
  | product Q fin c reps hkeep =>
    haveI := fin
    exact product_index_le (P := P) hBCP hS Q c

end Counts

end GI.DegreeD.M
