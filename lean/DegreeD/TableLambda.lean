import DegreeD.Induction

/-!
# The potential `Φ_Λ` and the charging table with parameter `Λ`

This file proves the abstract core of Theorem R*: Lemma 7.1 for the potential

  `Φ_Λ(S) = A (Λ x + Λ ρ + Λ σ + Q) + B h`,        `x = log(s+2)`,

for a weight function `Λ : ℕ → ℝ` of the domain size. Two cases matter:

* `Λ s = log(s+2)`, which is HJ's potential `A(x² + ρ x + σ x + Q) + B h` (`ΦL_x_eq`);
* `Λ s = Λ` constant, `Λ = log(8 max(d,6))`, the potential of Theorem R*.

The rows, the child relation `Row.Child` and the side conditions `Row.Valid` are HJ's
(`GI.Paper.Row`), reused verbatim. Only two columns change:

* **Potential decrease** (`Row.dropL`): `Λ` replaces `x` in every row except the cap row
  (`A c_β log q`), so at `Λ = x` it is HJ's `Row.drop` exactly (`dropL_x`);
* **Multiplicity** (`Row.multL`): `N^a` disappears. The multiplicities are `exp(a* Λ)` for the
  affected and unaffected rows, `exp((4(r-1)+a*) Λ)` for product refinement,
  `exp(c_E Λ log d)` for enumeration on a degree-`d` quotient, `q^a` for continuation.

`Row.multL_mul_exp_neg_dropL_le` is the charging inequality, uniform in `N`: there is no `N` in
its statement. The bound `N^a ≤ exp(a* x)` of eq. `main-phase-active` is the only place HJ's proof
needed `x ≥ γ log N` to pay a multiplicity, and `multL` has simply dropped that factor.

The constants are HJ's `ChargingConstants`, unchanged.

## Main results

* `PhaseTree.HypL`: the hypotheses with parameter `Λ`. All fields except `class_mult` are the
  fields of `PhaseTree.Hyp` verbatim (`PhaseCore`), so they hold for HJ's real runs
  (see `HJInstance.lean`).
* `PhaseTree.HypL.cost_le`: Lemma 7.1 with parameter `Λ`.
* `fresh_phase_boundL`: a fresh phase costs at most `K exp(C₁ log(N+2) Λ)`, with `C₁` absolute.
* `recurrenceL`, `abstract_R_star`: the recurrence is solved with a constant independent of `Λ`.
-/

namespace GI.DegreeD

open GI.Paper

/-! ## The potential -/

/-- The potential `Φ_Λ(S) = A (Λ x + Λ ρ + Λ σ + Q) + B h`, with `Λ` evaluated at the domain
size `s`. -/
noncomputable def ΦL (A B : ℝ) (Λ : ℕ → ℝ) (S : PotentialState) : ℝ :=
  A * (Λ S.s * S.x + Λ S.s * S.ρ + Λ S.s * S.σ + S.Q) + B * S.h

/-- HJ's `Λ`: the function `s ↦ log(s+2)`. -/
noncomputable def xFn (s : ℕ) : ℝ := Real.log ((s : ℝ) + 2)

/-- At `Λ = x` the potential is HJ's. -/
theorem ΦL_x_eq (A B : ℝ) (S : PotentialState) : ΦL A B xFn S = S.Φ A B := by
  unfold ΦL PotentialState.Φ xFn PotentialState.x
  ring

/-- Conditions on the weight function: nonnegative, monotone in `s`, and at least
`x₀ = log 8` at the internal sizes `s ≥ 6`. -/
structure WeightFn (Λ : ℕ → ℝ) : Prop where
  nonneg : ∀ s, 0 ≤ Λ s
  mono : ∀ {s t : ℕ}, s ≤ t → Λ s ≤ Λ t
  floor : ∀ {s : ℕ}, 6 ≤ s → xZero ≤ Λ s

theorem xFn_weightFn : WeightFn xFn where
  nonneg s := Real.log_nonneg (by have : (0 : ℝ) ≤ s := Nat.cast_nonneg _; linarith)
  mono {s t} h := Real.log_le_log (by positivity) (by have : (s : ℝ) ≤ t := by exact_mod_cast h
                                                      linarith)
  floor {s} h := Real.log_le_log (by norm_num) (by
    have : (6 : ℝ) ≤ s := by exact_mod_cast h
    linarith)

/-- A constant weight `Λ ≥ log 8` is a weight function. -/
theorem const_weightFn {Λ : ℝ} (h : xZero ≤ Λ) : WeightFn (fun _ => Λ) where
  nonneg _ := (ChargingConstants.xZero_pos.le).trans h
  mono _ := le_rfl
  floor _ := h

theorem ΦL_nonneg {A B : ℝ} {Λ : ℕ → ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hΛ : WeightFn Λ)
    {S : PotentialState} (hρ : 0 ≤ S.ρ) (hσ : 0 ≤ S.σ) (hQ : 0 ≤ S.Q) : 0 ≤ ΦL A B Λ S := by
  unfold ΦL
  have h0 := hΛ.nonneg S.s
  have hx := S.x_nonneg
  have h1 : 0 ≤ Λ S.s * S.x := mul_nonneg h0 hx
  have h2 : 0 ≤ Λ S.s * S.ρ := mul_nonneg h0 hρ
  have h3 : 0 ≤ Λ S.s * S.σ := mul_nonneg h0 hσ
  exact add_nonneg (mul_nonneg hA (by linarith)) (mul_nonneg hB (Nat.cast_nonneg _))

/-- The common estimate behind every row. -/
theorem ΦL_le_of {A B : ℝ} {Λ : ℕ → ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hΛ : WeightFn Λ)
    {S T : PotentialState} {y ρ' σ' Q' h' : ℝ} (hTρ : 0 ≤ T.ρ) (hTσ : 0 ≤ T.σ)
    (hTs : T.s ≤ S.s) (hy : T.x ≤ y) (hρ : T.ρ ≤ ρ') (hσ : T.σ ≤ σ') (hQ : T.Q ≤ Q')
    (hh : (T.h : ℝ) ≤ h') :
    ΦL A B Λ T ≤ A * (Λ S.s * y + Λ S.s * ρ' + Λ S.s * σ' + Q') + B * h' := by
  have hΛm : Λ T.s ≤ Λ S.s := hΛ.mono hTs
  have hΛ0 := hΛ.nonneg T.s
  have hy0 : 0 ≤ y := T.x_nonneg.trans hy
  have h1 : Λ T.s * T.x ≤ Λ S.s * y := mul_le_mul hΛm hy T.x_nonneg (hΛ.nonneg S.s)
  have h2 : Λ T.s * T.ρ ≤ Λ S.s * ρ' := mul_le_mul hΛm hρ hTρ (hΛ.nonneg S.s)
  have h3 : Λ T.s * T.σ ≤ Λ S.s * σ' := mul_le_mul hΛm hσ hTσ (hΛ.nonneg S.s)
  have hsum : Λ T.s * T.x + Λ T.s * T.ρ + Λ T.s * T.σ + T.Q ≤
      Λ S.s * y + Λ S.s * ρ' + Λ S.s * σ' + Q' := by linarith
  unfold ΦL
  have := mul_le_mul_of_nonneg_left hsum hA
  have := mul_le_mul_of_nonneg_left hh hB
  linarith

/-! ## The domain payment, in the form the `Λ` table uses -/

/-- `x − log(s/d + 2) ≥ (1/3) log d`, the first half of eq. `main-enumeration-payment`. -/
theorem enumeration_payment_log {s d : ℝ} (hd : 2 ≤ d) (hsd : d ≤ s) :
    (1 / 3) * Real.log d ≤ Real.log (s + 2) - Real.log (s / d + 2) := by
  have hd0 : 0 < d := by linarith
  have hs0 : 0 < s := by linarith
  have hy : 0 < s / d + 2 := by positivity
  obtain ⟨hratio, hamgm, -⟩ := eq_main_enumeration_payment hd hsd
  have h1 : Real.log (d ^ (1 / 3 : ℝ)) ≤ Real.log ((s + 2) / (s / d + 2)) :=
    Real.log_le_log (by positivity) (hamgm.trans hratio)
  rw [Real.log_rpow hd0, Real.log_div (by positivity) hy.ne'] at h1
  linarith

/-! ## The columns of the `Λ` table -/

namespace Row'

open Row

variable (C : ChargingConstants)

/-- The column "Potential decrease" with `Λ` in place of `x`, at a parent state `S`. At
`Λ = x` this is `GI.Paper.Row.drop` (`dropL_x`). -/
noncomputable def dropL (Λ : ℝ) : Row → ℝ
  | .affected => C.A * cTheta C.θ * Λ - 2 * C.B
  | .unaffected => C.A * C.κ * Λ - 2 * C.B
  | .product r => C.A * ((r : ℝ) - 1) * Λ - 2 * C.B
  | .enumeration d => C.A / 3 * Λ * Real.log d - 2 * C.B
  | .continuation q => C.A * cBeta C.β * Real.log q - 2 * C.B
  | .rowEvent => C.B

theorem dropL_x (S : PotentialState) (R : Row) : dropL C S.x R = Row.drop C S R := by
  cases R <;> rfl

/-- The column "Multiplicity bound" with the `N`-dependence removed. -/
noncomputable def multL (Λ : ℝ) : Row → ℝ
  | .affected => Real.exp (C.aStar * Λ)
  | .unaffected => Real.exp (C.aStar * Λ)
  | .product r => Real.exp ((4 * ((r : ℝ) - 1) + C.aStar) * Λ)
  | .enumeration d => Real.exp ((C.a + C.aStar / Real.log 2) * Λ * Real.log d)
  | .continuation q => (q : ℝ) ^ C.a
  | .rowEvent => C.b₀

/-- **Row by row: the child inequality with parameter `Λ`.** `Row.Child` and `Row.Valid` are
HJ's, verbatim. -/
theorem child_ΦL_le {Λ : ℕ → ℝ} (hΛ : WeightFn Λ) {S T : PotentialState} {R : Row}
    (hS6 : 6 ≤ (S.s : ℝ)) (hv : R.Valid C S) (hc : R.Child C S T) (hTρ : 0 ≤ T.ρ) (hTσ : 0 ≤ T.σ) :
    ΦL C.A C.B Λ T ≤ ΦL C.A C.B Λ S - dropL C (Λ S.s) R := by
  have hA := C.A_nonneg
  have hB := C.B_nonneg
  have hL := hΛ.nonneg S.s
  have hxS := S.x_nonneg
  cases R with
  | affected =>
    obtain ⟨hs, hρ, hσ, hQ, hh⟩ := hc
    have hθ := C.half_lt_θ
    have hθ1 := C.θ_lt_one
    have hTs : T.s ≤ S.s := by
      have h1 : (T.s : ℝ) ≤ S.s := hs.trans (by nlinarith)
      exact_mod_cast h1
    have hy : T.x ≤ Real.log (C.θ * S.s + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    have hpay := (eq_main_domain_payment hθ hθ1 hS6).1
    have hh' : (T.h : ℝ) ≤ S.h + 2 := by exact_mod_cast hh
    have h1 := ΦL_le_of hA hB hΛ hTρ hTσ hTs hy hρ hσ hQ hh'
    have h2 : C.A * Λ S.s * cTheta C.θ ≤ C.A * Λ S.s * (S.x - Real.log (C.θ * S.s + 2)) :=
      mul_le_mul_of_nonneg_left hpay (mul_nonneg hA hL)
    simp only [dropL, ΦL] at *
    nlinarith
  | unaffected =>
    obtain ⟨hs, hρ, hσ, hQ, hh⟩ := hc
    have hh' : (T.h : ℝ) ≤ S.h + 2 := by exact_mod_cast hh
    have hTx : T.x ≤ S.x := PotentialState.x_mono (by exact_mod_cast hs)
    have h1 := ΦL_le_of hA hB hΛ hTρ hTσ hs hTx hρ hσ hQ hh'
    simp only [dropL, ΦL] at *
    nlinarith
  | product r =>
    obtain ⟨hs, hρ, hσ, hQ, hh⟩ := hc
    have hh' : (T.h : ℝ) ≤ S.h + 2 := by exact_mod_cast hh
    have hTx : T.x ≤ S.x := PotentialState.x_mono (by exact_mod_cast hs)
    have h1 := ΦL_le_of hA hB hΛ hTρ hTσ hs hTx hρ hσ hQ hh'
    simp only [dropL, ΦL] at *
    nlinarith
  | enumeration d =>
    obtain ⟨hs, hρ, hσ, hQ, hh⟩ := hc
    obtain ⟨hd2, hds⟩ := hv
    have hd2' : (2 : ℝ) ≤ d := by exact_mod_cast hd2
    have hds' : (d : ℝ) ≤ S.s := by exact_mod_cast hds
    have hs' : (d : ℝ) * T.s ≤ S.s := by exact_mod_cast hs
    have hTs' : (T.s : ℝ) ≤ S.s / d := by rw [le_div_iff₀ (by linarith)]; linarith
    have hTs : T.s ≤ S.s := by
      have h1 : (T.s : ℝ) ≤ S.s := by
        have : (0 : ℝ) ≤ T.s := Nat.cast_nonneg _
        nlinarith
      exact_mod_cast h1
    have hy : T.x ≤ Real.log (S.s / d + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    have hpay := enumeration_payment_log hd2' hds'
    have hh' : (T.h : ℝ) ≤ S.h + 2 := by exact_mod_cast hh
    have h1 := ΦL_le_of hA hB hΛ hTρ hTσ hTs hy hρ hσ hQ hh'
    have h2 : C.A * Λ S.s * ((1 / 3) * Real.log d) ≤
        C.A * Λ S.s * (S.x - Real.log (S.s / d + 2)) :=
      mul_le_mul_of_nonneg_left hpay (mul_nonneg hA hL)
    simp only [dropL, ΦL] at *
    nlinarith
  | continuation q =>
    obtain ⟨hs, hρ, hσ, hQ, hh⟩ := hc
    have hh' : (T.h : ℝ) ≤ S.h + 2 := by exact_mod_cast hh
    have hTx : T.x ≤ S.x := PotentialState.x_mono (by exact_mod_cast hs)
    have h1 := ΦL_le_of hA hB hΛ hTρ hTσ hs hTx hρ hσ hQ hh'
    simp only [dropL, ΦL] at *
    nlinarith
  | rowEvent =>
    obtain ⟨hs, hρ, hσ, hQ, hh⟩ := hc
    have hh' : (T.h : ℝ) ≤ S.h - 1 := by
      have : (T.h : ℝ) + 1 ≤ S.h := by exact_mod_cast hh
      linarith
    have hTx : T.x ≤ S.x := PotentialState.x_mono (by exact_mod_cast hs)
    have h1 := ΦL_le_of hA hB hΛ hTρ hTσ hs hTx hρ hσ hQ hh'
    simp only [dropL, ΦL] at *
    nlinarith

variable {C}

/-- Enumeration margin: the `Λ`-analogue of `margin_enum`. Unlike HJ's, it does not need
`log d ≤ x`, because the multiplicity column is `exp(c_E Λ log d)`, not `exp(a (log d)²)`. -/
theorem margin_enumL {Λ ℓ : ℝ} (hΛ : xZero ≤ Λ) (hℓ2 : Real.log 2 ≤ ℓ) :
    (C.a + C.aStar / Real.log 2) * Λ * ℓ + Real.log (8 * C.J) ≤ C.A / 3 * Λ * ℓ - 2 * C.B := by
  have hl2 := ChargingConstants.log_two_pos'
  have hx0 := ChargingConstants.xZero_pos
  have hΛ0 : 0 < Λ := hx0.trans_le hΛ
  have hℓ0 : 0 < ℓ := hl2.trans_le hℓ2
  have hΛℓ : xZero * Real.log 2 ≤ Λ * ℓ := mul_le_mul hΛ hℓ2 hl2.le hΛ0.le
  have hH := C.hStar_nonneg
  have h1 : hStar C.B C.J ≤ hStar C.B C.J / (xZero * Real.log 2) * (Λ * ℓ) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (mul_pos hx0 hl2)]
    exact mul_le_mul_of_nonneg_left hΛℓ hH
  have h2 := mul_le_mul_of_nonneg_right C.A_enum (mul_pos hΛ0 hℓ0).le
  unfold hStar at h1 h2
  unfold ChargingConstants.aStar
  nlinarith

/-- **The charging inequality of the `Λ` table**: for every row and every `Λ ≥ log 8`,
`multL · exp(-dropL) ≤ 1/(8J)`. This is the row-by-row content of Theorem R*; the statement has
no `N` in it. -/
theorem multL_mul_exp_neg_dropL_le {Λ : ℝ} (hΛ : xZero ≤ Λ) {S : PotentialState} {R : Row}
    (hv : R.Valid C S) :
    multL C Λ R * Real.exp (-dropL C Λ R) ≤ 1 / (8 * C.J) := by
  have hJ : (0 : ℝ) < 8 * C.J := by
    have : (1 : ℝ) ≤ C.J := by exact_mod_cast C.one_le_J
    linarith
  suffices hM : multL C Λ R ≤ Real.exp (dropL C Λ R - Real.log (8 * C.J)) by
    calc multL C Λ R * Real.exp (-dropL C Λ R)
        ≤ Real.exp (dropL C Λ R - Real.log (8 * C.J)) * Real.exp (-dropL C Λ R) :=
          mul_le_mul_of_nonneg_right hM (Real.exp_pos _).le
      _ = 1 / (8 * C.J) := by
          rw [← Real.exp_add, show dropL C Λ R - Real.log (8 * C.J) + -dropL C Λ R =
            -Real.log (8 * C.J) by ring, Real.exp_neg, Real.exp_log hJ, one_div]
  cases R with
  | affected =>
    have := C.margin_domain hΛ
    exact Real.exp_le_exp.mpr (by simp only [dropL]; linarith)
  | unaffected =>
    have := C.margin_symmetry hΛ
    exact Real.exp_le_exp.mpr (by simp only [dropL]; linarith)
  | product r =>
    obtain ⟨hr, -⟩ := hv
    have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
    have := C.margin_product (L := 4 * ((r : ℝ) - 1) * Λ) hΛ hr' le_rfl
    exact Real.exp_le_exp.mpr (by simp only [dropL]; nlinarith)
  | enumeration d =>
    obtain ⟨hd2, -⟩ := hv
    have hd2' : (2 : ℝ) ≤ d := by exact_mod_cast hd2
    have := margin_enumL (C := C) hΛ (Real.log_le_log (by norm_num) hd2')
    exact Real.exp_le_exp.mpr (by simp only [dropL]; linarith)
  | continuation q =>
    have hq : C.q₀ ≤ q := hv
    have hq0 : (0 : ℝ) < q := by linarith [C.one_lt_q₀]
    have hm := C.margin_cap hq
    simp only [multL, dropL]
    rw [Real.rpow_def_of_pos hq0]
    exact Real.exp_le_exp.mpr (by nlinarith)
  | rowEvent =>
    have hm := C.B_ge
    simp only [multL, dropL]
    have hb : (0 : ℝ) < 8 * C.J * C.b₀ := by nlinarith [C.one_le_b₀]
    have hlb : (0 : ℝ) < C.b₀ := by linarith [C.one_le_b₀]
    calc C.b₀ = Real.exp (Real.log (8 * C.J * C.b₀) - Real.log (8 * C.J)) := by
          rw [Real.exp_sub, Real.exp_log hb, Real.exp_log hJ]
          have : (C.J : ℝ) ≠ 0 := by
            have : (1 : ℝ) ≤ C.J := by exact_mod_cast C.one_le_J
            linarith
          field_simp
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

/-- Every row's drop is at least the margin `log(8J)`, used for the orbit `h` reset. -/
theorem dropL_affected_nonneg {Λ : ℝ} (hΛ : xZero ≤ Λ) :
    0 ≤ dropL C Λ .affected := by
  have hm := C.margin_domain hΛ
  have h1 : 0 ≤ C.aStar * Λ := mul_nonneg C.aStar_nonneg (ChargingConstants.xZero_pos.le.trans hΛ)
  have h2 := C.log8J_pos
  simp only [dropL]
  linarith

end Row'

/-! ## The hypotheses with parameter `Λ` -/

/-- The fields of `PhaseTree.Hyp` other than the multiplicity column. They do not mention `x`,
the rows' `drop`, or `Λ`. -/
structure PhaseCore (C : ChargingConstants) (N : ℕ) (K : ℝ) {V : Type*} (T : PhaseTree V) :
    Prop where
  nonneg : ∀ v, 0 ≤ (T.state v).ρ ∧ 0 ≤ (T.state v).σ ∧ 0 ≤ (T.state v).Q
  leaf_small : ∀ v, T.kind v = .leaf → ((T.state v).s : ℝ) ≤ (N : ℝ) ^ C.γ
  leaf_cost : ∀ v, T.kind v = .leaf → T.cost v ≤ K
  internal_large : ∀ v, T.kind v ≠ .leaf → (N : ℝ) ^ C.γ < (T.state v).s
  toll : ∀ v, T.kind v ≠ .leaf →
    T.cost v ≤ (N : ℝ) ^ C.a * K + (((T.kind v).children).map T.cost).sum
  classes_le : ∀ v cls, T.kind v = .charged cls → cls.length ≤ C.J
  class_valid : ∀ v cls, T.kind v = .charged cls → ∀ c ∈ cls, c.row.Valid C (T.state v)
  branch_pos : ∀ v cls, T.kind v = .charged cls → ∀ c ∈ cls, ∀ b ∈ c.branches,
    ∀ u ∈ b, 1 ≤ (T.state u).s
  branch_disjoint : ∀ v cls, T.kind v = .charged cls → ∀ c ∈ cls, ∀ b ∈ c.branches,
    ((b.map fun u => (T.state u).s).sum) ≤ (T.state v).s
  branch_child : ∀ v cls, T.kind v = .charged cls → ∀ c ∈ cls, ∀ b ∈ c.branches,
    ∀ u ∈ b, c.row.Child C (T.state v) (T.state u)
  orbit_pos : ∀ v cs, T.kind v = .orbit cs → ∀ u ∈ cs,
    1 ≤ (T.state u).s ∧ (T.state u).s < (T.state v).s
  orbit_disjoint : ∀ v cs, T.kind v = .orbit cs →
    ((cs.map fun u => (T.state u).s).sum) ≤ (T.state v).s
  orbit_child : ∀ v cs, T.kind v = .orbit cs → ∀ u ∈ cs, OrbitChild (T.state v) (T.state u)

/-- HJ's hypotheses restrict to the common part. -/
theorem _root_.GI.Paper.PhaseTree.Hyp.toCore {C : ChargingConstants} {N : ℕ} {K : ℝ} {V : Type*}
    {T : PhaseTree V} (h : T.Hyp C N K) : PhaseCore C N K T where
  nonneg := h.nonneg
  leaf_small := h.leaf_small
  leaf_cost := h.leaf_cost
  internal_large := h.internal_large
  toll := h.toll
  classes_le := h.classes_le
  class_valid := h.class_valid
  branch_pos := h.branch_pos
  branch_disjoint := h.branch_disjoint
  branch_child := h.branch_child
  orbit_pos := h.orbit_pos
  orbit_disjoint := h.orbit_disjoint
  orbit_child := h.orbit_child

/-- **The hypotheses of Lemma 7.1 with parameter `Λ`.** The common fields (`PhaseCore`), and the
multiplicity column replaced by `multL`, in the family form: the branches of a class are grouped
into `M ≤ multL` families whose children have total size at most the parent's. HJ's form is one
family per branch (`M = length`). There is no `N` in `class_fam`. -/
structure _root_.GI.Paper.PhaseTree.HypL (C : ChargingConstants) (Λ : ℕ → ℝ) (N : ℕ) (K : ℝ) {V : Type*}
    (T : PhaseTree V) : Prop extends PhaseCore C N K T where
  class_fam : ∀ v cls, T.kind v = .charged cls → ∀ c ∈ cls,
    ∃ (M : ℕ) (fam : Fin c.branches.length → Fin M),
      (M : ℝ) ≤ Row'.multL C (Λ (T.state v).s) c.row ∧
      ∀ j : Fin M, ∑ i ∈ Finset.univ.filter (fun i => fam i = j),
        ((c.branches.get i).map fun u => (T.state u).s).sum ≤ (T.state v).s

section HypLemmas

variable {C : ChargingConstants} {Λ : ℕ → ℝ} {N : ℕ} {K : ℝ} {V : Type*} {T : PhaseTree V}

/-- A `HypL` tree satisfies the abstract charging conditions, for the potential `Φ_Λ` and the
drops `Row'.dropL`. -/
theorem _root_.GI.Paper.PhaseTree.HypL.toAbstract (h : T.HypL C Λ N K) (hΛ : WeightFn Λ) (hN6 : 6 ≤ (N : ℝ) ^ C.γ)
    (hN2 : 2 ≤ (N : ℝ) ^ (C.γ * C.D - C.a)) (hK : 0 ≤ K) :
    AbstractCharging C.D C.J K ((N : ℝ) ^ C.a) T (fun v => ΦL C.A C.B Λ (T.state v))
      (fun v c => Row'.dropL C (Λ (T.state v).s) c.row) := by
  have six : ∀ v, T.kind v ≠ .leaf → (6 : ℝ) ≤ ((T.state v).s : ℝ) := fun v hv =>
    hN6.trans (h.internal_large v hv).le
  have hsix : ∀ v, T.kind v ≠ .leaf → 6 ≤ (T.state v).s := fun v hv => by
    exact_mod_cast six v hv
  have hbelow : ∀ v, T.kind v ≠ .leaf → xZero ≤ Λ (T.state v).s := fun v hv =>
    hΛ.floor (hsix v hv)
  refine
    { Φ_nonneg := ?_
      K_nonneg := hK
      one_le_J := C.one_le_J
      three_le_D := C.three_le_D
      leaf_cost := h.leaf_cost
      toll := h.toll
      six_le := hsix
      two_τ_le := ?_
      τ_le_slack := ?_
      classes_le := h.classes_le
      class_families := ?_
      branch_pos := h.branch_pos
      branch_child := ?_
      orbit_pos := h.orbit_pos
      orbit_disjoint := h.orbit_disjoint
      orbit_child := ?_ }
  · intro v
    exact ΦL_nonneg C.A_nonneg C.B_nonneg hΛ (h.nonneg v).1 (h.nonneg v).2.1 (h.nonneg v).2.2
  · intro v hv
    exact two_rpow_a_le C hN6 hN2 (h.internal_large v hv)
  · intro v hv
    exact rpow_a_le_slack C hN6 (h.internal_large v hv)
  · intro v cls hk c hc
    have hne : T.kind v ≠ .leaf := by rw [hk]; simp
    have hmargin := Row'.multL_mul_exp_neg_dropL_le (hbelow v hne)
      (h.class_valid v cls hk c hc)
    obtain ⟨M, fam, hM, hfam⟩ := h.class_fam v cls hk c hc
    exact ⟨M, fam, (mul_le_mul_of_nonneg_right hM (Real.exp_pos _).le).trans hmargin, hfam⟩
  · intro v cls hk c hc b hb u hu
    have hne : T.kind v ≠ .leaf := by rw [hk]; simp
    exact Row'.child_ΦL_le C hΛ (six v hne) (h.class_valid v cls hk c hc)
      (h.branch_child v cls hk c hc b hb u hu) (h.nonneg u).1 (h.nonneg u).2.1
  · intro v cs hk u hu
    have hne : T.kind v ≠ .leaf := by rw [hk]; simp
    have h6 := six v hne
    obtain ⟨hρ, hσ, hQ, hh⟩ := h.orbit_child v cs hk u hu
    have hlt := (h.orbit_pos v cs hk u hu).2
    rcases hh with hh | ⟨hs2, hh⟩
    · -- The first child: nothing increases.
      have hh' : ((T.state u).h : ℝ) ≤ (T.state v).h := by exact_mod_cast hh
      have hx : (T.state u).x ≤ (T.state v).x := PotentialState.x_mono (by exact_mod_cast hlt.le)
      exact ΦL_le_of C.A_nonneg C.B_nonneg hΛ (h.nonneg u).1 (h.nonneg u).2.1
        hlt.le hx hρ hσ hQ hh'
    · -- A later child: `s_u ≤ s_v/2 ≤ θ s_v`, and the affected-row drop pays the `h` reset.
      have hθ : ((T.state u).s : ℝ) ≤ C.θ * (T.state v).s := by
        have : (2 : ℝ) * (T.state u).s ≤ (T.state v).s := by exact_mod_cast hs2
        nlinarith [C.half_lt_θ, (Nat.cast_nonneg _ : (0 : ℝ) ≤ (T.state v).s)]
      have hrow := Row'.child_ΦL_le C hΛ (R := .affected) h6 trivial ⟨hθ, hρ, hσ, hQ, hh⟩
        (h.nonneg u).1 (h.nonneg u).2.1
      have hpos := Row'.dropL_affected_nonneg (C := C) (hbelow v hne)
      linarith

/-- **Lemma 7.1 with parameter `Λ`.** Under `HypL` the phase terminates, and every node costs at
most `K (s+2)^D exp(Φ_Λ)`. -/
theorem _root_.GI.Paper.PhaseTree.HypL.cost_le (h : T.HypL C Λ N K) (hΛ : WeightFn Λ) (hN6 : 6 ≤ (N : ℝ) ^ C.γ)
    (hN2 : 2 ≤ (N : ℝ) ^ (C.γ * C.D - C.a)) (hK : 0 ≤ K) :
    WellFounded (fun u v => u ∈ (T.kind v).children) ∧
    ∀ v, T.cost v ≤ K * weight C.D (T.state v).s (ΦL C.A C.B Λ (T.state v)) := by
  have hA := h.toAbstract hΛ hN6 hN2 hK
  exact ⟨hA.wf, fun v => hA.cost_le v⟩

end HypLemmas

/-! ## The phase root and a fresh phase with parameter `Λ` -/

/-- `L(N) = log(N+2)`. -/
noncomputable def logN (N : ℕ) : ℝ := Real.log ((N : ℝ) + 2)

/-- The root resources with parameter `Λ`: HJ's `RootBounds`, except `Q ≤ Λ log s` instead of
`Q ≤ (log s)²`. (For `Λ ≥ log s` HJ's bound implies it, `RootBoundsL.of_root`; for
Theorem R* it is the bound `Q_d ≤ log s · log d̃` for caps initialized at `min(d_i, d)`.) -/
structure RootBoundsL (cσ Λ : ℝ) (N : ℕ) (S : PotentialState) : Prop where
  one_le_s : 1 ≤ S.s
  s_le_N : S.s ≤ N
  ρ_nonneg : 0 ≤ S.ρ
  ρ_le : S.ρ ≤ 2 * Real.logb 2 S.s
  σ_nonneg : 0 ≤ S.σ
  σ_le : S.σ ≤ cσ * Real.log ((S.s : ℝ) + 2)
  Q_nonneg : 0 ≤ S.Q
  Q_le : S.Q ≤ Λ * Real.log S.s
  h_le : S.h ≤ 2

theorem RootBoundsL.of_root {cσ Λ : ℝ} {N : ℕ} {S : PotentialState} (h : RootBounds cσ N S)
    (hΛ : Real.log S.s ≤ Λ) : RootBoundsL cσ Λ N S where
  one_le_s := h.one_le_s
  s_le_N := h.s_le_N
  ρ_nonneg := h.ρ_nonneg
  ρ_le := h.ρ_le
  σ_nonneg := h.σ_nonneg
  σ_le := h.σ_le
  Q_nonneg := h.Q_nonneg
  Q_le := by
    have hs1 : (1 : ℝ) ≤ S.s := by exact_mod_cast h.one_le_s
    have hl0 := Real.log_nonneg hs1
    calc S.Q ≤ Real.log S.s ^ 2 := h.Q_le
      _ ≤ Λ * Real.log S.s := by nlinarith
  h_le := h.h_le

/-- The potential at a phase root is `O(Λ log(N+2))`, with constant independent of `Λ`, `N`. -/
theorem root_potentialL (C : ChargingConstants) {cσ : ℝ} (hcσ : 0 ≤ cσ) :
    ∃ CΦ : ℝ, 0 ≤ CΦ ∧ ∀ (N : ℕ) (Λ : ℝ) (S : PotentialState), xZero ≤ Λ →
      RootBoundsL cσ Λ N S → ΦL C.A C.B (fun _ => Λ) S ≤ CΦ * (Λ * logN N) := by
  have hl2 := ChargingConstants.log_two_pos'
  have hx0 := ChargingConstants.xZero_pos
  refine ⟨C.A * (2 + 2 / Real.log 2 + cσ) + 2 * C.B / (xZero * Real.log 2), by
    have := C.A_nonneg; have := C.B_nonneg; positivity, ?_⟩
  intro N Λ S hΛ hS
  set L := logN N with hL
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hs1 : (1 : ℝ) ≤ S.s := by exact_mod_cast hS.one_le_s
  have hsN : (S.s : ℝ) ≤ N := by exact_mod_cast hS.s_le_N
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith)
  have hL0 : 0 ≤ L := hl2.le.trans hL2
  have hΛ0 : 0 < Λ := hx0.trans_le hΛ
  have hx0' := S.x_nonneg
  have hxL : S.x ≤ L := Real.log_le_log (by positivity) (by linarith)
  have hls0 : 0 ≤ Real.log S.s := Real.log_nonneg hs1
  have hlsL : Real.log S.s ≤ L := Real.log_le_log (by linarith) (by linarith)
  have h1 : S.ρ ≤ 2 / Real.log 2 * L := by
    have := hS.ρ_le
    rw [Real.logb] at this
    calc S.ρ ≤ 2 * (Real.log S.s / Real.log 2) := this
      _ ≤ 2 * (L / Real.log 2) := by gcongr
      _ = 2 / Real.log 2 * L := by ring
  have hσ : S.σ ≤ cσ * L := hS.σ_le.trans (mul_le_mul_of_nonneg_left hxL hcσ)
  have hQ : S.Q ≤ Λ * L := hS.Q_le.trans (mul_le_mul_of_nonneg_left hlsL hΛ0.le)
  have hh : (S.h : ℝ) ≤ 2 := by exact_mod_cast hS.h_le
  have hBh : C.B * S.h ≤ 2 * C.B / (xZero * Real.log 2) * (Λ * L) := by
    have hprod : xZero * Real.log 2 ≤ Λ * L := mul_le_mul hΛ hL2 hl2.le hΛ0.le
    have hone : 1 ≤ (Λ * L) / (xZero * Real.log 2) := by
      rw [le_div_iff₀ (mul_pos hx0 hl2), one_mul]; exact hprod
    calc C.B * S.h ≤ C.B * 2 := mul_le_mul_of_nonneg_left hh C.B_nonneg
      _ ≤ C.B * 2 * ((Λ * L) / (xZero * Real.log 2)) := le_mul_of_one_le_right
          (by linarith [C.B_nonneg]) hone
      _ = _ := by ring
  have hΛx : Λ * S.x ≤ Λ * L := mul_le_mul_of_nonneg_left hxL hΛ0.le
  have hΛρ : Λ * S.ρ ≤ 2 / Real.log 2 * (Λ * L) := by
    have := mul_le_mul_of_nonneg_left h1 hΛ0.le
    calc Λ * S.ρ ≤ Λ * (2 / Real.log 2 * L) := this
      _ = _ := by ring
  have hΛσ : Λ * S.σ ≤ cσ * (Λ * L) := by
    calc Λ * S.σ ≤ Λ * (cσ * L) := mul_le_mul_of_nonneg_left hσ hΛ0.le
      _ = _ := by ring
  have hsum : Λ * S.x + Λ * S.ρ + Λ * S.σ + S.Q ≤ (2 + 2 / Real.log 2 + cσ) * (Λ * L) := by
    linarith
  unfold ΦL
  have := mul_le_mul_of_nonneg_left hsum C.A_nonneg
  linarith

/-- **A fresh phase with parameter `Λ`.** A fresh input on `N` positions, a `HypL` phase tree
with toll `K`, and roots with `RootBoundsL`, has total cost at most `K exp(C₁ Λ log(N+2))`,
with `C₁` independent of `N`, `K`, `Λ`. -/
theorem fresh_phase_boundL (C : ChargingConstants) {cσ : ℝ} (hcσ : 0 ≤ cσ) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (N : ℕ) (K Λ : ℝ), 0 ≤ K → xZero ≤ Λ → 6 ≤ (N : ℝ) ^ C.γ →
      2 ≤ (N : ℝ) ^ (C.γ * C.D - C.a) →
      ∀ {V : Type*} (T : PhaseTree V), T.HypL C (fun _ => Λ) N K →
      ∀ (roots : List V) (phaseCost : ℝ),
        (∀ v ∈ roots, RootBoundsL cσ Λ N (T.state v)) →
        (roots.map fun v => (T.state v).s).sum ≤ N →
        phaseCost ≤ (N : ℝ) ^ C.a * K + (roots.map T.cost).sum →
        phaseCost ≤ K * Real.exp (C₁ * (Λ * logN N)) := by
  obtain ⟨CΦ, hCΦ, hΦ⟩ := root_potentialL C hcσ
  have hl2 := ChargingConstants.log_two_pos'
  have hx0 := ChargingConstants.xZero_pos
  have hD0 : (0 : ℝ) ≤ C.D := Nat.cast_nonneg _
  have hC₁ : 0 ≤ C.D / xZero + 1 / xZero + CΦ := by positivity
  refine ⟨C.D / xZero + 1 / xZero + CΦ, hC₁, ?_⟩
  intro N K Λ hK hΛ hN6 hN2 V T hT roots phaseCost hroots hsum hcost
  set L := logN N with hLdef
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith)
  have hL0 : 0 < L := hl2.trans_le hL2
  have hΛ0 : 0 < Λ := hx0.trans_le hΛ
  have hcost' := (hT.cost_le (const_weightFn hΛ) hN6 hN2 hK).2
  have hA : (N : ℝ) ^ C.a ≤ ((N : ℝ) + 2) ^ C.D := by
    have haD : C.a ≤ C.D := by
      have h := C.D_gt
      have : C.a ≤ C.a / C.γ := by
        rw [le_div_iff₀ C.γ_pos]; nlinarith [C.γ_lt_one, C.a_pos]
      linarith
    calc (N : ℝ) ^ C.a ≤ ((N : ℝ) + 2) ^ C.a :=
          Real.rpow_le_rpow hN0 (by linarith) C.a_pos.le
      _ ≤ ((N : ℝ) + 2) ^ (C.D : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) haD
      _ = _ := Real.rpow_natCast _ _
  have hWroots : (roots.map fun v => weight C.D (T.state v).s (ΦL C.A C.B (fun _ => Λ) (T.state v))).sum ≤
      ((N : ℝ) + 2) ^ C.D * Real.exp (CΦ * (Λ * L)) := by
    have hpre : ((roots.map T.state).map fun S => ((S.s : ℝ) + 2) ^ C.D).sum ≤ ((N : ℝ) + 2) ^ C.D := by
      apply list_prefactor_sum_le C.three_le_D
      · intro S hS
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hS
        exact (hroots v hv).one_le_s
      · have h' : ((roots.map fun v => (T.state v).s).sum : ℝ) ≤ N := by
          exact_mod_cast hsum
        simpa [Nat.cast_list_sum, List.map_map] using h'
    calc (roots.map fun v => weight C.D (T.state v).s (ΦL C.A C.B (fun _ => Λ) (T.state v))).sum
        ≤ (roots.map fun v => ((T.state v).s + 2 : ℝ) ^ C.D * Real.exp (CΦ * (Λ * L))).sum := by
          apply List.sum_le_sum
          intro v hv
          unfold weight
          exact mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (hΦ N Λ _ hΛ (hroots v hv))) (by positivity)
      _ = (roots.map fun v => ((T.state v).s + 2 : ℝ) ^ C.D).sum * Real.exp (CΦ * (Λ * L)) := by
          rw [List.sum_map_mul_right]
      _ = ((roots.map T.state).map fun S => ((S.s : ℝ) + 2) ^ C.D).sum * Real.exp (CΦ * (Λ * L)) := by
          rw [List.map_map]; rfl
      _ ≤ _ := mul_le_mul_of_nonneg_right hpre (Real.exp_pos _).le
  have hpre : ((N : ℝ) + 2) ^ C.D ≤ Real.exp (C.D / xZero * (Λ * L)) := by
    calc ((N : ℝ) + 2) ^ C.D = Real.exp (C.D * L) := by
          rw [← Real.exp_log (by positivity : (0 : ℝ) < (N : ℝ) + 2), ← Real.exp_nat_mul]
          simp only [hLdef, logN]
      _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          rw [div_mul_eq_mul_div, le_div_iff₀ hx0]
          nlinarith [mul_le_mul_of_nonneg_left hΛ (mul_nonneg hD0 hL0.le)]
  have htwo : (2 : ℝ) ≤ Real.exp (1 / xZero * (Λ * L)) := by
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hx0]
          nlinarith [mul_le_mul_of_nonneg_left hL2 hΛ0.le,
            mul_le_mul_of_nonneg_left hΛ hL0.le]
  have hE1 : 1 ≤ Real.exp (CΦ * (Λ * L)) :=
    Real.one_le_exp (by positivity)
  have hroot : (N : ℝ) ^ C.a + (roots.map fun v => weight C.D (T.state v).s (ΦL C.A C.B (fun _ => Λ) (T.state v))).sum ≤
      Real.exp ((C.D / xZero + 1 / xZero + CΦ) * (Λ * L)) := by
    have hP0 : 0 ≤ ((N : ℝ) + 2) ^ C.D := by positivity
    calc (N : ℝ) ^ C.a + (roots.map fun v => weight C.D (T.state v).s (ΦL C.A C.B (fun _ => Λ) (T.state v))).sum
        ≤ ((N : ℝ) + 2) ^ C.D * (2 * Real.exp (CΦ * (Λ * L))) := by nlinarith
      _ ≤ Real.exp (C.D / xZero * (Λ * L)) *
            (Real.exp (1 / xZero * (Λ * L)) * Real.exp (CΦ * (Λ * L))) := by
          apply mul_le_mul hpre _ (by positivity) (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have hcostroots : (roots.map T.cost).sum ≤
      K * (roots.map fun v => weight C.D (T.state v).s (ΦL C.A C.B (fun _ => Λ) (T.state v))).sum := by
    rw [← List.sum_map_mul_left]
    exact List.sum_le_sum (fun v _ => hcost' v)
  calc phaseCost ≤ K * ((N : ℝ) ^ C.a + (roots.map fun v => weight C.D (T.state v).s (ΦL C.A C.B (fun _ => Λ) (T.state v))).sum) := by
        nlinarith
    _ ≤ K * Real.exp ((C.D / xZero + 1 / xZero + CΦ) * (Λ * L)) :=
        mul_le_mul_of_nonneg_left hroot hK

/-! ## The recurrence with parameter `Λ` -/

/-- Solution of the phase recurrence, uniform in `Λ ≥ 1`. The hypothesis on small `n` is the
base case; the conclusion's constant depends only on `γ`, `C`, the base size and `B₀`, not on `Λ`
or on `F`. -/
theorem recurrenceL {γ C : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hC : 0 ≤ C) (N₁ : ℕ) (B₀ : ℝ)
    (hB₀ : 0 ≤ B₀) :
    ∃ base C' : ℕ, N₁ ≤ base ∧ ∀ (Λ : ℝ), 1 ≤ Λ → ∀ F : ℕ → ℝ,
      (∀ n < base, F n ≤ B₀) →
      (∀ N, base ≤ N → F N ≤ Real.exp (C * (Λ * logN N)) * (1 + F ⌈(N : ℝ) ^ γ⌉₊)) →
      ∀ N, F N ≤ Real.exp (C' * (Λ * logN N)) := by
  set γh := (1 + γ) / 2 with hγh
  have hγh1 : γh < 1 := by rw [hγh]; linarith
  have hγh0 : 0 < γh := by rw [hγh]; linarith
  have hev : ∀ᶠ n : ℕ in Filter.atTop, (4 : ℝ) ≤ (n : ℝ) ^ ((1 - γ) / 2) :=
    ((tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 4
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp hev
  set base := max N₁ (max N₂ 1) with hbase
  have hl2 := ChargingConstants.log_two_pos'
  set D : ℝ := max ((C + Real.log 2) / (1 - γh)) (Real.log (B₀ + 1) / Real.log 2)
  have hD1 : (C + Real.log 2) / (1 - γh) ≤ D := le_max_left _ _
  have hD2 : Real.log (B₀ + 1) / Real.log 2 ≤ D := le_max_right _ _
  have hD0 : 0 ≤ D := le_trans (div_nonneg (by linarith) (by linarith)) hD1
  refine ⟨base, ⌈D⌉₊, le_max_left _ _, ?_⟩
  intro Λ hΛ F hbaseF hrec N
  have hΛ0 : 0 < Λ := by linarith
  have hscore : ∀ n, 0 ≤ Λ * logN n := fun n =>
    mul_nonneg hΛ0.le (Real.log_nonneg (by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg _; linarith))
  have key : ∀ n, F n ≤ Real.exp (D * (Λ * logN n)) := by
    refine GI.contracting_recurrence_bound F (fun n => Λ * logN n)
      (fun n => ⌈(n : ℝ) ^ γ⌉₊) base C D γh hD0 hscore ?_ ?_ ?_
    · have := (div_le_iff₀ (by linarith : (0 : ℝ) < 1 - γh)).mp hD1
      nlinarith
    · intro n hn
      have hscoreL : Real.log 2 ≤ Λ * logN n := by
        have hLn : Real.log 2 ≤ logN n := Real.log_le_log (by norm_num)
          (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg _; linarith)
        nlinarith [hLn.trans (le_refl _), hl2.le]
      have hFB := hbaseF n hn
      have hlog1 : 0 ≤ Real.log (B₀ + 1) := Real.log_nonneg (by linarith)
      calc F n ≤ B₀ := hFB
        _ ≤ B₀ + 1 := by linarith
        _ = Real.exp (Real.log (B₀ + 1)) := (Real.exp_log (by linarith)).symm
        _ ≤ _ := by
            apply Real.exp_le_exp.mpr
            have : Real.log (B₀ + 1) = Real.log (B₀ + 1) / Real.log 2 * Real.log 2 := by
              field_simp
            rw [this]
            exact mul_le_mul hD2 hscoreL hl2.le hD0
    · intro n hn
      have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
      have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
      have hn3 : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
      have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn3
      have h4 := hN₂ n hn2
      have hnγ1 : (1 : ℝ) ≤ (n : ℝ) ^ γ := Real.one_le_rpow hN hγ0.le
      have hceil : (⌈(n : ℝ) ^ γ⌉₊ : ℝ) < (n : ℝ) ^ γ + 1 :=
        Nat.ceil_lt_add_one (by linarith)
      have hsplit : (n : ℝ) ^ γh = (n : ℝ) ^ ((1 - γ) / 2) * (n : ℝ) ^ γ := by
        rw [← Real.rpow_add (by linarith)]; congr 1; rw [hγh]; ring
      have hc1 : (⌈(n : ℝ) ^ γ⌉₊ : ℝ) + 2 ≤ (n : ℝ) ^ γh := by
        rw [hsplit]; nlinarith
      have hc2 : (n : ℝ) ^ γh ≤ ((n : ℝ) + 2) ^ γh :=
        Real.rpow_le_rpow (by linarith) (by linarith) hγh0.le
      have hc3 : (n : ℝ) ^ γh ≤ n := by
        calc (n : ℝ) ^ γh ≤ (n : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hN hγh1.le
          _ = n := Real.rpow_one _
      have h3 : 1 ≤ logN n := by
        unfold logN
        rw [Real.le_log_iff_exp_le (by positivity)]
        have := Real.exp_one_lt_d9
        linarith
      refine ⟨?_, ?_, ?_, hrec n hn⟩
      · have : (⌈(n : ℝ) ^ γ⌉₊ : ℝ) < n := by linarith
        exact_mod_cast this
      · nlinarith
      · have hlog : Real.log ((⌈(n : ℝ) ^ γ⌉₊ : ℝ) + 2) ≤ γh * Real.log ((n : ℝ) + 2) := by
          calc Real.log ((⌈(n : ℝ) ^ γ⌉₊ : ℝ) + 2)
              ≤ Real.log (((n : ℝ) + 2) ^ γh) := Real.log_le_log (by positivity) (by linarith)
            _ = γh * Real.log ((n : ℝ) + 2) := Real.log_rpow (by positivity) _
        have hlogN : logN ⌈(n : ℝ) ^ γ⌉₊ ≤ γh * logN n := hlog
        have := mul_le_mul_of_nonneg_left hlogN hΛ0.le
        show Λ * logN _ ≤ γh * (Λ * logN n)
        nlinarith
  calc F N ≤ Real.exp (D * (Λ * logN N)) := key N
    _ ≤ Real.exp ((⌈D⌉₊ : ℝ) * (Λ * logN N)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (Nat.le_ceil D) (hscore N))

/-! ## The abstract form of Theorem R* -/

/-- The toll of a phase of parameter `Λ`:
`K_N = exp(c_T Λ log(N+2)) (1 + F(⌈N^γ⌉))`. -/
noncomputable def tollL (cT γ : ℝ) (F : ℕ → ℝ) (Λ : ℝ) (N : ℕ) : ℝ :=
  Real.exp (cT * (Λ * logN N)) * (1 + F ⌈(N : ℝ) ^ γ⌉₊)

/-- **What one phase provides.** A phase of parameter `Λ` at size `N`: a phase tree satisfying
`HypL` with toll `tollL`, whose roots satisfy `RootBoundsL`, and whose fresh cost bounds `F N`. -/
structure PhaseStep (C : ChargingConstants) (cσ cT Λ : ℝ) (F : ℕ → ℝ) (N : ℕ) : Prop where
  exists_phase : ∃ (V : Type) (T : PhaseTree V) (roots : List V) (phaseCost : ℝ),
    T.HypL C (fun _ => Λ) N (tollL cT C.γ F Λ N) ∧
    (∀ v ∈ roots, RootBoundsL cσ Λ N (T.state v)) ∧
    (roots.map fun v => (T.state v).s).sum ≤ N ∧
    phaseCost ≤ (N : ℝ) ^ C.a * tollL cT C.γ F Λ N + (roots.map T.cost).sum ∧
    F N ≤ phaseCost

theorem exists_above_base (C : ChargingConstants) :
    ∃ N₃ : ℕ, ∀ N : ℕ, N₃ ≤ N → 6 ≤ (N : ℝ) ^ C.γ ∧ 2 ≤ (N : ℝ) ^ (C.γ * C.D - C.a) := by
  have hγ := C.γ_pos
  have hgap : 0 < C.γ * C.D - C.a := by
    have h := C.D_gt
    have hdiv : C.a / C.γ < C.D - 2 := by linarith
    rw [div_lt_iff₀ hγ] at hdiv
    nlinarith
  have h1 : ∀ᶠ N : ℕ in Filter.atTop, (6 : ℝ) ≤ (N : ℝ) ^ C.γ :=
    ((tendsto_rpow_atTop hγ).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 6
  have h2 : ∀ᶠ N : ℕ in Filter.atTop, (2 : ℝ) ≤ (N : ℝ) ^ (C.γ * C.D - C.a) :=
    ((tendsto_rpow_atTop hgap).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  obtain ⟨N₃, h⟩ := Filter.eventually_atTop.mp (h1.and h2)
  exact ⟨N₃, h⟩

/-- **The abstract form of Theorem R\*.** Let `C` be HJ's charging constants, `cσ, cT, B₀ ≥ 0`
absolute. There are absolute `base` and `C'` such that for every `Λ ≥ log 48` and every
`F ≥ 0`: if `F` is at most `B₀` below `base`, and every phase size `N ≥ base` is provided by a
phase of parameter `Λ` (`PhaseStep`), then `F N ≤ exp(C' Λ log(N+2))` for every `N`.

Taking `Λ = log(8 max(d,6))` this is `F N = exp(O(log(N+2) log(d+2)))`. -/
theorem abstract_R_star (C : ChargingConstants) {cσ cT B₀ : ℝ} (hcσ : 0 ≤ cσ) (hcT : 0 ≤ cT)
    (hB₀ : 0 ≤ B₀) :
    ∃ (base C' : ℕ), ∀ (Λ : ℝ), Real.log 48 ≤ Λ → ∀ F : ℕ → ℝ, (∀ n, 0 ≤ F n) →
      (∀ n < base, F n ≤ B₀) →
      (∀ N, base ≤ N → PhaseStep C cσ cT Λ F N) →
      ∀ N, F N ≤ Real.exp (C' * (Λ * logN N)) := by
  obtain ⟨C₁, hC₁, hphase⟩ := fresh_phase_boundL C hcσ
  obtain ⟨N₃, hN₃⟩ := exists_above_base C
  obtain ⟨base, C', hb, hrec⟩ := recurrenceL (γ := C.γ) (C := cT + C₁) C.γ_pos C.γ_lt_one
    (by linarith) N₃ B₀ hB₀
  refine ⟨base, C', ?_⟩
  intro Λ hΛ F hF hsmall hstep
  have hx0 : xZero ≤ Real.log 48 := Real.log_le_log (by norm_num) (by norm_num)
  have hx0' : xZero ≤ Λ := hx0.trans hΛ
  have hl3 : 1 ≤ Real.log 48 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9; linarith
  have hΛ1 : 1 ≤ Λ := hl3.trans hΛ
  refine hrec Λ hΛ1 F hsmall ?_
  intro N hN
  obtain ⟨V, T, roots, phaseCost, hT, hroots, hsum, hcost, hFN⟩ := (hstep N hN).exists_phase
  have hN36 := hN₃ N (hb.trans hN)
  have hK : 0 ≤ tollL cT C.γ F Λ N :=
    mul_nonneg (Real.exp_pos _).le (by linarith [hF ⌈(N : ℝ) ^ C.γ⌉₊])
  have := hphase N _ Λ hK hx0' hN36.1 hN36.2 T hT roots phaseCost hroots hsum hcost
  calc F N ≤ phaseCost := hFN
    _ ≤ tollL cT C.γ F Λ N * Real.exp (C₁ * (Λ * logN N)) := this
    _ = Real.exp ((cT + C₁) * (Λ * logN N)) * (1 + F ⌈(N : ℝ) ^ C.γ⌉₊) := by
        unfold tollL
        rw [add_mul, Real.exp_add]
        ring

/-- The polynomial phase toll of R*: `N^c (1+F(N^γ))` fits `tollL` for `Λ ≥ 1`. -/
theorem poly_toll_le_tollL {c γ Λ : ℝ} (hc : 0 ≤ c) (hΛ : 1 ≤ Λ) (F : ℕ → ℝ)
    (hF : ∀ n, 0 ≤ F n) (N : ℕ) :
    ((N : ℝ) + 2) ^ c * (1 + F ⌈(N : ℝ) ^ γ⌉₊) ≤ tollL c γ F Λ N := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hL : 0 ≤ logN N := Real.log_nonneg (by linarith)
  have h1 : ((N : ℝ) + 2) ^ c ≤ Real.exp (c * (Λ * logN N)) := by
    rw [Real.rpow_def_of_pos (by positivity)]
    apply Real.exp_le_exp.mpr
    have e : Real.log ((N : ℝ) + 2) = logN N := rfl
    rw [e]
    have : logN N ≤ Λ * logN N := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hc]
  have hF0 := hF ⌈(N : ℝ) ^ γ⌉₊
  unfold tollL
  exact mul_le_mul_of_nonneg_right h1 (by linarith)

/-- HJ's toll `exp(c log²(N+2))` fits `tollL` when `d ≥ N^α`, that is
`Λ ≥ α log(N+2)`. This is the case where `HJ` is run verbatim. -/
theorem hj_toll_le_tollL {c α γ Λ : ℝ} (hc : 0 ≤ c) (hα : 0 < α) {N : ℕ}
    (hΛ : α * logN N ≤ Λ) (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n) :
    Real.exp (c * logN N ^ 2) * (1 + F ⌈(N : ℝ) ^ γ⌉₊) ≤ tollL (c / α) γ F Λ N := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hL : 0 ≤ logN N := Real.log_nonneg (by linarith)
  have h1 : Real.exp (c * logN N ^ 2) ≤ Real.exp (c / α * (Λ * logN N)) := by
    apply Real.exp_le_exp.mpr
    have h2 : α * logN N * logN N ≤ Λ * logN N := mul_le_mul_of_nonneg_right hΛ hL
    have h3 : logN N ^ 2 ≤ (1 / α) * (Λ * logN N) := by
      rw [show (1 / α) * (Λ * logN N) = (Λ * logN N) / α by ring, le_div_iff₀ hα]
      nlinarith
    have := mul_le_mul_of_nonneg_left h3 hc
    calc c * logN N ^ 2 ≤ c * ((1 / α) * (Λ * logN N)) := this
      _ = c / α * (Λ * logN N) := by ring
  have hF0 := hF ⌈(N : ℝ) ^ γ⌉₊
  unfold tollL
  exact mul_le_mul_of_nonneg_right h1 (by linarith)

end GI.DegreeD
