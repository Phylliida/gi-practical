import DegreeD.M.Main
import Workspace.Paper.RunningTimeParameters
import Workspace.Paper.RunningTimeBaseSize

/-!
# The parameter hypotheses of `degreeD_stage1` are satisfiable

Non-vacuity of the numeric hypotheses. For every `A₀`, there are parameters `P` and charging
constants `cc` with `cc.a ≥ A₀` satisfying every parameter hypothesis of `degreeD_stage1`
(in particular `hcc`, given the constants `c₁, c₂` of `GNSPrimitive`). The values are the paper's:
`α = 2/5`, `γ = 9/10`, `κ = 64`, `θ = 3/4`, `β = 9/10`, `q₀ = 2064`, `b₀ = 2`, `J = 8`,
with `a` large and `N₀` above a base size.
-/

namespace GI.DegreeD.M

open GI.Algorithm GI.Paper

/-- **The parameter hypotheses are satisfiable, for any size of `a`.** -/
theorem params_exist (A₀ : ℝ) :
    ∃ (P : Params) (cc : ChargingConstants),
      P.Terminating ∧ 64 ≤ P.κ ∧ Compat P cc ∧ 2 * P.α ≤ P.γ ∧ AboveBase P cc ∧
      (∀ n : ℕ, P.N₀ < n → (4 : ℝ) ≤ (n : ℝ) ^ ((1 - P.γ) / 2)) ∧
      (((2 * P.κ : ℕ) : ℝ) + Real.log (9 : ℕ) / Real.log 48 ≤ cc.aStar) ∧
      (Real.log P.q₀.factorial / Real.log 48 + 1) / Real.log 17 ≤
        cc.a + cc.aStar / Real.log 2 ∧
      A₀ ≤ cc.a := by
  set a : ℝ := max A₀ 36001 with ha
  have ha1 : (36001 : ℝ) ≤ a := le_max_right _ _
  have haA : A₀ ≤ a := le_max_left _ _
  obtain ⟨cc, h1, h2, h3, h4, h5, h6, h7, h8⟩ := sec_parameters_item_iv (a := a) (γ := 9 / 10)
    (κ := 64) (θ := 3 / 4) (β := 9 / 10) (q₀ := 2064) (J := 8) (b₀ := 2)
    (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hD : a < 9 / 10 * (cc.D : ℝ) := by
    have h := cc.D_gt
    rw [h1, h2] at h
    have hγ : a / (9 / 10) = 10 / 9 * a := by ring
    rw [hγ] at h
    nlinarith
  obtain ⟨N₁, hN₁⟩ := sec_parameters_base_size_example 2064 a cc.D hD
  have hev : ∀ᶠ n : ℕ in Filter.atTop, (4 : ℝ) ≤ (n : ℝ) ^ ((1 - 9 / 10) / 2 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 4
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp hev
  let P : Params :=
    { α := 2 / 5, γ := 9 / 10, N₀ := max N₁ (max N₂ 1), κ := 64, a := a - 1, θ := 3 / 4
      β := 9 / 10, q₀ := 2064, b₀ := 2 }
  have hγP : P.γ = 9 / 10 := rfl
  have hPa : P.a = a - 1 := rfl
  refine ⟨P, cc, ?_, by norm_num [P], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨le_trans (le_max_right _ _) (le_max_right _ _), by norm_num [P], by norm_num [P],
      by norm_num [P], by norm_num [P], by norm_num [P], by norm_num [P], by norm_num [P],
      by norm_num [P]⟩
  · exact
      { γ_eq := by rw [h2]
        a_le := by rw [h1]; simp [P]
        θ_le := by rw [h4]; try norm_num [P]
        κ_le := by rw [h3]; try norm_num [P]
        κ_five := by norm_num [P]
        β_pos := by norm_num [P]
        β_le := by rw [h5]; try norm_num [P]
        q₀_le := by rw [h6]; try norm_num [P]
        βq₀ := by norm_num [P]
        J_six := by rw [h7]; norm_num }
  · norm_num [P]
  · intro n hn
    have hnN : N₁ ≤ n := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hn)
    obtain ⟨-, -, -, -, h61, hceil, h22⟩ := hN₁ n hnN
    refine ⟨by rw [h2]; exact h61, ?_, ?_⟩
    · rw [h2, h1]; exact h22
    · exact hceil
  · intro n hn
    have hnN : N₂ ≤ n := by
      have : N₂ ≤ P.N₀ := le_trans (le_max_left _ _) (le_max_right _ _)
      omega
    have := hN₂ n hnN
    rw [hγP]
    exact this
  · have hκ : ((2 * P.κ : ℕ) : ℝ) = 128 := by norm_num [P]
    rw [hκ]
    have hlog : Real.log (9 : ℕ) / Real.log 48 ≤ 1 := by
      rw [div_le_one (Real.log_pos (by norm_num))]
      exact Real.log_le_log (by norm_num) (by norm_num)
    have hstar : (40001 : ℝ) ≤ cc.aStar := by
      unfold ChargingConstants.aStar
      rw [h1, h2]
      rw [le_div_iff₀ (by norm_num)]
      linarith
    linarith
  · have hq : P.q₀ = 2064 := rfl
    rw [hq]
    have hfac : ((Nat.factorial 2064 : ℕ) : ℝ) ≤ (2064 : ℝ) ^ (2064 : ℕ) := by
      exact_mod_cast Nat.factorial_le_pow 2064
    have hlog2 : Real.log ((Nat.factorial 2064 : ℕ) : ℝ) ≤ 2064 * Real.log 2064 := by
      have hpos : (0 : ℝ) < ((Nat.factorial 2064 : ℕ) : ℝ) := by
        exact_mod_cast Nat.factorial_pos _
      calc Real.log ((Nat.factorial 2064 : ℕ) : ℝ) ≤ Real.log ((2064 : ℝ) ^ (2064 : ℕ)) :=
            Real.log_le_log hpos hfac
        _ = 2064 * Real.log 2064 := by rw [Real.log_pow]; norm_num
    have hl2 := Real.log_two_lt_d9
    have hlog3 : Real.log 2064 ≤ 12 * Real.log 2 := by
      calc Real.log 2064 ≤ Real.log ((2 : ℝ) ^ (12 : ℕ)) :=
            Real.log_le_log (by norm_num) (by norm_num)
        _ = 12 * Real.log 2 := by rw [Real.log_pow]; norm_num
    have h48 : (1 : ℝ) ≤ Real.log 48 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_one_lt_d9; linarith
    have h17 : (1 : ℝ) ≤ Real.log 17 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_one_lt_d9; linarith
    have hnum : Real.log ((Nat.factorial 2064 : ℕ) : ℝ) ≤ 18000 := by
      nlinarith
    have hquot : Real.log ((Nat.factorial 2064 : ℕ) : ℝ) / Real.log 48 ≤ 18000 := by
      apply div_le_of_le_mul₀ (by linarith) (by norm_num)
      nlinarith [Real.log_natCast_nonneg (Nat.factorial 2064)]
    have hfrac : (Real.log ((Nat.factorial 2064 : ℕ) : ℝ) / Real.log 48 + 1) / Real.log 17 ≤ 18001 := by
      apply div_le_of_le_mul₀ (by linarith) (by norm_num)
      have hq0 : 0 ≤ Real.log ((Nat.factorial 2064 : ℕ) : ℝ) / Real.log 48 :=
        div_nonneg (Real.log_natCast_nonneg _) (by linarith)
      nlinarith
    have hstar : 0 ≤ cc.aStar / Real.log 2 := by
      have := cc.aStar_nonneg
      have := ChargingConstants.log_two_pos'
      positivity
    have ha0 : (18001 : ℝ) ≤ cc.a := by rw [h1]; linarith
    linarith
  · rw [h1]; exact haA

/-- The parameters that fit given GNS constants `c₁, c₂` (non-vacuity of `degreeD_stage1`). -/
theorem params_fit_gns (c₁ c₂ : ℝ) :
    ∃ (P : Params) (cc : ChargingConstants),
      P.Terminating ∧ 64 ≤ P.κ ∧ Compat P cc ∧ 2 * P.α ≤ P.γ ∧ AboveBase P cc ∧
      (∀ n : ℕ, P.N₀ < n → (4 : ℝ) ≤ (n : ℝ) ^ ((1 - P.γ) / 2)) ∧
      (((2 * P.κ : ℕ) : ℝ) + Real.log (9 : ℕ) / Real.log 48 ≤ cc.aStar) ∧
      (Real.log P.q₀.factorial / Real.log 48 + 1) / Real.log 17 ≤
        cc.a + cc.aStar / Real.log 2 ∧
      c₁ / Real.log 2 + c₂ / Real.log 48 ≤ cc.a + cc.aStar / Real.log 2 := by
  obtain ⟨P, cc, h1, hk, h2, h3, h4, h5, h6, h7, h8⟩ :=
    params_exist (c₁ / Real.log 2 + c₂ / Real.log 48)
  refine ⟨P, cc, h1, hk, h2, h3, h4, h5, h6, h7, ?_⟩
  have := cc.aStar_nonneg
  have h2 : 0 < Real.log 2 := ChargingConstants.log_two_pos'
  have h9 : 0 ≤ cc.aStar / Real.log 2 := by positivity
  linarith

end GI.DegreeD.M
