import DegreeD.TableLambda

/-!
# The columns of the table of Theorem R*, against `multL`

For `d̃ = max(d, 6)` and `Λ = log(8 d̃)`, the branch counts of the `Γ̂_d` analysis
(docs/verify-theorem-R.md §4, docs/redteam-theorem-R.md §1.3) fit the multiplicity column
`Row'.multL` of `TableLambda.lean`:

| class | count (cited facts) | lemma |
|---|---|---|
| affected / unaffected: certificate, comparison, large-symmetry families | `b q^e` | `family_le_multL` |
| product refinement, `k ≥ 2`: `|P:A_m^k| ≤ 2^k |K|`, BCP gives `|K| ≤ d̃^{k-1}` | `2^k (d̃+1)^{k-1}` | `product_count_le_multL` |
| enumeration, GNS 3.13(1): `|P| ≤ d'^{c₁ log d + c₂}` | as stated | `gns_count_le_multL` |
| enumeration, GNS 3.13(2) with `m ≤ q₀` | `(q₀!)^k (d̃+1)^{k-1}`, `d' ≥ 17^k` | `small_cameron_count_le_multL` |
| continuation | `2 q^{κ+1}` | `continuation_count_le_multL` |

Each lemma is a numeric statement with the cited group-theoretic count as a hypothesis on the
numbers (no group theory here). The conditions on `a* = a/γ` hold for HJ's example constants
`a = 36001`, `γ = 9/10` (`a* = 40001`, with `κ = 64`, `2κ + 1 = 129`).
For the enumeration rows, the condition `c' ≤ a + a*/log 2` is met by enlarging `a`, as the
paper's "`a` large enough"; the GNS constants `c₁, c₂` are absolute but not explicit.

Everything in this file is unconditional arithmetic (no axioms beyond the standard three).
-/

namespace GI.DegreeD

open GI.Paper

/-- `Λ = log(8 max(d,6))`. -/
noncomputable def lam (d : ℕ) : ℝ := Real.log (8 * (max d 6 : ℕ))

theorem d_tilde_pos (d : ℕ) : (0 : ℝ) < (max d 6 : ℕ) := by
  have : 0 < max d 6 := by omega
  exact_mod_cast this

theorem log48_le_lam (d : ℕ) : Real.log 48 ≤ lam d := by
  have h : (48 : ℝ) ≤ 8 * ((max d 6 : ℕ) : ℝ) := by
    have : 6 ≤ max d 6 := le_max_right _ _
    have h' : (6 : ℝ) ≤ (max d 6 : ℕ) := by exact_mod_cast this
    linarith
  unfold lam
  exact Real.log_le_log (by norm_num) h

theorem xZero_le_lam (d : ℕ) : xZero ≤ lam d :=
  (Real.log_le_log (by norm_num) (by norm_num) : xZero ≤ Real.log 48).trans (log48_le_lam d)

theorem one_le_lam (d : ℕ) : 1 ≤ lam d := by
  have h3 : 1 ≤ Real.log 48 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9; linarith
  exact h3.trans (log48_le_lam d)

theorem lam_pos (d : ℕ) : 0 < lam d := by linarith [one_le_lam d]

theorem log_le_lam {d q : ℕ} (hq1 : 1 ≤ q) (hq : q ≤ max d 6) : Real.log q ≤ lam d := by
  have h1 : (0 : ℝ) < q := by exact_mod_cast hq1
  have h2 : (q : ℝ) ≤ 8 * (max d 6 : ℕ) := by
    have : (q : ℝ) ≤ (max d 6 : ℕ) := by exact_mod_cast hq
    have h0 := d_tilde_pos d
    linarith
  exact Real.log_le_log h1 h2

variable (C : ChargingConstants)

/-- **Affected and unaffected rows.** A family count `b q^e` (from the (H2) regrouping, with
`q ≤ d̃`), fits `multL`, provided `e + log b / log 48 ≤ a*`. For the families of Theorem R*,
`b = 32, e = 2κ`. -/
theorem family_le_multL {d q b e : ℕ} (hq1 : 1 ≤ q) (hq : q ≤ max d 6) (hb : 1 ≤ b)
    (hab : (e : ℝ) + Real.log b / Real.log 48 ≤ C.aStar) :
    (b : ℝ) * (q : ℝ) ^ e ≤ Row'.multL C (lam d) .affected := by
  have h48 : 0 < Real.log 48 := Real.log_pos (by norm_num)
  have hL := lam_pos d
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hlogb : 0 ≤ Real.log b := Real.log_natCast_nonneg b
  have h1 : Real.log b ≤ Real.log b / Real.log 48 * lam d := by
    rw [div_mul_eq_mul_div, le_div_iff₀ h48]
    exact mul_le_mul_of_nonneg_left (log48_le_lam d) hlogb
  have h2 : e * Real.log q ≤ e * lam d :=
    mul_le_mul_of_nonneg_left (log_le_lam hq1 hq) (Nat.cast_nonneg _)
  have h3 : (b : ℝ) * (q : ℝ) ^ e = Real.exp (Real.log b + e * Real.log q) := by
    rw [Real.exp_add, Real.exp_log hb0, ← Real.rpow_natCast, Real.rpow_def_of_pos hq0, mul_comm (e : ℝ)]
  simp only [Row'.multL]
  rw [h3]
  apply Real.exp_le_exp.mpr
  have := mul_le_mul_of_nonneg_right hab hL.le
  nlinarith

/-- **Product refinement**, `k ≥ 2`: `2^k (d̃+1)^{k-1} ≤ exp((k-1) Λ) ≤ multL`. -/
theorem product_count_le_multL {d k : ℕ} (hk : 2 ≤ k) :
    (2 : ℝ) ^ k * (((max d 6 : ℕ) : ℝ) + 1) ^ (k - 1) ≤ Row'.multL C (lam d) (.product k) := by
  have hdt := d_tilde_pos d
  have hL := lam_pos d
  have hdt6 : (6 : ℝ) ≤ (max d 6 : ℕ) := by exact_mod_cast (le_max_right d 6)
  have hk1 : 1 ≤ k - 1 := by omega
  have h1 : (2 : ℝ) ^ k * (((max d 6 : ℕ) : ℝ) + 1) ^ (k - 1) ≤
      (8 * ((max d 6 : ℕ) : ℝ)) ^ (k - 1) := by
    have e1 : (2 : ℝ) ^ k ≤ 4 ^ (k - 1) := by
      have : (2 : ℝ) ^ k ≤ 2 ^ (2 * (k - 1)) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      calc (2 : ℝ) ^ k ≤ 2 ^ (2 * (k - 1)) := this
        _ = 4 ^ (k - 1) := by rw [pow_mul]; norm_num
    calc (2 : ℝ) ^ k * (((max d 6 : ℕ) : ℝ) + 1) ^ (k - 1)
        ≤ 4 ^ (k - 1) * (((max d 6 : ℕ) : ℝ) + 1) ^ (k - 1) :=
          mul_le_mul_of_nonneg_right e1 (by positivity)
      _ = (4 * (((max d 6 : ℕ) : ℝ) + 1)) ^ (k - 1) := by rw [mul_pow]
      _ ≤ (8 * ((max d 6 : ℕ) : ℝ)) ^ (k - 1) :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
  have h2 : (8 * ((max d 6 : ℕ) : ℝ)) ^ (k - 1) = Real.exp ((k - 1 : ℕ) * lam d) := by
    conv_lhs => rw [← Real.exp_log (by positivity : 0 < 8 * ((max d 6 : ℕ) : ℝ)),
      ← Real.exp_nat_mul]
    rfl
  simp only [Row'.multL]
  calc (2 : ℝ) ^ k * (((max d 6 : ℕ) : ℝ) + 1) ^ (k - 1)
      ≤ Real.exp ((k - 1 : ℕ) * lam d) := h1.trans_eq h2
    _ ≤ Real.exp ((4 * ((k : ℝ) - 1) + C.aStar) * lam d) := by
        apply Real.exp_le_exp.mpr
        have hkc : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ k)]; simp
        rw [hkc]
        have hA := C.aStar_nonneg
        have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
        nlinarith

/-- **Enumeration, GNS Theorem 3.13(1)**: `|P| ≤ d'^{c₁ log d̃ + c₂}` fits `multL`, provided
`c₁ + c₂/log 48 ≤ a + a*/log 2` (the charging exponent `a` is taken large enough; `c₁, c₂` are
GNS's absolute constants). `d' ≥ 2` is the quotient degree. -/
theorem gns_count_le_multL {d d' : ℕ} {c₁ c₂ : ℝ} (hd' : 2 ≤ d') (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hc : c₁ + c₂ / Real.log 48 ≤ C.a + C.aStar / Real.log 2) :
    (d' : ℝ) ^ (c₁ * Real.log (max d 6 : ℕ) + c₂) ≤ Row'.multL C (lam d) (.enumeration d') := by
  have h48 : 0 < Real.log 48 := Real.log_pos (by norm_num)
  have hL := lam_pos d
  have hd'0 : (0 : ℝ) < d' := by exact_mod_cast (by omega : 0 < d')
  have hℓ : 0 ≤ Real.log d' := Real.log_natCast_nonneg _
  have hlog : Real.log (max d 6 : ℕ) ≤ lam d := log_le_lam (by simp) le_rfl
  have h1 : c₁ * Real.log (max d 6 : ℕ) + c₂ ≤ (c₁ + c₂ / Real.log 48) * lam d := by
    have h2 : c₂ ≤ c₂ / Real.log 48 * lam d := by
      rw [div_mul_eq_mul_div, le_div_iff₀ h48]
      exact mul_le_mul_of_nonneg_left (log48_le_lam d) hc₂
    nlinarith [mul_le_mul_of_nonneg_left hlog hc₁]
  simp only [Row'.multL]
  rw [Real.rpow_def_of_pos hd'0]
  apply Real.exp_le_exp.mpr
  have h3 := mul_le_mul_of_nonneg_right hc hL.le
  have h4 : (c₁ * Real.log (max d 6 : ℕ) + c₂) * Real.log d' ≤
      (C.a + C.aStar / Real.log 2) * lam d * Real.log d' :=
    mul_le_mul_of_nonneg_right (h1.trans h3) hℓ
  linarith

/-- **Enumeration, GNS Theorem 3.13(2) with `m ≤ q₀`**: `|P| ≤ Q^k (d̃+1)^{k-1}` with `Q = q₀!`,
and the quotient degree satisfies `d' ≥ 17^k`. Fits `multL`, provided
`(log Q / log 48 + 1) / log 17 ≤ a + a*/log 2`. -/
theorem small_cameron_count_le_multL {d d' k : ℕ} {Q : ℝ} (hQ : 1 ≤ Q) (hk : 1 ≤ k)
    (hd' : (17 : ℝ) ^ k ≤ d')
    (hc : (Real.log Q / Real.log 48 + 1) / Real.log 17 ≤ C.a + C.aStar / Real.log 2) :
    Q ^ k * (((max d 6 : ℕ) : ℝ) + 1) ^ (k - 1) ≤ Row'.multL C (lam d) (.enumeration d') := by
  have h48 : 0 < Real.log 48 := Real.log_pos (by norm_num)
  have h17 : 0 < Real.log 17 := Real.log_pos (by norm_num)
  have hL := lam_pos d
  have hdt := d_tilde_pos d
  have hQ0 : 0 < Q := by linarith
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hk0 : 0 < k := by omega
  have h17k : (0 : ℝ) < 17 ^ k := by positivity
  have hd'0 : (0 : ℝ) < d' := h17k.trans_le hd'
  -- `k log 17 ≤ log d'`
  have hℓ : (k : ℝ) * Real.log 17 ≤ Real.log d' := by
    rw [← Real.log_pow]
    exact Real.log_le_log h17k hd'
  have hℓ0 : 0 ≤ Real.log d' := le_trans (by positivity) hℓ
  have hkk : ((k - 1 : ℕ) : ℝ) ≤ k := by
    have : k - 1 ≤ k := Nat.sub_le _ _
    exact_mod_cast this
  have hlogD : Real.log (((max d 6 : ℕ) : ℝ) + 1) ≤ lam d := by
    unfold lam
    apply Real.log_le_log (by positivity)
    have h6 : (6 : ℝ) ≤ (max d 6 : ℕ) := by exact_mod_cast (le_max_right d 6)
    linarith
  have hlogD0 : 0 ≤ Real.log (((max d 6 : ℕ) : ℝ) + 1) :=
    Real.log_nonneg (by linarith)
  -- `log LHS ≤ k (log Q + Λ)`
  have hL1 : Real.log (Q ^ k * (((max d 6 : ℕ) : ℝ) + 1) ^ (k - 1)) ≤
      (k : ℝ) * (Real.log Q + lam d) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    have h1 : ((k - 1 : ℕ) : ℝ) * Real.log (((max d 6 : ℕ) : ℝ) + 1) ≤ k * lam d :=
      mul_le_mul hkk hlogD hlogD0 (by positivity)
    nlinarith
  have h2 : (k : ℝ) * (Real.log Q + lam d) ≤
      (Real.log Q / Real.log 48 + 1) / Real.log 17 * (lam d * Real.log d') := by
    have hrow : Real.log Q + lam d ≤ (Real.log Q / Real.log 48 + 1) * lam d := by
      have : Real.log Q ≤ Real.log Q / Real.log 48 * lam d := by
        rw [div_mul_eq_mul_div, le_div_iff₀ h48]
        exact mul_le_mul_of_nonneg_left (log48_le_lam d) hlogQ
      linarith
    have hkL : (k : ℝ) ≤ Real.log d' / Real.log 17 := by
      rw [le_div_iff₀ h17]; exact hℓ
    have hprod : 0 ≤ Real.log Q / Real.log 48 + 1 := by positivity
    calc (k : ℝ) * (Real.log Q + lam d)
        ≤ (k : ℝ) * ((Real.log Q / Real.log 48 + 1) * lam d) :=
          mul_le_mul_of_nonneg_left hrow (Nat.cast_nonneg _)
      _ ≤ (Real.log d' / Real.log 17) * ((Real.log Q / Real.log 48 + 1) * lam d) :=
          mul_le_mul_of_nonneg_right hkL (by positivity)
      _ = _ := by ring
  simp only [Row'.multL]
  have hposLHS : 0 < Q ^ k * (((max d 6 : ℕ) : ℝ) + 1) ^ (k - 1) := by positivity
  calc Q ^ k * (((max d 6 : ℕ) : ℝ) + 1) ^ (k - 1)
      = Real.exp (Real.log (Q ^ k * (((max d 6 : ℕ) : ℝ) + 1) ^ (k - 1))) :=
        (Real.exp_log hposLHS).symm
    _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have h3 := mul_le_mul_of_nonneg_right hc (mul_nonneg hL.le hℓ0)
        linarith

/-- **Continuation**: `2 q^{κ+1} ≤ q^a` when `q ≥ 2` and `κ + 2 ≤ a`. The cap row keeps HJ's
multiplicity column. -/
theorem continuation_count_le_multL {q κ : ℕ} (hq : 2 ≤ q) (hκ : (κ : ℝ) + 2 ≤ C.a) :
    2 * (q : ℝ) ^ (κ + 1) ≤ Row'.multL C (lam 0) (.continuation q) := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  simp only [Row'.multL]
  calc 2 * (q : ℝ) ^ (κ + 1) ≤ (q : ℝ) * (q : ℝ) ^ (κ + 1) := by
        apply mul_le_mul_of_nonneg_right hq2; positivity
    _ = (q : ℝ) ^ (κ + 2) := by ring
    _ = (q : ℝ) ^ ((κ : ℝ) + 2) := by rw [← Real.rpow_natCast]; push_cast; rfl
    _ ≤ (q : ℝ) ^ C.a := Real.rpow_le_rpow_of_exponent_le (by linarith) hκ

/-- HJ's example values satisfy the affected-row condition with `b = 32`, `e = 2κ = 128`. -/
theorem family_condition_example {aS : ℝ} (ha : 129 ≤ aS) :
    ((128 : ℕ) : ℝ) + Real.log (32 : ℕ) / Real.log 48 ≤ aS := by
  have h48 : 0 < Real.log 48 := Real.log_pos (by norm_num)
  have h : Real.log (32 : ℕ) / Real.log 48 ≤ 1 := by
    rw [div_le_one h48]
    exact Real.log_le_log (by norm_num) (by norm_num)
  push_cast
  linarith

end GI.DegreeD
