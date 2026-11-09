import QuarticH.Statement

/-! Part 2: arithmetic of the printed parameters. -/

namespace QuarticH

/-- `R = ⌈√(s'/2)⌉` is the least `r ≥ 1` with `s' ≤ 2r²`. -/
theorem R_spec {s' : ℕ} (hs : 1 ≤ s') :
    1 ≤ RParam s' ∧ s' ≤ 2 * RParam s' ^ 2 ∧ 2 * (RParam s' - 1) ^ 2 < s' := by
  have hs1 : (1 : ℝ) ≤ s' := by exact_mod_cast hs
  set x : ℝ := Real.sqrt ((s' : ℝ) / 2) with hx
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hxx : x ^ 2 = (s' : ℝ) / 2 := Real.sq_sqrt (by positivity)
  have hpos : 0 < x := Real.sqrt_pos.2 (by linarith)
  have hR : RParam s' = ⌈x⌉₊ := rfl
  have h1 : 1 ≤ RParam s' := by rw [hR]; exact Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hpos).ne'
  refine ⟨h1, ?_, ?_⟩
  · have hle : x ≤ RParam s' := by rw [hR]; exact Nat.le_ceil x
    have : (s' : ℝ) ≤ 2 * (RParam s' : ℝ) ^ 2 := by nlinarith
    exact_mod_cast this
  · have hlt : (RParam s' : ℝ) < x + 1 := by rw [hR]; exact Nat.ceil_lt_add_one hx0
    have h1' : (1 : ℝ) ≤ RParam s' := by exact_mod_cast h1
    have hc : ((RParam s' - 1 : ℕ) : ℝ) = RParam s' - 1 := by rw [Nat.cast_sub h1]; simp
    have : 2 * ((RParam s' : ℝ) - 1) ^ 2 < s' := by nlinarith
    have : 2 * ((RParam s' - 1 : ℕ) : ℝ) ^ 2 < s' := by rw [hc]; exact this
    exact_mod_cast this

/-- `R` is determined by the bracketing `2(r-1)² < s' ≤ 2r²`. -/
theorem R_eq {s' r : ℕ} (hr : 1 ≤ r) (h1 : s' ≤ 2 * r ^ 2) (h2 : 2 * (r - 1) ^ 2 < s') :
    RParam s' = r := by
  have hs : 1 ≤ s' := by omega
  obtain ⟨hR1, hR2, hR3⟩ := R_spec hs
  rcases lt_trichotomy (RParam s') r with h | h | h
  · have : RParam s' ≤ r - 1 := by omega
    have := Nat.pow_le_pow_left this 2
    omega
  · exact h
  · have : r ≤ RParam s' - 1 := by omega
    have := Nat.pow_le_pow_left this 2
    omega

/-- `m = ⌈(Rd+4)/(s'-1)⌉`: the two inequalities that pin it down. -/
theorem m_spec {s' R d : ℕ} (hs : 2 ≤ s') :
    R * d + 4 ≤ (s' - 1) * mParam s' R d ∧ (s' - 1) * mParam s' R d < R * d + 4 + (s' - 1) := by
  have hq : ((s' - 1 : ℕ) : ℝ) = (s' : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hq0 : (0 : ℝ) < (s' : ℝ) - 1 := by
    have : (2 : ℝ) ≤ s' := by exact_mod_cast hs
    linarith
  have ha0 : 0 ≤ ((R * d + 4 : ℕ) : ℝ) / ((s' : ℝ) - 1) := div_nonneg (Nat.cast_nonneg _) hq0.le
  have hm : mParam s' R d = ⌈((R * d + 4 : ℕ) : ℝ) / ((s' : ℝ) - 1)⌉₊ := rfl
  have hle := Nat.le_ceil (((R * d + 4 : ℕ) : ℝ) / ((s' : ℝ) - 1))
  have hlt := Nat.ceil_lt_add_one ha0
  rw [← hm] at hle hlt
  rw [div_le_iff₀ hq0] at hle
  rw [← sub_lt_iff_lt_add, lt_div_iff₀ hq0] at hlt
  constructor
  · have : ((R * d + 4 : ℕ) : ℝ) ≤ ((s' - 1 : ℕ) : ℝ) * (mParam s' R d : ℝ) := by
      rw [hq]; linarith
    exact_mod_cast this
  · have : ((s' - 1 : ℕ) : ℝ) * (mParam s' R d : ℝ) < ((R * d + 4 : ℕ) : ℝ) + ((s' - 1 : ℕ) : ℝ) := by
      rw [hq]; nlinarith
    exact_mod_cast this

/-- `b = ⌈(d+2)/R⌉`: the two inequalities that pin it down. -/
theorem b_spec {R d : ℕ} (hR : 1 ≤ R) :
    d + 2 ≤ R * bParam R d ∧ R * bParam R d < d + 2 + R := by
  have hq0 : (0 : ℝ) < R := by exact_mod_cast hR
  have ha0 : 0 ≤ ((d + 2 : ℕ) : ℝ) / (R : ℝ) := div_nonneg (Nat.cast_nonneg _) hq0.le
  have hb : bParam R d = ⌈((d + 2 : ℕ) : ℝ) / (R : ℝ)⌉₊ := rfl
  have hle := Nat.le_ceil (((d + 2 : ℕ) : ℝ) / (R : ℝ))
  have hlt := Nat.ceil_lt_add_one ha0
  rw [← hb] at hle hlt
  rw [div_le_iff₀ hq0] at hle
  rw [← sub_lt_iff_lt_add, lt_div_iff₀ hq0] at hlt
  constructor
  · have : ((d + 2 : ℕ) : ℝ) ≤ (R : ℝ) * (bParam R d : ℝ) := by linarith
    exact_mod_cast this
  · have : (R : ℝ) * (bParam R d : ℝ) < ((d + 2 : ℕ) : ℝ) + R := by nlinarith
    exact_mod_cast this

theorem m_eq {s' R d : ℕ} (hs : 2 ≤ s') :
    mParam s' R d = (R * d + 4 + (s' - 2)) / (s' - 1) := by
  obtain ⟨h1, h2⟩ := m_spec (R := R) (d := d) hs
  symm
  apply Nat.div_eq_of_lt_le
  · rw [Nat.mul_comm (mParam s' R d)]; omega
  · rw [add_mul, one_mul, Nat.mul_comm (mParam s' R d)]; omega

theorem b_eq {R d : ℕ} (hR : 1 ≤ R) : bParam R d = (d + 2 + (R - 1)) / R := by
  obtain ⟨h1, h2⟩ := b_spec (d := d) hR
  symm
  apply Nat.div_eq_of_lt_le
  · rw [Nat.mul_comm (bParam R d)]; omega
  · rw [add_mul, one_mul, Nat.mul_comm (bParam R d)]; omega

theorem sPrime_le (s d : ℕ) : 2 * sPrime s d ≤ d := by
  unfold sPrime; omega

/-! ### `s' ≥ 132`: the bound beats `d/4` for `d ≥ 2097` -/

theorem beats_core {s' R m b d : ℕ} (hs' : 132 ≤ s') (hd : 2097 ≤ d)
    (hR1 : 1 ≤ R) (hR2 : s' ≤ 2 * R ^ 2) (hR3 : 2 * (R - 1) ^ 2 < s')
    (hm : (s' - 1) * m < R * d + 4 + (s' - 1)) (hb : R * b < d + 2 + R) :
    4 * (2 * m + b) < d := by
  obtain ⟨x, rfl⟩ : ∃ x, s' = x + 1 := ⟨s' - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hm hR3
  have hR9 : 9 ≤ R := by
    by_contra h
    have : R ≤ 8 := by omega
    have := Nat.pow_le_pow_left this 2
    omega
  rcases Nat.lt_or_ge R 10 with hR | hR
  · have hR9' : R = 9 := by omega
    subst hR9'
    rcases Nat.lt_or_ge x 132 with hx | hx
    · have hx' : x = 131 := by omega
      subst hx'
      have hm' : 131 * m ≤ 9 * d + 134 := by omega
      have hb' : 9 * b ≤ d + 10 := by omega
      rcases Nat.lt_or_ge d 2127 with hd2 | hd2
      · interval_cases d <;> omega
      · omega
    · have hxm : x * m ≤ 9 * d + 3 + x := by omega
      have hb' : 9 * b ≤ d + 10 := by omega
      have hxmZ : (x : ℤ) * m ≤ 9 * d + 3 + x := by exact_mod_cast hxm
      have hbZ : (9 : ℤ) * b ≤ d + 10 := by exact_mod_cast hb'
      have hdZ : (2097 : ℤ) ≤ d := by exact_mod_cast hd
      have hxZ : (132 : ℤ) ≤ x := by exact_mod_cast hx
      have e3 := mul_le_mul_of_nonneg_left hbZ (by positivity : (0 : ℤ) ≤ 4 * x)
      have e4 := mul_nonneg (by linarith : (0 : ℤ) ≤ d - 2097) (by linarith : (0 : ℤ) ≤ 5 * x - 648)
      have key : (9 : ℤ) * x * (8 * m + 4 * b) < 9 * x * d := by nlinarith
      have := lt_of_mul_lt_mul_left key (by positivity)
      have : ((4 * (2 * m + b) : ℕ) : ℤ) < d := by push_cast; linarith
      exact_mod_cast this
  · obtain ⟨k, rfl⟩ : ∃ k, R = k + 10 := ⟨R - 10, by omega⟩
    simp only [show k + 10 - 1 = k + 9 by omega] at hR3
    have hxm : x * m ≤ (k + 10) * d + 3 + x := by omega
    have hb' : (k + 10) * b ≤ d + 1 + (k + 10) := by omega
    have hx : 2 * (k + 9) ^ 2 ≤ x := by omega
    -- work in `ℤ`
    have hxZ : (2 * ((k : ℤ) + 9) ^ 2) ≤ x := by exact_mod_cast hx
    have hxmZ : (x : ℤ) * m ≤ ((k : ℤ) + 10) * d + 3 + x := by exact_mod_cast hxm
    have hbZ : ((k : ℤ) + 10) * b ≤ d + 1 + (k + 10) := by exact_mod_cast hb'
    have hdZ : (2097 : ℤ) ≤ d := by exact_mod_cast hd
    have hk0 : (0 : ℤ) ≤ k := Nat.cast_nonneg k
    have hm0 : (0 : ℤ) ≤ m := Nat.cast_nonneg m
    have hb0 : (0 : ℤ) ≤ b := Nat.cast_nonneg b
    set c : ℤ := ((k : ℤ) + 6) * x - 8 * ((k : ℤ) + 10) ^ 2 with hc
    have hcpos : 0 < c := by
      have := mul_le_mul_of_nonneg_left hxZ (by linarith : (0 : ℤ) ≤ k + 6)
      nlinarith [sq_nonneg (k : ℤ), mul_nonneg hk0 (sq_nonneg (k : ℤ))]
    have hdc : 2097 * c ≤ d * c := mul_le_mul_of_nonneg_right hdZ hcpos.le
    have hrhs : 24 * ((k : ℤ) + 10) + 12 * ((k : ℤ) + 10) * x + 4 * x < 2097 * c := by
      have := mul_le_mul_of_nonneg_left hxZ (by linarith : (0 : ℤ) ≤ 2085 * k + 12458)
      nlinarith [sq_nonneg (k : ℤ), mul_nonneg hk0 (sq_nonneg (k : ℤ))]
    have e2 := mul_le_mul_of_nonneg_left hxmZ (by linarith : (0 : ℤ) ≤ 8 * (k + 10))
    have e3 := mul_le_mul_of_nonneg_left hbZ (by positivity : (0 : ℤ) ≤ 4 * x)
    have key : ((k : ℤ) + 10) * x * (8 * m + 4 * b) < ((k : ℤ) + 10) * x * d := by
      nlinarith
    have hpos : (0 : ℤ) < ((k : ℤ) + 10) * x := by
      have : (0 : ℤ) < x := by nlinarith
      positivity
    have := lt_of_mul_lt_mul_left key hpos.le
    have : ((4 * (2 * m + b) : ℕ) : ℤ) < d := by push_cast; linarith
    exact_mod_cast this

theorem beatsQuarter_proof : BeatsQuarter := by
  intro s d hs hd
  have hs' : 132 ≤ sPrime s d := by unfold sPrime; omega
  obtain ⟨hR1, hR2, hR3⟩ := R_spec (by omega : 1 ≤ sPrime s d)
  have hm := (m_spec (R := RParam (sPrime s d)) (d := d) (by omega : 2 ≤ sPrime s d)).2
  have hb := (b_spec (d := d) hR1).2
  exact beats_core hs' hd hR1 hR2 hR3 hm hb

/-! ### `s' ≤ 130`: never below `d/4` -/

/-- The per-`R` check `R(s'-1) ≤ 8R² + 4(s'-1)` for `2 ≤ s' ≤ 130`. -/
theorem slope_ge {s' R : ℕ} (hs1 : 2 ≤ s') (hs2 : s' ≤ 130)
    (hR1 : 1 ≤ R) (hR2 : s' ≤ 2 * R ^ 2) (hR3 : 2 * (R - 1) ^ 2 < s') :
    R * (s' - 1) ≤ 8 * R ^ 2 + 4 * (s' - 1) := by
  have hR9 : R ≤ 9 := by
    by_contra h
    have : 9 ≤ R - 1 := by omega
    have := Nat.pow_le_pow_left this 2
    omega
  interval_cases R <;> omega

theorem neverBeats_proof : NeverBeatsLe130 := by
  intro s d hs2 hs130 hd
  set s' := sPrime s d with hs'def
  have hs'2 : 2 ≤ s' := by simp only [hs'def, sPrime]; omega
  have hs'130 : s' ≤ 130 := by simp only [hs'def, sPrime]; omega
  obtain ⟨hR1, hR2, hR3⟩ := R_spec (by omega : 1 ≤ s')
  set R := RParam s'
  have hm := (m_spec (R := R) (d := d) hs'2).1
  have hb := (b_spec (d := d) hR1).1
  have hsl := slope_ge hs'2 hs'130 hR1 hR2 hR3
  show d < 4 * (2 * mParam s' R d + bParam R d)
  set m := mParam s' R d
  set b := bParam R d
  obtain ⟨x, hx⟩ : ∃ x, s' - 1 = x := ⟨_, rfl⟩
  rw [hx] at hm hsl
  have hx1 : 1 ≤ x := by omega
  have key : R * x * d < R * x * (4 * (2 * m + b)) := by
    have e1 : R * x * (4 * (2 * m + b)) = 8 * R * (x * m) + 4 * x * (R * b) := by ring
    have e2 : 8 * R * (R * d + 4) ≤ 8 * R * (x * m) := Nat.mul_le_mul_left _ hm
    have e3 : 4 * x * (d + 2) ≤ 4 * x * (R * b) := Nat.mul_le_mul_left _ hb
    have e4 : R * x * d ≤ (8 * R ^ 2 + 4 * x) * d := Nat.mul_le_mul_right _ hsl
    nlinarith
  exact Nat.lt_of_mul_lt_mul_left key

/-! ### The limit `2R/(s'-1) + 1/R` -/

theorem limit_iff_nat {s' : ℕ} (hs : 2 ≤ s') :
    8 * RParam s' ^ 2 + 4 * (s' - 1) < RParam s' * (s' - 1) ↔ 131 ≤ s' := by
  obtain ⟨hR1, hR2, hR3⟩ := R_spec (by omega : 1 ≤ s')
  set R := RParam s'
  constructor
  · intro h
    by_contra hlt
    have := slope_ge hs (by omega) hR1 hR2 hR3
    omega
  · intro h131
    obtain ⟨x, rfl⟩ : ∃ x, s' = x + 1 := ⟨s' - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hR3 ⊢
    have hR9 : 9 ≤ R := by
      by_contra h
      have : R ≤ 8 := by omega
      have := Nat.pow_le_pow_left this 2
      omega
    rcases Nat.lt_or_ge R 10 with hR | hR
    · have : R = 9 := by omega
      rw [this]; omega
    · obtain ⟨k, hk⟩ : ∃ k, R = k + 10 := ⟨R - 10, by omega⟩
      rw [hk] at hR3 ⊢
      simp only [show k + 10 - 1 = k + 9 by omega] at hR3
      have hx : 2 * (k + 9) ^ 2 ≤ x := by omega
      have := Nat.mul_le_mul_left (k + 6) hx
      nlinarith [Nat.zero_le k, Nat.zero_le (k * k), Nat.zero_le (k * k * k)]

theorem limitThreshold_proof : LimitThreshold := by
  intro s' hs
  have hR1 := (R_spec (by omega : 1 ≤ s')).1
  set R := RParam s'
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR1
  have hx : ((s' - 1 : ℕ) : ℝ) = (s' : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hx0 : (0 : ℝ) < (s' : ℝ) - 1 := by
    have : (2 : ℝ) ≤ s' := by exact_mod_cast hs
    linarith
  rw [← limit_iff_nat hs]
  have hreal : 2 * (R : ℝ) / ((s' : ℝ) - 1) + 1 / R = (2 * R ^ 2 + ((s' : ℝ) - 1)) / (R * ((s' : ℝ) - 1)) := by
    field_simp
  rw [hreal, div_lt_iff₀ (by positivity)]
  constructor
  · intro h
    have : ((8 * R ^ 2 + 4 * (s' - 1) : ℕ) : ℝ) < ((R * (s' - 1) : ℕ) : ℝ) := by
      push_cast [hx]; nlinarith
    exact_mod_cast this
  · intro h
    have : ((8 * R ^ 2 + 4 * (s' - 1) : ℕ) : ℝ) < ((R * (s' - 1) : ℕ) : ℝ) := by exact_mod_cast h
    push_cast [hx] at this
    nlinarith

theorem rValues_proof : RValues := by
  refine ⟨R_eq (by norm_num) (by norm_num) (by norm_num),
    R_eq (by norm_num) (by norm_num) (by norm_num), by norm_num, by norm_num, by norm_num⟩

theorem sharpAt2096_proof : SharpAt2096 := by
  have hs : sPrime 132 2096 = 132 := by decide
  have hR : RParam 132 = 9 := R_eq (by norm_num) (by norm_num) (by norm_num)
  simp only [SharpAt2096, tP, mP, bP, hs, hR, m_eq (by norm_num : 2 ≤ 132),
    b_eq (by norm_num : 1 ≤ 9)]

theorem sharpAt3144_proof : SharpAt3144 := by
  simp only [SharpAt3144, m_eq (by norm_num : 2 ≤ 130), b_eq (by norm_num : 1 ≤ 8)]
  norm_num

/-- With `R = 8` at `s' = 130`: below `d/4` from `d = 3145` on. -/
theorem repaired_arith {d : ℕ} (hd : 3145 ≤ d) :
    4 * (2 * mParam 130 8 d + bParam 8 d) < d := by
  have hm := (m_spec (s' := 130) (R := 8) (d := d) (by norm_num)).2
  have hb := (b_spec (R := 8) (d := d) (by norm_num)).2
  have hm' : 129 * mParam 130 8 d ≤ 8 * d + 131 := by clear hb; omega
  have hb' : 8 * bParam 8 d ≤ d + 9 := by clear hm hm'; omega
  generalize mParam 130 8 d = m at hm'
  generalize bParam 8 d = b at hb'
  rcases Nat.lt_or_ge d 3258 with hd2 | hd2
  · interval_cases d <;> omega
  · omega

end QuarticH
