import QuarticH.Statement

/-! Basic facts: permuting arguments over `𝔽₂`, linearity in a slot, pair matrices, kernel counts. -/

namespace QuarticH

open Module Matrix

variable {d : ℕ}

theorem neg_self (x : V d) : -x = x := funext fun _ => ZMod.neg_eq_self_mod_two _

theorem add_self (x : V d) : x + x = 0 := funext fun i => CharTwo.add_self_eq_zero (x i)

/-- Over `𝔽₂` an alternating form is symmetric under any transposition of arguments. -/
theorem swap_eq (τ : AltForm4 d) (v : Fin 4 → V d) (i j : Fin 4) :
    τ (v ∘ Equiv.swap i j) = τ v := by
  by_cases h : i = j
  · subst h; simp
  · rw [τ.map_swap v h, ZMod.neg_eq_self_mod_two]

theorem sw01 (τ : AltForm4 d) (a b c e : V d) : τ ![a, b, c, e] = τ ![b, a, c, e] := by
  rw [← swap_eq τ ![a, b, c, e] 0 1]; congr 1; funext k; fin_cases k <;> rfl

theorem sw12 (τ : AltForm4 d) (a b c e : V d) : τ ![a, b, c, e] = τ ![a, c, b, e] := by
  rw [← swap_eq τ ![a, b, c, e] 1 2]; congr 1; funext k; fin_cases k <;> rfl

theorem sw23 (τ : AltForm4 d) (a b c e : V d) : τ ![a, b, c, e] = τ ![a, b, e, c] := by
  rw [← swap_eq τ ![a, b, c, e] 2 3]; congr 1; funext k; fin_cases k <;> rfl

theorem sw02 (τ : AltForm4 d) (a b c e : V d) : τ ![a, b, c, e] = τ ![c, b, a, e] := by
  rw [← swap_eq τ ![a, b, c, e] 0 2]; congr 1; funext k; fin_cases k <;> rfl

theorem sw13 (τ : AltForm4 d) (a b c e : V d) : τ ![a, b, c, e] = τ ![a, e, c, b] := by
  rw [← swap_eq τ ![a, b, c, e] 1 3]; congr 1; funext k; fin_cases k <;> rfl

theorem zero_of_eq23 (τ : AltForm4 d) (a b c : V d) : τ ![a, b, c, c] = 0 :=
  τ.map_eq_zero_of_eq ![a, b, c, c] (i := 2) (j := 3) rfl (by decide)

/-- Additivity in the last slot (via `contr3`). -/
theorem add3 (τ : AltForm4 d) (a b c x y : V d) :
    τ ![a, b, c, x + y] = τ ![a, b, c, x] + τ ![a, b, c, y] := by
  simp only [← contr3_apply, map_add]

theorem add2 (τ : AltForm4 d) (a b c x y : V d) :
    τ ![a, b, x + y, c] = τ ![a, b, x, c] + τ ![a, b, y, c] := by
  rw [sw23 τ a b (x + y) c, add3, ← sw23 τ a b x c, ← sw23 τ a b y c]

theorem add1 (τ : AltForm4 d) (a b c x y : V d) :
    τ ![a, x + y, b, c] = τ ![a, x, b, c] + τ ![a, y, b, c] := by
  rw [sw13 τ a (x + y) b c, add3, ← sw13 τ a x b c, ← sw13 τ a y b c]

/-- Expansion in the last slot. -/
theorem slot3_sum (τ : AltForm4 d) (a b c x : V d) :
    τ ![a, b, c, x] = ∑ j, τ ![a, b, c, Pi.single j 1] * x j := by
  rw [← contr3_apply, LinearMap.pi_apply_eq_sum_univ (contr3 τ a b c) x]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hs : (fun k => if j = k then (1 : ZMod 2) else 0) = Pi.single j 1 := by
    funext k; simp [Pi.single_apply, eq_comm]
  rw [smul_eq_mul, mul_comm, hs, contr3_apply]

theorem slot2_sum (τ : AltForm4 d) (a b c x : V d) :
    τ ![a, b, x, c] = ∑ j, τ ![a, b, Pi.single j 1, c] * x j := by
  rw [sw23, slot3_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [← sw23]

theorem mulVec_pairMatrix (τ : AltForm4 d) (a c v : V d) (i : Fin d) :
    (pairMatrix τ a c *ᵥ v) i = τ ![a, c, Pi.single i 1, v] := by
  simp only [mulVec, dotProduct, pairMatrix, of_apply]
  rw [slot3_sum]

theorem dotProduct_mulVec_pairMatrix (τ : AltForm4 d) (a c x v : V d) :
    x ⬝ᵥ (pairMatrix τ a c *ᵥ v) = τ ![a, c, x, v] := by
  rw [slot2_sum]
  simp only [dotProduct, mulVec_pairMatrix]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- `|ker M| · 2^{rank M} = 2^d` for a matrix with `d` columns over `𝔽₂`. -/
theorem card_ker_mul_pow_rank {ι : Type*} [Fintype ι] (M : Matrix ι (Fin d) (ZMod 2)) :
    (Finset.univ.filter fun v : V d => M *ᵥ v = 0).card * 2 ^ M.rank = 2 ^ d := by
  have h1 : (Finset.univ.filter fun v : V d => M *ᵥ v = 0).card =
      Nat.card (LinearMap.ker M.mulVecLin) := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun v => by simp)
  have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker M.mulVecLin)
  have h3 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [h1, h2, Nat.card_zmod, Matrix.rank, ← pow_add, add_comm, h3, Module.finrank_fin_fun]

/-- Rank lower bound gives a kernel upper bound. -/
theorem card_ker_le {ι : Type*} [Fintype ι] (M : Matrix ι (Fin d) (ZMod 2)) {s : ℕ}
    (hs : s ≤ M.rank) :
    (Finset.univ.filter fun v : V d => M *ᵥ v = 0).card * 2 ^ s ≤ 2 ^ d := by
  rw [← card_ker_mul_pow_rank M]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hs)

/-- Over `𝔽₂`, `w, l` are independent iff `w ≠ 0`, `l ≠ 0`, `w ≠ l`. -/
theorem linIndep_pair {w l : V d} (hw : w ≠ 0) (hl : l ≠ 0) (hwl : w ≠ l) :
    LinearIndependent (ZMod 2) ![w, l] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases h01 a with rfl | rfl <;> rcases h01 b with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · simp at hab; exact absurd hab hl
  · simp at hab; exact absurd hab hw
  · simp only [one_smul] at hab
    exact absurd (by rw [← sub_eq_zero, sub_eq_add_neg, neg_self]; exact hab) hwl

/-- `s ≤ s(τ)` gives `s ≤ rank` for every independent pair (also when there is none). -/
theorem le_rank_of_le_sInv {τ : AltForm4 d} {s : ℕ} (h : s ≤ sInv τ) (w l : V d)
    (hwl : LinearIndependent (ZMod 2) ![w, l]) : s ≤ (pairMatrix τ w l).rank :=
  h.trans (Nat.sInf_le ⟨w, l, hwl, rfl⟩)

end QuarticH
