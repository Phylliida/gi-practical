import DegreeD.Luks.Graph
import DegreeD.M.NodeBoundOne

/-!
# GI of maximum degree `d`, connected graphs, at the level of runs

**Warning.** `graphIso_connected_weak` and `graphIso_connected_final_weak` say only that *some* script
has the stated value: the script is chosen after `X` and `Y`, and `Script.done` may carry any value,
so `done {iso set}` satisfies them trivially (docs/vacuity-graphIso-final.lean.txt). They are kept
only because the run bound below is used by the new statement. The theorem that means something
is `graphIso_reduction` in `DegreeD/Luks/Statement.lean`, about the named `luksScript`.

`graphIso_connected_weak`: from the conclusion of the Stage-1 theorem (`Stage1Conclusion`,
which `degreeD_stage1_cited` provides), for all connected graphs `X, Y` on `Fin n` of maximum
degree at most `d`, there is a script of `Solve` calls and a run of it (`M.Exec`) whose exact value is
the isomorphism set of `X` and `Y`, every call of which is a string-isomorphism instance on `≤ 3 n⁴`
positions with group in `Γ̂_d`, with total weight `exp(C log(d+2) log(n+2))`.
-/

namespace GI.DegreeD.Luks

open Equiv Equiv.Perm GI.Algorithm
open scoped Classical Pointwise

set_option linter.unusedSectionVars false

variable {P : Params}

/-- The conclusion of the Stage-1 degree-`d` theorem, as produced by `degreeD_stage1_cited`. -/
def Stage1Conclusion (P : Params) (w : M.Node P → ℝ) : Prop :=
  ∃ cσ C' : ℝ, 0 ≤ cσ ∧ ∀ (d : ℕ) {Ω C : Type} [Finite Ω] (S : State Ω C),
      GammaHat d S.G →
      (∃ r : M.Run P .solve S none S.answer, r.RootsOK cσ (max d 6)) ∧
      ∀ {A : Set (Perm Ω)} (r : M.Run P .solve S none A), r.RootsOK cσ (max d 6) →
        (A = {g | g ∈ S.G ∧ ∀ v ∈ S.dom, S.y (g v) = S.x v} ∧
          (A = ∅ ∨ ∃ t ∈ S.G, A = t • (autGroup S.G S.dom S.dom_inv S.x : Set (Perm Ω)))) ∧
        r.total w ≤ Real.exp (C' * (lam d * Real.log ((S.size : ℝ) + 2)))

/-! ### Numerics -/

theorem lam_le_log (d : ℕ) : lam d ≤ 6 * Real.log ((d : ℝ) + 2) := by
  have h : ((8 * (max d 6 : ℕ) : ℕ) : ℝ) ≤ (((d + 2) ^ 6 : ℕ) : ℝ) := by
    have h : 8 * max d 6 ≤ (d + 2) ^ 6 := by
      rcases le_total d 6 with h | h
      · rw [max_eq_right h]
        calc 8 * 6 ≤ 2 ^ 6 := by norm_num
          _ ≤ (d + 2) ^ 6 := Nat.pow_le_pow_left (by omega) 6
      · rw [max_eq_left h]
        have h1 : (d + 2) * (d + 2) ≤ (d + 2) ^ 6 := by
          calc (d + 2) * (d + 2) = (d + 2) ^ 2 := by ring
            _ ≤ (d + 2) ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
        nlinarith
    exact_mod_cast h
  have hpos : (0 : ℝ) < 8 * (max d 6 : ℕ) := by
    have : (0 : ℝ) < (max d 6 : ℕ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num) (le_max_right d 6))
    linarith
  have h2 : lam d ≤ Real.log (((d + 2 : ℕ) : ℝ) ^ 6) := by
    unfold lam
    apply Real.log_le_log hpos
    push_cast at h ⊢
    exact h
  rw [Real.log_pow] at h2
  push_cast at h2
  linarith

theorem card_om (n q : ℕ) :
    Nat.card (Om (Fin n) q) = n + (n * q + n * q * (n * q)) := by
  simp [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]

/-- The cost arithmetic. -/
theorem final_bound {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (n d q N : ℕ) (hq : q ≤ n) (hN : N ≤ (n + 2) ^ 5) :
    let B := n + (n * q + n * q * (n * q))
    (N : ℝ) * Real.exp (C₀ * (lam d * Real.log ((B : ℝ) + 2))) ≤
      Real.exp ((10 + 30 * C₀) * (Real.log ((d : ℝ) + 2) * Real.log ((n : ℝ) + 2))) := by
  intro B
  have hB : B + 2 ≤ (n + 2) ^ 5 := by
    have h1 : n * q ≤ n * n := Nat.mul_le_mul_left _ hq
    have h2 : n * q * (n * q) ≤ n * n * (n * n) := Nat.mul_le_mul h1 h1
    have h3 : n + (n * n + n * n * (n * n)) + 2 ≤ (n + 2) ^ 5 := by nlinarith [sq_nonneg n]
    show n + (n * q + n * q * (n * q)) + 2 ≤ _
    omega
  have hn2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    linarith
  have hL : Real.log 2 ≤ Real.log ((n : ℝ) + 2) := Real.log_le_log (by norm_num) hn2
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  set L := Real.log ((n : ℝ) + 2) with hLdef
  set M := Real.log ((d : ℝ) + 2) with hMdef
  have hd2 : (2 : ℝ) ≤ (d : ℝ) + 2 := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    linarith
  have hMge : Real.log 2 ≤ M := Real.log_le_log (by norm_num) hd2
  have hL0 : 0 ≤ L := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hlam : lam d ≤ 6 * M := lam_le_log d
  have hlam1 : (1 : ℝ) ≤ lam d := one_le_lam d
  have hlogB : Real.log ((B : ℝ) + 2) ≤ 5 * L := by
    have h : ((B : ℝ) + 2) ≤ (((n + 2) ^ 5 : ℕ) : ℝ) := by exact_mod_cast hB
    have hpos : (0 : ℝ) < (B : ℝ) + 2 := by
      have : (0 : ℝ) ≤ B := Nat.cast_nonneg _
      linarith
    have h2 := Real.log_le_log hpos h
    rw [Nat.cast_pow, Real.log_pow] at h2
    push_cast at h2
    linarith
  have hlogB0 : 0 ≤ Real.log ((B : ℝ) + 2) :=
    Real.log_nonneg (by have : (0 : ℝ) ≤ B := Nat.cast_nonneg _; linarith)
  -- the main inequality of the exponent
  have hmain : C₀ * (lam d * Real.log ((B : ℝ) + 2)) ≤ 30 * C₀ * (M * L) := by
    have h1 : lam d * Real.log ((B : ℝ) + 2) ≤ (6 * M) * (5 * L) :=
      mul_le_mul hlam hlogB hlogB0 (by linarith)
    have := mul_le_mul_of_nonneg_left h1 hC₀
    nlinarith
  have hn3 : (N : ℝ) ≤ Real.exp (5 * L) := by
    have hexp : Real.exp L = (n : ℝ) + 2 := Real.exp_log (by linarith)
    have h3 : Real.exp (5 * L) = ((n : ℝ) + 2) ^ 5 := by
      rw [← hexp, ← Real.exp_nat_mul]
      norm_num
    rw [h3]
    exact_mod_cast hN
  calc (N : ℝ) * Real.exp (C₀ * (lam d * Real.log ((B : ℝ) + 2)))
      ≤ Real.exp (5 * L) * Real.exp (30 * C₀ * (M * L)) := by
        apply mul_le_mul hn3 (Real.exp_le_exp.2 hmain) (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (5 * L + 30 * C₀ * (M * L)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((10 + 30 * C₀) * (M * L)) := by
        apply Real.exp_le_exp.2
        have hMl : (1 / 2 : ℝ) ≤ M := by linarith
        nlinarith [mul_nonneg hM0 hL0, mul_nonneg (by linarith : (0 : ℝ) ≤ M - 1 / 2) hL0]

/-! ### The theorem -/

variable {w : M.Node P → ℝ}

/-- **Weak form; vacuous as stated.** `s` is existentially quantified after `X, Y`, and a script may
be `Script.done` of any value (`docs/vacuity-graphIso-final.lean.txt`), so the conclusion holds with
`C = 0` by the script with no calls. Do not cite this; use `graphIso_reduction`. The proof does build the
real reduction; the statement does not expose it. -/
theorem graphIso_connected_weak (h : Stage1Conclusion P w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n d : ℕ) (X Y : SimpleGraph (Fin n)),
      X.Connected → Y.Connected → (∀ v, Nat.card (X.neighborSet v) ≤ d) →
      (∀ v, Nat.card (Y.neighborSet v) ≤ d) →
      ∃ (s : Script (Set (Perm (Fin n)))) (e : M.Exec P s s.evalExact),
        s.evalExact = {g | ∀ a b, X.Adj a b ↔ Y.Adj (g a) (g b)} ∧
        s.CallsExact (fun {_ _} m T => m = .solve ∧ GammaHat d T.G ∧ (T.size : ℝ) ≤ 3 * (n : ℝ) ^ 4) ∧
        e.total w ≤ Real.exp (C * (Real.log ((d : ℝ) + 2) * Real.log ((n : ℝ) + 2))) := by
  obtain ⟨cσ, C', hcσ, hS⟩ := h
  set C₀ := max C' 0
  refine ⟨10 + 30 * C₀, by have := le_max_right C' 0; simp only [C₀]; linarith, ?_⟩
  intro n d X Y hXc hYc hXd hYd
  by_cases hE : ∃ u v, X.Adj u v
  · obtain ⟨u, v, huv⟩ := hE
    set q := min d n with hq
    have hqd : q ≤ d := min_le_left _ _
    have hqn : q ≤ n := min_le_right _ _
    have hcardle : ∀ {G : SimpleGraph (Fin n)} (l : Fin n), Nat.card (G.neighborSet l) ≤ n := by
      intro G l
      calc Nat.card (G.neighborSet l) ≤ Nat.card (Fin n) :=
            Nat.card_le_card_of_injective _ Subtype.val_injective
        _ = n := by simp
    have hXq : ∀ l, Nat.card (X.neighborSet l) ≤ q := fun l => le_min (hXd l) (hcardle l)
    have hYq : ∀ l, Nat.card (Y.neighborSet l) ≤ q := fun l => le_min (hYd l) (hcardle l)
    set B := Nat.card (Om (Fin n) q) with hB
    have hBval : B = n + (n * q + n * q * (n * q)) := by rw [hB, card_om]
    have hsz : (B : ℝ) ≤ 3 * (n : ℝ) ^ 4 := by
      have h1 : n * q ≤ n * n := Nat.mul_le_mul_left _ hqn
      have h2 : n * q * (n * q) ≤ n * n * (n * n) := Nat.mul_le_mul h1 h1
      have hn : 1 ≤ n := by
        haveI := hXc.nonempty
        exact Fintype.card_pos (α := Fin n) |>.trans_eq (Fintype.card_fin n)
      have h3 : B ≤ 3 * n ^ 4 := by
        rw [hBval]
        have h5 : n ≤ n * n * (n * n) := by nlinarith [Nat.le_mul_self n, Nat.le_mul_self (n * n)]
        have h6 : n * n ≤ n * n * (n * n) := Nat.le_mul_self _
        calc n + (n * q + n * q * (n * q)) ≤ n * n * (n * n) + (n * n * (n * n) + n * n * (n * n)) := by
              have : n * q ≤ n * n * (n * n) := le_trans h1 h6
              omega
          _ = 3 * n ^ 4 := by ring
      exact_mod_cast h3
    have hXR : ∀ w, edgeLvl X u v w ≤ Fintype.card (Fin n) := fun w => edgeLvl_lt_card hXc w
    have hYR : ∀ (p : Fin n × Fin n) w, edgeLvl Y p.1 p.2 w ≤ Fintype.card (Fin n) :=
      fun p w => edgeLvl_lt_card hYc w
    obtain ⟨hc1, hc2, hc3⟩ := connScript_spec (q := q) (R := Fintype.card (Fin n)) hXc hYc hXq hYq (Or.inr huv) hXR hYR
    set S₀ := connScript (q := q) hXc hYc hXq hYq u v (Fintype.card (Fin n)) with hS₀
    let s : Script (Set (Perm (Fin n))) :=
      S₀.bind fun S => Script.done {g : Perm (Fin n) | (g : Fin n → Fin n) ∈ S}
    have hcalls_q : s.CallsExact (CallOK q B) := Script.callsExact_bind _ _ hc1 trivial
    have hcalls_d : s.CallsExact (CallOK d B) := hcalls_q.mono fun m T ⟨hm, hf, hg, hs⟩ =>
      ⟨hm, hf, by haveI := hf; exact hg.mono hqd, hs⟩
    have hnum : s.numCalls ≤ n ^ 3 := by
      show (S₀.bind _).numCalls ≤ _
      rw [Script.numCalls_bind]
      simp only [Script.numCalls, add_zero]
      calc S₀.numCalls ≤ Fintype.card (Fin n × Fin n) * Fintype.card (Fin n) := hc2
        _ = n ^ 3 := by simp; ring
    have hval : s.evalExact = {g | ∀ a b, X.Adj a b ↔ Y.Adj (g a) (g b)} := by
      show (S₀.bind _).evalExact = _
      rw [Script.evalExact_bind]
      show {g : Perm (Fin n) | (g : Fin n → Fin n) ∈ S₀.evalExact} = _
      rw [hc3]
      ext g
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨e, he⟩ a b
        rw [← he]
        exact e.map_rel_iff.symm
      · intro hg
        exact ⟨{ toEquiv := g, map_rel_iff' := fun {a b} => (hg a b).symm }, rfl⟩
    -- the runs
    have hruns : ∀ {Ω C : Type} [Finite Ω] (S : State Ω C), GammaHat d S.G →
        ∃ r : M.Run P .solve S none S.answer, r.RootsOK cσ (max d 6) :=
      fun S hg => (hS d S hg).1
    obtain ⟨e, he⟩ := exec_of_calls (d := d) (D := max d 6) (le_max_left _ _) hruns s B hcalls_d
    refine ⟨s, e, hval, ?_, ?_⟩
    · exact hcalls_d.mono fun m T ⟨hm, _, hg, hs⟩ => ⟨hm, hg, le_trans (by exact_mod_cast hs) hsz⟩
    · set K := Real.exp (C₀ * (lam d * Real.log ((B : ℝ) + 2))) with hK
      have hbound := exec_total_le (K := K) (p := CallOK d B) (cσ := cσ) (D := max d 6)
        (w := w) ?_ s e he hcalls_d
      · have hK0 : 0 ≤ K := (Real.exp_pos _).le
        have hfb := final_bound (C₀ := C₀) (le_max_right _ _) n d q (n ^ 5) hqn
          (Nat.pow_le_pow_left (by omega) 5)
        simp only at hfb
        rw [← hBval] at hfb
        have hle35 : n ^ 3 ≤ n ^ 5 := by
          rcases Nat.eq_zero_or_pos n with h0 | h0
          · subst h0; simp
          · exact Nat.pow_le_pow_right h0 (by norm_num)
        calc e.total w ≤ (s.numCalls : ℝ) * K := hbound
          _ ≤ ((n ^ 5 : ℕ) : ℝ) * K := by
            apply mul_le_mul_of_nonneg_right _ hK0
            exact_mod_cast hnum.trans hle35
          _ ≤ _ := hfb
      · intro Ω' Cc m T r hp hr
        obtain ⟨rfl, hf, hg, hs⟩ := hp
        haveI := hf
        have h1 := (hS d T hg).2 r hr
        refine h1.2.trans (Real.exp_le_exp.2 ?_)
        have hl0 : 0 ≤ Real.log ((T.size : ℝ) + 2) :=
          Real.log_nonneg (by have : (0 : ℝ) ≤ T.size := Nat.cast_nonneg _; linarith)
        have hl1 : Real.log ((T.size : ℝ) + 2) ≤ Real.log ((B : ℝ) + 2) :=
          Real.log_le_log (by have : (0 : ℝ) ≤ T.size := Nat.cast_nonneg _; linarith) (by
            have : (T.size : ℝ) ≤ B := by exact_mod_cast hs
            linarith)
        have hlam := lam_pos d
        calc C' * (lam d * Real.log ((T.size : ℝ) + 2))
            ≤ C₀ * (lam d * Real.log ((T.size : ℝ) + 2)) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hlam.le hl0)
          _ ≤ C₀ * (lam d * Real.log ((B : ℝ) + 2)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hl1 hlam.le) (le_max_right _ _)
  · -- no edge: `n ≤ 1`, and the isomorphism set is computed directly
    refine ⟨Script.done {g | ∀ a b, X.Adj a b ↔ Y.Adj (g a) (g b)}, M.Exec.done _, rfl, trivial, ?_⟩
    exact le_trans (le_of_eq (M.Exec.total_done w _)) (Real.exp_pos _).le

/-- **Weak form; vacuous as stated** (see `graphIso_connected_weak`). `graphIso_connected_weak` from the
cited results. Use `graphIso_reduction` in `DegreeD/Luks/Statement.lean`. -/
theorem graphIso_connected_final_weak (hcite : GI.Cited.TransitiveAffected)
    (hK : GI.Cited.KaryCoherentRefinement) (h6 : GI.Cited.SixTransitiveContainsAlt)
    (hDL : GI.Cited.DesignLemma) (hAut : GI.Cited.AutCardLeSq)
    (hLie : GI.Cited.SimpleValuationDegree) :
    ∃ (P : Params) (C : ℝ), 0 ≤ C ∧ ∀ (n d : ℕ) (X Y : SimpleGraph (Fin n)),
      X.Connected → Y.Connected → (∀ v, Nat.card (X.neighborSet v) ≤ d) →
      (∀ v, Nat.card (Y.neighborSet v) ≤ d) →
      ∃ (s : Script (Set (Perm (Fin n)))) (e : M.Exec P s s.evalExact),
        s.evalExact = {g | ∀ a b, X.Adj a b ↔ Y.Adj (g a) (g b)} ∧
        s.CallsExact (fun {_ _} m T => m = .solve ∧ GammaHat d T.G ∧ (T.size : ℝ) ≤ 3 * (n : ℝ) ^ 4) ∧
        e.total (fun _ => (1 : ℝ)) ≤ Real.exp (C * (Real.log ((d : ℝ) + 2) * Real.log ((n : ℝ) + 2))) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hG⟩ := M.gnsPrimitive
  obtain ⟨P, cc, hP, hκ, hc, hαγ, hbase, h4, hab, hq, hcc, hA, hT, hγ, hPa, ha198⟩ :=
    M.params_full hcite c₁ c₂
  have h5 : (5 : ℝ) ≤ P.a := by rw [hPa]; linarith
  have h197 : (0 : ℝ) ≤ P.a := by linarith
  refine ⟨P, ?_⟩
  exact graphIso_connected_weak (M.degreeD_stage1_cited hcite hK h6 hDL hAut hLie hP hA hT hκ hc hαγ
    hbase h4 hab M.bcp hG hc₁ hc₂ hcc hq (M.nodeBoundD_one h5) le_rfl h197
    (by rw [hPa]; linarith) hγ)

/-- `SimpleGraph.degree` form of the maximum-degree hypothesis (for `Nat.card` form, see above). -/
theorem card_neighborSet_le_of_degree {n d : ℕ} (X : SimpleGraph (Fin n)) [DecidableRel X.Adj]
    (h : ∀ v, X.degree v ≤ d) (v : Fin n) : Nat.card (X.neighborSet v) ≤ d := by
  rw [Nat.card_eq_fintype_card, X.card_neighborSet_eq_degree]
  exact h v

end GI.DegreeD.Luks
