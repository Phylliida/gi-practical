import DegreeD.M.PhaseCost
import DegreeD.M.QClip
import Workspace.Paper.MainTheorem

/-!
# The Stage-1 degree-`d` theorem

`degreeD_stage1` is the analogue, for the recursion `M.Run` with the dispatcher `(M′)`, of
HJ's `GI.Paper.thm_main_string_stage1`: runs of `Solve` on states in `Γ̂_d` cost at most
`exp(C' Λ log(s+2))` with `C'` independent of `d`, `Λ = log(8 max(d,6))`, under per-node
hypotheses of the same kinds (`NodeBoundD`), the root bounds, and the cited BCP and GNS results.
-/

namespace GI.DegreeD.M

open Equiv Equiv.Perm GI.Algorithm GI.Paper
open scoped Pointwise

variable {P : Params}

/-! ### The per-node hypothesis -/

/-- **The per-node hypothesis** (the shape of HJ's `NodeBound`, split): the structural work of a
node is polynomial in the phase size (per coset at a dispatcher node, since an enumeration under
`(M′)` can have super-polynomially many cosets), and only the row terminal has work
`exp(cw (log N)²)`. -/
structure NodeBoundD (w : Node P → ℝ) (cw af : ℝ) : Prop where
  nonneg : ∀ nd, 0 ≤ w nd
  work : ∀ nd : Node P, nd.m ≠ .solve → nd.S.size ≤ nd.S.N → nd.run.kind ≠ .rowTerminal →
    w nd ≤ (1 + (nd.run.fanout : ℝ)) * ((nd.S.N : ℝ) + 2) ^ cw
  rowTerminal : ∀ nd : Node P, nd.m ≠ .solve → nd.S.size ≤ nd.S.N → nd.run.kind = .rowTerminal →
    w nd ≤ expLogSq cw nd.S.N
  solve : ∀ nd : Node P, nd.m = .solve → w nd ≤ ((nd.S.size : ℝ) + 2) ^ cw
  calls : ∀ nd : Node P, nd.m ≠ .solve → nd.S.size ≤ nd.S.N →
    (nd.run.scriptCalls.length : ℝ) ≤ (nd.S.N : ℝ) ^ af

theorem one_le_pow_add_two (cw : ℝ) (hcw : 0 ≤ cw) (N : ℕ) : 1 ≤ ((N : ℝ) + 2) ^ cw :=
  Real.one_le_rpow (by have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith) hcw

theorem log_add_two_ge_half (N : ℕ) : (1 : ℝ) / 2 ≤ Real.log ((N : ℝ) + 2) := by
  have h2 : Real.log 2 ≤ Real.log ((N : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith)
  have := Real.log_two_gt_d9
  linarith

/-- `(N+2)^c ≤ exp(2c (log(N+2))²)`. -/
theorem pow_le_expLogSq {cw : ℝ} (hcw : 0 ≤ cw) (N : ℕ) :
    ((N : ℝ) + 2) ^ cw ≤ expLogSq (2 * cw) N := by
  have hL := log_add_two_ge_half N
  unfold expLogSq
  rw [Real.rpow_def_of_pos (by have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith)]
  apply Real.exp_le_exp.mpr
  have : Real.log ((N : ℝ) + 2) ≤ 2 * Real.log ((N : ℝ) + 2) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left this hcw]

/-- The node work at a phase of size `N`, for the class parameter `D`: polynomial when `D ≤ N^α`
(then the row terminal cannot occur); `exp(2cw (log N)²)` otherwise. -/
noncomputable def Eb (α : ℝ) (D : ℕ) (cw : ℝ) (N : ℕ) : ℝ :=
  if (D : ℝ) ≤ (N : ℝ) ^ α then ((N : ℝ) + 2) ^ cw else expLogSq (2 * cw) N

theorem Eb_ge {α : ℝ} {D : ℕ} {cw : ℝ} (hcw : 0 ≤ cw) (N : ℕ) :
    ((N : ℝ) + 2) ^ cw ≤ Eb α D cw N := by
  unfold Eb
  split_ifs
  · exact le_rfl
  · exact pow_le_expLogSq hcw N

theorem one_le_Eb {α : ℝ} {D : ℕ} {cw : ℝ} (hcw : 0 ≤ cw) (N : ℕ) : 1 ≤ Eb α D cw N :=
  (one_le_pow_add_two cw hcw N).trans (Eb_ge hcw N)

/-- `NodeBoundD` gives `NodeBoundE` for the class `D`: when `D ≤ N^α` a node of the class is not a
row terminal (`q ≤ D ≤ N^α < q` is impossible). -/
theorem NodeBoundD.toE {w : Node P → ℝ} {cw af : ℝ} (hw : NodeBoundD w cw af) (hcw : 0 ≤ cw)
    {D : ℕ} (hD : 6 ≤ D) : NodeBoundE D w (Eb P.α D cw) af where
  nonneg := hw.nonneg
  one_le := one_le_Eb hcw
  work := by
    intro nd hm hsz hg
    obtain ⟨m, Ω, C, S, L, A, r⟩ := nd
    simp only at hm hsz hg ⊢
    by_cases hR : (D : ℝ) ≤ (S.N : ℝ) ^ P.α
    · have hk : r.kind ≠ .rowTerminal := by
        intro hk
        cases r with
        | rowTerminal hs htr L hrow I e =>
          have h1 : (S.N : ℝ) ^ P.α < L.q := hrow.1
          have h2 : L.q ≤ max D 6 := labels_q_le hg L
          have h3 : max D 6 = D := by omega
          rw [h3] at h2
          have h4 : (L.q : ℝ) ≤ D := by exact_mod_cast h2
          linarith
        | _ => simp [Run.kind] at hk
      unfold Eb
      rw [if_pos hR]
      exact hw.work ⟨m, Ω, C, S, L, A, r⟩ hm hsz hk
    · unfold Eb
      rw [if_neg hR]
      by_cases hk : r.kind = .rowTerminal
      · refine (hw.rowTerminal ⟨m, Ω, C, S, L, A, r⟩ hm hsz hk).trans ?_
        have h1 : expLogSq cw S.N ≤ expLogSq (2 * cw) S.N := expLogSq_mono_left (by linarith) _
        have h2 : (1 : ℝ) ≤ 1 + (r.fanout : ℝ) := by
          have : (0 : ℝ) ≤ r.fanout := Nat.cast_nonneg _
          linarith
        exact h1.trans (le_mul_of_one_le_left (expLogSq_nonneg _ _) h2)
      · refine (hw.work ⟨m, Ω, C, S, L, A, r⟩ hm hsz hk).trans ?_
        have h2 : (0 : ℝ) ≤ 1 + (r.fanout : ℝ) := by
          have : (0 : ℝ) ≤ r.fanout := Nat.cast_nonneg _
          linarith
        exact mul_le_mul_of_nonneg_left (pow_le_expLogSq hcw S.N) h2
  calls := hw.calls

/-! ### Root bounds -/

/-- The product of a list of positive ratios: the logarithm of the product is the sum of the
logarithms. -/
theorem sum_log_ratio {Ω : Type} (l : List (Interval Ω)) (h : ∀ I ∈ l, 1 ≤ I.ratio) :
    (l.map fun I => Real.log I.ratio).sum = Real.log ((l.map Interval.ratio).prod : ℕ) := by
  induction l with
  | nil => simp
  | cons I l ih =>
    have hI : (0 : ℝ) < I.ratio := by exact_mod_cast (h I (by simp))
    have hp : (0 : ℝ) < ((l.map Interval.ratio).prod : ℕ) := by
      have : 0 < (l.map Interval.ratio).prod := by
        apply List.prod_pos
        intro n hn
        obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hn
        exact h J (List.mem_cons_of_mem _ hJ)
      exact_mod_cast this
    simp only [List.map_cons, List.sum_cons, List.prod_cons, Nat.cast_mul]
    rw [Real.log_mul hI.ne' hp.ne', ih (fun J hJ => h J (List.mem_cons_of_mem _ hJ))]

/-- `Q_d` at a phase root is at most `(log s)(log D)`, `D ≥ 2`. -/
theorem hierQd_root_le {Ω C : Type} [Finite Ω] {S : State Ω C} {S' : State S.dom C}
    (hS' : S.FreshOf S') {D : ℕ} (hD : 2 ≤ D) :
    hierQd D S'.hier ≤ Real.log (S'.size : ℝ) * Real.log D := by
  have htw := hS'.tower
  have hd := htw.one_le_ratio
  have hprod : (S'.hier.map Interval.ratio).prod ≤ S'.size := htw.prod_ratio_le S'.dom_inv
  have hD0 : (0 : ℝ) ≤ Real.log D := Real.log_natCast_nonneg D
  -- each term is at most `log d_i · log D`
  have hterm : ∀ x ∈ S'.hier.map (fun I => Real.log I.ratio * Real.log (max (min I.cap D) 2 : ℕ)),
      True := fun _ _ => trivial
  have hsum : hierQd D S'.hier ≤ (S'.hier.map fun I => Real.log I.ratio * Real.log D).sum := by
    unfold hierQd
    apply List.sum_le_sum
    intro I hI
    apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg _)
    apply Real.log_le_log (by positivity)
    have h2 : max (min I.cap D) 2 ≤ D := max_le (min_le_right _ _) hD
    exact_mod_cast h2
  have hsum2 : (S'.hier.map fun I => Real.log I.ratio * Real.log D).sum =
      (S'.hier.map fun I => Real.log I.ratio).sum * Real.log D := by
    rw [List.sum_map_mul_right]
  rw [hsum2, sum_log_ratio _ hd] at hsum
  refine hsum.trans (mul_le_mul_of_nonneg_right ?_ hD0)
  have hpos : (0 : ℝ) < ((S'.hier.map Interval.ratio).prod : ℕ) := by
    have : 0 < (S'.hier.map Interval.ratio).prod := by
      apply List.prod_pos
      intro n hn
      obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hn
      exact hd J hJ
    exact_mod_cast this
  exact Real.log_le_log hpos (by exact_mod_cast hprod)

/-! ### The row clauses for HJ's cap moment (the regime `D > N^α`) -/

section HJClauses

variable {cc : ChargingConstants}

theorem hj_clauses (hc : Compat P cc) {N d : ℕ} (hN2 : 2 ≤ N) :
    (∀ v : PNode P, v.Inv N → VClass d v → v.leaf.pt = none → ∀ cls,
      runKind v.leaf.run = .charged cls → ∀ c ∈ cls, ∀ b ∈ c.branches, ∀ u ∈ b,
        qClause cc (State.hierQ v.leaf.S.hier) (State.hierQ u.leaf.S.hier) c.row) ∧
    (∀ v : PNode P, v.Inv N → VClass d v → v.leaf.pt = none → ∀ cs,
      runKind v.leaf.run = .orbit cs → ∀ u ∈ cs,
        State.hierQ u.leaf.S.hier ≤ State.hierQ v.leaf.S.hier) := by
  refine ⟨?_, ?_⟩
  · intro v hv hg hpt cls hk c hc' b hb u hu
    obtain ⟨Ω', m, C', S, L, A, r, pt⟩ := v
    simp only at hpt
    subst hpt
    haveI := hv.fin
    have hN : S.N = N := hv.N_eq
    have hok := (runKind_charged_ok hc hN2 r hN hk).2 c hc'
    have hch := hok.child b hb u hu
    have hQ : (u.leaf.state P.κ).Q = State.hierQ u.leaf.S.hier := rfl
    cases hrow : c.row with
    | affected => rw [hrow] at hch; exact hQ ▸ hch.2.2.2.1
    | unaffected => rw [hrow] at hch; exact hQ ▸ hch.2.2.2.1
    | product r' => rw [hrow] at hch; exact hQ ▸ hch.2.2.2.1
    | enumeration d' => rw [hrow] at hch; exact hQ ▸ hch.2.2.2.1
    | continuation q => rw [hrow] at hch; exact hQ ▸ hch.2.2.2.1
    | rowEvent => rw [hrow] at hch; exact hQ ▸ hch.2.2.2.1
  · intro v hv hg hpt cs hk u hu
    obtain ⟨Ω', m, C', S, L, A, r, pt⟩ := v
    simp only at hpt
    subst hpt
    haveI := hv.fin
    have hN : S.N = N := hv.N_eq
    obtain ⟨-, -, -, horb⟩ := (runKind_orbit_ok r hN hc.κ_five (hv.orbit_h rfl) hk).1 u hu
    exact horb.2.2.1

end HJClauses

/-! ### One fresh phase -/

section Phase

variable {cc : ChargingConstants} {w : Node P → ℝ} {cw af cσ : ℝ}

theorem rootBoundsL_of {Ω C : Type} {S' : State Ω C} {cσ Λ q : ℝ} {n : ℕ}
    (h : GI.Paper.RootBounds cσ n (S'.res P.κ)) (hq : 0 ≤ q) (hQ : q ≤ Λ * Real.log (S'.res P.κ).s) :
    RootBoundsL cσ Λ n { S'.res P.κ with Q := q } where
  one_le_s := h.one_le_s
  s_le_N := h.s_le_N
  ρ_nonneg := h.ρ_nonneg
  ρ_le := h.ρ_le
  σ_nonneg := h.σ_nonneg
  σ_le := h.σ_le
  Q_nonneg := hq
  Q_le := hQ
  h_le := h.h_le

/-- **The phase core**: a `Continue` run that starts a phase on `n` positions costs at most
`K exp(C₁ Λ log(n+2))`, for any cap moment `Qf` with the row clauses. -/
theorem phase_core (hc : Compat P cc) (hαγ : 2 * P.α ≤ P.γ) (hα : 1 / 3 < P.α)
    (hab : ((2 * P.κ : ℕ) : ℝ) + Real.log (9 : ℕ) / Real.log 48 ≤ cc.aStar)
    {c₁ c₂ : ℝ} (hBCP : BCP) (hGNS : GNSPrimitive c₁ c₂) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hcc : c₁ / Real.log 2 + c₂ / Real.log 48 ≤ cc.a + cc.aStar / Real.log 2)
    (hq : (Real.log P.q₀.factorial / Real.log 48 + 1) / Real.log 17 ≤
      cc.a + cc.aStar / Real.log 2)
    {D : ℕ} {Λ : ℝ} (hΛ : lam D ≤ Λ) {Eb' : ℕ → ℝ} (hwE : NodeBoundE D w Eb' af) (haf : 0 ≤ af)
    (ha : af + 1 ≤ cc.a) {Qf : QFun} (hq0 : ∀ {Ω : Type} (l : List (Interval Ω)), 0 ≤ Qf l)
    {n : ℕ} (hn6 : 6 ≤ (n : ℝ) ^ cc.γ) (hn2 : 2 ≤ (n : ℝ) ^ (cc.γ * cc.D - cc.a))
    (hb : BddAbove (costSet D w cσ ⌈(n : ℝ) ^ P.γ⌉₊))
    (hqc : ∀ v : PNode P, v.Inv n → VClass D v → v.leaf.pt = none → ∀ cls,
      runKind v.leaf.run = .charged cls → ∀ c ∈ cls, ∀ b ∈ c.branches, ∀ u ∈ b,
        qClause cc (Qf v.leaf.S.hier) (Qf u.leaf.S.hier) c.row)
    (hqo : ∀ v : PNode P, v.Inv n → VClass D v → v.leaf.pt = none → ∀ cs,
      runKind v.leaf.run = .orbit cs → ∀ u ∈ cs, Qf u.leaf.S.hier ≤ Qf v.leaf.S.hier)
    {C₁ : ℝ}
    (hphase : ∀ (N : ℕ) (K Λ : ℝ), 0 ≤ K → xZero ≤ Λ → 6 ≤ (N : ℝ) ^ cc.γ →
      2 ≤ (N : ℝ) ^ (cc.γ * cc.D - cc.a) →
      ∀ {V : Type 1} (T : PhaseTree V), T.HypL cc (fun _ => Λ) N K →
      ∀ (roots : List V) (phaseCost : ℝ),
        (∀ v ∈ roots, RootBoundsL cσ Λ N (T.state v)) →
        (roots.map fun v => (T.state v).s).sum ≤ N →
        phaseCost ≤ (N : ℝ) ^ cc.a * K + (roots.map T.cost).sum →
        phaseCost ≤ K * Real.exp (C₁ * (Λ * logN N)))
    {Ω C : Type} [Finite Ω] {S' : State Ω C} {A : Set (Perm Ω)} (r : Run P .cont S' none A)
    (hSN : S'.N = n) (hh : S'.h = 2) (hfloor : S'.floor = false) (hsz : S'.size ≤ n)
    (hclass : GammaHat D S'.G) (hok : r.RootsOK cσ D)
    (hroot : RootBoundsL cσ Λ n { S'.res P.κ with Q := Qf S'.hier }) :
    r.total w + 4 * Eb' n ≤
      tollE Eb' P.γ (worstCost D w cσ) n * Real.exp (C₁ * (Λ * logN n)) := by
  have hγ : cc.γ = P.γ := hc.γ_eq
  have hn2' : 2 ≤ n := two_le_of_six_le cc.γ_pos.le hn6
  have hE0 : 0 ≤ Eb' n := zero_le_one.trans (hwE.one_le n)
  have hF0 := worstCost_nonneg hwE.nonneg D cσ ⌈(n : ℝ) ^ P.γ⌉₊
  set cost := vcost D w cσ (Eb' n) n with hcost
  set K := tollE Eb' P.γ (worstCost D w cσ) n with hK
  have hK0 : 0 ≤ K := by
    rw [hK]; unfold tollE; positivity
  have hleaf : ∀ v, (phaseTreeOn P n cost (VClass D) Qf).kind v = .leaf → cost v ≤ K :=
    fun v hk => leaf_cost hwE hb v hk
  have htoll : ∀ v, (phaseTreeOn P n cost (VClass D) Qf).kind v ≠ .leaf →
      cost v ≤ (n : ℝ) ^ cc.a * K +
        (((phaseTreeOn P n cost (VClass D) Qf).kind v).children.map cost).sum :=
    fun v hk => toll_bound hwE haf ha hαγ hα hn2' hb v hk
  have hxZero : xZero ≤ Λ := (xZero_le_lam D).trans hΛ
  have hHyp := phaseTreeOn_hypL (Good := VClass D) (Qf := Qf) (d := D) hc hn6 hab K hΛ
    (fun v hv hg u hu _ => vclass_closed hv hg hu)
    (fun v hv hg => by
      obtain ⟨Ω', m, C', S, L, A, r, pt⟩ := v
      haveI := hv.fin
      exact vertexBound_of_class hBCP hGNS hc₁ hc₂ hcc hq r hg)
    hq0 hqc hqo hleaf htoll
  -- the root
  set v₀ : PNode P := (Leaf.ofRun r).toP with hv₀
  have hgood : VGood D cσ n v₀ :=
    ⟨⟨‹_›, hSN, show Mode.cont ≠ Mode.solve by decide,
      fun a h => (by change (none : Option Ω) = some a at h; cases h), fun _ _ => hh⟩,
      hsz, hok, kind_of_floor r hfloor, hclass⟩
  have hcost₀ : cost v₀ = r.total w + 4 * Eb' n := vcost_of hgood
  have hinv₀ : v₀.Inv n := hgood.1
  have hgood₀ : VClass D v₀ := hgood.2.2.2.2
  have hst₀ : (phaseTreeOn P n cost (VClass D) Qf).state v₀ = vstate P Qf v₀ :=
    phaseTreeOn_state_of hinv₀ hgood₀
  have hroots : ∀ v ∈ [v₀], RootBoundsL cσ Λ n ((phaseTreeOn P n cost (VClass D) Qf).state v) := by
    intro v hv
    simp only [List.mem_singleton] at hv
    subst hv
    rw [hst₀]
    exact hroot
  have hs₀ : ((phaseTreeOn P n cost (VClass D) Qf).state v₀).s = S'.size := by
    rw [hst₀]; rfl
  have hsum : ([v₀].map fun v => ((phaseTreeOn P n cost (VClass D) Qf).state v).s).sum ≤ n := by
    simpa [hs₀] using hsz
  have hphaseCost : r.total w + 4 * Eb' n ≤ (n : ℝ) ^ cc.a * K +
      ([v₀].map (phaseTreeOn P n cost (VClass D) Qf).cost).sum := by
    have hNa0 : 0 ≤ (n : ℝ) ^ cc.a := by positivity
    have : 0 ≤ (n : ℝ) ^ cc.a * K := mul_nonneg hNa0 hK0
    show r.total w + 4 * Eb' n ≤ (n : ℝ) ^ cc.a * K + (List.map _ [v₀]).sum
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    show r.total w + 4 * Eb' n ≤ (n : ℝ) ^ cc.a * K + cost v₀
    rw [hcost₀]
    linarith
  exact hphase n K Λ hK0 hxZero hn6 hn2 _ hHyp [v₀] _ hroots hsum hphaseCost

end Phase

/-! ### A fresh phase of `Solve` -/

section Solve

variable {cc : ChargingConstants} {w : Node P → ℝ} {cw af cσ : ℝ}

/-- The weight `Λ_D = lam D / α` used in the phases. -/
noncomputable def lamA (P : Params) (D : ℕ) : ℝ := lam D / P.α

theorem lamA_ge_lam (hP : P.Terminating) (D : ℕ) : lam D ≤ lamA P D := by
  have hα := hP.α_pos
  have hα1 : P.α ≤ 1 := by have := hP.two_α_lt; linarith
  unfold lamA
  rw [le_div_iff₀ hα]
  have := lam_pos D
  nlinarith

/-- In the regime `D > n^α` (`D ≥ 6`, `n ≥ 1`) the logarithm of the domain is at most `Λ`. -/
theorem log_le_lamA_of_large (hP : P.Terminating) {D n : ℕ} (hD6 : 6 ≤ D)
    (hn1 : 1 ≤ n) (hR : ¬ (D : ℝ) ≤ (n : ℝ) ^ P.α) : Real.log n ≤ lamA P D := by
  have hα := hP.α_pos
  have hn : (0 : ℝ) < n := by exact_mod_cast hn1
  have hR' : (n : ℝ) ^ P.α < D := not_le.mp hR
  have hlog : P.α * Real.log n < Real.log D := by
    have h := Real.log_lt_log (Real.rpow_pos_of_pos hn P.α) hR'
    rwa [Real.log_rpow hn] at h
  have hDL : Real.log D ≤ lam D := by
    unfold lam
    apply Real.log_le_log (by exact_mod_cast (by omega : 0 < D))
    have : (D : ℝ) ≤ ((max D 6 : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
    linarith
  unfold lamA
  rw [le_div_iff₀ hα]
  linarith

/-- `2 ≤ lam D`. -/
theorem two_le_lam (D : ℕ) : 2 ≤ lam D := by
  have h48 : (2 : ℝ) ≤ Real.log 48 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have he := Real.exp_one_lt_d9
    rw [this]
    nlinarith [Real.exp_pos 1]
  exact h48.trans (log48_le_lam D)

theorem log_eleven_le : Real.log 11 ≤ 5 / 2 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 := Real.exp_one_gt_d9
  have h2 : (3 / 2 : ℝ) ≤ Real.exp (1 / 2) := by
    have := Real.add_one_le_exp (1 / 2 : ℝ)
    norm_num at this ⊢
    linarith
  have h3 : Real.exp (5 / 2) = Real.exp 1 * Real.exp 1 * Real.exp (1 / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  rw [h3]
  nlinarith [Real.exp_pos 1, Real.exp_pos (1 / 2 : ℝ)]

/-- `Eb n · 11` fits in `exp(c_T Λ log(n+2))`, in both regimes. -/
theorem eb_mul_eleven_le (hP : P.Terminating) (hcw : 0 ≤ cw) {D n : ℕ} (hD6 : 6 ≤ D)
    (hn1 : 1 ≤ n) :
    Eb P.α D cw n * 11 ≤ Real.exp ((4 * cw + 4) * (lamA P D * logN n)) := by
  have hL : (1 : ℝ) / 2 ≤ logN n := log_add_two_ge_half n
  have hΛ2 : 2 ≤ lamA P D := (two_le_lam D).trans (lamA_ge_lam hP D)
  set L := logN n with hLdef
  set Λ := lamA P D with hΛdef
  have hΛL : 1 ≤ Λ * L := by nlinarith
  have h11 : (11 : ℝ) ≤ Real.exp (4 * (Λ * L)) := by
    calc (11 : ℝ) = Real.exp (Real.log 11) := (Real.exp_log (by norm_num)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by have := log_eleven_le; linarith)
  have hE : Eb P.α D cw n ≤ Real.exp (4 * cw * (Λ * L)) := by
    unfold Eb
    split_ifs with hR
    · rw [Real.rpow_def_of_pos (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)]
      apply Real.exp_le_exp.mpr
      have heq : Real.log ((n : ℝ) + 2) = L := rfl
      rw [heq]
      have h4 : L ≤ 4 * (Λ * L) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h4 hcw]
    · have hlog := log_le_lamA_of_large hP hD6 hn1 hR
      have hn : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have hL2 : L ≤ 2 * Λ := by
        have h3 : (n : ℝ) + 2 ≤ 3 * n := by nlinarith
        have h4 : Real.log ((n : ℝ) + 2) ≤ Real.log 3 + Real.log n := by
          rw [← Real.log_mul (by norm_num) (by linarith)]
          exact Real.log_le_log (by linarith) h3
        have hlog3 : Real.log 3 ≤ 3 / 2 := by
          have h3e : (3 : ℝ) ≤ 2 ^ (2 : ℕ) := by norm_num
          have h6 : Real.log 3 ≤ 2 * Real.log 2 := by
            calc Real.log 3 ≤ Real.log ((2 : ℝ) ^ (2 : ℕ)) := Real.log_le_log (by norm_num) h3e
              _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
          have := Real.log_two_lt_d9
          linarith
        have heq : Real.log ((n : ℝ) + 2) = L := rfl
        rw [heq] at h4
        linarith
      unfold expLogSq
      apply Real.exp_le_exp.mpr
      have heq : Real.log ((n : ℝ) + 2) = L := rfl
      rw [heq]
      have hkey : L ^ 2 ≤ 2 * Λ * L := by
        have h0 : 0 ≤ L := by linarith
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hkey hcw]
  have hE0 : 0 ≤ Eb P.α D cw n := (zero_le_one.trans (one_le_Eb hcw n))
  calc Eb P.α D cw n * 11 ≤ Real.exp (4 * cw * (Λ * L)) * Real.exp (4 * (Λ * L)) :=
        mul_le_mul hE h11 (by norm_num) (Real.exp_pos _).le
    _ = Real.exp ((4 * cw + 4) * (Λ * L)) := by rw [← Real.exp_add]; ring_nf


/-- **A `Solve` run that starts a phase on `n` positions**, for a `Γ̂_D` state. -/
theorem solve_phase_bound (hP : P.Terminating) (hc : Compat P cc) (hαγ : 2 * P.α ≤ P.γ)
    (hab : ((2 * P.κ : ℕ) : ℝ) + Real.log (9 : ℕ) / Real.log 48 ≤ cc.aStar)
    {c₁ c₂ : ℝ} (hBCP : BCP) (hGNS : GNSPrimitive c₁ c₂) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hcc : c₁ / Real.log 2 + c₂ / Real.log 48 ≤ cc.a + cc.aStar / Real.log 2)
    (hq : (Real.log P.q₀.factorial / Real.log 48 + 1) / Real.log 17 ≤
      cc.a + cc.aStar / Real.log 2)
    (hw : NodeBoundD w cw af) (hcw : 0 ≤ cw) (haf : 0 ≤ af) (ha : af + 1 ≤ cc.a)
    {D : ℕ} (hD6 : 6 ≤ D) {C₁ : ℝ}
    (hphase : ∀ (N : ℕ) (K Λ : ℝ), 0 ≤ K → xZero ≤ Λ → 6 ≤ (N : ℝ) ^ cc.γ →
      2 ≤ (N : ℝ) ^ (cc.γ * cc.D - cc.a) →
      ∀ {V : Type 1} (T : PhaseTree V), T.HypL cc (fun _ => Λ) N K →
      ∀ (roots : List V) (phaseCost : ℝ),
        (∀ v ∈ roots, RootBoundsL cσ Λ N (T.state v)) →
        (roots.map fun v => (T.state v).s).sum ≤ N →
        phaseCost ≤ (N : ℝ) ^ cc.a * K + (roots.map T.cost).sum →
        phaseCost ≤ K * Real.exp (C₁ * (Λ * logN N)))
    {n : ℕ} (hn : P.N₀ < n) (hn1 : 1 ≤ n) (hn6 : 6 ≤ (n : ℝ) ^ cc.γ)
    (hn2 : 2 ≤ (n : ℝ) ^ (cc.γ * cc.D - cc.a))
    (hb : BddAbove (costSet D w cσ ⌈(n : ℝ) ^ P.γ⌉₊))
    {Ω C : Type} [Finite Ω] {S : State Ω C} {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)}
    (r : Run P .solve S L A) (hsn : S.size = n) (hg : GammaHat D S.G) (hok : r.RootsOK cσ D) :
    r.total w ≤ Real.exp ((4 * cw + 4 + C₁) * (lamA P D * logN n)) *
      (1 + worstCost D w cσ ⌈(n : ℝ) ^ P.γ⌉₊) := by
  have hD2 : 2 ≤ D := by omega
  have hΛ : lam D ≤ lamA P D := lamA_ge_lam hP D
  have hΛ0 : 0 < lamA P D := lt_of_lt_of_le (lam_pos D) hΛ
  have hF0 := worstCost_nonneg hw.nonneg D cσ ⌈(n : ℝ) ^ P.γ⌉₊
  have hLN : (0 : ℝ) ≤ logN n := Real.log_nonneg (by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  cases r with
  | direct _ hs' => omega
  | @fresh _ _ _ S' _ hs₀ hS' r' =>
    obtain ⟨hfin, hroot, hok'⟩ := hok
    have hwE : NodeBoundE D w (Eb P.α D cw) af := hw.toE hcw hD6
    haveI : Finite S.dom := hfin
    have hG' : GammaHat D S'.G := by
      rw [hS'.G_eq]
      exact GammaHat.range S.domHom hg
    have hSN' : S'.N = n := hS'.N_eq.trans hsn
    have hh := hS'.h_eq
    have hfloor := hS'.floor_eq
    have hsz : S'.size = n := hS'.size_eq.trans hsn
    rw [hSN'] at hroot
    have hsz1 : (1 : ℝ) ≤ S'.size := by rw [hsz]; exact_mod_cast hn1
    have hlogs0 : 0 ≤ Real.log (S'.size : ℝ) := Real.log_nonneg hsz1
    have hDL : Real.log D ≤ lamA P D := by
      have h1 : Real.log D ≤ lam D := by
        unfold lam
        apply Real.log_le_log (by exact_mod_cast (by omega : 0 < D))
        have : (D : ℝ) ≤ ((max D 6 : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
        linarith
      exact h1.trans hΛ
    -- the phase bound, in each regime
    have hcore : r'.total w + 4 * Eb P.α D cw n ≤
        tollE (Eb P.α D cw) P.γ (worstCost D w cσ) n * Real.exp (C₁ * (lamA P D * logN n)) := by
      by_cases hR : (D : ℝ) ≤ (n : ℝ) ^ P.α
      · -- the clipped regime: `hierQd D`
        have hR' : ((max D 6 : ℕ) : ℝ) ≤ (n : ℝ) ^ P.α := by
          have : max D 6 = D := by omega
          rw [this]; exact hR
        obtain ⟨hcl1, hcl2⟩ := clipped_clauses (P := P) (cc := cc) hc (d := D) hR'
        have hmax : max D 6 = D := by omega
        rw [hmax] at hcl1 hcl2
        have hrootL : RootBoundsL cσ (lamA P D) n { S'.res P.κ with Q := hierQd D S'.hier } :=
          rootBoundsL_of hroot (hierQd_nonneg D S'.hier) (by
            have h := hierQd_root_le hS' hD2
            calc hierQd D S'.hier ≤ Real.log (S'.size : ℝ) * Real.log D := h
              _ ≤ Real.log (S'.size : ℝ) * lamA P D :=
                  mul_le_mul_of_nonneg_left hDL hlogs0
              _ = lamA P D * Real.log (S'.size : ℝ) := by ring
              _ = _ := rfl)
        exact phase_core hc hαγ hP.third_lt_α hab hBCP hGNS hc₁ hc₂ hcc hq hΛ hwE haf ha
          (Qf := fun l => hierQd D l) (fun l => hierQd_nonneg D l) hn6 hn2 hb hcl1 hcl2 hphase
          r' hSN' hh hfloor hsz.le hG' hok' hrootL
      · -- the large regime: HJ's `hierQ`
        have hn2' : 2 ≤ n := two_le_of_six_le cc.γ_pos.le hn6
        obtain ⟨hcl1, hcl2⟩ := hj_clauses (P := P) (cc := cc) (d := D) hc (N := n) hn2'
        have hlog := log_le_lamA_of_large hP hD6 hn1 hR
        have hlogs : Real.log (S'.size : ℝ) ≤ lamA P D := by rw [hsz]; exact hlog
        have hrootL : RootBoundsL cσ (lamA P D) n { S'.res P.κ with Q := State.hierQ S'.hier } :=
          rootBoundsL_of hroot (State.hierQ_nonneg _) (by
            have h := hroot.Q_le
            change State.hierQ S'.hier ≤ Real.log (S'.size : ℝ) ^ 2 at h
            refine h.trans ?_
            change Real.log (S'.size : ℝ) ^ 2 ≤ lamA P D * Real.log (S'.size : ℝ)
            nlinarith)
        exact phase_core hc hαγ hP.third_lt_α hab hBCP hGNS hc₁ hc₂ hcc hq hΛ hwE haf ha
          (Qf := fun l => State.hierQ l) (fun l => State.hierQ_nonneg l) hn6 hn2 hb hcl1 hcl2 hphase
          r' hSN' hh hfloor hsz.le hG' hok' hrootL
    -- collect the factors
    have hE1 : 1 ≤ Eb P.α D cw n := one_le_Eb hcw n
    have hwk : w (Run.fresh hs₀ hS' r').node ≤ Eb P.α D cw n := by
      have h1 := hw.solve (Run.fresh hs₀ hS' r').node rfl
      have h2 : ((Run.fresh hs₀ hS' r').node.S.size : ℝ) = n := by
        exact_mod_cast hsn
      rw [h2] at h1
      exact h1.trans (Eb_ge hcw n)
    have htot : (Run.fresh hs₀ hS' r').total w ≤
        tollE (Eb P.α D cw) P.γ (worstCost D w cσ) n * Real.exp (C₁ * (lamA P D * logN n)) := by
      rw [Run.total_fresh]; nlinarith [hcore]
    refine htot.trans ?_
    unfold tollE
    set Λ := lamA P D
    have hΛL : 0 ≤ Λ * logN n := mul_nonneg hΛ0.le hLN
    have hE := eb_mul_eleven_le (P := P) hP hcw hD6 hn1
    have hF1 : 0 ≤ 1 + worstCost D w cσ ⌈(n : ℝ) ^ P.γ⌉₊ := by linarith
    calc Eb P.α D cw n * 11 * (1 + worstCost D w cσ ⌈(n : ℝ) ^ P.γ⌉₊) *
          Real.exp (C₁ * (Λ * logN n))
        ≤ Real.exp ((4 * cw + 4) * (Λ * logN n)) * (1 + worstCost D w cσ ⌈(n : ℝ) ^ P.γ⌉₊) *
          Real.exp (C₁ * (Λ * logN n)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_right hE hF1
      _ = Real.exp ((4 * cw + 4 + C₁) * (Λ * logN n)) *
          (1 + worstCost D w cσ ⌈(n : ℝ) ^ P.γ⌉₊) := by
          have hexp : Real.exp ((4 * cw + 4 + C₁) * (Λ * logN n)) =
              Real.exp ((4 * cw + 4) * (Λ * logN n)) * Real.exp (C₁ * (Λ * logN n)) := by
            rw [← Real.exp_add]; ring_nf
          rw [hexp]; ring

/-- The phase-work bound at small sizes, independent of `Λ`. -/
theorem total_le_of_small (hw : NodeBoundD w cw af) (hcw : 0 ≤ cw)
    {Ω C : Type} {S : State Ω C} {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)}
    (r : Run P .solve S L A) (hs : S.size ≤ P.N₀) :
    r.total w ≤ ((P.N₀ : ℝ) + 2) ^ cw := by
  cases r with
  | direct _ hs' =>
    rw [Run.total_direct]
    have h1 := hw.solve (Run.direct (P := P) S hs').node rfl
    have h2 : ((Run.direct (P := P) S hs').node.S.size : ℝ) = S.size := rfl
    refine h1.trans ?_
    rw [h2]
    apply Real.rpow_le_rpow (by positivity) (by exact_mod_cast (by omega : S.size + 2 ≤ P.N₀ + 2)) hcw
  | fresh hs' => omega

end Solve


section Recurrence

theorem recurrenceM {γ C : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hC : 0 ≤ C) (N₀ : ℕ) (B₀ : ℝ)
    (hB₀ : 0 ≤ B₀) (h4 : ∀ n : ℕ, N₀ < n → (4 : ℝ) ≤ (n : ℝ) ^ ((1 - γ) / 2)) :
    ∃ C' : ℕ, ∀ (Λ : ℝ), 1 ≤ Λ → ∀ F : ℕ → ℝ,
      (∀ n < N₀ + 1, F n ≤ B₀) →
      (∀ N, N₀ + 1 ≤ N → F N ≤ Real.exp (C * (Λ * logN N)) * (1 + F ⌈(N : ℝ) ^ γ⌉₊)) →
      ∀ N, F N ≤ Real.exp (C' * (Λ * logN N)) := by
  set γh := (1 + γ) / 2 with hγh
  have hγh1 : γh < 1 := by rw [hγh]; linarith
  have hγh0 : 0 < γh := by rw [hγh]; linarith
  set base := N₀ + 1 with hbase
  have hl2 := ChargingConstants.log_two_pos'
  set D : ℝ := max ((C + Real.log 2) / (1 - γh)) (Real.log (B₀ + 1) / Real.log 2)
  have hD1 : (C + Real.log 2) / (1 - γh) ≤ D := le_max_left _ _
  have hD2 : Real.log (B₀ + 1) / Real.log 2 ≤ D := le_max_right _ _
  have hD0 : 0 ≤ D := le_trans (div_nonneg (by linarith) (by linarith)) hD1
  refine ⟨⌈D⌉₊, ?_⟩
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
      have hn3 : 1 ≤ n := by omega
      have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn3
      have h4 := h4 n (by omega)
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


end Recurrence


/-! ### The final theorem -/

section Final

variable {cc : ChargingConstants} {w : Node P → ℝ} {cw af cσ : ℝ}

/-- **The worst-case-cost recurrence of `Γ̂_D`**, solved: `F_D(n) ≤ exp(C' Λ_D log(n+2))` for every
`n`, with `C'` independent of `D`. -/
theorem worstCost_bound (hP : P.Terminating) (hc : Compat P cc) (hαγ : 2 * P.α ≤ P.γ)
    (hbase : AboveBase P cc) (h4 : ∀ n : ℕ, P.N₀ < n → (4 : ℝ) ≤ (n : ℝ) ^ ((1 - P.γ) / 2))
    (hab : ((2 * P.κ : ℕ) : ℝ) + Real.log (9 : ℕ) / Real.log 48 ≤ cc.aStar)
    {c₁ c₂ : ℝ} (hBCP : BCP) (hGNS : GNSPrimitive c₁ c₂) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hcc : c₁ / Real.log 2 + c₂ / Real.log 48 ≤ cc.a + cc.aStar / Real.log 2)
    (hq : (Real.log P.q₀.factorial / Real.log 48 + 1) / Real.log 17 ≤
      cc.a + cc.aStar / Real.log 2)
    (hcσ : 0 ≤ cσ) (hw : NodeBoundD w cw af) (hcw : 0 ≤ cw) (haf : 0 ≤ af) (ha : af + 1 ≤ cc.a) :
    ∃ C' : ℝ, ∀ (D : ℕ), 6 ≤ D → ∀ n, BddAbove (costSet D w cσ n) ∧
      worstCost D w cσ n ≤ Real.exp (C' * (lamA P D * logN n)) := by
  obtain ⟨C₁, hC₁, hphase⟩ := fresh_phase_boundL.{1} cc hcσ
  set C₂ : ℝ := 4 * cw + 4 + C₁ with hC₂
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; positivity
  set B₀ : ℝ := ((P.N₀ : ℝ) + 2) ^ cw with hB₀
  have hB₀1 : 1 ≤ B₀ := one_le_pow_add_two cw hcw P.N₀
  obtain ⟨C', hC'⟩ := recurrenceM (γ := P.γ) (C := C₂) (hc.γ_eq ▸ cc.γ_pos) hP.γ_lt hC₂0 P.N₀ B₀
    (by linarith) h4
  refine ⟨C', ?_⟩
  intro D hD6
  set Λ := lamA P D with hΛ
  have hΛ1 : 1 ≤ Λ := (one_le_lam D).trans (lamA_ge_lam hP D)
  set F := worstCost D w cσ with hF
  have hF0 : ∀ n, 0 ≤ F n := fun n => worstCost_nonneg hw.nonneg D cσ n
  -- the elementary step
  have elem : ∀ n : ℕ, (∀ m < n, BddAbove (costSet D w cσ m)) → ∀ x ∈ costSet D w cσ n,
      x ≤ (if n ≤ P.N₀ then B₀ else Real.exp (C₂ * (Λ * logN n)) * (1 + F ⌈(n : ℝ) ^ P.γ⌉₊)) := by
    intro n IH x hx
    obtain ⟨Ω, C, S, L, A, r, hS, hfin, hg, hok, rfl⟩ := hx
    by_cases hs : S.size ≤ P.N₀
    · have h1 := total_le_of_small hw hcw r hs
      split_ifs with hnN
      · exact h1
      · refine h1.trans ?_
        have hL : Real.log ((P.N₀ : ℝ) + 2) ≤ logN n := by
          apply Real.log_le_log (by positivity)
          have : (P.N₀ : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_not_le hnN)
          linarith
        have hB : B₀ ≤ Real.exp (C₂ * (Λ * logN n)) := by
          rw [hB₀, Real.rpow_def_of_pos (by positivity)]
          apply Real.exp_le_exp.mpr
          have hL0 : (0 : ℝ) ≤ logN n := (Real.log_nonneg (by
            have : (0 : ℝ) ≤ P.N₀ := Nat.cast_nonneg _; linarith)).trans hL
          have h2 : cw * Real.log ((P.N₀ : ℝ) + 2) ≤ cw * logN n :=
            mul_le_mul_of_nonneg_left hL hcw
          have h3 : logN n ≤ Λ * logN n := by nlinarith
          have h4' : cw ≤ C₂ := by rw [hC₂]; linarith
          nlinarith [mul_le_mul_of_nonneg_left h3 hcw, mul_le_mul_of_nonneg_right h4' (mul_nonneg (by linarith : (0:ℝ) ≤ Λ) hL0)]
        have hexp0 := (Real.exp_pos (C₂ * (Λ * logN n))).le
        have := hF0 ⌈(n : ℝ) ^ P.γ⌉₊
        nlinarith
    · push Not at hs
      have hnN : ¬ n ≤ P.N₀ := by omega
      rw [if_neg hnN]
      obtain ⟨h6, h2, hlt⟩ := hbase S.size hs
      have hsn : S.size ≤ n := hS
      have hbs := IH _ (lt_of_lt_of_le hlt hsn)
      have hs1 : 1 ≤ S.size := by have := hP.N₀_pos; omega
      have h := solve_phase_bound (cσ := cσ) hP hc hαγ hab hBCP hGNS hc₁ hc₂ hcc hq hw hcw haf ha hD6 hphase hs hs1
        h6 h2 hbs r rfl hg hok
      refine h.trans ?_
      have hnN1 : P.N₀ < n := by omega
      obtain ⟨-, -, hlt'⟩ := hbase n hnN1
      have hbn := IH _ hlt'
      have hγ0 : 0 ≤ P.γ := (hc.γ_eq ▸ cc.γ_pos).le
      have hceil : ⌈(S.size : ℝ) ^ P.γ⌉₊ ≤ ⌈(n : ℝ) ^ P.γ⌉₊ :=
        Nat.ceil_mono (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hsn) hγ0)
      have hFm : F ⌈(S.size : ℝ) ^ P.γ⌉₊ ≤ F ⌈(n : ℝ) ^ P.γ⌉₊ :=
        worstCost_mono hw.nonneg hceil hbn
      have hLs : logN S.size ≤ logN n := by
        apply Real.log_le_log (by positivity)
        have : (S.size : ℝ) ≤ n := by exact_mod_cast hsn
        linarith
      have hΛ0 : 0 ≤ Λ := by linarith
      have hexp : Real.exp (C₂ * (Λ * logN S.size)) ≤ Real.exp (C₂ * (Λ * logN n)) := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ hC₂0
        exact mul_le_mul_of_nonneg_left hLs hΛ0
      have hF1 := hF0 ⌈(S.size : ℝ) ^ P.γ⌉₊
      exact mul_le_mul hexp (by linarith) (by linarith) (Real.exp_pos _).le
  -- boundedness for every `n`
  have hbdd : ∀ n : ℕ, BddAbove (costSet D w cσ n) := fun n =>
    Nat.strong_induction_on n fun n IH => ⟨_, elem n IH⟩
  refine fun n => ⟨hbdd n, ?_⟩
  -- solve the recurrence
  have hsmall : ∀ m < P.N₀ + 1, F m ≤ B₀ := fun m hm =>
    Real.sSup_le (fun x hx => by
      have := elem m (fun m' _ => hbdd m') x hx
      rwa [if_pos (by omega)] at this) (by linarith)
  have hstep : ∀ N, P.N₀ + 1 ≤ N → F N ≤ Real.exp (C₂ * (Λ * logN N)) *
      (1 + F ⌈(N : ℝ) ^ P.γ⌉₊) := by
    intro N hN
    have hnle : ¬ N ≤ P.N₀ := by omega
    have hup : 0 ≤ Real.exp (C₂ * (Λ * logN N)) * (1 + F ⌈(N : ℝ) ^ P.γ⌉₊) := by
      have := hF0 ⌈(N : ℝ) ^ P.γ⌉₊
      positivity
    exact Real.sSup_le (fun x hx => by
      have := elem N (fun m' _ => hbdd m') x hx
      rwa [if_neg hnle] at this) hup
  exact hC' Λ hΛ1 F hsmall hstep n

/-- `lam` depends only on `max(d, 6)`. -/
theorem lam_max_six (d : ℕ) : lam (max d 6) = lam d := by
  unfold lam
  have : max (max d 6) 6 = max d 6 := by omega
  rw [this]

/-- **The Stage-1 degree-`d` theorem** (Theorem R\* at the level of the abstract recursion `M.Run`,
with the dispatcher `(M′)`, under the cost hypotheses of the same kinds as
`GI.Paper.thm_main_string_stage1`, and the two cited results `BCP` and `GNSPrimitive`). -/
theorem degreeD_stage1 (hP : P.Terminating) (hc : Compat P cc) (hαγ : 2 * P.α ≤ P.γ)
    (hbase : AboveBase P cc) (h4 : ∀ n : ℕ, P.N₀ < n → (4 : ℝ) ≤ (n : ℝ) ^ ((1 - P.γ) / 2))
    (hab : ((2 * P.κ : ℕ) : ℝ) + Real.log (9 : ℕ) / Real.log 48 ≤ cc.aStar)
    {c₁ c₂ : ℝ} (hBCP : BCP) (hGNS : GNSPrimitive c₁ c₂) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hcc : c₁ / Real.log 2 + c₂ / Real.log 48 ≤ cc.a + cc.aStar / Real.log 2)
    (hq : (Real.log P.q₀.factorial / Real.log 48 + 1) / Real.log 17 ≤
      cc.a + cc.aStar / Real.log 2)
    (hcσ : 0 ≤ cσ) (hw : NodeBoundD w cw af) (hcw : 0 ≤ cw) (haf : 0 ≤ af) (ha : af + 1 ≤ cc.a) :
    ∃ C' : ℝ, ∀ (d : ℕ) {Ω C : Type} [Finite Ω] (S : State Ω C) {A : Set (Perm Ω)}
      (r : Run P .solve S none A), GammaHat d S.G → r.RootsOK cσ (max d 6) →
      (A = {g | g ∈ S.G ∧ ∀ v ∈ S.dom, S.y (g v) = S.x v} ∧
        (A = ∅ ∨ ∃ t ∈ S.G, A = t • (autGroup S.G S.dom S.dom_inv S.x : Set (Perm Ω)))) ∧
      r.total w ≤ Real.exp (C' * (lam d * Real.log ((S.size : ℝ) + 2))) := by
  obtain ⟨C', hC'⟩ := worstCost_bound hP hc hαγ hbase h4 hab hBCP hGNS hc₁ hc₂ hcc hq hcσ hw hcw haf ha
  refine ⟨C' / P.α, ?_⟩
  intro d Ω C _ S A r hg hok
  have hA : A = {g | g ∈ S.G ∧ ∀ v ∈ S.dom, S.y (g v) = S.x v} := r.exact
  refine ⟨⟨hA, ?_⟩, ?_⟩
  · rw [hA]; exact answer_empty_or_coset S.dom_inv S.x S.y
  · set D := max d 6 with hD
    have hD6 : 6 ≤ D := le_max_right _ _
    have hgD : GammaHat D S.G := hg.mono (le_max_left _ _)
    obtain ⟨hbdd, hbnd⟩ := hC' D hD6 S.size
    have htot : r.total w ≤ worstCost D w cσ S.size :=
      total_le_worstCost hbdd r le_rfl ‹_› hgD hok
    refine htot.trans (hbnd.trans (Real.exp_le_exp.mpr ?_))
    have hlam : lam D = lam d := lam_max_six d
    have hα := hP.α_pos
    unfold lamA
    rw [hlam]
    apply le_of_eq
    change C' * (lam d / P.α * logN S.size) = C' / P.α * (lam d * logN S.size)
    field_simp

end Final

end GI.DegreeD.M
