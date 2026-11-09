import DegreeD.TableLambda
import Workspace.Algorithm.PhaseTree

/-!
# HJ's Lemma 7.1 is the instance `Λ = x`, and the hypotheses are satisfiable

Two things are shown here.

1. **HJ's case.** `PhaseTree.Hyp` (HJ's hypotheses) implies `PhaseTree.HypL` at the weight
   `xFn = log(s+2)`: `Hyp.toHypL`. Since `Φ_{xFn}` is HJ's potential (`ΦL_x_eq`), `HypL.cost_le`
   re-derives the conclusion of `GI.Paper.lem_main_phase_bound` (`lem_main_phase_bound_of_general`).
   So the generalization does generalize: the proof of the Λ-version, specialized to `Λ = x`,
   gives back HJ's lemma.

2. **Non-vacuity of `HypL`.** The hypotheses are not vacuous, in two ways.
   * The real phase trees of HJ's algorithm (`GI.Algorithm.phaseTree`, built from actual runs) satisfy
     `PhaseCore` (every field except the multiplicity column) for *all* weights `Λ`, and satisfy
     `HypL` at `Λ = xFn` (`real_runs_core`, `real_runs_hypL_x`). This uses `phaseTree_hyp` of
     the development.
   * `example_hypL`: for every `t ≥ 1` (so `N = 2^{10t}` is arbitrarily large) and every
     constant `Λ ≥ log 8`, an explicit two-level tree whose root has a class in each of the six
     rows satisfies `HypL`, and its root has `s > N^γ`. So `HypL` is satisfiable with `Λ`
     constant and `N → ∞`, the regime Theorem R* is about.
-/

namespace GI.DegreeD

open GI.Paper

/-! ## `Hyp` implies `HypL` at `Λ = x` -/

/-- HJ's multiplicity column is bounded by `multL` at `Λ = x`, at any internal node. -/
theorem mult_le_multL_x (C : ChargingConstants) {N : ℕ} {S : PotentialState} {R : Row}
    (hNs : (N : ℝ) ^ C.γ < S.s) (hS6 : 6 ≤ (S.s : ℝ)) (hv : R.Valid C S) :
    Row.mult C N R ≤ Row'.multL C (xFn S.s) R := by
  have hx : xZero ≤ S.x := Row.xZero_le_x hS6
  have hNa : (N : ℝ) ^ C.a ≤ Real.exp (C.aStar * S.x) :=
    eq_main_phase_active (Nat.cast_nonneg N) C.a_pos.le C.γ_pos hNs
  have hx0 := S.x_nonneg
  have heq : xFn S.s = S.x := rfl
  rw [heq]
  cases R with
  | affected => simpa only [Row.mult, Row'.multL] using hNa
  | unaffected => simpa only [Row.mult, Row'.multL] using hNa
  | product r =>
    obtain ⟨hr, hrs⟩ := hv
    have hb := main_product_index_bound hr hrs
    have hL : Real.log ((2 : ℝ) ^ r * (r.factorial : ℝ)) ≤ 4 * ((r : ℝ) - 1) * S.x :=
      hb.1.trans hb.2
    have hpos : (0 : ℝ) < (2 : ℝ) ^ r * (r.factorial : ℝ) := by positivity
    simp only [Row.mult, Row'.multL]
    calc (N : ℝ) ^ C.a * ((2 : ℝ) ^ r * (r.factorial : ℝ))
        ≤ Real.exp (C.aStar * S.x) * Real.exp (Real.log ((2 : ℝ) ^ r * (r.factorial : ℝ))) := by
          rw [Real.exp_log hpos]; exact mul_le_mul_of_nonneg_right hNa hpos.le
      _ = Real.exp (C.aStar * S.x + Real.log ((2 : ℝ) ^ r * (r.factorial : ℝ))) := by
          rw [Real.exp_add]
      _ ≤ Real.exp ((4 * ((r : ℝ) - 1) + C.aStar) * S.x) :=
          Real.exp_le_exp.mpr (by nlinarith)
  | enumeration d =>
    obtain ⟨hd2, hds⟩ := hv
    have hd2' : (2 : ℝ) ≤ d := by exact_mod_cast hd2
    have hds' : (d : ℝ) ≤ S.s := by exact_mod_cast hds
    have hl2 := ChargingConstants.log_two_pos'
    set ℓ := Real.log d with hℓ
    have hℓ2 : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num) hd2'
    have hℓ0 : 0 < ℓ := hl2.trans_le hℓ2
    have hℓx : ℓ ≤ S.x := Real.log_le_log (by linarith) (by linarith)
    have hx0' : 0 ≤ S.x := hx0
    simp only [Row.mult, Row'.multL]
    calc (N : ℝ) ^ C.a * Real.exp (C.a * ℓ ^ 2)
        ≤ Real.exp (C.aStar * S.x) * Real.exp (C.a * ℓ ^ 2) :=
          mul_le_mul_of_nonneg_right hNa (Real.exp_pos _).le
      _ = Real.exp (C.aStar * S.x + C.a * ℓ ^ 2) := by rw [Real.exp_add]
      _ ≤ Real.exp ((C.a + C.aStar / Real.log 2) * S.x * ℓ) := by
          apply Real.exp_le_exp.mpr
          have h1 : C.a * ℓ ^ 2 ≤ C.a * (S.x * ℓ) := by
            apply mul_le_mul_of_nonneg_left _ C.a_pos.le
            nlinarith
          have h2 : C.aStar * S.x ≤ C.aStar / Real.log 2 * S.x * ℓ := by
            rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hl2]
            have := mul_le_mul_of_nonneg_left hℓ2 (mul_nonneg C.aStar_nonneg hx0')
            nlinarith
          nlinarith
  | continuation q => exact le_refl _
  | rowEvent => exact le_refl _

/-- **HJ's hypotheses imply the Λ-hypotheses at `Λ = x`.** -/
theorem _root_.GI.Paper.PhaseTree.Hyp.toHypL {C : ChargingConstants} {N : ℕ} {K : ℝ} {V : Type*}
    {T : PhaseTree V} (h : T.Hyp C N K) (hN6 : 6 ≤ (N : ℝ) ^ C.γ) :
    T.HypL C xFn N K where
  toPhaseCore := h.toCore
  class_fam := by
    intro v cls hk c hc
    have hne : T.kind v ≠ .leaf := by rw [hk]; simp
    have h6 : 6 ≤ ((T.state v).s : ℝ) := hN6.trans (h.internal_large v hne).le
    refine ⟨c.branches.length, id, ?_, ?_⟩
    · exact (h.class_mult v cls hk c hc).trans
        (mult_le_multL_x C (h.internal_large v hne) h6 (h.class_valid v cls hk c hc))
    · intro j
      have hfilter : (Finset.univ.filter (fun i : Fin c.branches.length => id i = j)) = {j} := by
        ext i; simp
      rw [hfilter, Finset.sum_singleton]
      exact h.branch_disjoint v cls hk c hc _ (List.get_mem _ _)

/-- **HJ's Lemma 7.1, re-derived from the general theorem** (with the same hypotheses and
conclusion as `GI.Paper.lem_main_phase_bound`, for an arbitrary toll `K ≥ 0`). -/
theorem lem_main_phase_bound_of_general (C : ChargingConstants) {V : Type*} (T : PhaseTree V)
    (N : ℕ) (K : ℝ) (hK : 0 ≤ K) (hN6 : 6 ≤ (N : ℝ) ^ C.γ)
    (hN2 : 2 ≤ (N : ℝ) ^ (C.γ * C.D - C.a)) (hT : T.Hyp C N K) :
    WellFounded (fun u v => u ∈ (T.kind v).children) ∧
    ∀ v, T.cost v ≤ K * (T.state v).W C.A C.B C.D := by
  have h := (hT.toHypL hN6).cost_le xFn_weightFn hN6 hN2 hK
  refine ⟨h.1, fun v => ?_⟩
  have e : weight C.D (T.state v).s (ΦL C.A C.B xFn (T.state v)) =
      (T.state v).W C.A C.B C.D := by
    unfold weight PotentialState.W
    rw [ΦL_x_eq]
  rw [← e]
  exact h.2 v

/-! ## The real runs satisfy `PhaseCore`, for every `Λ`, and `HypL` at `Λ = x` -/

section Real

variable {P : GI.Algorithm.Params} {N : ℕ} {cost : GI.Algorithm.PNode P → ℝ}

/-- **The real phase trees satisfy every field of `HypL` except the multiplicity column**, for
any weight `Λ` (the fields `PhaseCore` do not involve `Λ`). The hypotheses are those of
`GI.Algorithm.phaseTree_hyp`: the two cost fields, supplied by the stage-2 analysis. -/
theorem real_runs_core {cc : ChargingConstants} (hc : GI.Algorithm.Compat P cc)
    (hN6 : 6 ≤ (N : ℝ) ^ cc.γ) (K : ℝ)
    (leaf_cost : ∀ v, (GI.Algorithm.phaseTree P N cost).kind v = .leaf → cost v ≤ K)
    (toll : ∀ v, (GI.Algorithm.phaseTree P N cost).kind v ≠ .leaf →
      cost v ≤ (N : ℝ) ^ cc.a * K + (((GI.Algorithm.phaseTree P N cost).kind v).children.map cost).sum) :
    PhaseCore cc N K (GI.Algorithm.phaseTree P N cost) :=
  (GI.Algorithm.phaseTree_hyp hc hN6 K leaf_cost toll).toCore

/-- The real phase trees satisfy `HypL` at `Λ = x`. -/
theorem real_runs_hypL_x {cc : ChargingConstants} (hc : GI.Algorithm.Compat P cc)
    (hN6 : 6 ≤ (N : ℝ) ^ cc.γ) (K : ℝ)
    (leaf_cost : ∀ v, (GI.Algorithm.phaseTree P N cost).kind v = .leaf → cost v ≤ K)
    (toll : ∀ v, (GI.Algorithm.phaseTree P N cost).kind v ≠ .leaf →
      cost v ≤ (N : ℝ) ^ cc.a * K + (((GI.Algorithm.phaseTree P N cost).kind v).children.map cost).sum) :
    (GI.Algorithm.phaseTree P N cost).HypL cc xFn N K :=
  (GI.Algorithm.phaseTree_hyp hc hN6 K leaf_cost toll).toHypL hN6

end Real

/-! ## An explicit example with `Λ` constant and `N` arbitrarily large -/

section Example

open Real

variable (C : ChargingConstants) (hγ : C.γ = 9 / 10) (hJ : 6 ≤ C.J)

/-- The six classes of the example root: one child in each of the six rows. -/
noncomputable def exampleClasses (q : ℕ) : List (ChildClass Bool) :=
  [⟨.affected, [[false]]⟩, ⟨.unaffected, [[false]]⟩, ⟨.product 2, [[false]]⟩,
    ⟨.enumeration 2, [[false]]⟩, ⟨.continuation q, [[false]]⟩, ⟨.rowEvent, [[false]]⟩]

/-- The root state: domain size `2^(9t)+1` (just above `N^γ`). -/
noncomputable def exRoot (t : ℕ) : PotentialState :=
  ⟨2 ^ (9 * t) + 1, 1, C.κ, cBeta C.β * Real.log ⌈C.q₀⌉₊, 1⟩

/-- The child state: domain size `2^(9t-1)`. -/
noncomputable def exChild (t : ℕ) : PotentialState := ⟨2 ^ (9 * t - 1), 0, 0, 0, 0⟩

/-- The example phase tree. `true` is the root, `false` a leaf. -/
noncomputable def exampleTree (K : ℝ) (t : ℕ) : PhaseTree Bool where
  state := fun b => if b then exRoot C t else exChild t
  kind := fun b => if b then .charged (exampleClasses ⌈C.q₀⌉₊) else .leaf
  cost := fun b => if b then ((2 ^ (10 * t) : ℕ) : ℝ) ^ C.a * K + 6 * K else K

include hγ in
theorem ex_γ_rpow (t : ℕ) : ((2 ^ (10 * t) : ℕ) : ℝ) ^ C.γ = ((2 : ℝ) ^ (9 * t)) := by
  rw [hγ]
  push_cast
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have : ((10 * t : ℕ) : ℝ) * (9 / 10) = ((9 * t : ℕ) : ℝ) := by push_cast; ring
  rw [this, Real.rpow_natCast]

include hγ hJ in
/-- **`HypL` holds for the explicit two-level tree**, at every `t ≥ 1` and constant
`Λ ≥ log 8` (so `Λ` fixed, `N → ∞`). -/
theorem example_hypL {K Λ : ℝ} (hK : 0 ≤ K) (hΛ : xZero ≤ Λ) {t : ℕ} (ht : 1 ≤ t) :
    (exampleTree C K t).HypL C (fun _ => Λ) (2 ^ (10 * t)) K := by
  classical
  have hκ := C.κ_pos
  have hcβ0 := C.cBeta_pos
  have hq₀ := C.one_lt_q₀
  have hq1 : (1 : ℝ) ≤ ⌈C.q₀⌉₊ := by exact_mod_cast Nat.one_le_ceil_iff.mpr (by linarith)
  have hq₀' : C.q₀ ≤ (⌈C.q₀⌉₊ : ℝ) := Nat.le_ceil _
  have hlogq : 0 ≤ Real.log (⌈C.q₀⌉₊ : ℝ) := Real.log_nonneg hq1
  have hpow9 : (1 : ℕ) ≤ 2 ^ (9 * t - 1) := Nat.one_le_two_pow
  have hT9 : 2 * (2 ^ (9 * t - 1)) = 2 ^ (9 * t) := by
    rw [← pow_succ']; congr 1; omega
  have hpos : 512 ≤ 2 ^ (9 * t) := by
    calc 512 = 2 ^ 9 := by norm_num
      _ ≤ 2 ^ (9 * t) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrpow := ex_γ_rpow C hγ t
  have hθ12 := C.half_lt_θ
  have hsT : ((2 ^ (9 * t - 1) : ℕ) : ℝ) = ((2 ^ (9 * t) : ℕ) : ℝ) / 2 := by
    rw [← hT9]; push_cast; ring
  have hlogb2 : (2 : ℝ) ≤ Real.logb 2 ((2 ^ (9 * t) + 1 : ℕ) : ℝ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
    have : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
    rw [this]
    have h1 : ((512 : ℕ) : ℝ) ≤ ((2 ^ (9 * t) : ℕ) : ℝ) := by exact_mod_cast hpos
    push_cast at h1 ⊢
    linarith
  have hchild : ∀ c ∈ exampleClasses ⌈C.q₀⌉₊, ∀ b ∈ c.branches, ∀ u ∈ b,
      u = false ∧ c.row.Child C (exRoot C t) (exChild t) := by
    intro c hc b hb u hu
    simp only [exampleClasses, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
    have hcmono : (0 : ℝ) ≤ cBeta C.β * Real.log (⌈C.q₀⌉₊ : ℝ) := mul_nonneg hcβ0.le hlogq
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hb <;>
    subst hb <;> simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hu <;>
    subst hu <;> refine ⟨rfl, ?_⟩ <;>
    simp only [Row.Child, exRoot, exChild]
    · refine ⟨?_, by norm_num, ?_, ?_, by omega⟩
      · rw [hsT]; push_cast; nlinarith [(by norm_cast; omega : (1:ℝ) ≤ (2:ℝ)^(9*t)), pow_pos (by norm_num : (0:ℝ) < 2) (9*t)]
      · positivity
      · positivity
    · refine ⟨?_, by norm_num, ?_, ?_, by omega⟩
      · have : 2 ^ (9 * t - 1) ≤ 2 ^ (9 * t) := Nat.pow_le_pow_right (by norm_num) (by omega); omega
      · linarith
      · positivity
    · refine ⟨?_, by norm_num, ?_, ?_, by omega⟩
      · have : 2 ^ (9 * t - 1) ≤ 2 ^ (9 * t) := Nat.pow_le_pow_right (by norm_num) (by omega); omega
      · positivity
      · positivity
    · refine ⟨?_, by norm_num, ?_, ?_, by omega⟩
      · omega
      · positivity
      · positivity
    · refine ⟨?_, by norm_num, ?_, ?_, by omega⟩
      · have : 2 ^ (9 * t - 1) ≤ 2 ^ (9 * t) := Nat.pow_le_pow_right (by norm_num) (by omega); omega
      · positivity
      · linarith
    · refine ⟨?_, by norm_num, ?_, ?_, by omega⟩
      · have : 2 ^ (9 * t - 1) ≤ 2 ^ (9 * t) := Nat.pow_le_pow_right (by norm_num) (by omega); omega
      · positivity
      · positivity
  refine
    { nonneg := ?_
      leaf_small := ?_
      leaf_cost := ?_
      internal_large := ?_
      toll := ?_
      classes_le := ?_
      class_valid := ?_
      branch_pos := ?_
      branch_disjoint := ?_
      branch_child := ?_
      orbit_pos := ?_
      orbit_disjoint := ?_
      orbit_child := ?_
      class_fam := ?_ }
  · rintro (_ | _)
    · simp [exampleTree, exChild]
    · simp only [exampleTree, exRoot, if_true]
      refine ⟨by norm_num, hκ.le, mul_nonneg hcβ0.le hlogq⟩
  · rintro (_ | _) hk
    · simp only [exampleTree, exChild, Bool.false_eq_true, if_false]
      rw [hrpow]
      have : (2 ^ (9 * t - 1) : ℕ) ≤ 2 ^ (9 * t) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact_mod_cast this
    · simp [exampleTree] at hk
  · rintro (_ | _) hk
    · simp [exampleTree]
    · simp [exampleTree] at hk
  · rintro (_ | _) hk
    · simp [exampleTree] at hk
    · simp only [exampleTree, exRoot, if_true]
      rw [hrpow]
      have : ((2 ^ (9 * t) : ℕ) : ℝ) + 1 > ((2 ^ (9 * t) : ℕ) : ℝ) := by linarith
      push_cast at this ⊢
      linarith
  · rintro (_ | _) hk
    · simp [exampleTree] at hk
    · simp [exampleTree, exampleClasses, NodeKind.children]
      linarith
  · rintro (_ | _) cls hk
    · simp [exampleTree] at hk
    · simp [exampleTree] at hk
      subst hk
      simp only [exampleClasses, List.length_cons, List.length_nil]
      omega
  · rintro (_ | _) cls hk c hc
    · simp [exampleTree] at hk
    · simp [exampleTree] at hk
      subst hk
      simp only [exampleClasses, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · trivial
      · trivial
      · refine ⟨le_rfl, ?_⟩
        simp only [exampleTree, exRoot, if_true]
        exact hlogb2
      · refine ⟨le_rfl, ?_⟩
        simp only [exampleTree, exRoot, if_true]
        omega
      · exact hq₀'
      · trivial
  · rintro (_ | _) cls hk c hc b hb u hu
    · simp [exampleTree] at hk
    · simp [exampleTree] at hk
      subst hk
      obtain ⟨rfl, -⟩ := hchild c hc b hb u hu
      simp [exampleTree, exChild, hpow9]
  · rintro (_ | _) cls hk c hc b hb
    · simp [exampleTree] at hk
    · simp [exampleTree] at hk
      subst hk
      have hb' : b = [false] := by
        simp only [exampleClasses, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simpa using hb
      subst hb'
      simp only [exampleTree, exChild, exRoot, if_false, if_true, Bool.false_eq_true,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      have : 2 ^ (9 * t - 1) ≤ 2 ^ (9 * t) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  · rintro (_ | _) cls hk c hc b hb u hu
    · simp [exampleTree] at hk
    · simp [exampleTree] at hk
      subst hk
      obtain ⟨rfl, hch⟩ := hchild c hc b hb u hu
      simpa [exampleTree] using hch
  · rintro (_ | _) cs hk
    · simp [exampleTree] at hk
    · simp [exampleTree] at hk
  · rintro (_ | _) cs hk
    · simp [exampleTree] at hk
    · simp [exampleTree] at hk
  · rintro (_ | _) cs hk
    · simp [exampleTree] at hk
    · simp [exampleTree] at hk
  · rintro (_ | _) cls hk c hc
    · simp [exampleTree] at hk
    · simp [exampleTree] at hk
      subst hk
      have hdisj : ∀ c ∈ exampleClasses ⌈C.q₀⌉₊, ((1 : ℕ) : ℝ) ≤
          Row'.multL C ((fun _ => Λ) (exRoot C t).s) c.row := by
        intro c hc
        simp only [exampleClasses, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
        have hx0 := ChargingConstants.xZero_pos
        have hΛ0 : 0 < Λ := hx0.trans_le hΛ
        have hA1 := C.aStar_nonneg
        have ha0 := C.a_pos
        have hl2 := ChargingConstants.log_two_pos'
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
        · simp only [Nat.cast_one, Row'.multL]
          exact Real.one_le_exp (by positivity)
        · simp only [Nat.cast_one, Row'.multL]
          exact Real.one_le_exp (by positivity)
        · simp only [Nat.cast_one, Row'.multL]
          apply Real.one_le_exp
          push_cast
          positivity
        · simp only [Nat.cast_one, Row'.multL]
          apply Real.one_le_exp
          push_cast
          have : 0 ≤ Real.log 2 := hl2.le
          positivity
        · simp only [Nat.cast_one, Row'.multL]
          exact Real.one_le_rpow hq1 ha0.le
        · simp only [Nat.cast_one, Row'.multL]
          exact C.one_le_b₀
      have hc1 : (c.branches.length) = 1 := by
        simp only [exampleClasses, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      refine ⟨1, fun _ => 0, ?_, ?_⟩
      · exact hdisj c hc
      · intro j
        have hj : j = 0 := Fin.ext (by omega)
        subst hj
        have hbr : ∀ i : Fin c.branches.length, c.branches.get i = [false] := by
          intro i
          have hi := List.get_mem c.branches i
          simp only [exampleClasses, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
            simpa using hi
        have hfilter : (Finset.univ.filter (fun i : Fin c.branches.length =>
            (fun _ => (0 : Fin 1)) i = (0 : Fin 1))) = Finset.univ := by
          ext i; simp
        rw [hfilter]
        have hsum_eq : ∀ i ∈ (Finset.univ : Finset (Fin c.branches.length)),
            ((c.branches.get i).map fun u => ((exampleTree C K t).state u).s).sum =
              2 ^ (9 * t - 1) := by
          intro i _
          rw [hbr i]
          simp [exampleTree, exChild]
        rw [Finset.sum_congr rfl hsum_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, hc1]
        simp only [smul_eq_mul, one_mul]
        have h9 : 2 ^ (9 * t - 1) ≤ 2 ^ (9 * t) := Nat.pow_le_pow_right (by norm_num) (by omega)
        simp only [exampleTree, exRoot, if_true]
        omega

end Example

end GI.DegreeD
