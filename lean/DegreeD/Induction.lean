import Workspace.Paper.RunningTime

/-!
# Abstract weighted phase induction (Lemma 7.1 with the potential abstracted)

HJ's Lemma 7.1 (`GI.Paper.lem_main_phase_bound`) proves `cost v ≤ K * (s_v+2)^D exp(Φ v)`
for a phase tree whose children are charged against a *specific* potential `Φ`, using a
fixed six-row table. The induction itself does not care about the potential or the table.
This file proves it in that generality:

* the potential `Φ : V → ℝ` is arbitrary (nonnegative), and each class `c` of a charged node
  comes with a claimed drop `δ v c`;
* the branches of a class are grouped into at most `M` *families*, the sizes of the children
  in one family add up to at most the parent's size, and `M · exp(-δ v c) ≤ 1/(8J)`. These are
  the only facts about multiplicities the proof of Lemma 7.1 uses. Taking one family per
  branch gives HJ's form; grouping by (test, string, coset, …) gives the regrouping (H2) of
  Theorem R*.
* the node toll `τ` is arbitrary, charged against `(s+2)^D` (never against `Φ`).

This is the statement of "the potential induction", independent of any row table. The row
tables (HJ's table with `N^a` multiplicities, and the `Λ`-table for `n^{O(log d)}`) are
instances; see `HJInstance.lean` and `TableLambda.lean`.

Every lemma of the existing development that is used is proved there.
-/

namespace GI.DegreeD

open GI.Paper

variable {V : Type*}

/-- The weight `(s+2)^D exp(φ)`. -/
noncomputable def weight (D : ℕ) (s : ℕ) (φ : ℝ) : ℝ := ((s : ℝ) + 2) ^ D * Real.exp φ

/-- **The abstract charging conditions.** They are exactly the conditions that the proof of
Lemma 7.1 uses, with the potential `Φ` and the drops `δ` left abstract and the node toll `τ` a
parameter. -/
structure AbstractCharging (D J : ℕ) (K τ : ℝ) (T : PhaseTree V) (Φ : V → ℝ)
    (δ : V → ChildClass V → ℝ) : Prop where
  Φ_nonneg : ∀ v, 0 ≤ Φ v
  K_nonneg : 0 ≤ K
  one_le_J : 1 ≤ J
  three_le_D : 3 ≤ D
  /-- leaf cost -/
  leaf_cost : ∀ v, T.kind v = .leaf → T.cost v ≤ K
  /-- the node toll: an internal node costs at most `τ K` plus its children -/
  toll : ∀ v, T.kind v ≠ .leaf →
    T.cost v ≤ τ * K + (((T.kind v).children).map T.cost).sum
  /-- internal nodes have at least six positions -/
  six_le : ∀ v, T.kind v ≠ .leaf → 6 ≤ (T.state v).s
  /-- the toll is paid by the prefactor at a charged node -/
  two_τ_le : ∀ v, T.kind v ≠ .leaf → 2 * τ ≤ (((T.state v).s : ℝ) + 2) ^ D
  /-- the toll is paid by the orbit slack at an orbit node -/
  τ_le_slack : ∀ v, T.kind v ≠ .leaf → τ ≤ ((D : ℝ) / 2) * ((T.state v).s : ℝ) ^ (D - 1)
  /-- at most `J` classes per charged node -/
  classes_le : ∀ v cls, T.kind v = .charged cls → cls.length ≤ J
  /-- **the margin**: the branches of a class are grouped into `M` families, the children of one
  family have total size at most the parent's, and a family contributes `≤ exp(-δ) W`, so a
  class contributes at most `1/(8J)` of the parent's weight. -/
  class_families : ∀ v cls, T.kind v = .charged cls → ∀ c ∈ cls,
    ∃ (M : ℕ) (fam : Fin c.branches.length → Fin M),
      (M : ℝ) * Real.exp (-δ v c) ≤ 1 / (8 * J) ∧
      ∀ j : Fin M, ∑ i ∈ Finset.univ.filter (fun i => fam i = j),
        ((c.branches.get i).map fun u => (T.state u).s).sum ≤ (T.state v).s
  branch_pos : ∀ v cls, T.kind v = .charged cls → ∀ c ∈ cls, ∀ b ∈ c.branches,
    ∀ u ∈ b, 1 ≤ (T.state u).s
  /-- every child of a class drops the potential by at least its claimed drop -/
  branch_child : ∀ v cls, T.kind v = .charged cls → ∀ c ∈ cls, ∀ b ∈ c.branches,
    ∀ u ∈ b, Φ u ≤ Φ v - δ v c
  orbit_pos : ∀ v cs, T.kind v = .orbit cs → ∀ u ∈ cs,
    1 ≤ (T.state u).s ∧ (T.state u).s < (T.state v).s
  orbit_disjoint : ∀ v cs, T.kind v = .orbit cs →
    ((cs.map fun u => (T.state u).s).sum) ≤ (T.state v).s
  /-- children of an orbit node do not have a larger potential -/
  orbit_child : ∀ v cs, T.kind v = .orbit cs → ∀ u ∈ cs, Φ u ≤ Φ v

namespace AbstractCharging

variable {D J : ℕ} {K τ : ℝ} {T : PhaseTree V} {Φ : V → ℝ} {δ : V → ChildClass V → ℝ}

theorem J_pos (h : AbstractCharging D J K τ T Φ δ) : (0 : ℝ) < 8 * J := by
  have : (1 : ℝ) ≤ J := by exact_mod_cast h.one_le_J
  linarith

theorem log8J_pos (h : AbstractCharging D J K τ T Φ δ) : 0 < Real.log (8 * J) := by
  apply Real.log_pos
  have : (1 : ℝ) ≤ J := by exact_mod_cast h.one_le_J
  linarith

theorem W_ge (h : AbstractCharging D J K τ T Φ δ) (v : V) :
    ((((T.state v).s : ℝ) + 2) ^ D) ≤ weight D (T.state v).s (Φ v) := by
  unfold weight
  have h1 := Real.one_le_exp (h.Φ_nonneg v)
  have h0 : (0 : ℝ) ≤ (((T.state v).s : ℝ) + 2) ^ D := by positivity
  nlinarith

theorem one_le_W (h : AbstractCharging D J K τ T Φ δ) (v : V) :
    1 ≤ weight D (T.state v).s (Φ v) :=
  le_trans (one_le_pow₀ (by have : (0 : ℝ) ≤ (T.state v).s := Nat.cast_nonneg _; linarith))
    (h.W_ge v)

theorem W_pos (h : AbstractCharging D J K τ T Φ δ) (v : V) :
    0 ≤ weight D (T.state v).s (Φ v) := zero_le_one.trans (h.one_le_W v)

/-- A nonempty class has claimed drop at least `log(8J)`. This is where the positivity of the
drop used for termination comes from: it is a consequence of the margin, not an extra
hypothesis. -/
theorem drop_ge (h : AbstractCharging D J K τ T Φ δ) {v : V} {cls : List (ChildClass V)}
    (hv : T.kind v = .charged cls) {c : ChildClass V} (hc : c ∈ cls)
    {b : List V} (hb : b ∈ c.branches) : Real.log (8 * J) ≤ δ v c := by
  obtain ⟨M, fam, hm, -⟩ := h.class_families v cls hv c hc
  have hlen : (1 : ℝ) ≤ M := by
    obtain ⟨i, hi, -⟩ := List.mem_iff_getElem.mp hb
    have hM : 0 < M := Nat.lt_of_le_of_lt (Nat.zero_le _) (fam ⟨i, hi⟩).2
    exact_mod_cast hM
  have hJ := h.J_pos
  have hexp : Real.exp (-δ v c) ≤ 1 / (8 * J) := by
    have he := Real.exp_pos (-δ v c)
    nlinarith
  have hlog := Real.log_le_log (Real.exp_pos _) hexp
  rw [Real.log_exp, one_div, Real.log_inv] at hlog
  linarith

theorem mem_children_charged {v u : V} {cls : List (ChildClass V)}
    (hv : T.kind v = .charged cls) (hu : u ∈ (T.kind v).children) :
    ∃ c ∈ cls, ∃ b ∈ c.branches, u ∈ b := by
  rw [hv] at hu
  simp only [NodeKind.children] at hu
  obtain ⟨l, hl, hul⟩ := List.mem_flatten.mp hu
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hl
  obtain ⟨b, hb, hub⟩ := List.mem_flatten.mp hul
  exact ⟨c, hc, b, hb, hub⟩

/-- Well-foundedness of the child relation: an infinite path would drop `Φ` by a fixed
positive amount infinitely often, or decrease `s` forever. -/
theorem wf (h : AbstractCharging D J K τ T Φ δ) :
    WellFounded (fun u v => u ∈ (T.kind v).children) := by
  have hε := h.log8J_pos
  let μ : V → ℕ × ℕ := fun v => (⌊Φ v / Real.log (8 * J)⌋₊, (T.state v).s)
  have hwf : WellFounded (InvImage (Prod.Lex (· < ·) (· < ·)) μ) :=
    InvImage.wf μ (WellFounded.prod_lex wellFounded_lt wellFounded_lt)
  refine Subrelation.wf ?_ hwf
  intro u v hu
  have hΦu := h.Φ_nonneg u
  show Prod.Lex _ _ (μ u) (μ v)
  rw [Prod.lex_def]
  cases hk : T.kind v with
  | leaf => rw [hk] at hu; simp [NodeKind.children] at hu
  | charged cls =>
    left
    obtain ⟨c, hc, b, hb, hub⟩ := mem_children_charged hk hu
    have h1 := h.branch_child v cls hk c hc b hb u hub
    have h2 := h.drop_ge hk hc hb
    have h3 : Φ u / Real.log (8 * J) + 1 ≤ Φ v / Real.log (8 * J) := by
      rw [div_add_one hε.ne', div_le_div_iff_of_pos_right hε]; linarith
    have h4 := Nat.floor_le_floor (R := ℝ) h3
    rw [Nat.floor_add_one (div_nonneg hΦu hε.le)] at h4
    show ⌊Φ u / Real.log (8 * J)⌋₊ < ⌊Φ v / Real.log (8 * J)⌋₊
    omega
  | orbit cs =>
    rw [hk] at hu
    have h1 := h.orbit_child v cs hk u hu
    have h2 := (h.orbit_pos v cs hk u hu).2
    have h4 := Nat.floor_le_floor (R := ℝ) (div_le_div_of_nonneg_right h1 hε.le)
    show ⌊Φ u / Real.log (8 * J)⌋₊ < ⌊Φ v / Real.log (8 * J)⌋₊ ∨
      ⌊Φ u / Real.log (8 * J)⌋₊ = ⌊Φ v / Real.log (8 * J)⌋₊ ∧ (T.state u).s < (T.state v).s
    omega

/-- A list of children of `v`, all in one class, with total size at most `s_v`: its weight
is at most `exp(-δ) W(parent)`. -/
theorem list_weight (h : AbstractCharging D J K τ T Φ δ) {v : V} {cls : List (ChildClass V)}
    (hv : T.kind v = .charged cls) {c : ChildClass V} (hc : c ∈ cls) {l : List V}
    (hl : ∀ u ∈ l, ∃ b ∈ c.branches, u ∈ b)
    (hsize : ((l.map fun u => (T.state u).s).sum) ≤ (T.state v).s) :
    (l.map fun u => weight D (T.state u).s (Φ u)).sum ≤
      Real.exp (-δ v c) * weight D (T.state v).s (Φ v) := by
  have hprefactor : ((l.map T.state).map fun U => ((U.s : ℝ) + 2) ^ D).sum ≤
      (((T.state v).s : ℝ) + 2) ^ D :=
    list_prefactor_sum_le h.three_le_D (l.map T.state)
      (by
        intro U hU
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hU
        obtain ⟨b, hb, hub⟩ := hl u hu
        exact h.branch_pos v cls hv c hc b hb u hub)
      (by
        have h' : ((l.map fun u => (T.state u).s).sum : ℝ) ≤ (T.state v).s := by exact_mod_cast hsize
        simpa [Nat.cast_list_sum, List.map_map] using h')
  calc (l.map fun u => weight D (T.state u).s (Φ u)).sum
      ≤ (l.map fun u => (((T.state u).s : ℝ) + 2) ^ D * Real.exp (Φ v - δ v c)).sum := by
        apply List.sum_le_sum
        intro u hu
        obtain ⟨b, hb, hub⟩ := hl u hu
        unfold weight
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (h.branch_child v cls hv c hc b hb u hub)) (by positivity)
    _ = (l.map fun u => (((T.state u).s : ℝ) + 2) ^ D).sum * Real.exp (Φ v - δ v c) := by
        rw [List.sum_map_mul_right]
    _ = ((l.map T.state).map fun U => ((U.s : ℝ) + 2) ^ D).sum * Real.exp (Φ v - δ v c) := by
        rw [List.map_map]; rfl
    _ ≤ (((T.state v).s : ℝ) + 2) ^ D * Real.exp (Φ v - δ v c) :=
        mul_le_mul_of_nonneg_right hprefactor (Real.exp_pos _).le
    _ = Real.exp (-δ v c) * weight D (T.state v).s (Φ v) := by
        unfold weight
        rw [sub_eq_add_neg, Real.exp_add]; ring

/-- The weight of one class is at most `W(parent)/(8J)`: the branches are grouped into families
and each family contributes at most `exp(-δ) W`. This is the only place where the regrouping
(H2) enters the induction. -/
theorem class_weight (h : AbstractCharging D J K τ T Φ δ) {v : V} {cls : List (ChildClass V)}
    (hv : T.kind v = .charged cls) {c : ChildClass V} (hc : c ∈ cls) :
    (c.branches.flatten.map fun u => weight D (T.state u).s (Φ u)).sum ≤
      weight D (T.state v).s (Φ v) / (8 * J) := by
  have hJ := h.J_pos
  have hW := h.W_pos v
  obtain ⟨M, fam, hm, hfam⟩ := h.class_families v cls hv c hc
  rw [list_sum_map_flatten, ← Fin.sum_univ_fun_getElem]
  -- Group the sum over branches by family.
  have hsplit : ∑ i : Fin c.branches.length,
        ((c.branches[i.1]).map fun u => weight D (T.state u).s (Φ u)).sum =
      ∑ j : Fin M, ∑ i ∈ Finset.univ.filter (fun i => fam i = j),
        ((c.branches.get i).map fun u => weight D (T.state u).s (Φ u)).sum := by
    rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fam)]
    rfl
  rw [hsplit]
  have hbound : ∀ j : Fin M, ∑ i ∈ Finset.univ.filter (fun i => fam i = j),
      ((c.branches.get i).map fun u => weight D (T.state u).s (Φ u)).sum ≤
      Real.exp (-δ v c) * weight D (T.state v).s (Φ v) := by
    intro j
    set F := Finset.univ.filter (fun i => fam i = j) with hF
    -- The joint list of the family.
    set l : List V := (F.toList.map fun i => c.branches.get i).flatten with hl
    have hsum : ∀ g : V → ℝ, ∑ i ∈ F, ((c.branches.get i).map g).sum = (l.map g).sum := by
      intro g
      rw [hl, list_sum_map_flatten, List.map_map]
      exact (Finset.sum_map_toList F (fun i => ((c.branches.get i).map g).sum)).symm
    rw [hsum]
    apply h.list_weight hv hc
    · intro u hu
      rw [hl, List.mem_flatten] at hu
      obtain ⟨b, hb, hub⟩ := hu
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hb
      exact ⟨c.branches.get i, List.get_mem _ _, hub⟩
    · have := hsum (fun u => ((T.state u).s : ℝ))
      have hfamj := hfam j
      have h' : ((l.map fun u => (T.state u).s).sum : ℝ) ≤ (T.state v).s := by
        calc ((l.map fun u => (T.state u).s).sum : ℝ)
            = (l.map fun u => ((T.state u).s : ℝ)).sum := by
              simp [Nat.cast_list_sum, List.map_map]; rfl
          _ = ∑ i ∈ F, ((c.branches.get i).map fun u => ((T.state u).s : ℝ)).sum := this.symm
          _ = ((∑ i ∈ F, ((c.branches.get i).map fun u => (T.state u).s).sum : ℕ) : ℝ) := by
              push_cast
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [List.map_map]; rfl
          _ ≤ _ := by exact_mod_cast hfamj
      exact_mod_cast h'
  calc ∑ j : Fin M, ∑ i ∈ Finset.univ.filter (fun i => fam i = j),
        ((c.branches.get i).map fun u => weight D (T.state u).s (Φ u)).sum
      ≤ ∑ _j : Fin M, Real.exp (-δ v c) * weight D (T.state v).s (Φ v) :=
        Finset.sum_le_sum (fun j _ => hbound j)
    _ = M * (Real.exp (-δ v c) * weight D (T.state v).s (Φ v)) := by
        simp [Finset.sum_const, Finset.card_univ]
    _ = (M * Real.exp (-δ v c)) * weight D (T.state v).s (Φ v) := by ring
    _ ≤ 1 / (8 * J) * weight D (T.state v).s (Φ v) := mul_le_mul_of_nonneg_right hm hW
    _ = weight D (T.state v).s (Φ v) / (8 * J) := by ring

/-- The children of a charged node have total weight at most `W/2`. -/
theorem charged_children_weight (h : AbstractCharging D J K τ T Φ δ) {v : V}
    {cls : List (ChildClass V)} (hv : T.kind v = .charged cls) :
    (((T.kind v).children).map fun u => weight D (T.state u).s (Φ u)).sum ≤
      1 / 2 * weight D (T.state v).s (Φ v) := by
  have hJ := h.J_pos
  have hW := h.W_pos v
  let Wf : V → ℝ := fun u => weight D (T.state u).s (Φ u)
  have hsum : (((T.kind v).children).map Wf).sum =
      (cls.map fun c => (c.branches.flatten.map Wf).sum).sum := by
    rw [hv]; simp only [NodeKind.children]; rw [list_sum_map_flatten, List.map_map]; rfl
  have hcls : (cls.length : ℝ) ≤ J := by exact_mod_cast h.classes_le v cls hv
  calc (((T.kind v).children).map Wf).sum
      ≤ cls.length * (weight D (T.state v).s (Φ v) / (8 * J)) := by
        rw [hsum]; exact list_sum_le_length_mul _ _ _ (fun c hc => h.class_weight hv hc)
    _ ≤ J * (weight D (T.state v).s (Φ v) / (8 * J)) :=
        mul_le_mul_of_nonneg_right hcls (div_nonneg hW hJ.le)
    _ = weight D (T.state v).s (Φ v) / 8 := by
        have : (J : ℝ) ≠ 0 := by
          have : (1 : ℝ) ≤ J := by exact_mod_cast h.one_le_J
          linarith
        field_simp
    _ ≤ 1 / 2 * weight D (T.state v).s (Φ v) := by linarith

/-- At an orbit node the children have total weight at most `W − τ`. -/
theorem orbit_children_weight (h : AbstractCharging D J K τ T Φ δ) {v : V} {cs : List V}
    (hv : T.kind v = .orbit cs) :
    (((T.kind v).children).map fun u => weight D (T.state u).s (Φ u)).sum + τ ≤
      weight D (T.state v).s (Φ v) := by
  set S := T.state v with hS
  have hne : T.kind v ≠ .leaf := by rw [hv]; simp
  have h6 : (6 : ℝ) ≤ (S.s : ℝ) := by exact_mod_cast h.six_le v hne
  have hΦ0 := h.Φ_nonneg v
  rw [hv]
  simp only [NodeKind.children]
  have hpre : ((cs.map T.state).map fun U => ((U.s : ℝ) + 2) ^ D).sum ≤
      ((S.s : ℝ) + 1) ^ D + 3 ^ D :=
    list_orbit_prefactor_le h.three_le_D (cs.map T.state) (s := S.s)
      (by
        intro U hU
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hU
        exact h.orbit_pos v cs hv u hu)
      (by
        have := h.orbit_disjoint v cs hv
        have h' : ((cs.map fun u => (T.state u).s).sum : ℝ) ≤ S.s := by exact_mod_cast this
        simpa [Nat.cast_list_sum, List.map_map] using h')
  have hWsum : (cs.map fun u => weight D (T.state u).s (Φ u)).sum ≤
      (((S.s : ℝ) + 1) ^ D + 3 ^ D) * Real.exp (Φ v) := by
    calc (cs.map fun u => weight D (T.state u).s (Φ u)).sum
        ≤ (cs.map fun u => (((T.state u).s : ℝ) + 2) ^ D * Real.exp (Φ v)).sum := by
          apply List.sum_le_sum
          intro u hu
          unfold weight
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
            (h.orbit_child v cs hv u hu)) (by positivity)
      _ = (cs.map fun u => (((T.state u).s : ℝ) + 2) ^ D).sum * Real.exp (Φ v) := by
          rw [List.sum_map_mul_right]
      _ = ((cs.map T.state).map fun U => ((U.s : ℝ) + 2) ^ D).sum * Real.exp (Φ v) := by
          rw [List.map_map]; rfl
      _ ≤ _ := mul_le_mul_of_nonneg_right hpre (Real.exp_pos _).le
  have hgap := eq_main_orbit_slack_gap h.three_le_D h6
  have hτ := h.τ_le_slack v hne
  have he := Real.one_le_exp hΦ0
  have hgap0 : 0 ≤ ((S.s : ℝ) + 2) ^ D - ((S.s : ℝ) + 1) ^ D - 3 ^ D := by
    have : (0 : ℝ) ≤ ((D : ℝ) / 2) * (S.s : ℝ) ^ (D - 1) := by positivity
    linarith
  have hgapτ : τ ≤ ((S.s : ℝ) + 2) ^ D - ((S.s : ℝ) + 1) ^ D - 3 ^ D := hτ.trans hgap
  have hmul := mul_le_mul_of_nonneg_left he hgap0
  simp only [weight] at hWsum ⊢
  nlinarith

/-- **The abstract phase induction** (Lemma 7.1 in its general form). Under the abstract
charging conditions the child relation is well-founded and every node `v` costs at most
`K (s_v+2)^D exp(Φ v)`. -/
theorem cost_le (h : AbstractCharging D J K τ T Φ δ) (v : V) :
    T.cost v ≤ K * weight D (T.state v).s (Φ v) := by
  have hwf := h.wf
  refine hwf.induction (C := fun v => T.cost v ≤ K * weight D (T.state v).s (Φ v)) v ?_
  intro v ih
  have hK := h.K_nonneg
  have hW := h.W_pos v
  have hW1 := h.one_le_W v
  have hchildren : (((T.kind v).children).map T.cost).sum ≤
      K * (((T.kind v).children).map fun u => weight D (T.state u).s (Φ u)).sum := by
    rw [← List.sum_map_mul_left]
    exact List.sum_le_sum (fun u hu => ih u hu)
  cases hk : T.kind v with
  | leaf =>
    have := h.leaf_cost v hk
    nlinarith
  | charged cls =>
    have hne : T.kind v ≠ .leaf := by rw [hk]; simp
    have htoll := h.toll v hne
    have h1 := h.charged_children_weight hk
    have h2 := h.two_τ_le v hne
    have hWge := h.W_ge v
    have := mul_le_mul_of_nonneg_left h1 hK
    have hτW : 2 * τ ≤ weight D (T.state v).s (Φ v) := h2.trans hWge
    have := mul_le_mul_of_nonneg_left hτW hK
    nlinarith
  | orbit cs =>
    have hne : T.kind v ≠ .leaf := by rw [hk]; simp
    have htoll := h.toll v hne
    have h1 := h.orbit_children_weight hk
    have := mul_le_mul_of_nonneg_left h1 hK
    nlinarith

end AbstractCharging

end GI.DegreeD
