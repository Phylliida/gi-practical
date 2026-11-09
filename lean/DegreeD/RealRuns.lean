import DegreeD.ScriptFamilies
import DegreeD.RStarColumns
import DegreeD.HJInstance

/-!
# The real phase trees and the Λ-hypotheses

Connecting the abstract `PhaseTree.HypL` to the runs of HJ's algorithm (`GI.Algorithm.Run`).

* `giantClasses_fam`, `runKind_class_fam`: the family form of the multiplicity column holds at
  every charged vertex, under two local conditions on the vertex (`Run.VertexBound`):
  (i) the giant step of the vertex has `q ≤ d̃` (so `q ≤ max(d,6)`), (ii) a dispatcher vertex has
  at most `multL` cosets. Every other class is unconditional. In particular the affected and
  unaffected classes use the machine-checked regrouping (H2) (`aggregate_branch_fam`), with
  `9 q^{2κ}` families, which fits `multL` because of `family_le_multL`.
* `real_runs_hypL_const`: the phase tree restricted to a set `Good` of vertices, closed
  under children, satisfies `PhaseTree.HypL` with a *constant* weight `Λ = lam d`, under the
  conditions (i) and (ii) on `Good` vertices. Consequently (`real_runs_cost_le`) every `Good`
  vertex costs at most `K (s+2)^D exp(Φ_Λ)`. This is the real-run instance of Lemma 7.1 with
  parameter `Λ`. It holds with no assumption on `N` relative to `d`; it does not assert that any
  set `Good` with (i), (ii) is nonempty. That is the content of the remaining work: closure of
  `Γ̂_d` and the structural dispatcher `(M')` (see docs/w36-lean.md).
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.Paper GI.DegreeD
open scoped Pointwise

variable {P : Params}

/-! ### Local bounds of a vertex -/

/-- The local conditions a vertex needs for the Λ-table. An aggregation vertex: `q ≤ max(d,6)`.
A dispatcher vertex: at most `multL` cosets. Everything else: no condition. -/
def Run.LocalBound (cc : ChargingConstants) (d : ℕ) {m : Mode} {Ω C : Type} {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)} (r : Run P m S L A) : Prop :=
  match r with
  | .aggregate _ _ L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => L.q ≤ max d 6
  | .dispatch _ _ _ I _ _ _ _ _ _ _ => (I.n : ℝ) ≤ Row'.multL cc (lam d) I.kind.row
  | _ => True

/-- For a normalization vertex, the local conditions are those of its giant-step children. -/
def Run.VertexBound (cc : ChargingConstants) (d : ℕ) {m : Mode} {Ω C : Type} {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)} (r : Run P m S L A) : Prop :=
  match r with
  | .normalize _ _ _ _ _ _ _ _ _ _ _ _ _ _ r' => ∀ j, (r' j).LocalBound cc d
  | r => r.LocalBound cc d

/-- A class with `ClassOK` and at most `multL` branches has the identity family structure. -/
theorem class_fam_of_ok {cc : ChargingConstants} {N : ℕ} {X : PotentialState}
    {c : ChildClass (PNode P)} (hok : ClassOK cc N X c) {Λ : ℝ}
    (hM : (c.branches.length : ℝ) ≤ Row'.multL cc Λ c.row) :
    ∃ (M : ℕ) (fam : Fin c.branches.length → Fin M),
      (M : ℝ) ≤ Row'.multL cc Λ c.row ∧
      ∀ j : Fin M, ∑ i ∈ Finset.univ.filter (fun i => fam i = j),
        ((c.branches.get i).map fun u => (u.leaf.state P.κ).s).sum ≤ X.s := by
  have hs : ListFam (c.branches.map fun b => (b.map fun u => (u.leaf.state P.κ).s).sum)
      c.branches.length X.s := by
    have h := ListFam.singletons (L := c.branches.map fun b => (b.map fun u => (u.leaf.state P.κ).s).sum)
      (B := X.s) (by
      intro x hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
      exact hok.disj b hb)
    simpa using h
  obtain ⟨fam, hfam⟩ := ListFam.toFin_map _ _ hs
  exact ⟨c.branches.length, fam, hM, hfam⟩

theorem one_le_two_multL_affected (cc : ChargingConstants) (d : ℕ) :
    (2 : ℝ) ≤ Row'.multL cc (lam d) .affected := by
  have hL := lam_pos d
  have h1 : 1 ≤ cc.aStar := by
    unfold ChargingConstants.aStar
    rw [le_div_iff₀ cc.γ_pos]
    nlinarith [cc.γ_lt_one, cc.one_le_a]
  have hx : xZero ≤ lam d := xZero_le_lam d
  have h2 : 1 ≤ cc.aStar * lam d := by
    have : 1 ≤ lam d := one_le_lam d
    nlinarith
  have hlog2 : Real.log 2 ≤ cc.aStar * lam d := by
    have : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9; linarith
    linarith
  simp only [Row'.multL]
  calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
    _ ≤ Real.exp (cc.aStar * lam d) := Real.exp_le_exp.mpr hlog2

theorem one_le_multL_rowEvent (cc : ChargingConstants) (d : ℕ) :
    ((1 : ℕ) : ℝ) ≤ Row'.multL cc (lam d) .rowEvent := by
  simp only [Nat.cast_one, Row'.multL]; exact cc.one_le_b₀

/-! ### The family bounds of a giant step -/

/-- **The classes of a giant step have `multL`-many families.** The aggregation vertices use
`aggregate_branch_fam` (the regrouping (H2)); the continuation class and the row-event class keep
their branches as families. -/
theorem giantClasses_fam {cc : ChargingConstants} (hc : Compat P cc) {N : ℕ} (hN1 : 1 ≤ N) {d : ℕ}
    (hab : ((2 * P.κ : ℕ) : ℝ) + Real.log (9 : ℕ) / Real.log 48 ≤ cc.aStar)
    {m : Mode} {Ω C : Type} [Finite Ω] {S : State Ω C} {L : Option (SuppliedLabels S)}
    {A : Set (Perm Ω)} (r : Run P m S L A) (hSN : S.N = N) (hb : r.LocalBound cc d) :
    ∀ c ∈ giantClasses r, ∃ (M : ℕ) (fam : Fin c.branches.length → Fin M),
      (M : ℝ) ≤ Row'.multL cc (lam d) c.row ∧
      ∀ j : Fin M, ∑ i ∈ Finset.univ.filter (fun i => fam i = j),
        ((c.branches.get i).map fun u => (u.leaf.state P.κ).s).sum ≤ S.size := by
  have hok := (giantClasses_ok hc hN1 r hSN).2
  cases r with
  | rowColumns hs htr L hrow I hcore hR hh1 hh hN hhier r' =>
    intro c hc'
    simp only [giantClasses, List.mem_singleton] at hc'
    subst hc'
    apply class_fam_of_ok (hok _ (by simp [giantClasses]))
    simp only [List.length_singleton]
    exact one_le_multL_rowEvent cc d
  | aggregate hs htr L hnot hq₀ I hsel hcon b e τ hτ child hchild hN hhier hbk A' r' =>
    have hq : L.q ≤ max d 6 := hb
    have hq1 : 1 ≤ L.q := by have := I.q_two; omega
    have hM9 : ((9 * L.q ^ (2 * P.κ) : ℕ) : ℝ) ≤ Row'.multL cc (lam d) .affected := by
      have h := family_le_multL (C := cc) (d := d) (q := L.q) (b := 9) (e := 2 * P.κ) hq1 hq (by norm_num)
        hab
      push_cast at h ⊢
      exact h
    intro c hc'
    simp only [giantClasses, List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl
    · obtain ⟨fam, hfam⟩ := ListFam.toFin_map _ _ (aggregate_branch_fam I e (P.θ * S.size) true)
      exact ⟨9 * L.q ^ (2 * P.κ), fam, hM9, hfam⟩
    · obtain ⟨fam, hfam⟩ := ListFam.toFin_map _ _ (aggregate_branch_fam I e (P.θ * S.size) false)
      refine ⟨9 * L.q ^ (2 * P.κ), fam, ?_, hfam⟩
      simpa [Row'.multL] using hM9
    · apply class_fam_of_ok (hok _ (by simp [giantClasses]))
      exact (hok _ (by simp [giantClasses])).mult
  | _ => intro c hc'; simp [giantClasses] at hc'

/-- **The family form of the multiplicity column at every charged vertex.** -/
theorem runKind_class_fam {cc : ChargingConstants} (hc : Compat P cc) {N : ℕ} (hN2 : 2 ≤ N)
    {d : ℕ} (hab : ((2 * P.κ : ℕ) : ℝ) + Real.log (9 : ℕ) / Real.log 48 ≤ cc.aStar)
    {m : Mode} {Ω C : Type} [Finite Ω] {S : State Ω C} {L : Option (SuppliedLabels S)}
    {A : Set (Perm Ω)} (r : Run P m S L A) (hSN : S.N = N) (hb : r.VertexBound cc d)
    {cls : List (ChildClass (PNode P))} (hk : runKind r = .charged cls) :
    ∀ c ∈ cls, ∃ (M : ℕ) (fam : Fin c.branches.length → Fin M),
      (M : ℝ) ≤ Row'.multL cc (lam d) c.row ∧
      ∀ j : Fin M, ∑ i ∈ Finset.univ.filter (fun i => fam i = j),
        ((c.branches.get i).map fun u => (u.leaf.state P.κ).s).sum ≤ S.size := by
  have hN1 : 1 ≤ N := by omega
  have hok := (runKind_charged_ok hc hN2 r hSN hk).2
  cases r with
  | direct => simp [runKind] at hk
  | fresh => simp [runKind] at hk
  | threshold => simp [runKind] at hk
  | orbitStop => simp [runKind] at hk
  | orbitChain => simp [runKind] at hk
  | floorReset => simp only [runKind, NodeKind.charged.injEq] at hk; subst hk; simp
  | rowTerminal =>
    simp only [runKind, NodeKind.charged.injEq] at hk; subst hk
    exact giantClasses_fam hc hN1 hab _ hSN hb
  | rowColumns =>
    simp only [runKind, NodeKind.charged.injEq] at hk; subst hk
    exact giantClasses_fam hc hN1 hab _ hSN hb
  | aggregate =>
    simp only [runKind, NodeKind.charged.injEq] at hk; subst hk
    exact giantClasses_fam hc hN1 hab _ hSN hb
  | dispatch hs htr hfl I child hchild hN hhier hbk A' r' =>
    simp only [runKind, NodeKind.charged.injEq] at hk; subst hk
    have hb' : (I.n : ℝ) ≤ Row'.multL cc (lam d) I.kind.row := hb
    intro c hc'
    simp only [List.mem_singleton] at hc'
    subst hc'
    apply class_fam_of_ok (hok _ (by simp))
    simpa using hb'
  | normalize hs htr hfl Q hsm c' hq hkc hkl NA hNA m' hmode A' r' =>
    have hb' : ∀ j, (r' j).LocalBound cc d := hb
    simp only [runKind] at hk
    have hchild : ∀ j, (NA.child j).Inst NA.I.G' S.dom S.x (S.y ∘ NA.I.τ j) :=
      fun _ => ⟨rfl, rfl, rfl, rfl⟩
    have hN : ∀ j, (NA.child j).N = S.N := fun _ => rfl
    split_ifs at hk with hm'
    · simp only [NodeKind.charged.injEq] at hk; subst hk
      intro c hc'
      simp only [List.mem_singleton] at hc'
      subst hc'
      apply class_fam_of_ok (hok _ (by simp))
      simp only [List.length_ofFn]
      have hk2 : (NA.I.k : ℝ) ≤ 2 := by exact_mod_cast NA.I.k_le
      exact hk2.trans (one_le_two_multL_affected cc d)
    · simp only [NodeKind.charged.injEq] at hk; subst hk
      intro c hc'
      obtain ⟨l, hl, hcl⟩ := List.mem_flatten.1 hc'
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hl
      haveI : Finite Ω := ‹Finite Ω›
      obtain ⟨M, fam, hM, hfam⟩ := giantClasses_fam hc hN1 hab (r' j) ((hN j).trans hSN) (hb' j) c hcl
      refine ⟨M, fam, hM, fun t => (hfam t).trans ?_⟩
      exact size_le_of_subset (hchild j).2.1.le

/-! ### The phase tree restricted to a good set of vertices -/

section Restricted

open Classical in
/-- The phase tree of HJ's runs, restricted to the vertices `Good` (for Theorem R*: the runs
whose group lies in `Γ̂_d`). Other vertices are isolated leaves with zero resources, like the
vertices outside the phase in `phaseTree`. -/
noncomputable def phaseTreeOn (P : Params) (N : ℕ) (cost : PNode P → ℝ)
    (Good : PNode P → Prop) : PhaseTree (PNode P) where
  state p := if p.Inv N ∧ Good p then p.leaf.state P.κ else ⟨0, 0, 0, 0, 0⟩
  kind p := if p.Inv N ∧ Good p then p.rawKind else .leaf
  cost := cost

variable {N : ℕ} {cost : PNode P → ℝ} {Good : PNode P → Prop}

theorem phaseTreeOn_state_of {v : PNode P} (hv : v.Inv N) (hg : Good v) :
    (phaseTreeOn P N cost Good).state v = v.leaf.state P.κ := by
  simp [phaseTreeOn, hv, hg]

theorem phaseTreeOn_kind_of {v : PNode P} (hv : v.Inv N) (hg : Good v) :
    (phaseTreeOn P N cost Good).kind v = v.rawKind := by
  simp [phaseTreeOn, hv, hg]

theorem phaseTreeOn_kind_not {v : PNode P} (hv : ¬ (v.Inv N ∧ Good v)) :
    (phaseTreeOn P N cost Good).kind v = .leaf := by
  simp [phaseTreeOn, hv]

theorem phaseTreeOn_state_not {v : PNode P} (hv : ¬ (v.Inv N ∧ Good v)) :
    (phaseTreeOn P N cost Good).state v = ⟨0, 0, 0, 0, 0⟩ := by
  simp [phaseTreeOn, hv]

theorem phaseTreeOn_charged {v : PNode P} {cls : List (ChildClass (PNode P))}
    (hk : (phaseTreeOn P N cost Good).kind v = .charged cls) :
    v.Inv N ∧ Good v ∧ v.leaf.pt = none ∧ runKind v.leaf.run = .charged cls := by
  by_cases hv : v.Inv N ∧ Good v
  · rw [phaseTreeOn_kind_of hv.1 hv.2] at hk
    refine ⟨hv.1, hv.2, ?_⟩
    unfold PNode.rawKind at hk
    split at hk
    · cases hk
    · exact ⟨by assumption, hk⟩
  · rw [phaseTreeOn_kind_not hv] at hk; cases hk

theorem phaseTreeOn_orbit {v : PNode P} {cs : List (PNode P)}
    (hk : (phaseTreeOn P N cost Good).kind v = .orbit cs) :
    v.Inv N ∧ Good v ∧ v.leaf.pt = none ∧ runKind v.leaf.run = .orbit cs := by
  by_cases hv : v.Inv N ∧ Good v
  · rw [phaseTreeOn_kind_of hv.1 hv.2] at hk
    refine ⟨hv.1, hv.2, ?_⟩
    unfold PNode.rawKind at hk
    split at hk
    · cases hk
    · exact ⟨by assumption, hk⟩
  · rw [phaseTreeOn_kind_not hv] at hk; cases hk

theorem mem_children_of_class {cls : List (ChildClass (PNode P))} {c : ChildClass (PNode P)}
    (hc : c ∈ cls) {b : List (PNode P)} (hb : b ∈ c.branches) {u : PNode P} (hu : u ∈ b) :
    u ∈ (NodeKind.charged cls).children := by
  simp only [NodeKind.children]
  exact List.mem_flatten.2 ⟨_, List.mem_map_of_mem hc, List.mem_flatten.2 ⟨b, hb, hu⟩⟩

/-- **The real phase tree, restricted to a child-closed set `Good`, satisfies the hypotheses of
Lemma 7.1 with constant weight `Λ = lam d`**, provided every `Good` vertex satisfies the local
bounds (`Run.VertexBound`): a giant step at the vertex has `q ≤ max(d,6)`, a dispatcher vertex
has at most `multL` cosets. Everything else (the classes, sizes, child relations, the
multiplicity of the affected and unaffected rows by the regrouping (H2)) is proved here.
The cost hypotheses are those of `phaseTree_hyp`, on the restricted tree. -/
theorem phaseTreeOn_hypL {cc : ChargingConstants} (hc : Compat P cc) (hN6 : 6 ≤ (N : ℝ) ^ cc.γ)
    {d : ℕ} (hab : ((2 * P.κ : ℕ) : ℝ) + Real.log (9 : ℕ) / Real.log 48 ≤ cc.aStar) (K : ℝ)
    (hclosed : ∀ v, v.Inv N → Good v → ∀ u, u ∈ v.rawKind.children → u.Inv N → Good u)
    (hbound : ∀ v, v.Inv N → Good v → v.leaf.run.VertexBound cc d)
    (leaf_cost : ∀ v, (phaseTreeOn P N cost Good).kind v = .leaf → cost v ≤ K)
    (toll : ∀ v, (phaseTreeOn P N cost Good).kind v ≠ .leaf →
      cost v ≤ (N : ℝ) ^ cc.a * K +
        (((phaseTreeOn P N cost Good).kind v).children.map cost).sum) :
    (phaseTreeOn P N cost Good).HypL cc (fun _ => lam d) N K := by
  have hκ := hc.κ_five
  have hN2 : 2 ≤ N := two_le_of_six_le cc.γ_pos.le hN6
  have hγ : cc.γ = P.γ := hc.γ_eq
  set T := phaseTreeOn P N cost Good with hT
  have hst : ∀ u, u.Inv N → Good u → T.state u = u.leaf.state P.κ :=
    fun u hu hg => phaseTreeOn_state_of hu hg
  -- classes of a charged vertex
  have hcls : ∀ v cls, T.kind v = .charged cls →
      v.Inv N ∧ Good v ∧ cls.length ≤ 6 ∧ ∀ c ∈ cls, ClassOK cc N (T.state v) c := by
    intro v cls hk
    obtain ⟨hv, hg, hpt, hk'⟩ := phaseTreeOn_charged hk
    refine ⟨hv, hg, ?_⟩
    obtain ⟨Ω, m, C, S, L, A, r, pt⟩ := v
    simp only at hpt
    subst hpt
    haveI := hv.fin
    rw [hst _ hv hg]
    exact runKind_charged_ok hc hN2 r hv.N_eq hk'
  -- orbit vertices
  have horb : ∀ v cs, T.kind v = .orbit cs →
      v.Inv N ∧ Good v ∧ (∀ u ∈ cs, u.Inv N ∧ 1 ≤ (u.leaf.state P.κ).s ∧
        (u.leaf.state P.κ).s < (T.state v).s ∧
        GI.Paper.OrbitChild (T.state v) (u.leaf.state P.κ)) ∧
      (cs.map fun u => (u.leaf.state P.κ).s).sum ≤ (T.state v).s := by
    intro v cs hk
    obtain ⟨hv, hg, hpt, hk'⟩ := phaseTreeOn_orbit hk
    refine ⟨hv, hg, ?_⟩
    obtain ⟨Ω, m, C, S, L, A, r, pt⟩ := v
    simp only at hpt
    subst hpt
    haveI := hv.fin
    rw [hst _ hv hg]
    exact runKind_orbit_ok r hv.N_eq hκ (hv.orbit_h rfl) hk'
  -- the state of a charged child
  have hchildst : ∀ v cls, T.kind v = .charged cls → ∀ c ∈ cls, ∀ b ∈ c.branches, ∀ u ∈ b,
      T.state u = u.leaf.state P.κ := by
    intro v cls hk c hc' b hb u hu
    obtain ⟨hv, hg, -, hok⟩ := hcls v cls hk
    have hinv := (hok c hc').inv b hb u hu
    have hchild : u ∈ v.rawKind.children := by
      obtain ⟨-, -, hpt, hk'⟩ := phaseTreeOn_charged hk
      have : v.rawKind = .charged cls := by
        unfold PNode.rawKind; rw [hpt]; exact hk'
      rw [this]; exact mem_children_of_class hc' hb hu
    exact hst u hinv (hclosed v hv hg u hchild hinv)
  have horbst : ∀ v cs, T.kind v = .orbit cs → ∀ u ∈ cs, T.state u = u.leaf.state P.κ := by
    intro v cs hk u hu
    obtain ⟨hv, hg, h, -⟩ := horb v cs hk
    have hinv := (h u hu).1
    have hchild : u ∈ v.rawKind.children := by
      obtain ⟨-, -, hpt, hk'⟩ := phaseTreeOn_orbit hk
      have : v.rawKind = .orbit cs := by
        unfold PNode.rawKind; rw [hpt]; exact hk'
      rw [this]; exact hu
    exact hst u hinv (hclosed v hv hg u hchild hinv)
  refine
    { nonneg := ?_
      leaf_small := ?_
      leaf_cost := leaf_cost
      internal_large := ?_
      toll := toll
      classes_le := ?_
      class_valid := ?_
      branch_pos := ?_
      branch_disjoint := ?_
      branch_child := ?_
      orbit_pos := ?_
      orbit_disjoint := ?_
      orbit_child := ?_
      class_fam := ?_ }
  · intro v
    by_cases hv : v.Inv N ∧ Good v
    · rw [hst v hv.1 hv.2]
      exact ⟨State.hierRho_nonneg _, Nat.cast_nonneg _, State.hierQ_nonneg _⟩
    · rw [phaseTreeOn_state_not hv]; simp
  · intro v hk
    by_cases hv : v.Inv N ∧ Good v
    · rw [hst v hv.1 hv.2]
      rw [phaseTreeOn_kind_of hv.1 hv.2] at hk
      obtain ⟨Ω, m, C, S, L, A, r, pt⟩ := v
      haveI := hv.1.fin
      have hthr : r.kind = .threshold → (S.size : ℝ) ≤ (N : ℝ) ^ cc.γ := by
        intro hr
        cases r <;> simp [Run.kind] at hr
        rename_i hs _
        rw [hγ, ← hv.1.N_eq]; exact hs
      cases pt with
      | none =>
        have : runKind r = .leaf := hk
        exact hthr ((runKind_leaf r hv.1.mode).1 this)
      | some a =>
        obtain ⟨hr, ha⟩ := hv.1.virt a rfl
        refine le_trans ?_ (hthr hr)
        change ((Nat.card (orb S.G a) : ℕ) : ℝ) ≤ ((Nat.card S.dom : ℕ) : ℝ)
        exact_mod_cast Nat.card_mono (Set.toFinite _) (orb_subset S.dom_inv ha)
    · rw [phaseTreeOn_state_not hv]
      simp only [CharP.cast_eq_zero]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · intro v hk
    by_cases hv : v.Inv N ∧ Good v
    · rw [hst v hv.1 hv.2]
      rw [phaseTreeOn_kind_of hv.1 hv.2] at hk
      obtain ⟨Ω, m, C, S, L, A, r, pt⟩ := v
      cases pt with
      | none =>
        have hk' : runKind r ≠ .leaf := hk
        have hthr : r.kind ≠ .threshold := fun h => hk' ((runKind_leaf r hv.1.mode).2 h)
        have := Run.internal_large r hv.1.mode hthr
        rw [hγ, ← hv.1.N_eq]
        exact this
      | some a => exact absurd rfl hk
    · exact absurd (phaseTreeOn_kind_not hv) hk
  · intro v cls hk
    exact (hcls v cls hk).2.2.1.trans (by exact_mod_cast hc.J_six)
  · intro v cls hk c hc'
    exact ((hcls v cls hk).2.2.2 c hc').valid
  · intro v cls hk c hc' b hb u hu
    have h := (hcls v cls hk).2.2.2 c hc'
    rw [hchildst v cls hk c hc' b hb u hu]
    exact h.pos b hb u hu
  · intro v cls hk c hc' b hb
    have h := (hcls v cls hk).2.2.2 c hc'
    rw [List.map_congr_left (fun u hu => by rw [hchildst v cls hk c hc' b hb u hu])]
    exact h.disj b hb
  · intro v cls hk c hc' b hb u hu
    have h := (hcls v cls hk).2.2.2 c hc'
    rw [hchildst v cls hk c hc' b hb u hu]
    exact h.child b hb u hu
  · intro v cs hk u hu
    obtain ⟨-, -, h, -⟩ := horb v cs hk
    obtain ⟨h1, h2, h3, -⟩ := h u hu
    rw [horbst v cs hk u hu]
    exact ⟨h2, h3⟩
  · intro v cs hk
    rw [List.map_congr_left (fun u hu => by rw [horbst v cs hk u hu])]
    exact (horb v cs hk).2.2.2
  · intro v cs hk u hu
    obtain ⟨-, -, h, -⟩ := horb v cs hk
    obtain ⟨h1, -, -, h4⟩ := h u hu
    rw [horbst v cs hk u hu]
    exact h4
  · intro v cls hk c hc'
    obtain ⟨hv, hg, hpt, hk'⟩ := phaseTreeOn_charged hk
    obtain ⟨Ω, m, C, S, L, A, r, pt⟩ := v
    simp only at hpt
    subst hpt
    haveI := hv.fin
    have hb : r.VertexBound cc d := hbound _ hv hg
    obtain ⟨M, fam, hM, hfam⟩ := runKind_class_fam hc hN2 hab r hv.N_eq hb hk' c hc'
    have hstv : (T.state ⟨Ω, m, C, S, L, A, r, none⟩).s = S.size := by
      rw [hst _ hv hg]; rfl
    simp only [hstv]
    refine ⟨M, fam, ?_, fun j => ?_⟩
    · have hlam : (fun _ => lam d) (S.size) = lam d := rfl
      exact hM
    · refine le_trans (le_of_eq ?_) (hfam j)
      apply Finset.sum_congr rfl
      intro i _
      apply congrArg
      apply List.map_congr_left
      intro u hu
      rw [hchildst _ cls hk c hc' _ (List.get_mem _ _) u hu]

/-- The real-run form of Lemma 7.1 with parameter `Λ` (at `Λ = lam d`, constant). Under the
hypotheses of `phaseTreeOn_hypL`, every vertex of the restricted phase tree costs at most
`K (s+2)^D exp(Φ_Λ)`, and the tree terminates. -/
theorem real_runs_cost_le {cc : ChargingConstants} (hc : Compat P cc) (hN6 : 6 ≤ (N : ℝ) ^ cc.γ)
    (hN2 : 2 ≤ (N : ℝ) ^ (cc.γ * cc.D - cc.a))
    {d : ℕ} (hab : ((2 * P.κ : ℕ) : ℝ) + Real.log (9 : ℕ) / Real.log 48 ≤ cc.aStar)
    {K : ℝ} (hK : 0 ≤ K)
    (hclosed : ∀ v, v.Inv N → Good v → ∀ u, u ∈ v.rawKind.children → u.Inv N → Good u)
    (hbound : ∀ v, v.Inv N → Good v → v.leaf.run.VertexBound cc d)
    (leaf_cost : ∀ v, (phaseTreeOn P N cost Good).kind v = .leaf → cost v ≤ K)
    (toll : ∀ v, (phaseTreeOn P N cost Good).kind v ≠ .leaf →
      cost v ≤ (N : ℝ) ^ cc.a * K +
        (((phaseTreeOn P N cost Good).kind v).children.map cost).sum) :
    WellFounded (fun u v => u ∈ ((phaseTreeOn P N cost Good).kind v).children) ∧
    ∀ v, cost v ≤ K * GI.DegreeD.weight cc.D ((phaseTreeOn P N cost Good).state v).s
      (GI.DegreeD.ΦL cc.A cc.B (fun _ => lam d) ((phaseTreeOn P N cost Good).state v)) := by
  have h := phaseTreeOn_hypL hc hN6 hab K hclosed hbound leaf_cost toll
  exact h.cost_le (const_weightFn (xZero_le_lam d)) hN6 hN2 hK


/-! ### Satisfiability on the real runs: the regime `d ≥ N` -/

/-- `multL` is monotone in `Λ`. -/
theorem multL_mono (cc : ChargingConstants) {Λ Λ' : ℝ} (h0 : 0 ≤ Λ) (h : Λ ≤ Λ')
    {X : PotentialState} {R : Row} (hv : R.Valid cc X) :
    Row'.multL cc Λ R ≤ Row'.multL cc Λ' R := by
  have hA := cc.aStar_nonneg
  have ha := cc.a_pos
  cases R with
  | affected =>
    simp only [Row'.multL]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h hA)
  | unaffected =>
    simp only [Row'.multL]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h hA)
  | product r =>
    obtain ⟨hr, -⟩ := hv
    have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
    simp only [Row'.multL]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left h (by nlinarith)
  | enumeration d =>
    obtain ⟨hd, -⟩ := hv
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hl : 0 ≤ Real.log d := Real.log_nonneg (by linarith)
    simp only [Row'.multL]
    apply Real.exp_le_exp.mpr
    have hc : 0 ≤ cc.a + cc.aStar / Real.log 2 := by
      have := ChargingConstants.log_two_pos'; positivity
    calc (cc.a + cc.aStar / Real.log 2) * Λ * Real.log d
        ≤ (cc.a + cc.aStar / Real.log 2) * Λ' * Real.log d := by
          apply mul_le_mul_of_nonneg_right _ hl
          exact mul_le_mul_of_nonneg_left h hc
      _ = _ := rfl
  | continuation q => simp only [Row'.multL]; exact le_refl _
  | rowEvent => simp only [Row'.multL]; exact le_refl _

/-- `log(s+2) ≤ lam d` when `s ≤ N ≤ d`. -/
theorem xFn_le_lam {s N d : ℕ} (hs : s ≤ N) (hNd : N ≤ d) : xFn s ≤ lam d := by
  unfold xFn lam
  apply Real.log_le_log (by positivity)
  have h1 : (s : ℝ) ≤ d := by exact_mod_cast hs.trans hNd
  have h2 : (d : ℝ) ≤ (max d 6 : ℕ) := by exact_mod_cast le_max_left d 6
  have h6 : (6 : ℝ) ≤ (max d 6 : ℕ) := by exact_mod_cast le_max_right d 6
  linarith

/-- For a vertex with `s ≤ N ≤ d`, the dispatcher bound `I.n ≤ multL` of `Run.LocalBound`
holds automatically: `I.n ≤ Row.mult` by HJ, and `Row.mult ≤ multL` at `Λ = x ≤ lam d`. -/
theorem localBound_of_N_le {cc : ChargingConstants} (hc : Compat P cc) {N : ℕ}
    (hN6 : 6 ≤ (N : ℝ) ^ cc.γ) {d : ℕ} (hNd : N ≤ d) {m : Mode} {Ω C : Type} [Finite Ω]
    {S : State Ω C} {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)} (r : Run P m S L A)
    (hSN : S.N = N) (hSsize : S.size ≤ N) : r.LocalBound cc d := by
  have hN2 := two_le_of_six_le (N := N) cc.γ_pos.le hN6
  cases r with
  | aggregate hs htr L hnot hq₀ I hsel hcon b e τ hτ child hchild hN hhier hbk A' r' =>
    show L.q ≤ max d 6
    have h1 : L.q ≤ S.N := I.q_le
    rw [hSN] at h1
    exact (h1.trans hNd).trans (le_max_left _ _)
  | dispatch hs htr hfl I child hchild hN hhier hbk A' r' =>
    show (I.n : ℝ) ≤ Row'.multL cc (lam d) I.kind.row
    have hk : runKind (Run.dispatch (P := P) hs htr hfl I child hchild hN hhier hbk A' r') =
        .charged [⟨I.kind.row, List.ofFn fun j => (r' j).forestP⟩] := rfl
    obtain ⟨-, hok⟩ := runKind_charged_ok hc hN2 _ hSN hk
    have hok' := hok _ (List.mem_singleton.2 rfl)
    have hγeq : (N : ℝ) ^ cc.γ < (S.size : ℝ) := by
      have := hs; rw [hSN, ← hc.γ_eq] at this; exact this
    have h6 : 6 ≤ (S.size : ℝ) := hN6.trans hγeq.le
    have hmult : (I.n : ℝ) ≤ Row.mult cc N I.kind.row := by
      have := hok'.mult
      simpa only [List.length_ofFn] using this
    have hv := hok'.valid
    have h1 := mult_le_multL_x cc (N := N) (S := S.res P.κ) hγeq h6 hv
    have h2 := multL_mono cc (Λ := xFn S.size) (Λ' := lam d)
      (Real.log_nonneg (by have : (0 : ℝ) ≤ S.size := Nat.cast_nonneg _; linarith))
      (xFn_le_lam hSsize hNd) hv
    exact hmult.trans (h1.trans h2)
  | direct => trivial
  | fresh => trivial
  | threshold => trivial
  | orbitStop => trivial
  | orbitChain => trivial
  | floorReset => trivial
  | normalize => trivial
  | rowTerminal => trivial
  | rowColumns => trivial

/-- A child in any row has domain at most the parent's. -/
theorem Row.child_s_le (cc : ChargingConstants) {X T : PotentialState} {R : Row}
    (hv : R.Valid cc X) (h : R.Child cc X T) : T.s ≤ X.s := by
  cases R with
  | affected =>
    obtain ⟨hs, -⟩ := h
    have hθ := cc.θ_lt_one
    have h0 : (0 : ℝ) ≤ X.s := Nat.cast_nonneg _
    have : (T.s : ℝ) ≤ X.s := hs.trans (by nlinarith)
    exact_mod_cast this
  | unaffected => exact h.1
  | product r => exact h.1
  | enumeration d =>
    obtain ⟨hd, -⟩ := hv
    have h1 := h.1
    have : T.s ≤ d * T.s := Nat.le_mul_of_pos_left _ (by omega)
    omega
  | continuation q => exact h.1
  | rowEvent => exact h.1

/-- **Satisfiability of the hypotheses of `phaseTreeOn_hypL` on the real runs.** For every
degree parameter `d ≥ N`, the vertices with `s ≤ N` are closed under children, and every such
vertex satisfies the local bounds. So the restricted real phase tree does satisfy `HypL` at the
constant weight `Λ = lam d` (`Good v := s_v ≤ N`), for all real runs.

The regime `d < N` is exactly the content of Theorem R*: there `Good` must be the runs
whose group lies in `Γ̂_d`, and (`i`), (`ii`) of `Run.VertexBound` are what the closure of `Γ̂_d`
(GNS, BCP) and the dispatcher `(M')` have to provide. -/
theorem good_le_N_conditions {cc : ChargingConstants} (hc : Compat P cc)
    (hN6 : 6 ≤ (N : ℝ) ^ cc.γ) {d : ℕ} (hNd : N ≤ d) :
    (∀ v, v.Inv N → (fun v : PNode P => (v.leaf.state P.κ).s ≤ N) v →
      ∀ u, u ∈ v.rawKind.children → u.Inv N → (u.leaf.state P.κ).s ≤ N) ∧
    (∀ v, v.Inv N → (fun v : PNode P => (v.leaf.state P.κ).s ≤ N) v →
      v.leaf.run.VertexBound cc d) := by
  have hκ := hc.κ_five
  have hN2 := two_le_of_six_le (N := N) cc.γ_pos.le hN6
  refine ⟨fun v hv hG u hu _ => ?_, fun v hv hG => ?_⟩
  · -- closure: a child's size is at most the parent's
    obtain ⟨Ω, m, C, S, L, A, r, pt⟩ := v
    haveI := hv.fin
    unfold PNode.rawKind at hu
    cases pt with
    | some a => simp [NodeKind.children] at hu
    | none =>
      have hstate : (Leaf.state P.κ ⟨m, C, S, L, A, r, none⟩).s = S.size := rfl
      simp only [hstate] at hG
      change u ∈ (runKind r).children at hu
      cases hk : runKind r with
      | leaf => rw [hk] at hu; simp only [NodeKind.children] at hu; cases hu
      | charged cls =>
        rw [hk] at hu
        simp only [NodeKind.children] at hu
        obtain ⟨l, hl, hul⟩ := List.mem_flatten.mp hu
        obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hl
        obtain ⟨b, hb, hub⟩ := List.mem_flatten.mp hul
        have hok := (runKind_charged_ok hc hN2 r hv.N_eq hk).2 c hc'
        have h1 := Row.child_s_le cc hok.valid (hok.child b hb u hub)
        exact h1.trans hG
      | orbit cs =>
        rw [hk] at hu
        have hu' : u ∈ cs := hu
        have h2 := ((runKind_orbit_ok r hv.N_eq hκ (hv.orbit_h rfl) hk).1 u hu').2.2.1.le
        exact h2.trans hG
  · -- the local bounds
    obtain ⟨Ω, m, C, S, L, A, r, pt⟩ := v
    haveI := hv.fin
    cases pt with
    | some a =>
      -- an orbit vertex of a threshold run: no bounds needed
      obtain ⟨hr, -⟩ := hv.virt a rfl
      cases r <;> first | trivial | simp [Run.kind] at hr
    | none =>
      have hstate : (Leaf.state P.κ ⟨m, C, S, L, A, r, none⟩).s = S.size := rfl
      simp only [hstate] at hG
      cases r with
      | normalize hs htr hfl Q hsm c' hq hkc hkl NA hNA m' hmode A' r' =>
        show ∀ j, (r' j).LocalBound cc d
        intro j
        exact localBound_of_N_le hc hN6 hNd (r' j) (hv.N_eq) hG
      | aggregate hs htr L hnot hq₀ I hsel hcon b e τ hτ child hchild hN hhier hbk A' r' =>
        exact localBound_of_N_le hc hN6 hNd
          (Run.aggregate hs htr L hnot hq₀ I hsel hcon b e τ hτ child hchild hN hhier hbk A' r')
          hv.N_eq hG
      | dispatch hs htr hfl I child hchild hN hhier hbk A' r' =>
        exact localBound_of_N_le hc hN6 hNd
          (Run.dispatch hs htr hfl I child hchild hN hhier hbk A' r') hv.N_eq hG
      | direct => trivial
      | fresh => trivial
      | threshold => trivial
      | orbitStop => trivial
      | orbitChain => trivial
      | floorReset => trivial
      | rowTerminal => trivial
      | rowColumns => trivial


/-! ### Clipped caps: the cap moment `Q_d`, analysis-only -/

/-- The cap moment of Theorem R*, with the caps clipped at `D = max(d,6)`: an analysis-only
function of the state, needing no change to the runs, whose caps (`hierQ`) stay as in HJ. -/
noncomputable def hierQd {Ω : Type} (D : ℕ) (l : List (Interval Ω)) : ℝ :=
  (l.map fun I => Real.log I.ratio * Real.log (max (min I.cap D) 2 : ℕ)).sum

/-- **The cap payment survives clipping**: a cap update with `q ≤ D` drops the clipped
moment `Q_d` by at least `c_β log q` (eq. `main-cap-payment` for the caps `min(c, D)`). So the
potential `Φ_Λ` can use `Q_d` with HJ's runs unchanged, as long as the giant has `q ≤ D`. -/
theorem CapUpdate.Qd_drop {Ω : Type} {l l' : List (Interval Ω)} {q D : ℕ} (hqD : q ≤ D)
    (h : CapUpdate P l q l') (hβ0 : 0 < P.β) (hβ1 : P.β < 1) (hβq : 2 ≤ P.β * q) :
    hierQd D l' + cBeta P.β * Real.log q ≤ hierQd D l := by
  obtain ⟨i, hqc, hcd, rfl⟩ := h
  have hset := sum_map_set (fun I : Interval Ω => Real.log I.ratio * Real.log (max (min I.cap D) 2 : ℕ))
    l i i.2 ⟨l[i].part, l[i].ratio, min l[i].cap ⌊P.β * q⌋₊, l[i].origin⟩
  have hq' : (q : ℝ) ≤ (min l[i].cap D : ℕ) := by exact_mod_cast (le_min hqc hqD)
  have hcd' : ((min l[i].cap D : ℕ) : ℝ) ≤ l[i].ratio := by
    exact_mod_cast (min_le_left _ _).trans hcd
  have hnew : ((min (min l[i].cap ⌊P.β * q⌋₊) D : ℕ) : ℝ) ≤ P.β * q := by
    have h1 : ((min (min l[i].cap ⌊P.β * q⌋₊) D : ℕ) : ℝ) ≤ (⌊P.β * q⌋₊ : ℕ) := by
      exact_mod_cast (min_le_left _ _).trans (min_le_right _ _)
    exact h1.trans (Nat.floor_le (by linarith))
  obtain ⟨h1, h2⟩ := GI.Paper.eq_main_cap_payment hβ0 hβ1 hβq hq' hcd' hnew
  have hmax : ∀ c : ℕ, max (c : ℝ) 2 = ((max c 2 : ℕ) : ℝ) := fun c => by push_cast; rfl
  rw [hmax, hmax] at h1
  unfold hierQd GI.Paper.cBeta
  simp only [Fin.getElem_fin] at hset h1 h2 ⊢
  linarith

end Restricted

end GI.Algorithm
