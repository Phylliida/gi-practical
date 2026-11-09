-- Generated from upstream `Workspace/Paper/PhaseCost.lean` by gen.py, then edited by hand
-- (node work `Eb`, the class Γ̂, the toll `tollE`). Not regenerated.
import DegreeD.M.TotalCost

/-!
# The cost hypotheses of Lemma 7.1 from the per-node hypothesis

`GI.Paper.lem_main_phase_bound_run` (Lemma 7.1 for runs) assumes two facts about the cost
of the vertices of the phase tree (`GI.Algorithm.phaseTree`): a leaf costs at most
`K_N`, and a vertex costs at most `N^a K_N` plus the costs of its children. Here these
are proved for the total cost of runs (`GI.Algorithm.Run.total`) from the per-node
hypothesis `GI.Algorithm.NodeBound`, with `K_N` the toll of eq. `main-phase-toll`:

`K_N = exp(c_T (log(N+2))²) (1 + F(⌈N^γ⌉))`,

where `F` is the worst-case cost `GI.Algorithm.worstCost` and `c_T = cw + 20`.

## The cost of a vertex

A vertex of the phase tree is a run, or an orbit of a threshold run
(`GI.Algorithm.PNode`). Its cost (`vcost`) is the total cost of its run plus `4 E_N`,
where `E_N = exp(cw (log(N+2))²)` bounds the work of one node. The extra `4 E_N` pays
for the nodes that are not vertices: the orbit-chain runs and floor resets that the
forest of a run flattens (Section 7.4: "The polynomial work of expanding the forest is
included in `N^a`"). An orbit chain has two children, the first of them transitive, and
a floor reset has a transitive child that is not a floor reset; so an orbit forest has
at most two flattened nodes for each of its vertices, and the vertices pay for them
(`forest_bound`). An orbit vertex of a threshold run gets the cost of the whole
threshold run; this counts that run once for each of its orbits, which only makes the
bound weaker.

The cost is `0` at vertices that do not belong to the phase (`VGood`).

## The toll

At a vertex, the work of the node, the work of its flattened children, and its fresh
calls cost at most `N^a K_N` (`toll_bound`): the node makes at most `N^{af}` script
calls, each fresh call is on at most `⌈N^γ⌉` positions and so costs at most `F(⌈N^γ⌉)`,
and `af + 1 ≤ a`.
-/

namespace GI.DegreeD.M

open GI.Algorithm GI.Paper

open Equiv Equiv.Perm
open scoped Pointwise
open GI.Paper (PhaseTree NodeKind ChildClass)

variable {P : Params} {d : ℕ}

/-! ### Small facts -/

theorem expLogSq_nonneg (c : ℝ) (n : ℕ) : 0 ≤ expLogSq c n := (Real.exp_pos _).le

theorem one_le_expLogSq {c : ℝ} (hc : 0 ≤ c) (n : ℕ) : 1 ≤ expLogSq c n :=
  Real.one_le_exp (mul_nonneg hc (sq_nonneg _))

theorem log_two_sq_le (n : ℕ) : Real.log 2 ^ 2 ≤ Real.log ((n : ℝ) + 2) ^ 2 := by
  have h2 : Real.log 2 ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  exact pow_le_pow_left₀ (Real.log_nonneg (by norm_num)) h2 2

/-- `(log 2)² > 0.48`. -/
theorem log_two_sq_gt : (0.48 : ℝ) < Real.log 2 ^ 2 := by
  have := Real.log_two_gt_d9
  nlinarith

/-- `exp(k (log(n+2))²) ≥ 1 + 0.48 k` for `k ≥ 0`. -/
theorem expLogSq_ge (k : ℝ) (hk : 0 ≤ k) (n : ℕ) : 1 + 0.48 * k ≤ expLogSq k n := by
  have h := log_two_sq_le n
  have := log_two_sq_gt
  calc 1 + 0.48 * k ≤ 1 + k * Real.log ((n : ℝ) + 2) ^ 2 := by nlinarith
    _ ≤ _ := by rw [add_comm]; exact Real.add_one_le_exp _

theorem expLogSq_add (a b : ℝ) (n : ℕ) : expLogSq (a + b) n = expLogSq a n * expLogSq b n := by
  unfold expLogSq; rw [← Real.exp_add]; ring_nf

theorem expLogSq_mono_left {a b : ℝ} (h : a ≤ b) (n : ℕ) : expLogSq a n ≤ expLogSq b n :=
  Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h (sq_nonneg _))

theorem expLogSq_mono_right {c : ℝ} (hc : 0 ≤ c) {m n : ℕ} (h : m ≤ n) :
    expLogSq c m ≤ expLogSq c n := by
  unfold expLogSq
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ hc
  have hm : (m : ℝ) ≤ n := by exact_mod_cast h
  exact pow_le_pow_left₀ (Real.log_nonneg (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]))
    (Real.log_le_log (by positivity) (by linarith)) 2

/-! ### The cost of a vertex -/

/-- A vertex that belongs to the phase with phase size `N`: a vertex of the phase tree
(`PNode.Inv`), on at most `N` positions, whose run has root bounds and is not a floor
reset (a floor reset is never a vertex of a forest, `Leaf.InForest.honest`, nor a phase
root, whose floor mode is off). -/
def VGood (d : ℕ) (cσ : ℝ) (N : ℕ) (v : PNode P) : Prop :=
  v.Inv N ∧ v.leaf.S.size ≤ N ∧ v.leaf.run.RootsOK cσ d ∧ v.leaf.run.kind ≠ .floorReset ∧ VClass d v

open Classical in
/-- **The cost of a vertex** of the phase tree with phase size `N`: the total cost of its
run plus `4c`, where `c = E_N` bounds the work of one node; `0` off the phase. -/
noncomputable def vcost (d : ℕ) (w : Node P → ℝ) (cσ c : ℝ) (N : ℕ) (v : PNode P) : ℝ :=
  if VGood d cσ N v then v.leaf.run.total w + 4 * c else 0

theorem vcost_of {w : Node P → ℝ} {cσ c : ℝ} {N : ℕ} {v : PNode P} (h : VGood d cσ N v) :
    vcost d w cσ c N v = v.leaf.run.total w + 4 * c := by
  simp [vcost, h]

theorem vcost_nonneg {w : Node P → ℝ} (hw : ∀ nd, 0 ≤ w nd) {cσ c : ℝ} (hc : 0 ≤ c) (N : ℕ)
    (v : PNode P) : 0 ≤ vcost d w cσ c N v := by
  unfold vcost
  split_ifs
  · have := v.leaf.run.total_nonneg hw; linarith
  · exact le_refl _

/-- The `level` of a run in its forest: how much of `E_N` its forest has left over after
paying for its total cost. -/
def level : CallKind → ℝ
  | .orbitStop => 1
  | .orbitChain => 1
  | .floorReset => 3
  | _ => 4

theorem one_le_level (k : CallKind) : 1 ≤ level k := by cases k <;> norm_num [level]

/-! ### Facts about states -/

theorem size_eq_of_dom {Ω C C' : Type} {S : State Ω C} {T : State Ω C'} (h : T.dom = S.dom) :
    T.size = S.size := by
  unfold State.size; rw [h]

theorem transitive_of_largestOrbit {Ω C : Type} {S S₁ : State Ω C} {D₁ : Set Ω}
    (hD₁ : S.LargestOrbit D₁) (h₁ : S₁.Inst S.G D₁ S.x S.y) : S₁.Transitive := by
  obtain ⟨a, -, hD⟩ := hD₁.orbit
  obtain ⟨hG, hdom, -, -⟩ := h₁
  intro v hv u hu
  rw [hdom, hD] at hv hu
  obtain ⟨g, hg, rfl⟩ := hv
  obtain ⟨k, hk, rfl⟩ := hu
  exact ⟨k * g⁻¹, hG ▸ S.G.mul_mem hk (S.G.inv_mem hg), by simp⟩

theorem nonempty_of_largestOrbit {Ω C : Type} {S S₁ : State Ω C} {D₁ : Set Ω}
    (hD₁ : S.LargestOrbit D₁) (h₁ : S₁.Inst S.G D₁ S.x S.y) : S₁.dom.Nonempty := by
  obtain ⟨a, -, hD⟩ := hD₁.orbit
  rw [h₁.2.1, hD]
  exact ⟨a, 1, S.G.one_mem, rfl⟩

/-- A run on a transitive state is not an orbit-chain run. -/
theorem kind_of_transitive {m : Mode} {Ω C : Type} {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)}
    (r : Run P m S L A) (htr : S.Transitive) :
    r.kind ≠ .orbitStop ∧ r.kind ≠ .orbitChain := by
  cases r with
  | orbitStop _ hint => exact absurd htr hint
  | orbitChain _ hint => exact absurd htr hint
  | _ => simp [Run.kind]

/-- A run on a state with the floor mode off is not a floor reset. -/
theorem kind_of_floor {m : Mode} {Ω C : Type} {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)}
    (r : Run P m S L A) (hfl : S.floor = false) : r.kind ≠ .floorReset := by
  cases r with
  | floorReset _ _ h => exact absurd h.1 (by simp [hfl])
  | _ => simp [Run.kind]

theorem orbitReps_ne_nil {Ω C : Type} [Finite Ω] {S : State Ω C} (hne : S.dom.Nonempty) :
    orbitReps S ≠ [] := by
  classical
  obtain ⟨v, hv⟩ := hne
  have hfin : S.dom.Finite := Set.toFinite _
  set a := orbRep S.G v
  have ha : a ∈ S.dom := orb_subset S.dom_inv hv (orbRep_mem S.G v)
  have haa : orbRep S.G a = a :=
    orbRep_congr (orb_eq_of_mem (orbRep_mem S.G v))
  unfold orbitReps
  rw [dif_pos hfin]
  intro h
  have : a ∈ (hfin.toFinset.filter fun u => orbRep S.G u = u).toList := by
    simp [ha, haa]
  rw [h] at this
  simp at this

/-! ### Fresh calls -/

section Fresh

variable {d : ℕ} {w : Node P → ℝ} {cσ : ℝ} {N : ℕ}

/-- A fresh call on at most `N^γ` positions costs at most `F(⌈N^γ⌉)`. -/
theorem solve_le {Ω C : Type} {T : State Ω C}
    {L : Option (SuppliedLabels T)} {A : Set (Perm Ω)} (r : Run P .solve T L A)
    (hb : BddAbove (costSet d w cσ ⌈(N : ℝ) ^ P.γ⌉₊)) (hT : (T.size : ℝ) ≤ (N : ℝ) ^ P.γ)
    (hfin : Finite Ω) (hg : GammaHat d T.G) (hr : r.RootsOK cσ d) :
    r.total w ≤ worstCost d w cσ ⌈(N : ℝ) ^ P.γ⌉₊ :=
  total_le_worstCost hb r (by exact_mod_cast hT.trans (Nat.le_ceil _)) hfin hg hr

theorem rpow_le_rpow_gamma {N : ℕ} (hN : 1 ≤ N) {e : ℝ} (he : e ≤ P.γ) :
    (N : ℝ) ^ e ≤ (N : ℝ) ^ P.γ :=
  Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) he

end Fresh

/-! ### The forest of a run pays for it -/

section Forest

variable {d : ℕ} {w : Node P → ℝ} {Eb : ℕ → ℝ} {cσ af : ℝ} {N : ℕ}

theorem level_ge_three {k : CallKind} (h1 : k ≠ .orbitStop) (h2 : k ≠ .orbitChain) :
    3 ≤ level k := by
  cases k <;> simp_all [level] <;> norm_num

theorem level_eq_four {k : CallKind} (h1 : k ≠ .orbitStop) (h2 : k ≠ .orbitChain)
    (h3 : k ≠ .floorReset) : level k = 4 := by
  cases k <;> simp_all [level]

/-- The work of a node of the phase is at most `E_N`. -/
theorem work_le (hw : NodeBoundE d w Eb af) {m : Mode} {Ω C : Type} {S : State Ω C}
    {L : Option (SuppliedLabels S)}
    {A : Set (Perm Ω)} (r : Run P m S L A) (hm : m ≠ .solve) (hN : S.N = N)
    (hsz : S.size ≤ N) (hg : GammaHat d S.G) : w r.node ≤ Eb N := by
  have := hw.work r.node hm (hN ▸ hsz) hg
  rwa [show r.node.S.N = N from hN] at this

/-- A run that is its own forest vertex is a vertex of the phase. -/
theorem vgood_self {m : Mode} {Ω C : Type} [Finite Ω] {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)}
    (r : Run P m S L A) (hm : m ≠ .solve) (hN : S.N = N) (hsz : S.size ≤ N)
    (hok : r.RootsOK cσ d) (hg : GammaHat d S.G) (h1 : r.kind ≠ .orbitStop)
    (h2 : r.kind ≠ .orbitChain)
    (h3 : r.kind ≠ .floorReset) : VGood d cσ N (Leaf.ofRun r).toP :=
  ⟨{ fin := ‹_›
     N_eq := hN
     mode := hm
     virt := fun a h => by simp [Leaf.ofRun, Leaf.toP] at h
     orbit_h := fun _ hk => by rcases hk with hk | hk <;> contradiction },
    hsz, hok, h3, hg⟩

/-- A run that is its own forest pays for its total cost with `4 E_N` to spare. -/
theorem self_bound {m : Mode} {Ω C : Type} [Finite Ω] {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)}
    (r : Run P m S L A)
    (hk : r.kind ≠ .threshold ∧ r.kind ≠ .orbitChain ∧ r.kind ≠ .orbitStop ∧
      r.kind ≠ .floorReset)
    (hm : m ≠ .solve) (hN : S.N = N) (hsz : S.size ≤ N) (hok : r.RootsOK cσ d)
    (hg : GammaHat d S.G) :
    r.total w + Eb N * level r.kind ≤
      (r.forest.map fun ℓ => vcost d w cσ (Eb N) N ℓ.toP).sum := by
  rw [forest_of_kind r hk, level_eq_four hk.2.2.1 hk.2.1 hk.2.2.2]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [vcost_of (vgood_self r hm hN hsz hok hg hk.2.2.1 hk.2.1 hk.2.2.2)]
  simp only [Leaf.toP, Leaf.ofRun]
  linarith

/-- **The forest of a run pays for it** (Section 7.4: "The polynomial work of expanding
the forest is included in `N^a`"). For a `Continue` or `GiantStep` run of the phase on
a nonempty domain, its total cost plus `level · E_N` is at most the sum of the costs of
its forest vertices. -/
theorem forest_bound (hw : NodeBoundE d w Eb af) :
    ∀ {m : Mode} {Ω C : Type} {S : State Ω C}
      {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)} (r : Run P m S L A),
      Finite Ω → m ≠ .solve → S.N = N → S.size ≤ N → r.RootsOK cσ d → GammaHat d S.G →
      S.dom.Nonempty →
      r.total w + Eb N * level r.kind ≤
        (r.forest.map fun ℓ => vcost d w cσ (Eb N) N ℓ.toP).sum := by
  intro m Ω C S L A r
  have hc0 : 0 ≤ Eb N := (zero_le_one.trans (hw.one_le N))
  refine Run.rec (motive_1 := fun m {Ω C} S _ A r =>
      Finite Ω → m ≠ .solve → S.N = N → S.size ≤ N → r.RootsOK cσ d → GammaHat d S.G →
      S.dom.Nonempty →
      r.total w + Eb N * level r.kind ≤
        (r.forest.map fun ℓ => vcost d w cσ (Eb N) N ℓ.toP).sum)
    (motive_2 := fun _ _ _ => True)
    ?direct ?fresh ?threshold ?orbitStop ?orbitChain ?floorReset ?dispatch ?normalize
    ?rowTerminal ?rowColumns ?aggregate (fun _ => trivial) (fun _ _ _ _ => trivial) r
  case direct => intro _ _ _ _ _ hm; exact absurd rfl hm
  case fresh => intro _ _ _ _ _ _ _ _ _ _ hm; exact absurd rfl hm
  case threshold =>
    intro Ω C S A hs r₀ _ hfin hm hN hsz hok hgG hne
    have hf : (Run.threshold hs r₀).forest =
        (orbitReps S).map fun a => ⟨.cont, C, S, none, A, Run.threshold hs r₀, some a⟩ := rfl
    rw [hf, List.map_map]
    have hgood : ∀ a ∈ orbitReps S, VGood d cσ N
        (Leaf.toP (⟨.cont, C, S, none, A, Run.threshold hs r₀, some a⟩ : Leaf P Ω)) := by
      intro a ha
      refine ⟨⟨hfin, hN, by simp [Leaf.toP], ?_, ?_⟩, hsz, hok, ?_, hgG⟩
      rotate_left
      · intro h; simp [Leaf.toP] at h
      · change (Run.threshold hs r₀).kind ≠ _; simp [Run.kind]
      · intro a' h
        simp only [Leaf.toP, Option.some.injEq] at h
        subst h
        exact ⟨rfl, (mem_orbitReps ha).1⟩
    rw [List.map_congr_left (fun a ha => by
      rw [Function.comp_apply, vcost_of (hgood a ha)])]
    simp only [Leaf.toP, List.map_const', List.sum_replicate, nsmul_eq_mul]
    have hlen : (1 : ℝ) ≤ (orbitReps S).length := by
      have := List.length_pos_of_ne_nil (orbitReps_ne_nil hne)
      exact_mod_cast this
    have h0 := (Run.threshold hs r₀).total_nonneg hw.nonneg
    have hl : level (Run.threshold hs r₀).kind = 4 := rfl
    rw [hl]
    nlinarith
  case orbitStop =>
    intro Ω C S S₁ D₁ hs hint hD₁ h₁ hN₁ hhier₁ hb₁ r₁ ih₁ hfin hm hN hsz hok hgG hne
    have hsz₁ : S₁.size ≤ N :=
      (size_le_of_subset (h₁.2.1 ▸ hD₁.subset)).trans hsz
    have := ih₁ hfin (by decide) (hN₁.trans hN) hsz₁ hok (GammaHat.of_le hgG h₁.1.le)
      (nonempty_of_largestOrbit hD₁ h₁)
    have hk := kind_of_transitive r₁ (transitive_of_largestOrbit hD₁ h₁)
    have h3 := mul_le_mul_of_nonneg_left (level_ge_three hk.1 hk.2) hc0
    have hwk := work_le hw (Run.orbitStop hs hint hD₁ h₁ hN₁ hhier₁ hb₁ r₁) (by decide) hN hsz hgG
    change w _ + r₁.total w + Eb N * 1 ≤ (r₁.forest.map _).sum
    linarith
  case orbitChain =>
    intro Ω C S S₁ S₂ D₁ A₁ A₂ hs hint hD₁ h₁ hN₁ hhier₁ hb₁ r₁ t ht h₂ hN₂ hhier₂ hb₂ r₂ ih₁ ih₂
      hfin hm hN hsz hok hgG hne
    have hsizes := orbitChain_sizes hint hD₁ h₁.2.1 h₂.2.1
    have hsz₁ : S₁.size ≤ N := by omega
    have hsz₂ : S₂.size ≤ N := by omega
    have hne₂ : S₂.dom.Nonempty := by
      have : 0 < Nat.card S₂.dom := hsizes.2.2
      exact Set.nonempty_coe_sort.1 (Nat.card_pos_iff.1 this).1
    have hG₂ : S₂.G ≤ S.G := h₂.1.le.trans (autGroup_le S.G D₁ hD₁.invariant S.x)
    have e₁ := ih₁ hfin (by decide) (hN₁.trans hN) hsz₁ hok.1 (GammaHat.of_le hgG h₁.1.le)
      (nonempty_of_largestOrbit hD₁ h₁)
    have e₂ := ih₂ hfin (by decide) (hN₂.trans hN) hsz₂ hok.2 (GammaHat.of_le hgG hG₂) hne₂
    have hk := kind_of_transitive r₁ (transitive_of_largestOrbit hD₁ h₁)
    have h3 := mul_le_mul_of_nonneg_left (level_ge_three hk.1 hk.2) hc0
    have h1 := mul_le_mul_of_nonneg_left (one_le_level r₂.kind) hc0
    have hwk := work_le hw (Run.orbitChain hs hint hD₁ h₁ hN₁ hhier₁ hb₁ r₁ t ht h₂ hN₂ hhier₂ hb₂ r₂)
      (by decide) hN hsz hgG
    change w _ + r₁.total w + r₂.total w + Eb N * 1 ≤
      ((r₁.forest ++ r₂.forest).map _).sum
    rw [List.map_append, List.sum_append]
    linarith
  case floorReset =>
    intro Ω C S S' A hs htr hfl hcore hrows hfloor hh hN' hhier r ih hfin hm hN hsz hok hgG hne
    have hdom : S'.dom = S.dom := hcore.2.1
    have htr' : S'.Transitive := by
      intro v hv u hu
      rw [hdom] at hv hu
      obtain ⟨g, hg, hgv⟩ := htr v hv u hu
      exact ⟨g, hcore.1 ▸ hg, hgv⟩
    have hk := kind_of_transitive r htr'
    have hf := kind_of_floor r hfloor
    have e := ih hfin (by decide) (hN'.trans hN) ((size_eq_of_dom hdom).trans_le hsz) hok
      (GammaHat.of_le hgG hcore.1.le) (hdom ▸ hne)
    rw [level_eq_four hk.1 hk.2 hf] at e
    have hwk := work_le hw (Run.floorReset hs htr hfl hcore hrows hfloor hh hN' hhier r)
      (by decide) hN hsz hgG
    change w _ + r.total w + Eb N * 3 ≤ (r.forest.map _).sum
    linarith
  case dispatch =>
    intros
    intro hfin hm hN hsz hok hgG _
    exact self_bound _ (by simp [Run.kind]) hm hN hsz hok hgG
  case normalize =>
    intros
    intro hfin hm hN hsz hok hgG _
    exact self_bound _ (by simp [Run.kind]) hm hN hsz hok hgG
  case rowTerminal =>
    intros
    intro hfin hm hN hsz hok hgG _
    exact self_bound _ (by simp [Run.kind]) hm hN hsz hok hgG
  case rowColumns =>
    intros
    intro hfin hm hN hsz hok hgG _
    exact self_bound _ (by simp [Run.kind]) hm hN hsz hok hgG
  case aggregate =>
    intros
    intro hfin hm hN hsz hok hgG _
    exact self_bound _ (by simp [Run.kind]) hm hN hsz hok hgG

end Forest

/-! ### List sums -/

section Lists

open GI.Paper (list_sum_map_flatten list_sum_le_length_mul)

theorem sum_filter_eq {β : Type*} (l : List β) (p : β → Bool) (h : β → ℝ) :
    ((l.filter p).map h).sum = (l.map fun x => if p x then h x else 0).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases hp : p a <;> simp [hp, ih]

theorem sum_filter_split {β : Type*} (l : List β) (q : β → Bool) (h : β → ℝ) :
    ((l.filter fun b => decide (q b = true)).map h).sum +
      ((l.filter fun b => decide (q b = false)).map h).sum = (l.map h).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases hq : q a <;> simp [hq] at ih ⊢ <;> linarith

/-- The children of a charged vertex, summed class by class and branch by branch. -/
theorem sum_children_charged {V : Type*} (cls : List (ChildClass V)) (g : V → ℝ) :
    (((NodeKind.charged cls).children).map g).sum =
      (cls.map fun c => (c.branches.map fun b => (b.map g).sum).sum).sum := by
  simp only [NodeKind.children]
  rw [list_sum_map_flatten, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c _
  simp only [Function.comp_apply]
  rw [list_sum_map_flatten]

/-- The branches of the inherited calls of a script run, of both types together, are the
forests of its `Continue` calls. -/
theorem callBranches_sum (θs : ℝ) {α : Type} {s : Script α} {a : α} (e : Exec P s a)
    (f : PNode P → ℝ) :
    ((callBranches θs true e).map fun b => (b.map f).sum).sum +
      ((callBranches θs false e).map fun b => (b.map f).sum).sum =
      (e.calls.map fun nd => if nd.m = .cont then
        (nd.run.forest.map fun ℓ => f ℓ.toP).sum else 0).sum := by
  classical
  unfold callBranches
  simp only [List.map_map]
  rw [← List.sum_map_add]
  have : ∀ nd : Node P, (((nd.run.forest.filter fun ℓ =>
      decide (decide (((Nat.card ℓ.dom : ℕ) : ℝ) ≤ θs) = true)).map Leaf.toP).map f).sum +
      (((nd.run.forest.filter fun ℓ =>
      decide (decide (((Nat.card ℓ.dom : ℕ) : ℝ) ≤ θs) = false)).map Leaf.toP).map f).sum =
      (nd.run.forest.map fun ℓ => f ℓ.toP).sum := by
    intro nd
    simp only [List.map_map]
    exact sum_filter_split _ _ _
  simp only [Function.comp_def] at this ⊢
  rw [List.map_congr_left (fun nd _ => this nd), sum_filter_eq]
  congr 1
  apply List.map_congr_left
  intro nd _
  simp

end Lists

/-! ### Calls and giant steps -/

section Giant

variable {d : ℕ} {w : Node P → ℝ} {Eb : ℕ → ℝ} {cσ af : ℝ} {N : ℕ}

/-- An inherited call of an aggregation round, possibly on an empty domain, costs at most
its forest plus `E_N + F(⌈N^γ⌉)`. -/
theorem call_bound (hw : NodeBoundE d w Eb af)
    (hb : BddAbove (costSet d w cσ ⌈(N : ℝ) ^ P.γ⌉₊)) {Ω C : Type} [Finite Ω] {T : State Ω C}
    {L : Option (SuppliedLabels T)}
    {A : Set (Perm Ω)} (r : Run P .cont T L A) (hN : T.N = N) (hsz : T.size ≤ N)
    (hok : r.RootsOK cσ d) (hg : GammaHat d T.G) :
    r.total w ≤ (r.forest.map fun ℓ => vcost d w cσ (Eb N) N ℓ.toP).sum +
      Eb N + worstCost d w cσ ⌈(N : ℝ) ^ P.γ⌉₊ := by
  have hc0 : 0 ≤ Eb N := (zero_le_one.trans (hw.one_le N))
  have hF0 := worstCost_nonneg hw.nonneg d cσ ⌈(N : ℝ) ^ P.γ⌉₊
  by_cases hne : T.dom.Nonempty
  · have h := forest_bound hw r ‹_› (by decide) hN hsz hok hg hne
    have h1 := mul_le_mul_of_nonneg_left (one_le_level r.kind) hc0
    linarith
  · have hS0 : 0 ≤ (r.forest.map fun ℓ => vcost d w cσ (Eb N) N ℓ.toP).sum :=
      List.sum_nonneg fun x hx => by
        obtain ⟨ℓ, -, rfl⟩ := List.mem_map.1 hx
        exact vcost_nonneg hw.nonneg hc0 N _
    cases r with
    | threshold hs r₀ =>
      have hwk := work_le hw (Run.threshold hs r₀) (by decide) hN hsz hg
      have h₀ := solve_le r₀ hb (by rw [← hN]; exact hs) ‹_› hg hok
      rw [Run.total_threshold]
      linarith
    | orbitStop hs => exact absurd (dom_nonempty_of_large hs) hne
    | orbitChain hs => exact absurd (dom_nonempty_of_large hs) hne
    | floorReset hs => exact absurd (dom_nonempty_of_large hs) hne
    | dispatch hs => exact absurd (dom_nonempty_of_large hs) hne
    | normalize hs => exact absurd (dom_nonempty_of_large hs) hne

/-- **A giant step pays for its fresh calls**: its total cost is at most `E_N`, plus
`E_N + F(⌈N^γ⌉)` for each script call, plus the costs of its charged children. The row
terminal's calls are on rows of at most `N^{1-α}` positions, the configuration calls of
an aggregation round on at most `N^{2α}` positions (Section 7.4), and `1 - α < 2α ≤ γ`
(eq. `scale-constraints`). -/
theorem giant_bound (hw : NodeBoundE d w Eb af) (hαγ : 2 * P.α ≤ P.γ) (hα : 1 / 3 < P.α)
    (hN1 : 1 ≤ N) (hb : BddAbove (costSet d w cσ ⌈(N : ℝ) ^ P.γ⌉₊)) {Ω C : Type} [Finite Ω]
    {T : State Ω C}
    {L : Option (SuppliedLabels T)} {A : Set (Perm Ω)} (g : Run P .giant T L A) (hN : T.N = N)
    (hsz : T.size ≤ N) (hok : g.RootsOK cσ d) (hg : GammaHat d T.G) :
    g.total w ≤ Eb N + g.scriptCalls.length *
      (Eb N + worstCost d w cσ ⌈(N : ℝ) ^ P.γ⌉₊) +
      (((NodeKind.charged (giantClasses g)).children).map
        (vcost d w cσ (Eb N) N)).sum := by
  have hc0 : 0 ≤ Eb N := (zero_le_one.trans (hw.one_le N))
  have hF0 := worstCost_nonneg hw.nonneg d cσ ⌈(N : ℝ) ^ P.γ⌉₊
  set c := Eb N
  set Fm := worstCost d w cσ ⌈(N : ℝ) ^ P.γ⌉₊
  rw [sum_children_charged]
  cases g with
  | rowTerminal hs htr L hrow I e =>
    have hwk := work_le hw (Run.rowTerminal hs htr L hrow I e) (by decide) hN hsz hg
    have hcalls := (Exec.calls_spec e _ I.calls).1
    have hroots := (Exec.rootsOK_calls e hok).1
    have hsolve := (Exec.rootsOK_calls e hok).2
    have he : e.total w ≤ e.calls.length * Fm := by
      rw [Exec.total_eq_calls]
      apply GI.Paper.list_sum_le_length_mul
      intro nd hnd
      obtain ⟨m', Ω', C', T', L', A', r'⟩ := nd
      obtain ⟨hm', hsz'⟩ := hcalls _ hnd
      simp only at hm' hsz'
      subst hm'
      obtain ⟨hfin', hg'⟩ := hsolve _ hnd rfl
      refine solve_le r' hb (hsz'.trans ?_) hfin' hg' (hroots _ hnd)
      rw [hN]
      exact rpow_le_rpow_gamma hN1 (by linarith)
    change w _ + e.total w ≤ c + (e.calls.length : ℝ) * (c + Fm) + ([] : List ℝ).sum
    have hl : (0 : ℝ) ≤ e.calls.length := Nat.cast_nonneg _
    simp only [List.sum_nil, add_zero]
    nlinarith
  | rowColumns hs htr L hrow I hcore hR hh1 hh hN' hhier r' =>
    have hwk := work_le hw (Run.rowColumns hs htr L hrow I hcore hR hh1 hh hN' hhier r')
      (by decide) hN hsz hg
    have hdom : _ = T.dom := hcore.2.1
    have h := forest_bound hw r' ‹_› (by decide) (hN'.trans hN)
      ((size_eq_of_dom hdom).trans_le hsz) hok (GammaHat.of_le hg hcore.1.le)
      (hdom ▸ dom_nonempty_of_large hs)
    have h1 := mul_le_mul_of_nonneg_left (one_le_level r'.kind) hc0
    have ht : (Run.rowColumns hs htr L hrow I hcore hR hh1 hh hN' hhier r').total w =
        w (Run.rowColumns hs htr L hrow I hcore hR hh1 hh hN' hhier r').node + r'.total w := rfl
    rw [ht]
    simp only [giantClasses, Run.scriptCalls, List.length_nil, Nat.cast_zero, zero_mul,
      add_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Run.forestP,
      List.map_map, Function.comp_def]
    linarith
  | aggregate hs htr L hnot hq₀ I hsel hcon b e τ hτ child hchild hN' hhier hbk A r =>
    have hwk := work_le hw
      (Run.aggregate hs htr L hnot hq₀ I hsel hcon b e τ hτ child hchild hN' hhier hbk A r)
      (by decide) hN hsz hg
    have hcalls := (Exec.calls_spec e _ I.calls).1
    have hroots := (Exec.rootsOK_calls e hok.1).1
    have hsolve := (Exec.rootsOK_calls e hok.1).2
    -- Each call costs at most `E_N + F(⌈N^γ⌉)` plus its forest if it is inherited.
    have he : e.total w ≤ e.calls.length * (c + Fm) +
        (e.calls.map fun nd => if nd.m = .cont then
          (nd.run.forest.map fun ℓ => vcost d w cσ c N ℓ.toP).sum else 0).sum := by
      rw [Exec.total_eq_calls]
      have hle : ∀ nd ∈ e.calls, nd.run.total w ≤ (c + Fm) + (if nd.m = .cont then
          (nd.run.forest.map fun ℓ => vcost d w cσ c N ℓ.toP).sum else 0) := by
        intro nd hnd
        obtain ⟨m', Ω', C', T', L', A', r'⟩ := nd
        rcases hcalls _ hnd with ⟨hm', hsz'⟩ | ⟨hm', e', hch⟩
        · simp only at hm' hsz'
          subst hm'
          obtain ⟨hfin', hg'⟩ := hsolve _ hnd rfl
          have := solve_le r' hb (hsz'.trans (by rw [hN]; exact rpow_le_rpow_gamma hN1 hαγ))
            hfin' hg' (hroots _ hnd)
          simp only [reduceCtorEq, if_false, add_zero]
          linarith
        · simp only at hm' e' hch
          subst hm' e'
          replace hch : ChargedCall P T T' := hch
          have := call_bound hw hb r' (hch.N_eq.trans hN)
            ((size_le_of_subset hch.sub).trans hsz) (hroots _ hnd) (GammaHat.of_le hg hch.le)
          simp only [if_true]
          linarith
      calc (e.calls.map fun nd => nd.run.total w).sum
          ≤ (e.calls.map fun nd => (c + Fm) + (if nd.m = .cont then
              (nd.run.forest.map fun ℓ => vcost d w cσ c N ℓ.toP).sum else 0)).sum :=
            List.sum_le_sum hle
        _ = _ := by
            rw [List.sum_map_add]
            simp [List.map_const', nsmul_eq_mul]
            ring
    -- Each continuation costs at most its forest.
    have hbe := e.exact
    subst hbe
    have hr : ∀ j, (r j).total w ≤ ((r j).forest.map fun ℓ => vcost d w cσ c N ℓ.toP).sum := by
      intro j
      have hdom : (child j).dom = T.dom := (hchild j).2.1
      have hGj : (child j).G ≤ T.G := (hchild j).1.le.trans (I.covers.overs_le j)
      have h := forest_bound hw (r j) ‹_› (by decide) ((hN' j).trans hN)
        ((size_eq_of_dom hdom).trans_le hsz) (hok.2 j) (GammaHat.of_le hg hGj)
        (hdom ▸ dom_nonempty_of_large hs)
      have h1 := mul_le_mul_of_nonneg_left (one_le_level (r j).kind) hc0
      linarith
    have hsplit := callBranches_sum (P.θ * T.size) e (vcost d w cσ c N)
    have ht : (Run.aggregate hs htr L hnot hq₀ I hsel hcon _ e τ hτ child hchild hN' hhier hbk A r).total w =
        w (Run.aggregate hs htr L hnot hq₀ I hsel hcon _ e τ hτ child hchild hN' hhier hbk A r).node +
          e.total w + ∑ j, (r j).total w := rfl
    rw [ht]
    simp only [giantClasses, Run.scriptCalls, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, List.map_ofFn, List.sum_ofFn, Function.comp_def, Run.forestP,
      List.map_map]
    have hrs := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hr j
    linarith

end Giant

/-! ### The two cost hypotheses of Lemma 7.1 -/

section Hyp

variable {d : ℕ} {w : Node P → ℝ} {Eb : ℕ → ℝ} {cσ af a : ℝ} {N : ℕ}

/-- **The node toll** with node work `Eb N`: `K = 11 E (1 + F(⌈N^γ⌉))`. -/
noncomputable def tollE (Eb : ℕ → ℝ) (γ : ℝ) (F : ℕ → ℝ) (N : ℕ) : ℝ :=
  Eb N * 11 * (1 + F ⌈(N : ℝ) ^ γ⌉₊)

/-- The arithmetic of the toll: `(9 + 2x) E + 2x F ≤ N^a K` when `x ≤ N^{af}`, `af + 1 ≤ a`. -/
theorem toll_numeric (hE1 : 1 ≤ Eb N) (haf : 0 ≤ af) (ha : af + 1 ≤ a) (hN2 : 2 ≤ N)
    {Fm x : ℝ} (hFm : 0 ≤ Fm) (hx0 : 0 ≤ x) (hx : x ≤ (N : ℝ) ^ af) :
    (9 + 2 * x) * Eb N + 2 * x * Fm ≤ (N : ℝ) ^ a * (Eb N * 11 * (1 + Fm)) := by
  have hN : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNaf : 1 ≤ (N : ℝ) ^ af := Real.one_le_rpow (by linarith) haf
  have hNa : 2 * (N : ℝ) ^ af ≤ (N : ℝ) ^ a := by
    calc 2 * (N : ℝ) ^ af ≤ (N : ℝ) ^ af * N := by nlinarith
      _ = (N : ℝ) ^ (af + 1) := (Real.rpow_add_one (by positivity) af).symm
      _ ≤ (N : ℝ) ^ a := Real.rpow_le_rpow_of_exponent_le (by linarith) ha
  set c := Eb N
  set Na := (N : ℝ) ^ a
  set Naf := (N : ℝ) ^ af
  have h1 : (9 + 2 * x) * c ≤ Na * (c * 11) := by
    have : 9 + 2 * x ≤ Na * 11 := by nlinarith
    nlinarith
  have h2 : 2 * x * Fm ≤ Na * (c * 11) * Fm := by
    have : 2 * x ≤ Na * (c * 11) := by nlinarith
    exact mul_le_mul_of_nonneg_right this hFm
  nlinarith

/-- The vertex of a phase tree, as a run with its fields. -/
theorem vgood_run {v : PNode P} (hv : VGood d cσ N v) :
    v.Inv N ∧ v.leaf.S.size ≤ N ∧ v.leaf.run.RootsOK cσ d ∧ v.leaf.run.kind ≠ .floorReset :=
  ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1⟩

/-- **Leaf cost** (Section 7.4: "An ordinary threshold leaf has cost at most `K_N`"). A
threshold leaf costs its work, at most `E_N`, plus one fresh call on at most `N^γ`
positions, at most `F(⌈N^γ⌉)`. -/
theorem leaf_cost (hw : NodeBoundE d w Eb af) {Qf : QFun}
    (hb : BddAbove (costSet d w cσ ⌈(N : ℝ) ^ P.γ⌉₊)) (v : PNode P)
    (hk : (phaseTreeOn P N (vcost d w cσ (Eb N) N) (VClass d) Qf).kind v = .leaf) :
    vcost d w cσ (Eb N) N v ≤ tollE Eb P.γ (worstCost d w cσ) N := by
  have hc1 := hw.one_le N
  have hc0 : 0 ≤ Eb N := zero_le_one.trans hc1
  have hF0 := worstCost_nonneg hw.nonneg d cσ ⌈(N : ℝ) ^ P.γ⌉₊
  unfold tollE
  have hK : 10 * Eb N + worstCost d w cσ ⌈(N : ℝ) ^ P.γ⌉₊ ≤
      Eb N * 11 * (1 + worstCost d w cσ ⌈(N : ℝ) ^ P.γ⌉₊) := by
    nlinarith
  by_cases hv : VGood d cσ N v
  swap
  · simp only [vcost, hv, if_false]; linarith
  rw [vcost_of hv]
  obtain ⟨hinv, hsz, hok, -, hcl⟩ := hv
  rw [phaseTreeOn_kind_of hinv hcl] at hk
  obtain ⟨Ω, m, C, S, L, A, run, pt⟩ := v
  haveI := hinv.fin
  have hg : GammaHat d S.G := hcl
  have hthr : run.kind = .threshold := by
    cases pt with
    | some a => exact (hinv.virt a rfl).1
    | none => exact (runKind_leaf run hinv.mode).1 hk
  simp only at hsz hok hthr ⊢
  cases run with
  | threshold hs r₀ =>
    have hN : S.N = N := hinv.N_eq
    have hwk := work_le hw (Run.threshold hs r₀) (by decide) hN hsz hg
    have h₀ := solve_le r₀ hb (by rw [← hN]; exact hs) ‹_› hg hok
    rw [Run.total_threshold]
    linarith
  | _ => simp [Run.kind] at hthr

/-- **The node toll** (Section 7.4: "all structural work and all fresh configuration or
row calls at one node have total cost at most `N^a K_N`"; "The polynomial work of
expanding the forest is included in `N^a`"). -/
theorem toll_bound (hw : NodeBoundE d w Eb af) {Qf : QFun} (haf : 0 ≤ af) (ha : af + 1 ≤ a)
    (hαγ : 2 * P.α ≤ P.γ) (hα : 1 / 3 < P.α) (hN2 : 2 ≤ N)
    (hb : BddAbove (costSet d w cσ ⌈(N : ℝ) ^ P.γ⌉₊)) (v : PNode P)
    (hk : (phaseTreeOn P N (vcost d w cσ (Eb N) N) (VClass d) Qf).kind v ≠ .leaf) :
    vcost d w cσ (Eb N) N v ≤
      (N : ℝ) ^ a * tollE Eb P.γ (worstCost d w cσ) N +
      (((phaseTreeOn P N (vcost d w cσ (Eb N) N) (VClass d) Qf).kind v).children.map
        (vcost d w cσ (Eb N) N)).sum := by
  have hN1 : 1 ≤ N := by omega
  have hc0 : 0 ≤ Eb N := zero_le_one.trans (hw.one_le N)
  have hF0 := worstCost_nonneg hw.nonneg d cσ ⌈(N : ℝ) ^ P.γ⌉₊
  have hE1 := hw.one_le N
  unfold tollE
  set c := Eb N
  set Fm := worstCost d w cσ ⌈(N : ℝ) ^ P.γ⌉₊
  set f := vcost d w cσ c N
  have hf0 : ∀ u, 0 ≤ f u := vcost_nonneg hw.nonneg hc0 N
  have hNa := toll_numeric (N := N) (Eb := Eb) (a := a) (af := af) hE1 haf ha hN2 hF0 (le_refl 0)
    (Real.rpow_nonneg (Nat.cast_nonneg N) af)
  simp only [mul_zero, zero_mul, add_zero] at hNa
  have hK0 : 0 ≤ (N : ℝ) ^ a * (c * 11 * (1 + Fm)) := by positivity
  by_cases hv : VGood d cσ N v
  swap
  · simp only [f, vcost, hv, if_false]
    exact add_nonneg hK0 (List.sum_nonneg fun x hx => by
      obtain ⟨u, -, rfl⟩ := List.mem_map.1 hx; exact hf0 u)
  have hfv : f v = v.leaf.run.total w + 4 * c := vcost_of hv
  rw [hfv]
  obtain ⟨hinv, hsz, hok, hfl, hcl⟩ := hv
  rw [phaseTreeOn_kind_of hinv hcl] at hk ⊢
  obtain ⟨Ω, m, C, S, L, A, run, pt⟩ := v
  haveI := hinv.fin
  cases pt with
  | some a' => exact absurd rfl hk
  | none =>
  have hN : S.N = N := hinv.N_eq
  have hm : m ≠ .solve := hinv.mode
  have hg : GammaHat d S.G := hcl
  simp only [PNode.rawKind] at hk ⊢
  simp only at hsz hok hfl
  -- The forest of an inherited child pays for it.
  have hinh : ∀ {T : State Ω C}
      {L : Option (SuppliedLabels T)} {A' : Set (Perm Ω)} (r : Run P .cont T L A'), T.N = N →
      T.dom = S.dom → T.G ≤ S.G → r.RootsOK cσ d → (S.N : ℝ) ^ P.γ < S.size →
      r.total w + c ≤ (r.forest.map fun ℓ => f ℓ.toP).sum := by
    intro T L' A' r hTN hdom hTG hok' hs
    have h := forest_bound hw r ‹_› (by decide) hTN ((size_eq_of_dom hdom).trans_le hsz) hok'
      (GammaHat.of_le hg hTG) (hdom ▸ dom_nonempty_of_large hs)
    have h1 := mul_le_mul_of_nonneg_left (one_le_level r.kind) hc0
    linarith
  -- A giant step pays for itself.
  have hgiant : ∀ {T : State Ω C}
      {L : Option (SuppliedLabels T)} {A' : Set (Perm Ω)} (g : Run P .giant T L A'), T.N = N →
      T.dom = S.dom → T.G ≤ S.G → g.RootsOK cσ d →
      g.total w ≤ c + (N : ℝ) ^ af * (c + Fm) +
        ((giantClasses g).map fun c' => (c'.branches.map fun b => (b.map f).sum).sum).sum := by
    intro T L' A' g hTN hdom hTG hok'
    have hsz' : T.size ≤ N := (size_eq_of_dom hdom).trans_le hsz
    have h := giant_bound hw hαγ hα hN1 hb g hTN hsz' hok' (GammaHat.of_le hg hTG)
    rw [sum_children_charged] at h
    have hcalls := hw.calls g.node (show Mode.giant ≠ Mode.solve by decide) (hTN ▸ hsz')
    rw [show g.node.S.N = N from hTN] at hcalls
    change (g.scriptCalls.length : ℝ) ≤ _ at hcalls
    have := mul_le_mul_of_nonneg_right hcalls (add_nonneg hc0 hF0)
    linarith
  cases run with
  | direct => exact absurd rfl hm
  | fresh => exact absurd rfl hm
  | threshold => exact absurd rfl hk
  | floorReset => exact absurd rfl hfl
  | orbitStop hs hint hD₁ h₁ hN₁ hhier₁ hb₁ r₁ =>
    have h := forest_bound hw (Run.orbitStop hs hint hD₁ h₁ hN₁ hhier₁ hb₁ r₁) ‹_› (by decide) hN
      hsz hok hg (dom_nonempty_of_large hs)
    simp only [runKind, NodeKind.children, Run.forestP, List.map_map]
    change _ + c * 1 ≤ _ at h
    simp only [Function.comp_def]
    linarith
  | orbitChain hs hint hD₁ h₁ hN₁ hhier₁ hb₁ r₁ t ht h₂ hN₂ hhier₂ hb₂ r₂ =>
    have h := forest_bound hw (Run.orbitChain hs hint hD₁ h₁ hN₁ hhier₁ hb₁ r₁ t ht h₂ hN₂ hhier₂ hb₂ r₂)
      ‹_› (by decide) hN hsz hok hg (dom_nonempty_of_large hs)
    simp only [runKind, NodeKind.children, Run.forestP, List.map_map]
    change _ + c * 1 ≤ _ at h
    simp only [Function.comp_def]
    linarith
  | dispatch hs htr hfl' I child hchild hN' hhier hbk A r =>
    have hwk := work_le hw (Run.dispatch hs htr hfl' I child hchild hN' hhier hbk A r) (by decide)
      hN hsz hg
    have hr := fun j => hinh (r j) ((hN' j).trans hN) (hchild j).2.1
      ((hchild j).1.le.trans I.K_le) (hok j) hs
    have hrs := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hr j
    have ht : (Run.dispatch hs htr hfl' I child hchild hN' hhier hbk A r).total w =
        w (Run.dispatch hs htr hfl' I child hchild hN' hhier hbk A r).node +
          ∑ j, (r j).total w := rfl
    rw [ht, runKind, sum_children_charged]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      List.map_ofFn, List.sum_ofFn, Function.comp_def, Run.forestP, List.map_map]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hrs
    have : (0 : ℝ) ≤ I.n * c := by positivity
    linarith
  | normalize hs htr hfl' Q hsm h1 hq hkc hkl NA hNA m' hmode A r =>
    let I := NA.I
    have hN' : ∀ j, (NA.child j).N = S.N := fun _ => rfl
    have hchild : ∀ j, (NA.child j).Inst I.G' S.dom S.x (S.y ∘ I.τ j) :=
      fun _ => ⟨rfl, rfl, rfl, rfl⟩
    have hwk := work_le hw (Run.normalize hs htr hfl' Q hsm h1 hq hkc hkl NA hNA m' hmode A r)
      (by decide) hN hsz hg
    have ht : (Run.normalize hs htr hfl' Q hsm h1 hq hkc hkl NA hNA m' hmode A r).total w =
        w (Run.normalize hs htr hfl' Q hsm h1 hq hkc hkl NA hNA m' hmode A r).node +
          ∑ j, (r j).total w := rfl
    rw [ht]
    cases m' with
    | solve =>
      have : IsEmpty (Fin I.k) :=
        ⟨fun j => by rcases hmode j with h | h <;> exact absurd h.1 (by decide)⟩
      simp only [runKind, reduceCtorEq, if_false, Finset.univ_eq_empty, Finset.sum_empty]
      have : (0 : ℝ) ≤ (((NodeKind.charged (List.ofFn fun j => giantClasses (r j)).flatten
        ).children).map f).sum := List.sum_nonneg fun x hx => by
          obtain ⟨u, -, rfl⟩ := List.mem_map.1 hx; exact hf0 u
      linarith
    | cont =>
      have hr := fun j => hinh (r j) ((hN' j).trans hN) (hchild j).2.1 ((hchild j).1.le.trans I.le)
        (hok j) hs
      have hrs := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hr j
      simp only [runKind, if_true, sum_children_charged]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        List.map_ofFn, List.sum_ofFn, Function.comp_def, Run.forestP, List.map_map]
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul] at hrs
      have : (0 : ℝ) ≤ I.k * c := by positivity
      linarith
    | giant =>
      have hr := fun j => hgiant (r j) ((hN' j).trans hN) (hchild j).2.1 ((hchild j).1.le.trans I.le)
        (hok j)
      have hrs := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hr j
      simp only [runKind, reduceCtorEq, if_false, sum_children_charged]
      rw [GI.Paper.list_sum_map_flatten]
      simp only [List.map_ofFn, List.sum_ofFn, Function.comp_def]
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul] at hrs
      have hk2 : (I.k : ℝ) ≤ 2 := by exact_mod_cast I.k_le
      have hNaf : 0 ≤ (N : ℝ) ^ af * (c + Fm) := by positivity
      have h2 := toll_numeric (N := N) (Eb := Eb) (a := a) (af := af) hE1 haf ha hN2 hF0 (Real.rpow_nonneg (Nat.cast_nonneg N) af)
        le_rfl
      have : (I.k : ℝ) * (c + (N : ℝ) ^ af * (c + Fm)) ≤ 2 * (c + (N : ℝ) ^ af * (c + Fm)) :=
        mul_le_mul_of_nonneg_right hk2 (by positivity)
      nlinarith
  | rowTerminal hs htr L hrow I e =>
    have h := hgiant (Run.rowTerminal hs htr L hrow I e) hN rfl le_rfl hok
    simp only [runKind, sum_children_charged]
    have h2 := toll_numeric (N := N) (Eb := Eb) (a := a) (af := af) hE1 haf ha hN2 hF0 (Real.rpow_nonneg (Nat.cast_nonneg N) af) le_rfl
    nlinarith
  | rowColumns hs htr L hrow I hcore hR hh1 hh hN' hhier r =>
    have h := hgiant (Run.rowColumns hs htr L hrow I hcore hR hh1 hh hN' hhier r) hN rfl le_rfl hok
    simp only [runKind, sum_children_charged]
    have h2 := toll_numeric (N := N) (Eb := Eb) (a := a) (af := af) hE1 haf ha hN2 hF0 (Real.rpow_nonneg (Nat.cast_nonneg N) af) le_rfl
    nlinarith
  | aggregate hs htr L hnot hq₀ I hsel hcon b e τ hτ child hchild hN' hhier hbk A r =>
    have h := hgiant
      (Run.aggregate hs htr L hnot hq₀ I hsel hcon b e τ hτ child hchild hN' hhier hbk A r) hN rfl
      le_rfl hok
    simp only [runKind, sum_children_charged]
    have h2 := toll_numeric (N := N) (Eb := Eb) (a := a) (af := af) hE1 haf ha hN2 hF0 (Real.rpow_nonneg (Nat.cast_nonneg N) af) le_rfl
    nlinarith

end Hyp

end GI.DegreeD.M
