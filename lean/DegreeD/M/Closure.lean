import DegreeD.M.RealRuns
import DegreeD.M.Bounds

/-!
# `Γ̂_d` is closed along the runs of `M.Run`, and the local bounds hold on it

`Good := VClass d`: the group of the state lies in `Γ̂_d`.

* `runKind_children_le`: every child of a vertex is a forest vertex under a subgroup of the
  vertex's group. So `VClass d` is closed under children (`vclass_closed`). (No property of the
  class is needed beyond closure under subgroups.)
* `localBound_of_class`, `vertexBound_of_class`: the local conditions of `Run.VertexBound`
  hold on `VClass d`: `q ≤ max(d,6)` at a giant step (`GammaHat.sectionsEmbed`,
  `q_le_of_surjective`) and the dispatcher count (`DispatchStep.n_le_multL`).
-/

namespace GI.DegreeD.M

open Equiv Equiv.Perm GI.Algorithm GI.Paper
open scoped Pointwise

variable {P : Params} {Ω C : Type}

/-- The group of `H ≤ G` of a `Γ̂_d` group is in `Γ̂_d`. -/
theorem GammaHat.of_le [Finite Ω] {d : ℕ} {G H : Subgroup (Perm Ω)} (hG : GammaHat d G)
    (h : H ≤ G) : GammaHat d H :=
  hG.of_injective (Subgroup.inclusion h) (Subgroup.inclusion_injective h)

/-- A child in the forest of a run under `T` lives in a subgroup of `T`'s group. -/
theorem mem_forestP_le {m : Mode} {T : State Ω C} {L : Option (SuppliedLabels T)}
    {A : Set (Perm Ω)} (r : Run P m T L A) (hm : m ≠ .solve) {u : PNode P} (hu : u ∈ r.forestP) :
    ∃ ℓ : Leaf P Ω, u = ℓ.toP ∧ ℓ.S.G ≤ T.G := by
  obtain ⟨ℓ, hℓ, rfl⟩ := mem_forestP hu
  exact ⟨ℓ, rfl, ((forest_spec r).2.1 hm ℓ hℓ).le⟩

/-- **The children of a giant step are forest vertices under a subgroup.** -/
theorem giantClasses_children_le [Finite Ω] {m : Mode} {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)} (r : Run P m S L A)
    {c : ChildClass (PNode P)} (hc : c ∈ giantClasses r) {b : List (PNode P)}
    (hb : b ∈ c.branches) {u : PNode P} (hu : u ∈ b) :
    ∃ ℓ : Leaf P Ω, u = ℓ.toP ∧ ℓ.S.G ≤ S.G := by
  cases r with
  | rowColumns hs htr L hrow I hcore hR hh1 hh hN hhier r' =>
    simp only [giantClasses, List.mem_singleton] at hc
    subst hc
    simp only [List.mem_singleton] at hb
    subst hb
    obtain ⟨ℓ, rfl, hℓ⟩ := mem_forestP_le r' (by simp) hu
    exact ⟨ℓ, rfl, hℓ.trans hcore.1.le⟩
  | aggregate hs htr L hnot hq₀ I _ _ b' e τ hτ child hchild hN hhier hbk A' r' =>
    have hbe := e.exact
    subst hbe
    simp only [giantClasses, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · obtain ⟨C', T, hT, -, hus⟩ := callBranches_spec e I.calls _ _ b hb
      obtain ⟨ℓ, rfl, hℓ, -, -⟩ := hus u hu
      exact ⟨ℓ, rfl, hℓ.le.trans hT.le⟩
    · obtain ⟨C', T, hT, -, hus⟩ := callBranches_spec e I.calls _ _ b hb
      obtain ⟨ℓ, rfl, hℓ, -, -⟩ := hus u hu
      exact ⟨ℓ, rfl, hℓ.le.trans hT.le⟩
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hb
      obtain ⟨ℓ, rfl, hℓ⟩ := mem_forestP_le (r' j) (by simp) hu
      have hG : (child j).G ≤ S.G := (hchild j).1.le.trans (I.covers.overs_le j)
      exact ⟨ℓ, rfl, hℓ.trans hG⟩
  | _ => simp [giantClasses] at hc

/-- **The children of a vertex are forest vertices under a subgroup.** -/
theorem runKind_children_le [Finite Ω] {m : Mode} {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)} (r : Run P m S L A)
    {u : PNode P} (hu : u ∈ (runKind r).children) :
    ∃ ℓ : Leaf P Ω, u = ℓ.toP ∧ ℓ.S.G ≤ S.G := by
  have hch : ∀ {cls : List (ChildClass (PNode P))} (h : u ∈ (NodeKind.charged cls).children),
      ∃ c ∈ cls, ∃ b ∈ c.branches, u ∈ b := by
    intro cls h
    simp only [NodeKind.children] at h
    obtain ⟨l, hl, hul⟩ := List.mem_flatten.1 h
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hl
    obtain ⟨b, hb, hub⟩ := List.mem_flatten.1 hul
    exact ⟨c, hc, b, hb, hub⟩
  cases r with
  | direct => simp [runKind, NodeKind.children] at hu
  | fresh => simp [runKind, NodeKind.children] at hu
  | threshold => simp [runKind, NodeKind.children] at hu
  | orbitStop hs hint hD₁ h₁ hN₁ hhier₁ hb₁ r₁ =>
    rename_i S₁ D₁
    have hu' : u ∈ (Run.orbitStop hs hint hD₁ h₁ hN₁ hhier₁ hb₁ r₁).forestP := hu
    exact mem_forestP_le _ (by simp) hu'
  | orbitChain hs hint hD₁ h₁ hN₁ hhier₁ hb₁ r₁ t ht h₂ hN₂ hhier₂ hb₂ r₂ =>
    rename_i S₁ S₂ D₁ A₁ A₂
    have hu' : u ∈ (Run.orbitChain hs hint hD₁ h₁ hN₁ hhier₁ hb₁ r₁ t ht h₂ hN₂ hhier₂ hb₂ r₂).forestP := hu
    exact mem_forestP_le _ (by simp) hu'
  | floorReset => simp [runKind, NodeKind.children] at hu
  | rowTerminal =>
    obtain ⟨c, hc, b, hb, hub⟩ := hch hu
    exact giantClasses_children_le _ hc hb hub
  | rowColumns =>
    obtain ⟨c, hc, b, hb, hub⟩ := hch hu
    exact giantClasses_children_le _ hc hb hub
  | aggregate =>
    obtain ⟨c, hc, b, hb, hub⟩ := hch hu
    exact giantClasses_children_le _ hc hb hub
  | dispatch hs htr hfl I child hchild hN hhier hbk A' r' =>
    obtain ⟨c, hc, b, hb, hub⟩ := hch hu
    simp only [List.mem_singleton] at hc
    subst hc
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hb
    obtain ⟨ℓ, rfl, hℓ⟩ := mem_forestP_le (r' j) (by simp) hub
    have hG : (child j).G ≤ S.G := (hchild j).1.le.trans I.K_le
    exact ⟨ℓ, rfl, hℓ.trans hG⟩
  | normalize hs htr hfl Q hsm c' hq hkc hkl NA hNA m' hmode A' r' =>
    simp only [runKind] at hu
    have hG : ∀ j, (NA.child j).G ≤ S.G := fun j => NA.I.le
    split_ifs at hu with hm'
    · obtain ⟨c, hc, b, hb, hub⟩ := hch hu
      simp only [List.mem_singleton] at hc
      subst hc
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hb
      subst hm'
      obtain ⟨ℓ, rfl, hℓ⟩ := mem_forestP_le (r' j) (by simp) hub
      exact ⟨ℓ, rfl, hℓ.trans (hG j)⟩
    · obtain ⟨c, hc, b, hb, hub⟩ := hch hu
      obtain ⟨l, hl, hcl⟩ := List.mem_flatten.1 hc
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hl
      obtain ⟨ℓ, rfl, hℓ⟩ := giantClasses_children_le (r' j) hcl hb hub
      exact ⟨ℓ, rfl, hℓ.trans (hG j)⟩

/-! ### The class of a vertex -/

/-- The group of the state of a vertex lies in `Γ̂_d`. -/
def VClass (d : ℕ) (p : PNode P) : Prop := GammaHat d p.leaf.S.G

theorem vclass_closed {d N : ℕ} {v : PNode P} (hv : v.Inv N) (hg : VClass d v) {u : PNode P}
    (hu : u ∈ v.rawKind.children) : VClass d u := by
  obtain ⟨Ω', m, C', S, L, A, r, pt⟩ := v
  haveI := hv.fin
  cases pt with
  | some a => simp [PNode.rawKind, NodeKind.children] at hu
  | none =>
    change u ∈ (runKind r).children at hu
    obtain ⟨ℓ, rfl, hℓ⟩ := runKind_children_le r hu
    have h : GammaHat d ℓ.S.G := GammaHat.of_le (Ω := Ω') (show GammaHat d S.G from hg) hℓ
    exact h

/-- `q ≤ max(d, 6)` at a giant step: if `q ≥ 5` the embedding `Alt(q) ≤ S_d` forces `q ≤ d`. -/
theorem labels_q_le {d : ℕ} {S : State Ω C} (hg : GammaHat d S.G) (L : SuppliedLabels S) :
    L.q ≤ max d 6 := by
  by_cases h5 : 5 ≤ L.q
  · exact (q_le_of_surjective h5 hg.sectionsEmbed L.π L.π_surj).trans (le_max_left _ _)
  · exact (by omega : L.q ≤ 6).trans (le_max_right _ _)

section Local

variable {cc : ChargingConstants} {c₁ c₂ : ℝ} {d : ℕ}

/-- **`Run.LocalBound` on `Γ̂_d` states.** -/
theorem localBound_of_class (hBCP : BCP) (hGNS : GNSPrimitive c₁ c₂) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hcc : c₁ / Real.log 2 + c₂ / Real.log 48 ≤ cc.a + cc.aStar / Real.log 2)
    (hq : (Real.log P.q₀.factorial / Real.log 48 + 1) / Real.log 17 ≤
      cc.a + cc.aStar / Real.log 2)
    {m : Mode} {S : State Ω C} {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)}
    (r : Run P m S L A) (hg : GammaHat d S.G) : r.LocalBound cc d := by
  cases r with
  | aggregate hs htr L hnot hq₀ I hsel hcon b e τ hτ child hchild hN hhier hbk A' r' =>
    show L.q ≤ max d 6
    exact labels_q_le hg L
  | dispatch hs htr hfl I child hchild hN hhier hbk A' r' =>
    show (I.n : ℝ) ≤ Row'.multL cc (lam d) (kindRow I.kind)
    exact DispatchStep.n_le_multL hBCP hGNS hc₁ hc₂ hcc hq hg I
  | direct => trivial
  | fresh => trivial
  | threshold => trivial
  | orbitStop => trivial
  | orbitChain => trivial
  | floorReset => trivial
  | normalize => trivial
  | rowTerminal => trivial
  | rowColumns => trivial

/-- **`Run.VertexBound` on `Γ̂_d` states.** -/
theorem vertexBound_of_class [Finite Ω] (hBCP : BCP) (hGNS : GNSPrimitive c₁ c₂) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hcc : c₁ / Real.log 2 + c₂ / Real.log 48 ≤ cc.a + cc.aStar / Real.log 2)
    (hq : (Real.log P.q₀.factorial / Real.log 48 + 1) / Real.log 17 ≤
      cc.a + cc.aStar / Real.log 2)
    {m : Mode} {S : State Ω C} {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)}
    (r : Run P m S L A) (hg : GammaHat d S.G) : r.VertexBound cc d := by
  have hl := localBound_of_class hBCP hGNS hc₁ hc₂ hcc hq r hg
  cases r with
  | normalize hs htr hfl Q hsm c' hq' hkc hkl NA hNA m' hmode A' r' =>
    show ∀ j, (r' j).LocalBound cc d
    intro j
    exact localBound_of_class hBCP hGNS hc₁ hc₂ hcc hq (r' j)
      (GammaHat.of_le hg (NA.I.le))
  | direct => exact hl
  | fresh => exact hl
  | threshold => exact hl
  | orbitStop => exact hl
  | orbitChain => exact hl
  | floorReset => exact hl
  | dispatch => exact hl
  | rowTerminal => exact hl
  | rowColumns => exact hl
  | aggregate => exact hl

end Local

end GI.DegreeD.M
