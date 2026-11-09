import DegreeD.Luks.Final

/-!
# GI of maximum degree `d`, all graphs: from components

`graphScript`: for every pair of a connected component of `X` and a connected component of `Y`,
the connected-graph reduction, each answer lifted to partial maps on `Fin n` so that the answers
have one type. A permutation `g` is returned exactly when its restriction to every component of `X`
is one of the lifted isomorphisms. `graphIso_general` is the theorem of `DegreeD/Luks/Final.lean`
for arbitrary graphs; `graphIso_final` with the cited results.
-/

namespace GI.DegreeD.Luks

open Equiv Equiv.Perm GI.Algorithm SimpleGraph
open scoped Classical

set_option linter.unusedSectionVars false

section Any

variable {V W : Type} [Fintype V] [Fintype W] {X : SimpleGraph V} {Y : SimpleGraph W} {q R : ℕ}

/-- The reduction for connected graphs, edge-rooted when `X` has an edge, and direct
when it has none (then it has at most one vertex). -/
noncomputable def anyScript (hX : X.Connected) (hY : Y.Connected)
    (hXd : ∀ l, Nat.card (X.neighborSet l) ≤ q) (hYd : ∀ l, Nat.card (Y.neighborSet l) ≤ q)
    (R : ℕ) : Script (Set (V → W)) :=
  if h : ∃ u v, X.Adj u v then connScript hX hY hXd hYd h.choose h.choose_spec.choose R
  else Script.done {f | ∃ e : X ≃g Y, (e : V → W) = f}

theorem anyScript_spec (hX : X.Connected) (hY : Y.Connected)
    (hXd : ∀ l, Nat.card (X.neighborSet l) ≤ q) (hYd : ∀ l, Nat.card (Y.neighborSet l) ≤ q)
    (hXR : ∀ u v w, edgeLvl X u v w ≤ R) (hYR : ∀ (p : W × W) w, edgeLvl Y p.1 p.2 w ≤ R) :
    (anyScript hX hY hXd hYd R).CallsExact (CallOK q (Nat.card (Om V q))) ∧
      (anyScript hX hY hXd hYd R).numCalls ≤ Fintype.card (W × W) * R ∧
      (anyScript hX hY hXd hYd R).evalExact = {f | ∃ e : X ≃g Y, (e : V → W) = f} := by
  unfold anyScript
  split_ifs with h
  · exact connScript_spec hX hY hXd hYd h.choose_spec.choose_spec (hXR _ _) hYR
  · exact ⟨trivial, Nat.zero_le _, rfl⟩

end Any

section Comp

variable {n : ℕ} {X Y : SimpleGraph (Fin n)} {q : ℕ}

/-- The degree bound on a component. -/
theorem comp_deg_le {G : SimpleGraph (Fin n)} (hd : ∀ l, Nat.card (G.neighborSet l) ≤ q)
    (c : G.ConnectedComponent) (l : c) : Nat.card (c.toSimpleGraph.neighborSet l) ≤ q := by
  refine le_trans ?_ (hd l.1)
  let f : c.toSimpleGraph.neighborSet l → G.neighborSet l.1 := fun w =>
    ⟨w.1.1, (c.toSimpleGraph_adj l.2 w.1.2).1 w.2⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : G.neighborSet l.1 => x.1) h
  exact Nat.card_le_card_of_injective f hf

/-- A component has at most `n` vertices. -/
theorem card_comp_le {G : SimpleGraph (Fin n)} (c : G.ConnectedComponent) :
    Fintype.card c ≤ n := by
  calc Fintype.card c ≤ Fintype.card (Fin n) :=
        Fintype.card_le_of_injective _ Subtype.val_injective
    _ = n := Fintype.card_fin n

/-- A partial map on `Fin n` from a map between components. -/
noncomputable def liftMap {c : X.ConnectedComponent} {c' : Y.ConnectedComponent} (f : c → c') :
    Fin n → Option (Fin n) :=
  fun v => if h : v ∈ c then some (f ⟨v, h⟩ : Fin n) else none

/-- The restriction of a permutation to a component, as a partial map. -/
noncomputable def restr (X : SimpleGraph (Fin n)) (g : Perm (Fin n)) (c : X.ConnectedComponent) :
    Fin n → Option (Fin n) :=
  fun v => if v ∈ c then some (g v) else none

/-- The script of one pair of components. -/
noncomputable def compScript (hXd : ∀ l, Nat.card (X.neighborSet l) ≤ q)
    (hYd : ∀ l, Nat.card (Y.neighborSet l) ≤ q)
    (p : X.ConnectedComponent × Y.ConnectedComponent) : Script (Set (Fin n → Option (Fin n))) :=
  (anyScript p.1.connected_toSimpleGraph p.2.connected_toSimpleGraph
      (comp_deg_le hXd p.1) (comp_deg_le hYd p.2) n).bind fun S => Script.done (liftMap '' S)

/-- The bound for the calls of a component script. -/
noncomputable abbrev bOm (n q : ℕ) : ℕ := n + (n * q + n * q * (n * q))

theorem card_om_comp_le {G : SimpleGraph (Fin n)} (c : G.ConnectedComponent) :
    Nat.card (Om c q) ≤ bOm n q := by
  have hc : Fintype.card c ≤ n := card_comp_le c
  have h : Nat.card (Om c q) = Fintype.card c + (Fintype.card c * q + Fintype.card c * q * (Fintype.card c * q)) := by
    simp [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  rw [h, bOm]
  have h1 : Fintype.card c * q ≤ n * q := Nat.mul_le_mul_right _ hc
  have h2 : Fintype.card c * q * (Fintype.card c * q) ≤ n * q * (n * q) := Nat.mul_le_mul h1 h1
  omega

theorem compScript_spec (hXd : ∀ l, Nat.card (X.neighborSet l) ≤ q)
    (hYd : ∀ l, Nat.card (Y.neighborSet l) ≤ q) (p : X.ConnectedComponent × Y.ConnectedComponent) :
    (compScript hXd hYd p).CallsExact (CallOK q (bOm n q)) ∧
      (compScript hXd hYd p).numCalls ≤ n ^ 3 ∧
      (compScript hXd hYd p).evalExact =
        liftMap '' {f | ∃ e : p.1.toSimpleGraph ≃g p.2.toSimpleGraph, (e : p.1 → p.2) = f} := by
  have hXR : ∀ u v w, edgeLvl p.1.toSimpleGraph u v w ≤ n := fun u v w =>
    (edgeLvl_lt_card p.1.connected_toSimpleGraph w).trans (card_comp_le p.1)
  have hYR : ∀ (r : p.2 × p.2) w, edgeLvl p.2.toSimpleGraph r.1 r.2 w ≤ n := fun r w =>
    (edgeLvl_lt_card p.2.connected_toSimpleGraph w).trans (card_comp_le p.2)
  obtain ⟨h1, h2, h3⟩ := anyScript_spec (R := n) p.1.connected_toSimpleGraph
    p.2.connected_toSimpleGraph (comp_deg_le hXd p.1) (comp_deg_le hYd p.2) hXR hYR
  refine ⟨?_, ?_, ?_⟩
  · refine Script.callsExact_bind _ _ (h1.mono fun m T hT => ?_) trivial
    exact ⟨hT.1, hT.2.1, hT.2.2.1, hT.2.2.2.trans (card_om_comp_le p.1)⟩
  · unfold compScript
    rw [Script.numCalls_bind]
    simp only [Script.numCalls, add_zero]
    refine h2.trans ?_
    have h4 : Fintype.card (p.2 × p.2) = Fintype.card p.2 * Fintype.card p.2 := Fintype.card_prod _ _
    have h5 := card_comp_le p.2
    rw [h4]
    calc Fintype.card p.2 * Fintype.card p.2 * n ≤ n * n * n :=
          Nat.mul_le_mul (Nat.mul_le_mul h5 h5) le_rfl
      _ = n ^ 3 := by ring
  · unfold compScript
    rw [Script.evalExact_bind, h3]
    rfl

/-- An isomorphism `X ≃g Y` restricts to each component, as a lifted isomorphism. -/
theorem restr_of_iso (e : X ≃g Y) (c : X.ConnectedComponent) :
    ∃ c' : Y.ConnectedComponent, ∃ f : c → c',
      (∃ e₁ : c.toSimpleGraph ≃g c'.toSimpleGraph, (e₁ : c → c') = f) ∧
      liftMap f = restr X (e : Fin n ≃ Fin n) c := by
  let c' := e.connectedComponentEquiv c
  let f₀ := ConnectedComponent.isoEquivSupp e c
  let e₁ : c.toSimpleGraph ≃g c'.toSimpleGraph :=
    { toEquiv := f₀
      map_rel_iff' := by
        intro a b
        exact e.map_rel_iff }
  refine ⟨c', e₁, ⟨e₁, rfl⟩, ?_⟩
  funext v
  unfold liftMap restr
  split_ifs with h
  · rfl
  · rfl

/-- Reading an element of the lifted answers: the permutation restricted to `c` is an isomorphism of
`c` onto a component `c'`. -/
theorem lift_eq_restr {g : Perm (Fin n)} {c c₁ : X.ConnectedComponent}
    {c' : Y.ConnectedComponent} {f : c₁ → c'} (h : liftMap f = restr X g c) :
    c₁ = c ∧ ∀ v (hv : v ∈ c₁), (f ⟨v, hv⟩ : Fin n) = g v ∧ g v ∈ c' ∧ v ∈ c := by
  have hforward : ∀ v (hv : v ∈ c₁), (f ⟨v, hv⟩ : Fin n) = g v ∧ g v ∈ c' ∧ v ∈ c := by
    intro v hv
    have h2 := congrFun h v
    simp only [liftMap, restr, dif_pos hv] at h2
    split_ifs at h2 with hc
    have hval : (f ⟨v, hv⟩ : Fin n) = g v := Option.some.inj h2
    refine ⟨hval, ?_, hc⟩
    rw [← hval]
    exact (f ⟨v, hv⟩).2
  obtain ⟨v, hv⟩ := c₁.nonempty_supp
  have hvc₁ : v ∈ c₁ := hv
  have hc : c₁ = c := by
    have hvc : v ∈ c.supp := (hforward v hvc₁).2.2
    exact ConnectedComponent.eq_of_common_vertex hv hvc
  exact ⟨hc, hforward⟩

/-- **The characterization of isomorphisms by their restrictions to components.** -/
theorem iso_iff_restr (g : Perm (Fin n)) :
    (∀ a b, X.Adj a b ↔ Y.Adj (g a) (g b)) ↔
      ∀ c : X.ConnectedComponent, ∃ (c₁ : X.ConnectedComponent) (c' : Y.ConnectedComponent)
        (f : c₁ → c'), (∃ e₁ : c₁.toSimpleGraph ≃g c'.toSimpleGraph, (e₁ : c₁ → c') = f) ∧
          liftMap f = restr X g c := by
  constructor
  · intro h c
    let e : X ≃g Y := { toEquiv := g, map_rel_iff' := fun {a b} => (h a b).symm }
    obtain ⟨c', f, he, hf⟩ := restr_of_iso e c
    exact ⟨c, c', f, he, hf⟩
  · intro h a b
    -- the data at the component of `a`
    obtain ⟨c₁, hac₁⟩ : ∃ c₁ : X.ConnectedComponent, a ∈ c₁ :=
      ⟨_, ConnectedComponent.connectedComponentMk_mem⟩
    obtain ⟨c₀, c', f, ⟨e₁, rfl⟩, hf⟩ := h c₁
    obtain ⟨hc₀, hval⟩ := lift_eq_restr hf
    subst hc₀
    obtain ⟨hga, hgac', -⟩ := hval a hac₁
    constructor
    · intro hab
      have hb : b ∈ c₀ := (ConnectedComponent.mem_supp_congr_adj c₀ hab).1 hac₁
      obtain ⟨hgb, -, -⟩ := hval b hb
      have h1 : c₀.toSimpleGraph.Adj ⟨a, hac₁⟩ ⟨b, hb⟩ := (c₀.toSimpleGraph_adj hac₁ hb).2 hab
      have h2 := e₁.map_rel_iff.2 h1
      have h3 := (c'.toSimpleGraph_adj (e₁ ⟨a, hac₁⟩).2 (e₁ ⟨b, hb⟩).2).1 h2
      rw [hga, hgb] at h3
      exact h3
    · intro hab
      -- `g b` is in the component `c'` of `g a`
      have hgb' : g b ∈ c' := (ConnectedComponent.mem_supp_congr_adj c' hab).1 hgac'
      -- `g b` is the image under `e₁` of a vertex of `c₀`, necessarily `b`
      obtain ⟨x, hx⟩ := e₁.surjective ⟨g b, hgb'⟩
      have hxval : (e₁ x : Fin n) = g b := congrArg Subtype.val hx
      obtain ⟨hgx, -, -⟩ := hval x.1 x.2
      rw [hxval] at hgx
      have hxb : x.1 = b := g.injective hgx.symm
      have hbc₁ : b ∈ c₀ := by
        rw [← hxb]; exact x.2
      have hbval := hval b hbc₁
      have h1 : c'.toSimpleGraph.Adj (e₁ ⟨a, hac₁⟩) (e₁ ⟨b, hbc₁⟩) := by
        refine (c'.toSimpleGraph_adj _ _).2 ?_
        show Y.Adj ((e₁ ⟨a, hac₁⟩ : c') : Fin n) ((e₁ ⟨b, hbc₁⟩ : c') : Fin n)
        rw [hga, hbval.1]
        exact hab
      have h2 := e₁.map_rel_iff.1 h1
      exact (c₀.toSimpleGraph_adj hac₁ hbc₁).1 h2

end Comp

/-! ### All graphs -/

section Graph

variable {n : ℕ} {X Y : SimpleGraph (Fin n)} {q : ℕ}
  [Fintype X.ConnectedComponent] [Fintype Y.ConnectedComponent]

/-- **The reduction of a general graph**: for each pair of components, the connected reduction;
a permutation is returned when its restriction to each component of `X` is one of the lifted
isomorphisms. -/
noncomputable def graphScript (hXd : ∀ l, Nat.card (X.neighborSet l) ≤ q)
    (hYd : ∀ l, Nat.card (Y.neighborSet l) ≤ q) : Script (Set (Perm (Fin n))) :=
  (Script.seqList ((Finset.univ : Finset (X.ConnectedComponent × Y.ConnectedComponent)).toList.map
      (compScript hXd hYd))).bind fun L =>
    Script.done {g : Perm (Fin n) | ∀ c : X.ConnectedComponent, restr X g c ∈ ⋃ S ∈ L, S}

theorem graphScript_spec (hXd : ∀ l, Nat.card (X.neighborSet l) ≤ q)
    (hYd : ∀ l, Nat.card (Y.neighborSet l) ≤ q) :
    (graphScript hXd hYd).CallsExact (CallOK q (bOm n q)) ∧
      (graphScript hXd hYd).numCalls ≤
        Fintype.card (X.ConnectedComponent × Y.ConnectedComponent) * n ^ 3 ∧
      (graphScript hXd hYd).evalExact = {g | ∀ a b, X.Adj a b ↔ Y.Adj (g a) (g b)} := by
  have hspec := compScript_spec hXd hYd
  refine ⟨?_, ?_, ?_⟩
  · refine Script.callsExact_bind _ _ (Script.callsExact_seqList _ fun s hs => ?_) trivial
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hs
    exact (hspec p).1
  · unfold graphScript
    rw [Script.numCalls_bind, Script.numCalls_seqList]
    simp only [Script.numCalls, add_zero, List.map_map]
    have hle : ∀ x ∈ ((Finset.univ : Finset (X.ConnectedComponent × Y.ConnectedComponent)).toList.map
        (Script.numCalls ∘ compScript hXd hYd)), x ≤ n ^ 3 := by
      intro x hx
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
      exact (hspec p).2.1
    calc _ ≤ ((Finset.univ : Finset (X.ConnectedComponent × Y.ConnectedComponent)).toList.map
              (Script.numCalls ∘ compScript hXd hYd)).length • n ^ 3 :=
          List.sum_le_card_nsmul _ _ hle
      _ = Fintype.card (X.ConnectedComponent × Y.ConnectedComponent) * n ^ 3 := by simp
  · unfold graphScript
    rw [Script.evalExact_bind, Script.evalExact_seqList]
    show {g : Perm (Fin n) | ∀ c : X.ConnectedComponent, restr X g c ∈ ⋃ S ∈ _, S} = _
    ext g
    simp only [Set.mem_setOf_eq]
    rw [iso_iff_restr g]
    simp only [Set.mem_iUnion, exists_prop, List.mem_map, Finset.mem_toList, Finset.mem_univ,
      true_and]
    constructor
    · intro h c
      obtain ⟨S, ⟨s, ⟨p, rfl⟩, rfl⟩, hmem⟩ := h c
      rw [(hspec p).2.2] at hmem
      obtain ⟨f, hf, hfeq⟩ := hmem
      exact ⟨p.1, p.2, f, hf, hfeq⟩
    · intro h c
      obtain ⟨c₁, c', f, hf, hfeq⟩ := h c
      refine ⟨_, ⟨compScript hXd hYd (c₁, c'), ⟨(c₁, c'), rfl⟩, rfl⟩, ?_⟩
      rw [(hspec (c₁, c')).2.2]
      exact ⟨f, hf, hfeq⟩

end Graph

/-! ### The theorem for all graphs -/

open GI.DegreeD.M in
/-- **GI of maximum degree `d`, at the level of runs, for all graphs.** The statement of
`graphIso_connected` without the connectivity hypotheses. -/
theorem graphIso_general {P : Params} {w : M.Node P → ℝ} (h : Stage1Conclusion P w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n d : ℕ) (X Y : SimpleGraph (Fin n)),
      (∀ v, Nat.card (X.neighborSet v) ≤ d) → (∀ v, Nat.card (Y.neighborSet v) ≤ d) →
      ∃ (s : Script (Set (Perm (Fin n)))) (e : M.Exec P s s.evalExact),
        s.evalExact = {g | ∀ a b, X.Adj a b ↔ Y.Adj (g a) (g b)} ∧
        s.CallsExact (fun {_ _} m T => m = .solve ∧ GammaHat d T.G ∧ (T.size : ℝ) ≤ 3 * (n : ℝ) ^ 4) ∧
        e.total w ≤ Real.exp (C * (Real.log ((d : ℝ) + 2) * Real.log ((n : ℝ) + 2))) := by
  obtain ⟨cσ, C', hcσ, hS⟩ := h
  set C₀ := max C' 0
  refine ⟨10 + 30 * C₀, by have := le_max_right C' 0; simp only [C₀]; linarith, ?_⟩
  intro n d X Y hXd hYd
  letI : Fintype X.ConnectedComponent := Fintype.ofFinite _
  letI : Fintype Y.ConnectedComponent := Fintype.ofFinite _
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
  obtain ⟨hc1, hc2, hc3⟩ := graphScript_spec hXq hYq
  set B := bOm n q with hB
  set s := graphScript hXq hYq with hs
  have hBval : B = n + (n * q + n * q * (n * q)) := rfl
  have hsz : (B : ℝ) ≤ 3 * (n : ℝ) ^ 4 := by
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · subst h0
      have hq0 : q = 0 := by omega
      simp [hB, bOm, hq0]
    · have h1 : n * q ≤ n * n := Nat.mul_le_mul_left _ hqn
      have h2 : n * q * (n * q) ≤ n * n * (n * n) := Nat.mul_le_mul h1 h1
      have h3 : B ≤ 3 * n ^ 4 := by
        rw [hBval]
        have h6 : n * n ≤ n * n * (n * n) := Nat.le_mul_self _
        have h5 : n ≤ n * n := Nat.le_mul_self _
        calc n + (n * q + n * q * (n * q)) ≤ n * n * (n * n) + (n * n * (n * n) + n * n * (n * n)) := by
              have : n * q ≤ n * n * (n * n) := le_trans h1 h6
              omega
          _ = 3 * n ^ 4 := by ring
      exact_mod_cast h3
  have hcalls_d : s.CallsExact (CallOK d B) := hc1.mono fun m T ⟨hm, hf, hg, hs⟩ =>
    ⟨hm, hf, by haveI := hf; exact hg.mono hqd, hs⟩
  have hnum : s.numCalls ≤ n ^ 5 := by
    refine hc2.trans ?_
    have hX : Fintype.card X.ConnectedComponent ≤ n := by
      calc Fintype.card X.ConnectedComponent ≤ Fintype.card (Fin n) :=
            Fintype.card_le_of_surjective _ (Quot.mk_surjective)
        _ = n := Fintype.card_fin n
    have hY : Fintype.card Y.ConnectedComponent ≤ n := by
      calc Fintype.card Y.ConnectedComponent ≤ Fintype.card (Fin n) :=
            Fintype.card_le_of_surjective _ (Quot.mk_surjective)
        _ = n := Fintype.card_fin n
    rw [Fintype.card_prod]
    calc Fintype.card X.ConnectedComponent * Fintype.card Y.ConnectedComponent * n ^ 3
        ≤ n * n * n ^ 3 := Nat.mul_le_mul (Nat.mul_le_mul hX hY) le_rfl
      _ = n ^ 5 := by ring
  have hruns : ∀ {Ω C : Type} [Finite Ω] (S : State Ω C), GammaHat d S.G →
      ∃ r : M.Run P .solve S none S.answer, r.RootsOK cσ (max d 6) :=
    fun S hg => (hS d S hg).1
  obtain ⟨e, he⟩ := exec_of_calls (d := d) (D := max d 6) (le_max_left _ _) hruns s B hcalls_d
  refine ⟨s, e, hc3, ?_, ?_⟩
  · exact hcalls_d.mono fun m T ⟨hm, _, hg, hs⟩ => ⟨hm, hg, le_trans (by exact_mod_cast hs) hsz⟩
  · set K := Real.exp (C₀ * (lam d * Real.log ((B : ℝ) + 2))) with hK
    have hbound := exec_total_le (K := K) (p := CallOK d B) (cσ := cσ) (D := max d 6)
      (w := w) ?_ s e he hcalls_d
    · have hK0 : 0 ≤ K := (Real.exp_pos _).le
      have hfb := final_bound (C₀ := C₀) (le_max_right _ _) n d q (n ^ 5) hqn
        (Nat.pow_le_pow_left (by omega) 5)
      simp only at hfb
      rw [← hBval] at hfb
      calc e.total w ≤ (s.numCalls : ℝ) * K := hbound
        _ ≤ ((n ^ 5 : ℕ) : ℝ) * K := by
          apply mul_le_mul_of_nonneg_right _ hK0
          exact_mod_cast hnum
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

/-- **GI of maximum degree `d`, from the cited results.** With HJ's cited results and the axioms
`bcp`, `gnsPrimitive`: there are parameters `P` and a constant `C` such that for all graphs `X, Y` of
maximum degree `≤ d` on `Fin n`, there is a run of a script of string-isomorphism calls, in `Γ̂_d` and
on at most `3 n⁴` positions each, whose exact value is the isomorphism set of `X` and `Y`,
and with at most `exp(C log(d+2) log(n+2))` nodes. -/
theorem graphIso_final (hcite : GI.Cited.TransitiveAffected)
    (hK : GI.Cited.KaryCoherentRefinement) (h6 : GI.Cited.SixTransitiveContainsAlt)
    (hDL : GI.Cited.DesignLemma) (hAut : GI.Cited.AutCardLeSq)
    (hLie : GI.Cited.SimpleValuationDegree) :
    ∃ (P : Params) (C : ℝ), 0 ≤ C ∧ ∀ (n d : ℕ) (X Y : SimpleGraph (Fin n)),
      (∀ v, Nat.card (X.neighborSet v) ≤ d) → (∀ v, Nat.card (Y.neighborSet v) ≤ d) →
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
  exact graphIso_general (M.degreeD_stage1_cited hcite hK h6 hDL hAut hLie hP hA hT hκ hc hαγ
    hbase h4 hab M.bcp hG hc₁ hc₂ hcc hq (M.nodeBoundD_one h5) le_rfl h197
    (by rw [hPa]; linarith) hγ)

end GI.DegreeD.Luks
