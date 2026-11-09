import DegreeD.Luks.Reduction
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Luks's reduction for graphs

From a connected graph and a root edge: levels by distance to the root edge (`edgeLvl`) and slots
(`mkLG`, an `LG`). The rooted isomorphisms of the whole graph are exactly the elements of
`IsIso … R`, for `R` at least the eccentricity (`rooted_iff`). `connScript` asks, for each
ordered pair of adjacent vertices of `Y` as the image of the root edge, the layers of the
reduction, and returns all isomorphisms; `connScript_spec` is its correctness.
-/

namespace GI.DegreeD.Luks

open Equiv Equiv.Perm GI.Algorithm
open scoped Classical

set_option linter.unusedSectionVars false

/-! ### Levels of a rooted connected graph -/

section Levels

variable {V : Type} {G : SimpleGraph V} {u v : V}

/-- The level of a vertex: the distance to the root edge `{u, v}`. -/
noncomputable def edgeLvl (G : SimpleGraph V) (u v w : V) : ℕ := min (G.dist u w) (G.dist v w)

theorem edgeLvl_zero (hG : G.Connected) {w : V} : edgeLvl G u v w = 0 ↔ w = u ∨ w = v := by
  unfold edgeLvl
  constructor
  · intro h
    rcases Nat.min_eq_zero_iff.1 h with h1 | h2
    · left; exact ((hG.dist_eq_zero_iff).1 h1).symm
    · right; exact ((hG.dist_eq_zero_iff).1 h2).symm
  · rintro (rfl | rfl) <;> simp

theorem edgeLvl_adj_le (hG : G.Connected) {a b : V} (h : G.Adj a b) :
    edgeLvl G u v b ≤ edgeLvl G u v a + 1 := by
  unfold edgeLvl
  have h1 : G.dist u b ≤ G.dist u a + G.dist a b := hG.dist_triangle
  have h2 : G.dist v b ≤ G.dist v a + G.dist a b := hG.dist_triangle
  have h3 : G.dist a b = 1 := SimpleGraph.dist_eq_one_iff_adj.2 h
  simp only [_root_.min_def]
  split_ifs <;> omega

theorem exists_up_dist (hG : G.Connected) {a w : V} (h : G.dist a w ≠ 0) :
    ∃ y, G.Adj y w ∧ G.dist a w = G.dist a y + 1 := by
  obtain ⟨q, hq⟩ := hG.exists_walk_length_eq_dist w a
  cases q with
  | nil => exact absurd SimpleGraph.dist_self h
  | @cons _ y _ hadj q' =>
    refine ⟨y, hadj.symm, ?_⟩
    have h1 : G.dist y a ≤ q'.length := SimpleGraph.dist_le q'
    have h2 : G.dist a y = G.dist y a := SimpleGraph.dist_comm
    have h3 : G.dist a w ≤ G.dist a y + G.dist y w := hG.dist_triangle
    have h4 : G.dist y w = 1 := SimpleGraph.dist_eq_one_iff_adj.2 hadj.symm
    have h5 : G.dist w a = G.dist a w := SimpleGraph.dist_comm
    simp only [SimpleGraph.Walk.length_cons] at hq
    omega

theorem edgeLvl_up (hG : G.Connected) {w : V} (h : edgeLvl G u v w ≠ 0) :
    ∃ y, G.Adj y w ∧ edgeLvl G u v w = edgeLvl G u v y + 1 := by
  unfold edgeLvl at h ⊢
  by_cases huv : G.dist u w ≤ G.dist v w
  · have h1 : G.dist u w ≠ 0 := by
      intro h0
      apply h
      rw [min_eq_left huv, h0]
    obtain ⟨y, hy, hdy⟩ := exists_up_dist hG h1
    refine ⟨y, hy, ?_⟩
    have hv : G.dist v w ≤ G.dist v y + G.dist y w := hG.dist_triangle
    have h3 : G.dist y w = 1 := SimpleGraph.dist_eq_one_iff_adj.2 hy
    simp only [_root_.min_def]
    split_ifs <;> omega
  · have huv' : G.dist v w ≤ G.dist u w := by omega
    have h1 : G.dist v w ≠ 0 := by
      intro h0
      apply h
      rw [min_eq_right huv', h0]
    obtain ⟨y, hy, hdy⟩ := exists_up_dist hG h1
    refine ⟨y, hy, ?_⟩
    have hv : G.dist u w ≤ G.dist u y + G.dist y w := hG.dist_triangle
    have h3 : G.dist y w = 1 := SimpleGraph.dist_eq_one_iff_adj.2 hy
    simp only [_root_.min_def]
    split_ifs <;> omega

theorem edgeLvl_lt_card [Fintype V] (hG : G.Connected) (w : V) :
    edgeLvl G u v w ≤ Fintype.card V := by
  obtain ⟨p, hp⟩ := hG.exists_isPath u w
  have h1 : G.dist u w ≤ p.length := SimpleGraph.dist_le p
  have h2 : p.length < Fintype.card V := hp.length_lt
  have h3 : edgeLvl G u v w ≤ G.dist u w := min_le_left _ _
  omega

/-- A graph isomorphism preserves distances (one inequality). -/
theorem dist_le_of_iso {W : Type} {Y : SimpleGraph W} (hY : Y.Connected) (e : G ≃g Y) (a b : V) :
    G.dist a b ≤ Y.dist (e a) (e b) := by
  obtain ⟨p, hp⟩ := hY.exists_walk_length_eq_dist (e a) (e b)
  have h : (p.map e.symm.toHom).copy (e.symm_apply_apply a) (e.symm_apply_apply b) = _ := rfl
  calc G.dist a b ≤ ((p.map e.symm.toHom).copy (e.symm_apply_apply a) (e.symm_apply_apply b)).length :=
        SimpleGraph.dist_le _
    _ = p.length := by simp
    _ = Y.dist (e a) (e b) := hp

/-- A graph isomorphism preserves distances. -/
theorem dist_eq_of_iso {W : Type} {Y : SimpleGraph W} (hG : G.Connected) (hY : Y.Connected)
    (e : G ≃g Y) (a b : V) : Y.dist (e a) (e b) = G.dist a b := by
  apply le_antisymm
  · have := dist_le_of_iso hG e.symm (e a) (e b)
    simpa using this
  · exact dist_le_of_iso hY e a b

end Levels

/-! ### Slots -/

/-- An injective assignment of slots to each of the given sets of size at most `q`. -/
theorem exists_nb {V : Type} [Finite V] {q : ℕ} (S : V → Set V) (hq : ∀ l, Nat.card (S l) ≤ q) :
    ∃ nb : V → Fin q → Option V, (∀ l i w, nb l i = some w → w ∈ S l) ∧
      (∀ l w, w ∈ S l → ∃ i, nb l i = some w) ∧
      (∀ l i j w, nb l i = some w → nb l j = some w → i = j) := by
  have he : ∀ l, Nonempty (S l ↪ Fin q) := fun l => by
    letI : Fintype (S l) := Fintype.ofFinite _
    apply Function.Embedding.nonempty_of_card_le
    have := hq l
    rw [Nat.card_eq_fintype_card] at this
    simpa using this
  let e : ∀ l, S l ↪ Fin q := fun l => (he l).some
  have hspec : ∀ l, Function.IsPartialInv (e l) (Function.partialInv (e l)) := fun l =>
    (e l).injective.isPartialInv
  refine ⟨fun l i => (Function.partialInv (e l) i).map Subtype.val, ?_, ?_, ?_⟩
  · intro l i w h
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
    exact x.2
  · intro l w hw
    refine ⟨e l ⟨w, hw⟩, ?_⟩
    have h : Function.partialInv (e l) (e l ⟨w, hw⟩) = some ⟨w, hw⟩ := (hspec l _ _).2 rfl
    simp only [h, Option.map_some]
  · intro l i j w h1 h2
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h1
    obtain ⟨x', hx', hx'e⟩ := Option.map_eq_some_iff.1 h2
    have hxx : x' = x := Subtype.ext hx'e
    subst hxx
    have h3 := (hspec l _ _).1 hx
    have h4 := (hspec l _ _).1 hx'
    rw [← h3, ← h4]

section MkLG

variable {V : Type} [Finite V] {G : SimpleGraph V} {u v : V}

/-- The down-neighbours of `l` for the root edge `{u, v}`. -/
def downSet (G : SimpleGraph V) (u v l : V) : Set V :=
  {w | G.Adj l w ∧ edgeLvl G u v w = edgeLvl G u v l + 1}

theorem downSet_card_le {q : ℕ} (hd : ∀ l, Nat.card (G.neighborSet l) ≤ q) (l : V) :
    Nat.card (downSet G u v l) ≤ q := by
  refine le_trans ?_ (hd l)
  let f : downSet G u v l → G.neighborSet l := fun w => ⟨w.1, w.2.1⟩
  have hf : Function.Injective f := fun a b h => Subtype.ext (congrArg (fun x => x.1) h)
  exact Nat.card_le_card_of_injective f hf

/-- **The graph with levels and slots** of a connected graph with a root edge, for slots `q ≥` the
maximum degree. -/
noncomputable def mkLG (G : SimpleGraph V) (hG : G.Connected) (u v : V) (q : ℕ)
    (hd : ∀ l, Nat.card (G.neighborSet l) ≤ q) : LG V q :=
  have hS := exists_nb (q := q) (downSet G u v) (fun l => downSet_card_le hd l)
  { G := G
    lvl := edgeLvl G u v
    nb := hS.choose
    nb_down := fun l i w h => hS.choose_spec.1 l i w h
    nb_all := fun l w h h' => hS.choose_spec.2.1 l w ⟨h, h'⟩
    nb_inj := fun l i j w h h' => hS.choose_spec.2.2 l i j w h h'
    up := fun _ h => edgeLvl_up hG h
    adj_le := fun _ _ h => edgeLvl_adj_le hG h }

@[simp] theorem mkLG_G (hG : G.Connected) (q : ℕ) (hd : ∀ l, Nat.card (G.neighborSet l) ≤ q) :
    (mkLG G hG u v q hd).G = G := rfl

@[simp] theorem mkLG_lvl (hG : G.Connected) (q : ℕ) (hd : ∀ l, Nat.card (G.neighborSet l) ≤ q) :
    (mkLG G hG u v q hd).lvl = edgeLvl G u v := rfl

end MkLG

/-! ### The rooted isomorphisms -/

section Rooted

variable {V W : Type} [Fintype V] [Fintype W] {X : SimpleGraph V} {Y : SimpleGraph W} {q R : ℕ}
  {u v : V} {p : W × W}

/-- The base map of a root edge: `u ↦ p.1` and `v ↦ p.2`. -/
noncomputable def f₀ (u : V) (p : W × W) (w : V) : W := if w = u then p.1 else p.2

theorem f₀_left (u : V) (p : W × W) : f₀ u p u = p.1 := if_pos rfl

theorem f₀_right {v : V} (h : v ≠ u) (p : W × W) : f₀ u p v = p.2 := if_neg h

/-- The base map is an isomorphism of the balls of radius `0`, for adjacent image points. -/
theorem base_isIso (hX : X.Connected) (hY : Y.Connected) (hXd : ∀ l, Nat.card (X.neighborSet l) ≤ q)
    (hYd : ∀ l, Nat.card (Y.neighborSet l) ≤ q) (huv : X.Adj u v) (hp : Y.Adj p.1 p.2) :
    IsIso (mkLG X hX u v q hXd) (mkLG Y hY p.1 p.2 q hYd) (f₀ u p) 0 (f₀ u p) := by
  have hne : v ≠ u := huv.ne'
  have hne' : p.2 ≠ p.1 := hp.ne'
  have hzeroX : ∀ w, edgeLvl X u v w ≤ 0 ↔ w = u ∨ w = v := fun w => by
    rw [Nat.le_zero, edgeLvl_zero hX]
  have hzeroY : ∀ w, edgeLvl Y p.1 p.2 w ≤ 0 ↔ w = p.1 ∨ w = p.2 := fun w => by
    rw [Nat.le_zero, edgeLvl_zero hY]
  have hlvl : ∀ w, w = u ∨ w = v → edgeLvl Y p.1 p.2 (f₀ u p w) = edgeLvl X u v w := by
    rintro w (rfl | rfl)
    · rw [f₀_left]
      have h1 : edgeLvl Y p.1 p.2 p.1 = 0 := (edgeLvl_zero hY).2 (Or.inl rfl)
      have h2 : edgeLvl X w v w = 0 := (edgeLvl_zero hX).2 (Or.inl rfl)
      rw [h1, h2]
    · rw [f₀_right hne]
      have h1 : edgeLvl Y p.1 p.2 p.2 = 0 := (edgeLvl_zero hY).2 (Or.inr rfl)
      have h2 : edgeLvl X u w w = 0 := (edgeLvl_zero hX).2 (Or.inr rfl)
      rw [h1, h2]
  have hmem : ∀ w, w = u ∨ w = v → f₀ u p w = p.1 ∨ f₀ u p w = p.2 := by
    rintro w (rfl | rfl)
    · left; exact f₀_left _ _
    · right; exact f₀_right hne _
  refine ⟨fun w hw => hlvl w ((hzeroX w).1 hw), ?_, fun w _ => rfl, ?_⟩
  · refine ⟨fun w hw => (hzeroY _).2 (hmem w ((hzeroX w).1 hw)), ?_, ?_⟩
    · intro a ha b hb hab
      rcases (hzeroX a).1 ha with rfl | rfl <;> rcases (hzeroX b).1 hb with rfl | rfl
      · rfl
      · rw [f₀_left, f₀_right hne] at hab
        exact absurd hab.symm hne'
      · rw [f₀_right hne, f₀_left] at hab
        exact absurd hab hne'
      · rfl
    · intro y hy
      rcases (hzeroY y).1 hy with rfl | rfl
      · exact ⟨u, (hzeroX u).2 (Or.inl rfl), f₀_left _ _⟩
      · exact ⟨v, (hzeroX v).2 (Or.inr rfl), f₀_right hne _⟩
  · intro a b ha hb
    show X.Adj a b ↔ Y.Adj (f₀ u p a) (f₀ u p b)
    rcases (hzeroX a).1 ha with rfl | rfl <;> rcases (hzeroX b).1 hb with rfl | rfl
    · simp [f₀_left]
    · rw [f₀_left, f₀_right hne]
      exact ⟨fun _ => hp, fun _ => huv⟩
    · rw [f₀_right hne, f₀_left]
      exact ⟨fun _ => hp.symm, fun _ => huv.symm⟩
    · simp [f₀_right hne]

/-- **The isomorphisms of the top ball are the rooted graph isomorphisms.** -/
theorem rooted_iff (hX : X.Connected) (hY : Y.Connected) (hXd : ∀ l, Nat.card (X.neighborSet l) ≤ q)
    (hYd : ∀ l, Nat.card (Y.neighborSet l) ≤ q) (huv : X.Adj u v)
    (hXR : ∀ w, edgeLvl X u v w ≤ R) (hYR : ∀ w, edgeLvl Y p.1 p.2 w ≤ R) (f : V → W) :
    IsIso (mkLG X hX u v q hXd) (mkLG Y hY p.1 p.2 q hYd) (f₀ u p) R f ↔
      ∃ e : X ≃g Y, (e : V → W) = f ∧ e u = p.1 ∧ e v = p.2 := by
  have hne : v ≠ u := huv.ne'
  constructor
  · intro h
    have hbij : Function.Bijective f := by
      have hb := h.bij
      constructor
      · intro a b hab
        exact hb.injOn (hXR a) (hXR b) hab
      · intro y
        obtain ⟨x, -, hx⟩ := hb.surjOn (hYR y)
        exact ⟨x, hx⟩
    let e' : V ≃ W := Equiv.ofBijective f hbij
    let e : X ≃g Y := { toEquiv := e', map_rel_iff' := fun {a b} => (h.adj a b (hXR a) (hXR b)).symm }
    have hu0 : (mkLG X hX u v q hXd).lvl u = 0 := by
      rw [mkLG_lvl]; exact (edgeLvl_zero hX).2 (Or.inl rfl)
    have hv0 : (mkLG X hX u v q hXd).lvl v = 0 := by
      rw [mkLG_lvl]; exact (edgeLvl_zero hX).2 (Or.inr rfl)
    refine ⟨e, rfl, ?_, ?_⟩
    · show f u = p.1
      rw [h.root u hu0, f₀_left]
    · show f v = p.2
      rw [h.root v hv0, f₀_right hne]
  · rintro ⟨e, rfl, heu, hev⟩
    refine ⟨fun w hw => ?_, ?_, fun w hw => ?_, fun a b ha hb => ?_⟩
    · show edgeLvl Y p.1 p.2 (e w) = edgeLvl X u v w
      unfold edgeLvl
      rw [← heu, ← hev, dist_eq_of_iso hX hY, dist_eq_of_iso hX hY]
    · constructor
      · intro w hw
        exact hYR _
      · constructor
        · intro a _ b _ hab
          exact e.injective hab
        · intro y _
          exact ⟨e.symm y, hXR _, e.apply_symm_apply y⟩
    · have hw0 : edgeLvl X u v w = 0 := hw
      rcases (edgeLvl_zero hX).1 hw0 with rfl | rfl
      · rw [heu, f₀_left]
      · rw [hev, f₀_right hne]
    · show X.Adj a b ↔ Y.Adj (e a) (e b)
      exact e.map_rel_iff.symm

end Rooted

/-! ### Connected graphs -/

section Conn

variable {V W : Type} [Fintype V] [Fintype W] {X : SimpleGraph V} {Y : SimpleGraph W} {q R : ℕ}
  {u v : V}

/-- The script of one candidate image of the root edge. -/
noncomputable def candScript (hX : X.Connected) (hY : Y.Connected)
    (hXd : ∀ l, Nat.card (X.neighborSet l) ≤ q) (hYd : ∀ l, Nat.card (Y.neighborSet l) ≤ q)
    (u v : V) (R : ℕ) (p : W × W) : Script (Set (V → W)) :=
  if _h : Y.Adj p.1 p.2 then
    rootedScript (mkLG X hX u v q hXd) (mkLG Y hY p.1 p.2 q hYd) (f₀ u p) R
  else Script.done ∅

/-- **The reduction of a connected graph**: for every ordered pair of adjacent vertices of `Y`
as the image of the root edge `(u, v)`, the layers of the reduction. -/
noncomputable def connScript (hX : X.Connected) (hY : Y.Connected)
    (hXd : ∀ l, Nat.card (X.neighborSet l) ≤ q) (hYd : ∀ l, Nat.card (Y.neighborSet l) ≤ q)
    (u v : V) (R : ℕ) : Script (Set (V → W)) :=
  (Script.seqList ((Finset.univ : Finset (W × W)).toList.map
      (candScript hX hY hXd hYd u v R))).bind fun l => Script.done (⋃ s ∈ l, s)

/-- **Correctness of the reduction for connected graphs.** The script returns exactly the
graph isomorphisms; its calls are `Solve` calls in `Γ̂_q` on `|Om V q|` positions, and it makes at most
`|W|² R` calls. -/
theorem connScript_spec (hX : X.Connected) (hY : Y.Connected)
    (hXd : ∀ l, Nat.card (X.neighborSet l) ≤ q) (hYd : ∀ l, Nat.card (Y.neighborSet l) ≤ q)
    (huv : X.Adj u v) (hXR : ∀ w, edgeLvl X u v w ≤ R)
    (hYR : ∀ (p : W × W) w, edgeLvl Y p.1 p.2 w ≤ R) :
    (connScript hX hY hXd hYd u v R).CallsExact (CallOK q (Nat.card (Om V q))) ∧
      (connScript hX hY hXd hYd u v R).numCalls ≤ Fintype.card (W × W) * R ∧
      (connScript hX hY hXd hYd u v R).evalExact =
        {f | ∃ e : X ≃g Y, (e : V → W) = f} := by
  have hcand : ∀ p : W × W, (candScript hX hY hXd hYd u v R p).CallsExact
      (CallOK q (Nat.card (Om V q))) ∧ (candScript hX hY hXd hYd u v R p).numCalls ≤ R ∧
      (candScript hX hY hXd hYd u v R p).evalExact =
        {f | Y.Adj p.1 p.2 ∧ ∃ e : X ≃g Y, (e : V → W) = f ∧ e u = p.1 ∧ e v = p.2} := by
    intro p
    unfold candScript
    split_ifs with hp
    · obtain ⟨h1, h2, h3⟩ := rootedScript_spec (X := mkLG X hX u v q hXd)
        (Y := mkLG Y hY p.1 p.2 q hYd) (f₀ := f₀ u p) (R := R)
        (base_isIso hX hY hXd hYd huv hp) hXR
      refine ⟨h1, h2, ?_⟩
      rw [h3]
      ext f
      simp only [Set.mem_setOf_eq]
      rw [rooted_iff hX hY hXd hYd huv hXR (hYR p) f]
      exact ⟨fun h => ⟨hp, h⟩, fun h => h.2⟩
    · refine ⟨trivial, by simp [Script.numCalls], ?_⟩
      show (∅ : Set (V → W)) = _
      ext f
      simp only [Set.mem_empty_iff_false, Set.mem_setOf_eq, false_iff, not_and]
      intro hadj
      exact absurd hadj hp
  refine ⟨?_, ?_, ?_⟩
  · refine Script.callsExact_bind _ _ (Script.callsExact_seqList _ fun s hs => ?_) trivial
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hs
    exact (hcand p).1
  · unfold connScript
    rw [Script.numCalls_bind, Script.numCalls_seqList]
    simp only [Script.numCalls, add_zero, List.map_map]
    have hle : ∀ x ∈ ((Finset.univ : Finset (W × W)).toList.map
        (Script.numCalls ∘ candScript hX hY hXd hYd u v R)), x ≤ R := by
      intro x hx
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
      exact (hcand p).2.1
    calc _ ≤ ((Finset.univ : Finset (W × W)).toList.map
              (Script.numCalls ∘ candScript hX hY hXd hYd u v R)).length • R :=
          List.sum_le_card_nsmul _ _ hle
      _ = Fintype.card (W × W) * R := by
          simp
  · unfold connScript
    rw [Script.evalExact_bind, Script.evalExact_seqList]
    ext f
    simp only [Script.evalExact, Set.mem_iUnion, exists_prop, List.mem_map, Finset.mem_toList,
      Finset.mem_univ, true_and, Function.comp, List.map_map]
    constructor
    · rintro ⟨s, ⟨p, rfl⟩, hs⟩
      rw [(hcand p).2.2] at hs
      obtain ⟨-, e, he, -⟩ := hs
      exact ⟨e, he⟩
    · rintro ⟨e, rfl⟩
      let p : W × W := (e u, e v)
      have hp : Y.Adj p.1 p.2 := e.map_rel_iff.2 huv
      refine ⟨_, ⟨p, rfl⟩, ?_⟩
      rw [(hcand p).2.2]
      exact ⟨hp, e, rfl, rfl, rfl⟩

end Conn

end GI.DegreeD.Luks
