import DegreeD.Luks.Wreath
import Workspace.Algorithm.AuxConfig

/-!
# One layer of Luks's reduction

A graph with levels and slots (`LG`): `lvl : V → ℕ` where adjacent vertices differ by at most
one level and every vertex above level `0` has a neighbour one level below, and for each vertex
`l` a slot assignment `nb l : Fin q → Option V` of its down-neighbours. The partial
isomorphisms of the balls `{lvl ≤ r}` (`IsIso`) and the partial automorphisms (`LG.aut`).

The reduction step: `layerState X Y A τ r`, the string-isomorphism instance whose group is
`S_q ≀_V A` (acting on vertices, slots and pairs of slots) and whose strings are `str X X id r`
and `str X Y τ r`. Theorem `extf_isIso`: every element of the answer induces an isomorphism of the
next ball (`extf`), and `extf_surj`: every isomorphism of the next ball is induced by an element
of the answer.
-/

namespace GI.DegreeD.Luks

open Equiv Equiv.Perm GI.Algorithm
open scoped Classical

set_option linter.unusedSectionVars false

variable {V W : Type} {q : ℕ}

/-- **A graph with levels and `q` down-slots at each vertex.** -/
structure LG (V : Type) (q : ℕ) where
  G : SimpleGraph V
  lvl : V → ℕ
  nb : V → Fin q → Option V
  nb_down : ∀ l i w, nb l i = some w → G.Adj l w ∧ lvl w = lvl l + 1
  nb_all : ∀ l w, G.Adj l w → lvl w = lvl l + 1 → ∃ i, nb l i = some w
  nb_inj : ∀ l i j w, nb l i = some w → nb l j = some w → i = j
  up : ∀ w, lvl w ≠ 0 → ∃ y, G.Adj y w ∧ lvl w = lvl y + 1
  adj_le : ∀ a b, G.Adj a b → lvl b ≤ lvl a + 1

/-- Occupancy of a slot. -/
def occ {α : Type*} : Option α → ℕ
  | some _ => 1
  | none => 0

open Classical in
/-- The value of a pair of slots: `0` if a slot is empty; `2` if the occupants are equal;
`3` if they are adjacent, `4` otherwise. -/
noncomputable def pv (Z : LG W q) : Option W → Option W → ℕ
  | some w, some w' => if w = w' then 2 else if Z.G.Adj w w' then 3 else 4
  | _, _ => 0

@[simp] theorem occ_some {α : Type*} (a : α) : occ (some a) = 1 := rfl
@[simp] theorem occ_none {α : Type*} : occ (none : Option α) = 0 := rfl

theorem occ_eq_iff {α β : Type*} {o : Option α} {o' : Option β} :
    occ o = occ o' ↔ (o.isSome ↔ o'.isSome) := by
  cases o <;> cases o' <;> simp [occ]

theorem pv_some_some (Z : LG W q) (w w' : W) :
    pv Z (some w) (some w') = if w = w' then 2 else if Z.G.Adj w w' then 3 else 4 := rfl

@[simp] theorem pv_none_left (Z : LG W q) (o : Option W) : pv Z none o = 0 := by
  cases o <;> rfl

@[simp] theorem pv_none_right (Z : LG W q) (o : Option W) : pv Z o none = 0 := by
  cases o <;> rfl

theorem pv_self (Z : LG W q) (a : W) : pv Z (some a) (some a) = 2 := by
  simp [pv_some_some]

theorem pv_eq_two {Z : LG W q} {o o' : Option W} (h : pv Z o o' = 2) :
    ∃ z, o = some z ∧ o' = some z := by
  cases o with
  | none => simp at h
  | some w =>
    cases o' with
    | none => simp at h
    | some w' =>
      rw [pv_some_some] at h
      split_ifs at h with h1 <;> simp_all

theorem adj_iff_pv (Z : LG W q) (a b : W) :
    Z.G.Adj a b ↔ pv Z (some a) (some b) = 3 := by
  rw [pv_some_some]
  by_cases hab : a = b
  · subst hab
    simp
  · simp only [hab, if_false]
    split_ifs with h <;> simp [h]

theorem pv_eq_two_iff (Z : LG W q) (a b : W) : pv Z (some a) (some b) = 2 ↔ a = b := by
  rw [pv_some_some]
  by_cases hab : a = b
  · simp [hab]
  · simp only [hab, if_false]
    split_ifs <;> simp

/-- The string of the instance: the graph `Y`, read along `τ` at the slots of `V` in level `r`. -/
noncomputable def str (X : LG V q) (Y : LG W q) (τ : V → W) (r : ℕ) : Om V q → ℕ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl p) => if X.lvl p.1 = r then occ (Y.nb (τ p.1) p.2) else 0
  | Sum.inr (Sum.inr (p, p')) =>
      if X.lvl p.1 = r ∧ X.lvl p'.1 = r then pv Y (Y.nb (τ p.1) p.2) (Y.nb (τ p'.1) p'.2) else 0

@[simp] theorem str_inl (X : LG V q) (Y : LG W q) (τ : V → W) (r : ℕ) (v : V) :
    str X Y τ r (Sum.inl v) = 0 := rfl

theorem str_slot (X : LG V q) (Y : LG W q) (τ : V → W) (r : ℕ) (p : Sl V q) :
    str X Y τ r (Sum.inr (Sum.inl p)) =
      if X.lvl p.1 = r then occ (Y.nb (τ p.1) p.2) else 0 := rfl

theorem str_pair (X : LG V q) (Y : LG W q) (τ : V → W) (r : ℕ) (p p' : Sl V q) :
    str X Y τ r (Sum.inr (Sum.inr (p, p'))) =
      if X.lvl p.1 = r ∧ X.lvl p'.1 = r then pv Y (Y.nb (τ p.1) p.2) (Y.nb (τ p'.1) p'.2) else 0 := rfl

/-- The partial isomorphisms of the balls of radius `r`. -/
structure IsIso (X : LG V q) (Y : LG W q) (f₀ : V → W) (r : ℕ) (f : V → W) : Prop where
  lvl_eq : ∀ w, X.lvl w ≤ r → Y.lvl (f w) = X.lvl w
  bij : Set.BijOn f {w | X.lvl w ≤ r} {w | Y.lvl w ≤ r}
  root : ∀ w, X.lvl w = 0 → f w = f₀ w
  adj : ∀ a b, X.lvl a ≤ r → X.lvl b ≤ r → (X.G.Adj a b ↔ Y.G.Adj (f a) (f b))

/-- The automorphisms of the ball of radius `r`, as permutations of the whole vertex set which
fix everything beyond level `r` and at level `0`, and preserve levels. -/
def LG.aut (X : LG V q) (r : ℕ) : Subgroup (Perm V) where
  carrier := {a | (∀ w, r < X.lvl w → a w = w) ∧ (∀ w, X.lvl w = 0 → a w = w) ∧
    (∀ w, X.lvl (a w) = X.lvl w) ∧
    ∀ u v, X.lvl u ≤ r → X.lvl v ≤ r → (X.G.Adj u v ↔ X.G.Adj (a u) (a v))}
  mul_mem' := by
    rintro a b ⟨h1, h2, h3, h4⟩ ⟨h1', h2', h3', h4'⟩
    refine ⟨fun w hw => ?_, fun w hw => ?_, fun w => ?_, fun u v hu hv => ?_⟩
    · simp only [Perm.mul_apply, h1' w hw, h1 w hw]
    · simp only [Perm.mul_apply, h2' w hw, h2 w hw]
    · simp only [Perm.mul_apply, h3, h3']
    · simp only [Perm.mul_apply]
      rw [h4' u v hu hv]
      exact h4 _ _ (by rw [h3']; exact hu) (by rw [h3']; exact hv)
  one_mem' := ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ _ _ => Iff.rfl⟩
  inv_mem' := by
    rintro a ⟨h1, h2, h3, h4⟩
    have h1' : ∀ w, r < X.lvl w → a⁻¹ w = w := fun w hw => by
      rw [Perm.inv_eq_iff_eq]; exact (h1 w hw).symm
    have h2' : ∀ w, X.lvl w = 0 → a⁻¹ w = w := fun w hw => by
      rw [Perm.inv_eq_iff_eq]; exact (h2 w hw).symm
    have h3' : ∀ w, X.lvl (a⁻¹ w) = X.lvl w := fun w => by
      rw [← h3 (a⁻¹ w)]; simp
    refine ⟨h1', h2', h3', fun u v hu hv => ?_⟩
    have := h4 (a⁻¹ u) (a⁻¹ v) (by rw [h3']; exact hu) (by rw [h3']; exact hv)
    simp only [apply_inv_self] at this
    exact this.symm

theorem LG.mem_aut {X : LG V q} {r : ℕ} {a : Perm V} : a ∈ X.aut r ↔
    (∀ w, r < X.lvl w → a w = w) ∧ (∀ w, X.lvl w = 0 → a w = w) ∧
    (∀ w, X.lvl (a w) = X.lvl w) ∧
    ∀ u v, X.lvl u ≤ r → X.lvl v ≤ r → (X.G.Adj u v ↔ X.G.Adj (a u) (a v)) := Iff.rfl

/-- `IsIso` restricts to smaller balls. -/
theorem IsIso.mono {X : LG V q} {Y : LG W q} {f₀ : V → W} {r r' : ℕ} {f : V → W}
    (h : IsIso X Y f₀ r' f) (hr : r ≤ r') : IsIso X Y f₀ r f where
  lvl_eq w hw := h.lvl_eq w (hw.trans hr)
  bij := by
    refine ⟨fun w hw => ?_, fun u hu v hv huv => ?_, fun y hy => ?_⟩
    · show Y.lvl (f w) ≤ r
      rw [h.lvl_eq w (le_trans hw hr)]
      exact hw
    · exact h.bij.injOn (show X.lvl u ≤ r' from le_trans hu hr)
        (show X.lvl v ≤ r' from le_trans hv hr) huv
    · obtain ⟨x, hx, hxy⟩ := h.bij.surjOn (show Y.lvl y ≤ r' from le_trans hy hr)
      refine ⟨x, ?_, hxy⟩
      show X.lvl x ≤ r
      have := h.lvl_eq x hx
      rw [hxy] at this
      rw [← this]
      exact hy
  root := h.root
  adj a b ha hb := h.adj a b (ha.trans hr) (hb.trans hr)

/-- Two isomorphisms of the same ball differ by an automorphism. -/
theorem IsIso.exists_aut [Finite V] {X : LG V q} {Y : LG W q} {f₀ : V → W} {r : ℕ} {τ f : V → W}
    (hτ : IsIso X Y f₀ r τ) (hf : IsIso X Y f₀ r f) :
    ∃ a ∈ X.aut r, ∀ w, X.lvl w ≤ r → τ (a w) = f w := by
  classical
  have hB : ∀ w, X.lvl w ≤ r → ∃ x, X.lvl x ≤ r ∧ τ x = f w := fun w hw => by
    have hmem : Y.lvl (f w) ≤ r := by rw [hf.lvl_eq w hw]; exact hw
    obtain ⟨x, hx, hxe⟩ := hτ.bij.surjOn hmem
    exact ⟨x, hx, hxe⟩
  let a₀ : V → V := fun w => if hw : X.lvl w ≤ r then (hB w hw).choose else w
  have ha₀ : ∀ w, X.lvl w ≤ r → X.lvl (a₀ w) ≤ r ∧ τ (a₀ w) = f w := fun w hw => by
    simp only [a₀, dif_pos hw]
    exact (hB w hw).choose_spec
  have ha₀' : ∀ w, ¬ X.lvl w ≤ r → a₀ w = w := fun w hw => by
    simp only [a₀, dif_neg hw]
  have hinj : Function.Injective a₀ := by
    intro w₁ w₂ h
    by_cases h1 : X.lvl w₁ ≤ r
    · by_cases h2 : X.lvl w₂ ≤ r
      · have e1 := (ha₀ w₁ h1).2
        have e2 := (ha₀ w₂ h2).2
        rw [h] at e1
        exact hf.bij.injOn h1 h2 (e1.symm.trans e2)
      · have h3 := (ha₀ w₁ h1).1
        rw [h, ha₀' w₂ h2] at h3
        exact absurd h3 h2
    · by_cases h2 : X.lvl w₂ ≤ r
      · have h3 := (ha₀ w₂ h2).1
        rw [← h, ha₀' w₁ h1] at h3
        exact absurd h3 h1
      · rwa [ha₀' w₁ h1, ha₀' w₂ h2] at h
  have hbij : Function.Bijective a₀ := Finite.injective_iff_bijective.1 hinj
  refine ⟨Equiv.ofBijective a₀ hbij, ?_, fun w hw => (ha₀ w hw).2⟩
  refine ⟨fun w hw => ha₀' w (by omega), fun w hw => ?_, fun w => ?_, fun u v hu hv => ?_⟩
  · show a₀ w = w
    have hw0 : X.lvl w ≤ r := by omega
    obtain ⟨h1, h2⟩ := ha₀ w hw0
    have e : τ (a₀ w) = τ w := by rw [h2, hf.root w hw, hτ.root w hw]
    exact hτ.bij.injOn h1 hw0 e
  · show X.lvl (a₀ w) = X.lvl w
    by_cases hw : X.lvl w ≤ r
    · obtain ⟨h1, h2⟩ := ha₀ w hw
      rw [← hτ.lvl_eq _ h1, h2, hf.lvl_eq w hw]
    · rw [ha₀' w hw]
  · show X.G.Adj u v ↔ X.G.Adj (a₀ u) (a₀ v)
    obtain ⟨h1, h2⟩ := ha₀ u hu
    obtain ⟨h1', h2'⟩ := ha₀ v hv
    rw [hf.adj u v hu hv, hτ.adj _ _ h1 h1', h2, h2']

/-- An isomorphism composed with an automorphism. -/
theorem IsIso.comp_aut {X : LG V q} {Y : LG W q} {f₀ : V → W} {r : ℕ} {τ : V → W}
    (hτ : IsIso X Y f₀ r τ) {a : Perm V} (ha : a ∈ X.aut r) : IsIso X Y f₀ r (fun w => τ (a w)) := by
  obtain ⟨h1, h2, h3, h4⟩ := LG.mem_aut.1 ha
  have hb : ∀ w, X.lvl w ≤ r → X.lvl (a w) ≤ r := fun w hw => by rw [h3]; exact hw
  refine ⟨fun w hw => by rw [hτ.lvl_eq _ (hb w hw), h3], ?_, fun w hw => by rw [h2 w hw, hτ.root w hw],
    fun u v hu hv => by rw [h4 u v hu hv]; exact hτ.adj _ _ (hb u hu) (hb v hv)⟩
  refine ⟨fun w hw => ?_, fun u hu v hv huv => ?_, fun y hy => ?_⟩
  · show Y.lvl (τ (a w)) ≤ r
    rw [hτ.lvl_eq _ (hb w hw), h3]
    exact hw
  · exact a.injective (hτ.bij.injOn (hb u hu) (hb v hv) huv)
  · obtain ⟨x, hx, hxy⟩ := hτ.bij.surjOn hy
    have hx' : X.lvl x ≤ r := hx
    refine ⟨a⁻¹ x, ?_, ?_⟩
    · show X.lvl (a⁻¹ x) ≤ r
      have := h3 (a⁻¹ x)
      rw [apply_inv_self] at this
      omega
    · show τ (a (a⁻¹ x)) = y
      rw [apply_inv_self, hxy]

/-- If `f = τ ∘ b` on a ball with `f, τ` isomorphisms and `b` fixing the outside, then `b` is
an automorphism of the ball. -/
theorem IsIso.mem_aut {X : LG V q} {Y : LG W q} {f₀ : V → W} {r : ℕ} {τ f : V → W}
    (hτ : IsIso X Y f₀ r τ) (hf : IsIso X Y f₀ r f) {b : Perm V}
    (hout : ∀ w, r < X.lvl w → b w = w) (hb : ∀ w, X.lvl w ≤ r → f w = τ (b w)) :
    b ∈ X.aut r := by
  have hin : ∀ w, X.lvl w ≤ r → X.lvl (b w) ≤ r := fun w hw => by
    by_contra h
    have h' : r < X.lvl (b w) := by omega
    have := hout (b w) h'
    have hbw : b w = w := b.injective this
    rw [hbw] at h'
    omega
  have hlvl : ∀ w, X.lvl (b w) = X.lvl w := fun w => by
    by_cases hw : X.lvl w ≤ r
    · have e1 := hf.lvl_eq w hw
      have e2 := hτ.lvl_eq _ (hin w hw)
      rw [← hb w hw] at e2
      omega
    · rw [hout w (by omega)]
  refine ⟨hout, fun w hw => ?_, hlvl, fun u v hu hv => ?_⟩
  · have hw0 : X.lvl w ≤ r := by omega
    have e : τ (b w) = τ w := by rw [← hb w hw0, hf.root w hw, hτ.root w hw]
    exact hτ.bij.injOn (hin w hw0) hw0 e
  · rw [hf.adj u v hu hv, hb u hu, hb v hv]
    exact (hτ.adj _ _ (hin u hu) (hin v hv)).symm

/-! ### Reading the answer of the instance -/

/-- The vertex component of a permutation of the domain. -/
def hV (h : Perm (Om V q)) (v : V) : V :=
  match h (Sum.inl v) with
  | Sum.inl w => w
  | Sum.inr _ => v

/-- The slot component of a permutation of the domain. -/
def hSl (h : Perm (Om V q)) (p : Sl V q) : Sl V q :=
  match h (Sum.inr (Sum.inl p)) with
  | Sum.inr (Sum.inl p') => p'
  | _ => p

@[simp] theorem hV_act (a : Perm V) (s : V → Perm (Fin q)) (v : V) : hV (act a s) v = a v := rfl

@[simp] theorem hSl_act (a : Perm V) (s : V → Perm (Fin q)) (p : Sl V q) :
    hSl (act a s) p = (a p.1, s p.1 p.2) := rfl

theorem LG.exists_upSlot (X : LG V q) {w : V} (h : X.lvl w ≠ 0) :
    ∃ p : Sl V q, X.nb p.1 p.2 = some w ∧ X.lvl w = X.lvl p.1 + 1 := by
  obtain ⟨y, hy, hl⟩ := X.up w h
  obtain ⟨i, hi⟩ := X.nb_all y w hy hl
  exact ⟨(y, i), hi, hl⟩

/-- A chosen slot of a vertex of positive level. -/
noncomputable def LG.upSlot (X : LG V q) (w : V) (h : X.lvl w ≠ 0) : Sl V q :=
  (X.exists_upSlot h).choose

theorem LG.upSlot_spec (X : LG V q) (w : V) (h : X.lvl w ≠ 0) :
    X.nb (X.upSlot w h).1 (X.upSlot w h).2 = some w ∧ X.lvl w = X.lvl (X.upSlot w h).1 + 1 :=
  (X.exists_upSlot h).choose_spec

open Classical in
/-- **The map of the balls induced by a permutation of the domain.** On the ball of radius `r`,
`τ ∘ a`; on level `r + 1`, the occupant in `Y` of the image of a chosen slot of `w`. -/
noncomputable def extf (X : LG V q) (Y : LG W q) (τ : V → W) (r : ℕ) (h : Perm (Om V q)) (w : V) : W :=
  if hw : X.lvl w ≤ r then τ (hV h w)
  else if hw' : X.lvl w = r + 1 then
    (Y.nb (τ (hSl h (X.upSlot w (by omega))).1) (hSl h (X.upSlot w (by omega))).2).getD (τ w)
  else τ w

/-! ### Soundness of a step -/

section Sound

variable {X : LG V q} {Y : LG W q} {f₀ : V → W} {τ : V → W} {r : ℕ} {a : Perm V}
  {s : V → Perm (Fin q)}

theorem extf_of_le (w : V) (h : Perm (Om V q)) (hw : X.lvl w ≤ r) :
    extf X Y τ r h w = τ (hV h w) := by
  simp [extf, hw]

theorem extf_of_succ (w : V) (h : Perm (Om V q)) (hw : X.lvl w = r + 1) :
    extf X Y τ r h w =
      (Y.nb (τ (hSl h (X.upSlot w (by omega))).1) (hSl h (X.upSlot w (by omega))).2).getD (τ w) := by
  simp [extf, hw]

/-- The hypotheses and first consequences of a step. -/
structure StepHyp (X : LG V q) (Y : LG W q) (f₀ : V → W) (τ : V → W) (r : ℕ) (a : Perm V)
    (s : V → Perm (Fin q)) : Prop where
  hτ : IsIso X Y f₀ r τ
  ha : a ∈ X.aut r
  hans : ∀ ω, str X Y τ r (act a s ω) = str X X id r ω

variable (hS : StepHyp X Y f₀ τ r a s)
include hS

theorem StepHyp.lvl_a (l : V) : X.lvl (a l) = X.lvl l := (LG.mem_aut.1 hS.ha).2.2.1 l

theorem StepHyp.C1 (l : V) (i : Fin q) (hl : X.lvl l = r) :
    occ (Y.nb (τ (a l)) (s l i)) = occ (X.nb l i) := by
  have := hS.hans (Sum.inr (Sum.inl (l, i)))
  simpa only [act_slot, str_slot, hS.lvl_a, hl, if_true, id] using this

theorem StepHyp.C2 (l : V) (i : Fin q) (l' : V) (i' : Fin q) (hl : X.lvl l = r)
    (hl' : X.lvl l' = r) :
    pv Y (Y.nb (τ (a l)) (s l i)) (Y.nb (τ (a l')) (s l' i')) = pv X (X.nb l i) (X.nb l' i') := by
  have := hS.hans (Sum.inr (Sum.inr ((l, i), (l', i'))))
  simpa only [act_pair, str_pair, hS.lvl_a, hl, hl', if_true, id, and_self] using this

/-- Abbreviation for the image of the chosen slot of `w`. -/
theorem StepHyp.slot_upSlot (w : V) (hw : X.lvl w = r + 1) :
    Y.nb (τ (a (X.upSlot w (by omega)).1)) (s (X.upSlot w (by omega)).1 (X.upSlot w (by omega)).2)
      = some (extf X Y τ r (act a s) w) := by
  have hnz : X.lvl w ≠ 0 := by omega
  obtain ⟨hp, hplvl⟩ := X.upSlot_spec w hnz
  have hl : X.lvl (X.upSlot w hnz).1 = r := by omega
  have h := hS.C1 (X.upSlot w hnz).1 (X.upSlot w hnz).2 hl
  rw [hp, occ_some] at h
  rw [extf_of_succ w _ hw, hSl_act]
  cases hO : Y.nb (τ (a (X.upSlot w hnz).1)) (s (X.upSlot w hnz).1 (X.upSlot w hnz).2) with
  | none => rw [hO] at h; simp at h
  | some z =>
    rw [Option.getD_some]

/-- The occupants of the images of two slots with the same occupant agree. The occupant of the image
of a slot `(l, i)` occupied by `w` is the value of `extf` at `w`. -/
theorem StepHyp.slot_image (l : V) (i : Fin q) (w : V) (hl : X.lvl l = r)
    (hw : X.nb l i = some w) : Y.nb (τ (a l)) (s l i) = some (extf X Y τ r (act a s) w) := by
  obtain ⟨-, hlw⟩ := X.nb_down l i w hw
  have hw' : X.lvl w = r + 1 := by omega
  have hnz : X.lvl w ≠ 0 := by omega
  obtain ⟨hp, hplvl⟩ := X.upSlot_spec w hnz
  have hl' : X.lvl (X.upSlot w hnz).1 = r := by omega
  have h := hS.C2 l i (X.upSlot w hnz).1 (X.upSlot w hnz).2 hl hl'
  rw [hw, hp, hS.slot_upSlot w hw', pv_self] at h
  obtain ⟨z, h1, h2⟩ := pv_eq_two h
  rw [h1]
  simp only [Option.some.injEq] at h2
  rw [h2]

/-- Occupied slots at level `r` correspond under the step. -/
theorem StepHyp.occ_of_image (l : V) (i : Fin q) (w' : W) (hl : X.lvl l = r)
    (hw' : Y.nb (τ (a l)) (s l i) = some w') : ∃ w, X.nb l i = some w := by
  have h := hS.C1 l i hl
  rw [hw', occ_some] at h
  cases hO : X.nb l i with
  | none => rw [hO] at h; simp at h
  | some z => exact ⟨z, rfl⟩

/-- `extf` is injective on level `r + 1`. -/
theorem StepHyp.inj_succ (w w' : V) (hw : X.lvl w = r + 1) (hw' : X.lvl w' = r + 1)
    (h : extf X Y τ r (act a s) w = extf X Y τ r (act a s) w') : w = w' := by
  have hnz : X.lvl w ≠ 0 := by omega
  have hnz' : X.lvl w' ≠ 0 := by omega
  obtain ⟨hp, hplvl⟩ := X.upSlot_spec w hnz
  obtain ⟨hp', hplvl'⟩ := X.upSlot_spec w' hnz'
  have hC := hS.C2 (X.upSlot w hnz).1 (X.upSlot w hnz).2 (X.upSlot w' hnz').1 (X.upSlot w' hnz').2
    (by omega) (by omega)
  rw [hS.slot_upSlot w hw, hS.slot_upSlot w' hw', hp, hp', h, pv_self] at hC
  exact (pv_eq_two_iff X w w').1 hC.symm

/-- The level of `extf` on the next ball. -/
theorem StepHyp.lvl_extf (w : V) (hw : X.lvl w ≤ r + 1) :
    Y.lvl (extf X Y τ r (act a s) w) = X.lvl w := by
  by_cases h : X.lvl w ≤ r
  · rw [extf_of_le w _ h, hV_act, hS.hτ.lvl_eq _ (by rw [hS.lvl_a]; exact h), hS.lvl_a]
  · have hw' : X.lvl w = r + 1 := by omega
    have hnz : X.lvl w ≠ 0 := by omega
    obtain ⟨hp, hplvl⟩ := X.upSlot_spec w hnz
    have hl : X.lvl (X.upSlot w hnz).1 = r := by omega
    have h1 := hS.slot_upSlot w hw'
    obtain ⟨-, h2⟩ := Y.nb_down _ _ _ h1
    rw [hS.hτ.lvl_eq _ (by rw [hS.lvl_a]; omega), hS.lvl_a] at h2
    omega

/-- **Soundness of a step.** A permutation of the domain in the answer induces an isomorphism of
the next ball. -/
theorem extf_isIso : IsIso X Y f₀ (r + 1) (extf X Y τ r (act a s)) := by
  obtain ⟨ha_out, ha_root, ha_lvl, ha_adj⟩ := LG.mem_aut.1 hS.ha
  have hτ := hS.hτ
  have hle : ∀ w, X.lvl w ≤ r → extf X Y τ r (act a s) w = τ (a w) := fun w hw => by
    rw [extf_of_le w _ hw, hV_act]
  set F := extf X Y τ r (act a s) with hF
  have hlvlF : ∀ w, X.lvl w ≤ r + 1 → Y.lvl (F w) = X.lvl w := hS.lvl_extf
  have hinjS : ∀ w w', X.lvl w = r + 1 → X.lvl w' = r + 1 → F w = F w' → w = w' := hS.inj_succ
  have hslot : ∀ l i w, X.lvl l = r → X.nb l i = some w → Y.nb (τ (a l)) (s l i) = some (F w) :=
    hS.slot_image
  have hball : ∀ w, X.lvl w ≤ r → X.lvl (a w) ≤ r := fun w hw => by rw [ha_lvl]; exact hw
  -- adjacency between level `r` and level `r + 1`
  have hadj : ∀ u v, X.lvl u = r → X.lvl v = r + 1 → (X.G.Adj u v ↔ Y.G.Adj (F u) (F v)) := by
    intro u v hu hv
    have huF : F u = τ (a u) := hle u (by omega)
    have hlu : Y.lvl (F u) = r := by rw [hlvlF u (by omega)]; exact hu
    have hlv : Y.lvl (F v) = r + 1 := by rw [hlvlF v (by omega)]; exact hv
    constructor
    · intro hadj
      obtain ⟨i, hi⟩ := X.nb_all u v hadj (by omega)
      have h1 := hslot u i v hu hi
      rw [huF]
      exact (Y.nb_down _ _ _ h1).1
    · intro hadj
      rw [huF] at hadj
      obtain ⟨i', hi'⟩ := Y.nb_all _ _ hadj (by rw [← huF, hlu]; omega)
      have hsi : s u ((s u)⁻¹ i') = i' := by simp
      have h2 : Y.nb (τ (a u)) (s u ((s u)⁻¹ i')) = some (F v) := by rw [hsi]; exact hi'
      obtain ⟨w, hw⟩ := hS.occ_of_image u _ _ hu h2
      have h3 := hslot u _ w hu hw
      rw [h2] at h3
      have hww : v = w := by
        have hFw : F v = F w := Option.some.inj h3
        obtain ⟨-, hlw⟩ := X.nb_down u _ w hw
        exact hinjS v w hv (by omega) hFw
      subst hww
      exact (X.nb_down u _ _ hw).1
  refine ⟨hlvlF, ?_, ?_, ?_⟩
  · -- the bijection
    refine ⟨fun w hw => ?_, fun w₁ hw₁ w₂ hw₂ h => ?_, fun y hy => ?_⟩
    · show Y.lvl (F w) ≤ r + 1
      rw [hlvlF w hw]; exact hw
    · have hw₁' : X.lvl w₁ ≤ r + 1 := hw₁
      have hw₂' : X.lvl w₂ ≤ r + 1 := hw₂
      by_cases h1 : X.lvl w₁ ≤ r
      · by_cases h2 : X.lvl w₂ ≤ r
        · rw [hle w₁ h1, hle w₂ h2] at h
          exact a.injective (hτ.bij.injOn (hball _ h1) (hball _ h2) h)
        · exfalso
          have e1 := hlvlF w₁ hw₁'
          have e2 := hlvlF w₂ hw₂'
          rw [h] at e1
          omega
      · by_cases h2 : X.lvl w₂ ≤ r
        · exfalso
          have e1 := hlvlF w₁ hw₁'
          have e2 := hlvlF w₂ hw₂'
          rw [h] at e1
          omega
        · exact hinjS w₁ w₂ (by omega) (by omega) h
    · have hy' : Y.lvl y ≤ r + 1 := hy
      by_cases hyr : Y.lvl y ≤ r
      · obtain ⟨x, hx, hxy⟩ := hτ.bij.surjOn hyr
        have hx' : X.lvl x ≤ r := hx
        refine ⟨a⁻¹ x, ?_, ?_⟩
        · show X.lvl (a⁻¹ x) ≤ r + 1
          have := ha_lvl (a⁻¹ x)
          rw [apply_inv_self] at this
          omega
        · show F (a⁻¹ x) = y
          have hax : X.lvl (a⁻¹ x) ≤ r := by
            have := ha_lvl (a⁻¹ x)
            rw [apply_inv_self] at this
            omega
          rw [hle _ hax, apply_inv_self, hxy]
      · have hyl : Y.lvl y = r + 1 := by omega
        have hnz : Y.lvl y ≠ 0 := by omega
        obtain ⟨y', hy'adj, hy'l⟩ := Y.up y hnz
        have hy'r : Y.lvl y' ≤ r := by omega
        obtain ⟨z, hz, hzy⟩ := hτ.bij.surjOn hy'r
        have hz' : X.lvl z ≤ r := hz
        have hlz : X.lvl z = r := by
          have := hτ.lvl_eq z hz'
          rw [hzy] at this
          omega
        have hl : X.lvl (a⁻¹ z) = r := by
          have := ha_lvl (a⁻¹ z)
          rw [apply_inv_self] at this
          omega
        have hazy : τ (a (a⁻¹ z)) = y' := by rw [apply_inv_self, hzy]
        obtain ⟨i', hi'⟩ := Y.nb_all y' y hy'adj hy'l
        have hsi : s (a⁻¹ z) ((s (a⁻¹ z))⁻¹ i') = i' := by simp
        have h2 : Y.nb (τ (a (a⁻¹ z))) (s (a⁻¹ z) ((s (a⁻¹ z))⁻¹ i')) = some y := by
          rw [hsi, hazy]; exact hi'
        obtain ⟨w, hw⟩ := hS.occ_of_image _ _ _ hl h2
        have h3 := hslot _ _ w hl hw
        rw [h2] at h3
        obtain ⟨-, hlw⟩ := X.nb_down _ _ w hw
        refine ⟨w, ?_, (Option.some.inj h3).symm⟩
        show X.lvl w ≤ r + 1
        omega
  · -- the roots
    intro w hw
    have hw0 : X.lvl w ≤ r := by omega
    rw [hle w hw0, ha_root w hw, hτ.root w hw]
  · -- adjacency
    intro u v hu hv
    by_cases h1 : X.lvl u ≤ r
    · by_cases h2 : X.lvl v ≤ r
      · rw [hle u h1, hle v h2]
        rw [ha_adj u v h1 h2]
        exact hτ.adj _ _ (hball u h1) (hball v h2)
      · have hvl : X.lvl v = r + 1 := by omega
        by_cases hur : X.lvl u = r
        · exact hadj u v hur hvl
        · have huv : ¬ X.G.Adj u v := fun h => by
            have := X.adj_le u v h
            omega
          have huv' : ¬ Y.G.Adj (F u) (F v) := fun h => by
            have := Y.adj_le _ _ h
            rw [hlvlF u (by omega), hlvlF v hv] at this
            omega
          exact ⟨fun h => absurd h huv, fun h => absurd h huv'⟩
    · have hul : X.lvl u = r + 1 := by omega
      by_cases h2 : X.lvl v ≤ r
      · rw [SimpleGraph.adj_comm, SimpleGraph.adj_comm (Y.G)]
        by_cases hvr : X.lvl v = r
        · exact hadj v u hvr hul
        · have huv : ¬ X.G.Adj v u := fun h => by
            have := X.adj_le v u h
            omega
          have huv' : ¬ Y.G.Adj (F v) (F u) := fun h => by
            have := Y.adj_le _ _ h
            rw [hlvlF v (by omega), hlvlF u hu] at this
            omega
          exact ⟨fun h => absurd h huv, fun h => absurd h huv'⟩
      · have hvl : X.lvl v = r + 1 := by omega
        have hnzu : X.lvl u ≠ 0 := by omega
        have hnzv : X.lvl v ≠ 0 := by omega
        obtain ⟨hpu, hplu⟩ := X.upSlot_spec u hnzu
        obtain ⟨hpv, hplv⟩ := X.upSlot_spec v hnzv
        have hC := hS.C2 (X.upSlot u hnzu).1 (X.upSlot u hnzu).2 (X.upSlot v hnzv).1
          (X.upSlot v hnzv).2 (by omega) (by omega)
        rw [hS.slot_upSlot u hul, hS.slot_upSlot v hvl, hpu, hpv] at hC
        rw [adj_iff_pv, adj_iff_pv]
        rw [hC]

end Sound

/-! ### Completeness of a step -/

/-- A permutation of the slots realizing a bijection of the occupants. -/
theorem exists_slotPerm {α β : Type} (p : Fin q → Option α) (p' : Fin q → Option β) (g : α → β)
    (hgo : ∀ i w, p i = some w → ∃ j, p' j = some (g w))
    (hginj : ∀ i j w w', p i = some w → p j = some w' → g w = g w' → i = j)
    (hsurj : ∀ j z, p' j = some z → ∃ i w, p i = some w ∧ g w = z)
    (hp'inj : ∀ i j z, p' i = some z → p' j = some z → i = j) :
    ∃ σ : Perm (Fin q), (∀ i w, p i = some w → p' (σ i) = some (g w)) ∧
      ∀ i, p i = none → p' (σ i) = none := by
  classical
  have hpsome : ∀ i : {i // (p i).isSome = true}, ∃ w, p i.1 = some w := fun i =>
    Option.isSome_iff_exists.1 i.2
  have hf : ∀ i : {i // (p i).isSome = true}, ∃ j : {j // (p' j).isSome = true},
      ∀ w, p i.1 = some w → p' j.1 = some (g w) := by
    intro i
    obtain ⟨w, hw⟩ := hpsome i
    obtain ⟨j, hj⟩ := hgo _ _ hw
    refine ⟨⟨j, by rw [hj]; rfl⟩, fun w' hw' => ?_⟩
    rw [hw] at hw'
    rw [hj, Option.some.inj hw']
  choose f hfs using hf
  have hfinj : Function.Injective f := by
    intro i i' h
    obtain ⟨w, hw⟩ := hpsome i
    obtain ⟨w', hw'⟩ := hpsome i'
    have e1 := hfs i w hw
    have e2 := hfs i' w' hw'
    rw [h, e2] at e1
    have hgw : g w = g w' := (Option.some.inj e1).symm
    exact Subtype.ext (hginj _ _ _ _ hw hw' hgw)
  have hfsurj : Function.Surjective f := by
    intro j
    obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 j.2
    obtain ⟨i, w, hi, rfl⟩ := hsurj _ _ hz
    refine ⟨⟨i, by rw [hi]; rfl⟩, ?_⟩
    have e1 := hfs ⟨i, by rw [hi]; rfl⟩ w hi
    apply Subtype.ext
    exact hp'inj _ _ _ e1 hz
  let e := Equiv.ofBijective f ⟨hfinj, hfsurj⟩
  refine ⟨e.extendSubtype, fun i w hw => ?_, fun i hi => ?_⟩
  · rw [e.extendSubtype_apply_of_mem i (by rw [hw]; rfl)]
    exact hfs ⟨i, by rw [hw]; rfl⟩ w hw
  · by_contra hne
    obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 hne
    obtain ⟨i', w, hi', rfl⟩ := hsurj _ _ hz
    have e1 : p' (e.extendSubtype i') = some (g w) := by
      rw [e.extendSubtype_apply_of_mem i' (by rw [hi']; rfl)]
      exact hfs ⟨i', by rw [hi']; rfl⟩ w hi'
    have hii : e.extendSubtype i' = e.extendSubtype i := hp'inj _ _ _ e1 hz
    have := e.extendSubtype.injective hii
    subst this
    rw [hi] at hi'
    simp at hi'

theorem pv_some_congr {Z : LG V q} {Z' : LG W q} {a b : V} {a' b' : W} (he : a = b ↔ a' = b')
    (hadj : Z.G.Adj a b ↔ Z'.G.Adj a' b') :
    pv Z' (some a') (some b') = pv Z (some a) (some b) := by
  rw [pv_some_some, pv_some_some]
  by_cases h : a = b
  · simp [h, he.1 h]
  · have h' : ¬ a' = b' := fun h' => h (he.2 h')
    simp only [h, h', if_false, hadj]

section Complete

variable [Finite V] {X : LG V q} {Y : LG W q} {f₀ : V → W} {τ : V → W} {r : ℕ} {f : V → W}

/-- **Completeness of a step.** Every isomorphism of the next ball extends an element of the
current coset, and is read off an element of the answer. -/
theorem extf_surj (hτ : IsIso X Y f₀ r τ) (hf : IsIso X Y f₀ (r + 1) f) :
    ∃ (a : Perm V) (s : V → Perm (Fin q)), StepHyp X Y f₀ τ r a s ∧
      ∀ w, X.lvl w ≤ r + 1 → extf X Y τ r (act a s) w = f w := by
  obtain ⟨a, ha, haτ⟩ := hτ.exists_aut (hf.mono (Nat.le_succ r))
  obtain ⟨ha_out, ha_root, ha_lvl, ha_adj⟩ := LG.mem_aut.1 ha
  have hlvl_f : ∀ w, X.lvl w ≤ r + 1 → Y.lvl (f w) = X.lvl w := hf.lvl_eq
  have hs : ∀ l, X.lvl l = r → ∃ σ : Perm (Fin q),
      (∀ i w, X.nb l i = some w → Y.nb (τ (a l)) (σ i) = some (f w)) ∧
        ∀ i, X.nb l i = none → Y.nb (τ (a l)) (σ i) = none := by
    intro l hl
    have hfl : f l = τ (a l) := (haτ l (by omega)).symm
    refine exists_slotPerm (X.nb l) (Y.nb (τ (a l))) f ?_ ?_ ?_ ?_
    · intro i w hw
      obtain ⟨hadj, hlw⟩ := X.nb_down l i w hw
      rw [← hfl]
      refine Y.nb_all (f l) (f w) ((hf.adj l w (by omega) (by omega)).1 hadj) ?_
      rw [hlvl_f l (by omega), hlvl_f w (by omega), hlw]
    · intro i j w w' hw hw' hww
      obtain ⟨-, h1⟩ := X.nb_down l i w hw
      obtain ⟨-, h2⟩ := X.nb_down l j w' hw'
      have : w = w' := hf.bij.injOn (show X.lvl w ≤ r + 1 by omega)
        (show X.lvl w' ≤ r + 1 by omega) hww
      subst this
      exact X.nb_inj l i j w hw hw'
    · intro j z hz
      obtain ⟨hadj, hlz⟩ := Y.nb_down _ _ _ hz
      have hlv : Y.lvl (τ (a l)) = r := by rw [← hfl, hlvl_f _ (by omega)]; exact hl
      have hz' : Y.lvl z ≤ r + 1 := by omega
      obtain ⟨w, hw, hwz⟩ := hf.bij.surjOn hz'
      have hw' : X.lvl w ≤ r + 1 := hw
      have hlw : X.lvl w = r + 1 := by
        have := hlvl_f w hw'
        rw [hwz] at this
        omega
      have hadj' : X.G.Adj l w := by
        rw [hf.adj l w (by omega) hw', hwz, hfl]
        exact hadj
      obtain ⟨i, hi⟩ := X.nb_all l w hadj' (by omega)
      exact ⟨i, w, hi, hwz⟩
    · intro i j z h1 h2
      exact Y.nb_inj _ i j z h1 h2
  let s : V → Perm (Fin q) := fun l => if hl : X.lvl l = r then (hs l hl).choose else 1
  have hs1 : ∀ l, X.lvl l = r → ∀ i w, X.nb l i = some w → Y.nb (τ (a l)) (s l i) = some (f w) := by
    intro l hl i w hw
    have : s l = (hs l hl).choose := dif_pos hl
    rw [this]
    exact (hs l hl).choose_spec.1 i w hw
  have hs2 : ∀ l, X.lvl l = r → ∀ i, X.nb l i = none → Y.nb (τ (a l)) (s l i) = none := by
    intro l hl i hi
    have : s l = (hs l hl).choose := dif_pos hl
    rw [this]
    exact (hs l hl).choose_spec.2 i hi
  refine ⟨a, s, ⟨hτ, ha, ?_⟩, ?_⟩
  · intro ω
    rcases ω with v | ⟨l, i⟩ | ⟨⟨l, i⟩, ⟨l', i'⟩⟩
    · rfl
    · rw [act_slot, str_slot, str_slot]
      simp only [ha_lvl, id]
      by_cases hl : X.lvl l = r
      · simp only [hl, if_true]
        cases hx : X.nb l i with
        | none => rw [hs2 l hl i hx]; rfl
        | some w => rw [hs1 l hl i w hx]; simp
      · simp only [hl, if_false]
    · rw [act_pair, str_pair, str_pair]
      simp only [ha_lvl, id]
      by_cases hl : X.lvl l = r ∧ X.lvl l' = r
      · obtain ⟨h1, h2⟩ := hl
        simp only [h1, h2, if_true, and_self]
        cases hx : X.nb l i with
        | none => rw [hs2 l h1 i hx]; simp
        | some w =>
          cases hx' : X.nb l' i' with
          | none => rw [hs2 l' h2 i' hx']; simp
          | some w' =>
            rw [hs1 l h1 i w hx, hs1 l' h2 i' w' hx']
            obtain ⟨-, h3⟩ := X.nb_down l i w hx
            obtain ⟨-, h4⟩ := X.nb_down l' i' w' hx'
            refine pv_some_congr ?_ ?_
            · constructor
              · rintro rfl; rfl
              · intro e
                exact hf.bij.injOn (show X.lvl w ≤ r + 1 by omega) (show X.lvl w' ≤ r + 1 by omega) e
            · exact hf.adj w w' (by omega) (by omega)
      · rw [if_neg hl, if_neg hl]
  · intro w hw
    by_cases h : X.lvl w ≤ r
    · rw [extf_of_le w _ h, hV_act, haτ w h]
    · have hw' : X.lvl w = r + 1 := by omega
      have hnz : X.lvl w ≠ 0 := by omega
      obtain ⟨hp, hplvl⟩ := X.upSlot_spec w hnz
      rw [extf_of_succ w _ hw', hSl_act]
      simp only
      rw [hs1 _ (by omega) _ _ hp, Option.getD_some]

end Complete

/-! ### The instance -/

/-- **The string-isomorphism instance of one layer of the reduction**: the group `S_q ≀_V A`, on
`V ⊔ Sl ⊔ Sl²`, the strings `str X X id r` and `str X Y τ r`, a fresh call. -/
noncomputable def layerState (X : LG V q) (Y : LG W q) (A : Subgroup (Perm V)) (τ : V → W)
    (r : ℕ) : State (Om V q) ℕ :=
  ⟨wreath A, Set.univ, fun _ _ _ => Iff.rfl, str X X id r, str X Y τ r, [], none, false, 2,
    le_rfl, Nat.card (Om V q), CounterInv.reset _ _ _ _, CarrierOK.none _ _ _⟩

theorem mem_layerState_answer {X : LG V q} {Y : LG W q} {A : Subgroup (Perm V)} {τ : V → W}
    {r : ℕ} {g : Perm (Om V q)} :
    g ∈ (layerState X Y A τ r).answer ↔ ∃ a ∈ A, ∃ s : V → Perm (Fin q), g = act a s ∧
      ∀ ω, str X Y τ r (act a s ω) = str X X id r ω := by
  constructor
  · rintro ⟨⟨a, ha, s, rfl⟩, h⟩
    exact ⟨a, ha, s, rfl, fun ω => h ω trivial⟩
  · rintro ⟨a, ha, s, rfl, h⟩
    exact ⟨⟨a, ha, s, rfl⟩, fun ω _ => h ω⟩

/-! ### Reading the next level from the answer -/

/-- **Reading the next coset off the answer**: a chosen element of the answer gives `τ'`, and
`A'` is generated by the permutations `b` fixing the outside of the next ball such that
`τ' ∘ b` is induced by some element of the answer. -/
noncomputable def readStep (X : LG V q) (Y : LG W q) (r : ℕ) (τ : V → W)
    (ans : Set (Perm (Om V q))) : Option (Subgroup (Perm V) × (V → W)) :=
  if h : ans.Nonempty then
    some (Subgroup.closure {b | (∀ w, r + 1 < X.lvl w → b w = w) ∧ ∃ g ∈ ans, ∀ w,
        X.lvl w ≤ r + 1 → extf X Y τ r g w = extf X Y τ r h.some (b w)},
      extf X Y τ r h.some)
  else none

section Read

variable [Finite V] {X : LG V q} {Y : LG W q} {f₀ : V → W} {τ : V → W} {r : ℕ}

/-- An element of the answer gives a step's hypotheses. -/
theorem stepHyp_of_mem (hτ : IsIso X Y f₀ r τ) {g : Perm (Om V q)}
    (hg : g ∈ (layerState X Y (X.aut r) τ r).answer) :
    ∃ a s, g = act a s ∧ StepHyp X Y f₀ τ r a s := by
  obtain ⟨a, ha, s, rfl, h⟩ := mem_layerState_answer.1 hg
  exact ⟨a, s, rfl, hτ, ha, h⟩

/-- An element of the answer induces an isomorphism of the next ball. -/
theorem extf_mem_answer (hτ : IsIso X Y f₀ r τ) {g : Perm (Om V q)}
    (hg : g ∈ (layerState X Y (X.aut r) τ r).answer) : IsIso X Y f₀ (r + 1) (extf X Y τ r g) := by
  obtain ⟨a, s, rfl, h⟩ := stepHyp_of_mem hτ hg
  exact extf_isIso h

/-- **The exact correspondence of one layer**, if the next ball has no isomorphism. -/
theorem readStep_none (hτ : IsIso X Y f₀ r τ)
    (h : readStep X Y r τ (layerState X Y (X.aut r) τ r).answer = none) :
    ¬ ∃ f, IsIso X Y f₀ (r + 1) f := by
  rintro ⟨f, hf⟩
  obtain ⟨a, s, hS, -⟩ := extf_surj hτ hf
  unfold readStep at h
  split_ifs at h with hne
  exact hne ⟨act a s, mem_layerState_answer.2 ⟨a, hS.ha, s, rfl, hS.hans⟩⟩

/-- **The exact correspondence of one layer**, with the next coset. -/
theorem readStep_some (hτ : IsIso X Y f₀ r τ) {A' : Subgroup (Perm V)} {τ' : V → W}
    (h : readStep X Y r τ (layerState X Y (X.aut r) τ r).answer = some (A', τ')) :
    A' = X.aut (r + 1) ∧ IsIso X Y f₀ (r + 1) τ' := by
  set ans := (layerState X Y (X.aut r) τ r).answer with hans
  unfold readStep at h
  split_ifs at h with hne
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hτ' : IsIso X Y f₀ (r + 1) (extf X Y τ r hne.some) := extf_mem_answer hτ hne.some_mem
  refine ⟨?_, hτ'⟩
  refine Subgroup.closure_eq_of_le _ ?_ ?_
  · rintro b ⟨hout, g, hg, hb⟩
    exact hτ'.mem_aut (extf_mem_answer hτ hg) hout hb
  · intro b hb
    obtain ⟨h1, h2, h3, h4⟩ := LG.mem_aut.1 hb
    have hcomp := hτ'.comp_aut hb
    obtain ⟨a, s, hS, hext⟩ := extf_surj hτ hcomp
    refine Subgroup.subset_closure ⟨h1, act a s, mem_layerState_answer.2 ⟨a, hS.ha, s, rfl, hS.hans⟩,
      fun w hw => ?_⟩
    exact hext w hw

end Read

/-! ### `Aut` in the class -/

section Class

variable [Finite V] (X : LG V q)

/-- The restriction of an automorphism of the next ball to the ball, extended by the identity. -/
noncomputable def LG.restrictFun (X : LG V q) (r : ℕ) (a : X.aut (r + 1)) : X.aut r :=
  ⟨Equiv.Perm.ofSubtype ((a : Perm V).subtypePerm (p := fun w => X.lvl w ≤ r) (fun w => by
      show X.lvl ((a : Perm V) w) ≤ r ↔ X.lvl w ≤ r
      rw [(LG.mem_aut.1 a.2).2.2.1])), by
    have ha := LG.mem_aut.1 a.2
    refine ⟨fun w hw => ?_, fun w hw => ?_, fun w => ?_, fun u v hu hv => ?_⟩
    · exact Equiv.Perm.ofSubtype_apply_of_not_mem _ (by simp; omega)
    · rw [Equiv.Perm.ofSubtype_apply_of_mem _ (by simp; omega)]
      exact ha.2.1 w hw
    · by_cases hw : X.lvl w ≤ r
      · rw [Equiv.Perm.ofSubtype_apply_of_mem _ (by simp [hw])]
        exact ha.2.2.1 w
      · rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ (by simpa using hw)]
    · rw [Equiv.Perm.ofSubtype_apply_of_mem _ (by simp [hu]),
        Equiv.Perm.ofSubtype_apply_of_mem _ (by simp [hv])]
      exact ha.2.2.2 u v (by omega) (by omega)⟩

omit [Finite V] in
theorem LG.restrictFun_apply_of_le (X : LG V q) {r : ℕ} (a : X.aut (r + 1)) {w : V}
    (hw : X.lvl w ≤ r) : (X.restrictFun r a : Perm V) w = (a : Perm V) w := by
  simp only [LG.restrictFun]
  rw [Equiv.Perm.ofSubtype_apply_of_mem _ (by simp [hw])]
  rfl

omit [Finite V] in
theorem LG.restrictFun_apply_of_not_le (X : LG V q) {r : ℕ} (a : X.aut (r + 1)) {w : V}
    (hw : ¬ X.lvl w ≤ r) : (X.restrictFun r a : Perm V) w = w := by
  simp only [LG.restrictFun]
  rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ (by simpa using hw)]

/-- The restriction homomorphism `aut (r + 1) → aut r`. -/
noncomputable def LG.restrictHom (X : LG V q) (r : ℕ) : X.aut (r + 1) →* X.aut r where
  toFun := X.restrictFun r
  map_one' := by
    apply Subtype.ext
    ext w
    by_cases hw : X.lvl w ≤ r
    · rw [X.restrictFun_apply_of_le _ hw]; rfl
    · simp only [LG.restrictFun]
      rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ (by simpa using hw)]
      rfl
  map_mul' a b := by
    apply Subtype.ext
    ext w
    rw [Subgroup.coe_mul, Perm.mul_apply]
    by_cases hw : X.lvl w ≤ r
    · have hb := (LG.mem_aut.1 b.2).2.2.1 w
      rw [X.restrictFun_apply_of_le _ hw, X.restrictFun_apply_of_le _ hw,
        X.restrictFun_apply_of_le _ (show X.lvl ((b : Perm V) w) ≤ r by rw [hb]; exact hw)]
      rfl
    · rw [X.restrictFun_apply_of_not_le _ hw, X.restrictFun_apply_of_not_le _ hw,
        X.restrictFun_apply_of_not_le _ hw]

/-- The down-neighbours of `l`, when `l` is at level `r`. -/
def LG.Down (X : LG V q) (r : ℕ) (l : V) : Type :=
  {w : V // X.lvl l = r ∧ X.G.Adj l w ∧ X.lvl w = X.lvl l + 1}

instance (X : LG V q) (r : ℕ) (l : V) : Finite (X.Down r l) := by
  unfold LG.Down; infer_instance

theorem LG.card_down_le (X : LG V q) (r : ℕ) (l : V) : Nat.card (X.Down r l) ≤ q := by
  have hslot : ∀ d : X.Down r l, ∃ i, X.nb l i = some d.1 := fun d =>
    X.nb_all l d.1 d.2.2.1 d.2.2.2
  choose f hf using hslot
  have hinj : Function.Injective f := by
    intro d d' h
    apply Subtype.ext
    have e := hf d
    rw [h, hf d'] at e
    exact (Option.some.inj e).symm
  calc Nat.card (X.Down r l) ≤ Nat.card (Fin q) := Nat.card_le_card_of_injective f hinj
    _ = q := by simp

/-- Kernel of the restriction: elements of `aut (r + 1)` fixing the ball of radius `r`. -/
theorem LG.ker_iff {X : LG V q} {r : ℕ} {a : X.aut (r + 1)} :
    a ∈ (X.restrictHom r).ker ↔ ∀ w, X.lvl w ≤ r → (a : Perm V) w = w := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h w hw
    have := congrArg (fun z : X.aut r => (z : Perm V) w) h
    simp only [show (X.restrictHom r) a = X.restrictFun r a from rfl,
      X.restrictFun_apply_of_le _ hw] at this
    exact this
  · intro h
    apply Subtype.ext
    ext w
    show ((X.restrictFun r a : Perm V) w) = w
    by_cases hw : X.lvl w ≤ r
    · rw [X.restrictFun_apply_of_le _ hw]; exact h w hw
    · simp only [LG.restrictFun]
      rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ (by simpa using hw)]

/-- `aut (r + 1)` acts on the down-neighbours of `l`. -/
theorem LG.down_stable (X : LG V q) {r : ℕ} {a : X.aut (r + 1)}
    (ha : a ∈ (X.restrictHom r).ker) (l w : V) :
    (X.lvl l = r ∧ X.G.Adj l ((a : Perm V) w) ∧ X.lvl ((a : Perm V) w) = X.lvl l + 1) ↔
      (X.lvl l = r ∧ X.G.Adj l w ∧ X.lvl w = X.lvl l + 1) := by
  have hfix := LG.ker_iff.1 ha
  obtain ⟨h1, h2, h3, h4⟩ := LG.mem_aut.1 a.2
  constructor
  · rintro ⟨hl, hadj, hlw⟩
    have hlw' : X.lvl w = X.lvl l + 1 := by rw [← h3 w]; exact hlw
    refine ⟨hl, ?_, hlw'⟩
    have := (h4 l w (by omega) (by omega)).2
    rw [hfix l (by omega)] at this
    exact this hadj
  · rintro ⟨hl, hadj, hlw⟩
    refine ⟨hl, ?_, by rw [h3 w]; exact hlw⟩
    have := (h4 l w (by omega) (by omega)).1 hadj
    rwa [hfix l (by omega)] at this

/-- **`Aut(X_r, roots) ∈ Γ̂_q`** (Luks). -/
theorem LG.gammaHat_aut (X : LG V q) (r : ℕ) : GammaHat q (X.aut r) := by
  induction r with
  | zero =>
    have hsub : Subsingleton (X.aut 0) := by
      refine ⟨fun a b => Subtype.ext ?_⟩
      ext w
      obtain ⟨h1, h2, -, -⟩ := LG.mem_aut.1 a.2
      obtain ⟨h1', h2', -, -⟩ := LG.mem_aut.1 b.2
      by_cases hw : X.lvl w = 0
      · rw [h2 w hw, h2' w hw]
      · rw [h1 w (by omega), h1' w (by omega)]
    exact GammaHat.trivial _
  | succ r ih =>
    refine gammaHat_of_hom (X.restrictHom r) ?_ (ih.subgroup _)
    have hpi : GammaHat q (∀ l : V, Perm (X.Down r l)) :=
      gammaHat_piDep V _ fun l => gammaHat_perm (MonoidHom.id _) Function.injective_id
        (X.card_down_le r l)
    let ψ : (X.restrictHom r).ker →* ∀ l : V, Perm (X.Down r l) :=
      { toFun := fun a l => ((a : X.aut (r + 1)) : Perm V).subtypePerm
          (p := fun w => X.lvl l = r ∧ X.G.Adj l w ∧ X.lvl w = X.lvl l + 1)
          (fun w => X.down_stable a.2 l w)
        map_one' := by ext l w; rfl
        map_mul' := fun a b => by ext l w; rfl }
    refine GammaHat.of_injective ψ ?_ hpi
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    ext w
    have ha1 := LG.ker_iff.1 a.2
    have hb1 := LG.ker_iff.1 b.2
    obtain ⟨h1, -, -, -⟩ := LG.mem_aut.1 a.1.2
    obtain ⟨h1', -, -, -⟩ := LG.mem_aut.1 b.1.2
    by_cases hw : X.lvl w ≤ r
    · rw [ha1 w hw, hb1 w hw]
    · by_cases hw2 : r + 1 < X.lvl w
      · rw [h1 w hw2, h1' w hw2]
      · have hlw : X.lvl w = r + 1 := by omega
        obtain ⟨y, hy, hl⟩ := X.up w (by omega)
        have hdown : X.lvl y = r ∧ X.G.Adj y w ∧ X.lvl w = X.lvl y + 1 := ⟨by omega, hy, hl⟩
        have := congrArg (fun z : ∀ l : V, Perm (X.Down r l) => ((z y ⟨w, hdown⟩ : X.Down r y)).1) hab
        exact this

end Class

end GI.DegreeD.Luks
