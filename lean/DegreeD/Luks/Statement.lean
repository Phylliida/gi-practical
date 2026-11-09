import DegreeD.Luks.Components

/-!
# GI of maximum degree `d`: the statement that means something

`graphIso_final` and its relatives (`DegreeD/Luks/Components.lean`, renamed `..._weak`) quantified
over a script `∃ s`, after `X` and `Y`, with `Script.done` allowed to carry any value built
classically. So `done {iso set}` satisfied them with `C = 0`. This file gives the reduction
statement.

* `Script.evalWith o`: the value of a script run against an **arbitrary** oracle `o` for its
  calls (`Oracle.exact` gives `evalExact`). `luksOff hX hY o` (`graphOff`, `compOff`, `anyOff`, `connOff`,
  `candOff`, `rootedOff`, `layerLoop`): the **explicit read-off**, the output as a closed term in the
  oracle's answers. `luksScript_evalWith` : `(luksScript hX hY).evalWith o = luksOff hX hY o`.
* `IsLuksReduction hX hY s`: for all oracles, `s` computes `luksOff` from the answers (`readOff`);
  every call that `s` can make, on any branch, is a layer instance `layerState` of connected
  components of `X, Y` (`layered`); along the exact answers its calls are in `Γ̂_d`, of size
  at most `3 n⁴` (`calls`); and its exact value is the isomorphism set (`exact`).
* `not_isLuksReduction_done`, `not_isLuksReduction_useless`: the constant scripts fail the
  predicate, whenever `X ≅ Y`, `n ≥ 1`. In fact `luksOff` with all answers empty is `∅` (`luksOff_null`).
* `graphIso_reduction`: the theorem. No script is quantified: it is about the named `luksScript`.

**Residual weakness.** `Oracle` and `IsLuksReduction` pin down the input–output behaviour of a
script, not its computational cost: in Lean a `Script` (and `luksOff` itself) is a classical term.
The definitions `luksOff`, `layerState`, `readStep`, `extf`, `mkLG` are read, not checked. See
`docs/w43-lean-statement.md`.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm

/-- An **oracle** for the recursive calls of a script: for any state, in any mode, some set of
permutations. `Oracle.exact` is the true answer of each state; `Oracle.null` answers `∅`. -/
abbrev Oracle : Type 1 := ∀ (Ω C : Type), Mode → State Ω C → Set (Perm Ω)

namespace Oracle

/-- The exact answers. -/
def exact : Oracle := fun _ _ _ S => S.answer

/-- Every answer is empty. -/
def null : Oracle := fun _ _ _ _ => ∅

end Oracle

namespace Script

variable {α β : Type}

/-- The result of a script when each call is answered by the oracle `o`. -/
def evalWith (o : Oracle) : Script α → α
  | done a => a
  | ask m S k => (k (o _ _ m S)).evalWith o

@[simp] theorem evalWith_done (o : Oracle) (a : α) : (done a : Script α).evalWith o = a := rfl

@[simp] theorem evalWith_ask (o : Oracle) {Ω C : Type} (m : Mode) (S : State Ω C)
    (k : Set (Perm Ω) → Script α) : (ask m S k).evalWith o = (k (o _ _ m S)).evalWith o := rfl

theorem evalWith_exact (s : Script α) : s.evalWith Oracle.exact = s.evalExact := by
  induction s with
  | done a => rfl
  | ask m S k ih => exact ih _

theorem evalWith_bind (o : Oracle) (s : Script α) (f : α → Script β) :
    (s.bind f).evalWith o = (f (s.evalWith o)).evalWith o := by
  induction s with
  | done a => rfl
  | ask m S k ih => exact ih _

theorem evalWith_seqList (o : Oracle) (l : List (Script α)) :
    (seqList l).evalWith o = l.map (evalWith o) := by
  induction l with
  | nil => rfl
  | cons s ss ih =>
    simp only [seqList, evalWith_bind, List.map_cons]
    rw [ih]
    rfl

/-- Every call the script can make, on **any** branch of answers, satisfies `p`. -/
def AllCalls (p : ∀ {Ω' C' : Type}, Mode → State Ω' C' → Prop) : Script α → Prop
  | done _ => True
  | ask m S k => p m S ∧ ∀ A, (k A).AllCalls p

theorem AllCalls.mono {p q : ∀ {Ω' C' : Type}, Mode → State Ω' C' → Prop}
    (h : ∀ {Ω' C' : Type} (m : Mode) (T : State Ω' C'), p m T → q m T) :
    ∀ {s : Script α}, s.AllCalls p → s.AllCalls q
  | done _, _ => trivial
  | ask _ _ _, hs => ⟨h _ _ hs.1, fun A => AllCalls.mono h (hs.2 A)⟩

theorem AllCalls.bind {p : ∀ {Ω' C' : Type}, Mode → State Ω' C' → Prop} {s : Script α}
    {f : α → Script β} (hs : s.AllCalls p) (hf : ∀ a, (f a).AllCalls p) :
    (s.bind f).AllCalls p := by
  induction s with
  | done a => exact hf a
  | ask m S k ih => exact ⟨hs.1, fun A => ih A (hs.2 A)⟩

theorem AllCalls.seqList {p : ∀ {Ω' C' : Type}, Mode → State Ω' C' → Prop} :
    ∀ {l : List (Script α)}, (∀ s ∈ l, s.AllCalls p) → (Script.seqList l).AllCalls p
  | [], _ => trivial
  | s :: ss, h =>
    AllCalls.bind (h s (by simp)) fun _ =>
      AllCalls.bind (AllCalls.seqList fun t ht => h t (by simp [ht])) fun _ => trivial

end Script

end GI.Algorithm

namespace GI.DegreeD.Luks

open Equiv Equiv.Perm GI.Algorithm SimpleGraph
open scoped Classical

set_option linter.unusedSectionVars false

/-! ### The explicit read-off -/

section ReadOff

variable {V W : Type} [Fintype V] [Fintype W] {q R : ℕ}

/-- **The layer loop**: the data flow of `layersScript`, with the answers given by the oracle.
At each level the state `(A, τ)` determines the question `layerState X Y A τ r`; the answer
determines the next state by `readStep`; an empty answer stops the loop. -/
noncomputable def layerLoop (o : Oracle) (X : LG V q) (Y : LG W q) :
    ℕ → ℕ → Subgroup (Perm V) → (V → W) → Option (Subgroup (Perm V) × (V → W))
  | 0, _, A, τ => some (A, τ)
  | f + 1, r, A, τ =>
      (readStep X Y r τ (o _ _ .solve (layerState X Y A τ r))).bind fun d' =>
        layerLoop o X Y f (r + 1) d'.1 d'.2

theorem layersScript_evalWith (o : Oracle) (X : LG V q) (Y : LG W q) (f : ℕ) :
    ∀ (r : ℕ) (A : Subgroup (Perm V)) (τ : V → W),
      (layersScript X Y f r A τ).evalWith o = layerLoop o X Y f r A τ := by
  induction f with
  | zero => intro r A τ; rfl
  | succ f ih =>
    intro r A τ
    show (match readStep X Y r τ (o _ _ .solve (layerState X Y A τ r)) with
      | none => Script.done none
      | some d' => layersScript X Y f (r + 1) d'.1 d'.2).evalWith o =
      (readStep X Y r τ (o _ _ .solve (layerState X Y A τ r))).bind fun d' =>
        layerLoop o X Y f (r + 1) d'.1 d'.2
    rcases readStep X Y r τ (o _ _ .solve (layerState X Y A τ r)) with _ | d'
    · rfl
    · exact ih (r + 1) d'.1 d'.2

/-- The read-off of the rooted script: from the layer loop started at `(⊥, f₀)`, the maps
`τ ∘ a`, `a ∈ A`. -/
noncomputable def rootedOff (o : Oracle) (X : LG V q) (Y : LG W q) (f₀ : V → W) (R : ℕ) :
    Set (V → W) :=
  match layerLoop o X Y R 0 ⊥ f₀ with
  | none => ∅
  | some d => {f | ∃ a ∈ d.1, f = fun w => d.2 (a w)}

theorem rootedScript_evalWith (o : Oracle) (X : LG V q) (Y : LG W q) (f₀ : V → W) (R : ℕ) :
    (rootedScript X Y f₀ R).evalWith o = rootedOff o X Y f₀ R := by
  unfold rootedScript rootedOff
  rw [Script.evalWith_bind, layersScript_evalWith]
  rfl

variable {X : SimpleGraph V} {Y : SimpleGraph W}

/-- The read-off of one candidate image `p` of the root. -/
noncomputable def candOff (o : Oracle) (hX : X.Connected) (hY : Y.Connected)
    (hXd : ∀ l, Nat.card (X.neighborSet l) ≤ q) (hYd : ∀ l, Nat.card (Y.neighborSet l) ≤ q)
    (u v : V) (R : ℕ) (p : W × W) : Set (V → W) :=
  if _h : RootImg Y u v p then
    rootedOff o (mkLG X hX u v q hXd) (mkLG Y hY p.1 p.2 q hYd) (f₀ u p) R
  else ∅

theorem candScript_evalWith (o : Oracle) (hX : X.Connected) (hY : Y.Connected)
    (hXd : ∀ l, Nat.card (X.neighborSet l) ≤ q) (hYd : ∀ l, Nat.card (Y.neighborSet l) ≤ q)
    (u v : V) (R : ℕ) (p : W × W) :
    (candScript hX hY hXd hYd u v R p).evalWith o = candOff o hX hY hXd hYd u v R p := by
  unfold candScript candOff
  split_ifs
  · exact rootedScript_evalWith o _ _ _ _
  · rfl

/-- The read-off of the connected reduction: the union over the candidate images. -/
noncomputable def connOff (o : Oracle) (hX : X.Connected) (hY : Y.Connected)
    (hXd : ∀ l, Nat.card (X.neighborSet l) ≤ q) (hYd : ∀ l, Nat.card (Y.neighborSet l) ≤ q)
    (u v : V) (R : ℕ) : Set (V → W) :=
  ⋃ p : W × W, candOff o hX hY hXd hYd u v R p

theorem connScript_evalWith (o : Oracle) (hX : X.Connected) (hY : Y.Connected)
    (hXd : ∀ l, Nat.card (X.neighborSet l) ≤ q) (hYd : ∀ l, Nat.card (Y.neighborSet l) ≤ q)
    (u v : V) (R : ℕ) :
    (connScript hX hY hXd hYd u v R).evalWith o = connOff o hX hY hXd hYd u v R := by
  unfold connScript connOff
  rw [Script.evalWith_bind, Script.evalWith_seqList]
  ext f
  simp only [Script.evalWith_done, Set.mem_iUnion, exists_prop, List.mem_map, Finset.mem_toList,
    Finset.mem_univ, true_and, List.map_map, Function.comp]
  constructor
  · rintro ⟨s, ⟨p, rfl⟩, hs⟩
    rw [candScript_evalWith] at hs
    exact ⟨p, hs⟩
  · rintro ⟨p, hp⟩
    refine ⟨_, ⟨p, rfl⟩, ?_⟩
    rw [candScript_evalWith]
    exact hp

/-- The read-off of the connected reduction of a pair of connected graphs, on all branches: root
at an edge of `X`, or at a vertex when `X` has no edge. -/
noncomputable def anyOff (o : Oracle) (hX : X.Connected) (hY : Y.Connected)
    (hXd : ∀ l, Nat.card (X.neighborSet l) ≤ q) (hYd : ∀ l, Nat.card (Y.neighborSet l) ≤ q)
    (R : ℕ) : Set (V → W) :=
  if h : ∃ u v, X.Adj u v then connOff o hX hY hXd hYd h.choose h.choose_spec.choose R
  else connOff o hX hY hXd hYd hX.nonempty.some hX.nonempty.some R

theorem anyScript_evalWith (o : Oracle) (hX : X.Connected) (hY : Y.Connected)
    (hXd : ∀ l, Nat.card (X.neighborSet l) ≤ q) (hYd : ∀ l, Nat.card (Y.neighborSet l) ≤ q)
    (R : ℕ) : (anyScript hX hY hXd hYd R).evalWith o = anyOff o hX hY hXd hYd R := by
  unfold anyScript anyOff
  split_ifs <;> exact connScript_evalWith _ _ _ _ _ _ _ _

end ReadOff

section ReadOffGraph

variable {n q : ℕ} {X Y : SimpleGraph (Fin n)}

/-- The read-off of the pair `p` of a component of `X` and a component of `Y`: the lifted maps. -/
noncomputable def compOff (o : Oracle) (hXd : ∀ l, Nat.card (X.neighborSet l) ≤ q)
    (hYd : ∀ l, Nat.card (Y.neighborSet l) ≤ q)
    (p : X.ConnectedComponent × Y.ConnectedComponent) : Set (Fin n → Option (Fin n)) :=
  liftMap '' anyOff o p.1.connected_toSimpleGraph p.2.connected_toSimpleGraph
    (comp_deg_le hXd p.1) (comp_deg_le hYd p.2) n

theorem compScript_evalWith (o : Oracle) (hXd : ∀ l, Nat.card (X.neighborSet l) ≤ q)
    (hYd : ∀ l, Nat.card (Y.neighborSet l) ≤ q)
    (p : X.ConnectedComponent × Y.ConnectedComponent) :
    (compScript hXd hYd p).evalWith o = compOff o hXd hYd p := by
  unfold compScript compOff
  rw [Script.evalWith_bind, anyScript_evalWith]
  rfl

/-- **The explicit read-off of the graph reduction.** The set of `g` whose restriction to each
component of `X` is one of the lifted maps read off from the answers. -/
noncomputable def graphOff (o : Oracle) (hXd : ∀ l, Nat.card (X.neighborSet l) ≤ q)
    (hYd : ∀ l, Nat.card (Y.neighborSet l) ≤ q) : Set (Perm (Fin n)) :=
  {g | ∀ c : X.ConnectedComponent,
    ∃ p : X.ConnectedComponent × Y.ConnectedComponent, restr X g c ∈ compOff o hXd hYd p}

theorem graphScript_evalWith [Fintype X.ConnectedComponent] [Fintype Y.ConnectedComponent]
    (o : Oracle) (hXd : ∀ l, Nat.card (X.neighborSet l) ≤ q)
    (hYd : ∀ l, Nat.card (Y.neighborSet l) ≤ q) :
    (graphScript hXd hYd).evalWith o = graphOff o hXd hYd := by
  unfold graphScript graphOff
  rw [Script.evalWith_bind, Script.evalWith_seqList]
  ext g
  simp only [Script.evalWith_done, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop, List.mem_map,
    Finset.mem_toList, Finset.mem_univ, true_and, List.map_map, Function.comp]
  constructor
  · intro h c
    obtain ⟨S, ⟨p, rfl⟩, hS⟩ := h c
    rw [compScript_evalWith] at hS
    exact ⟨p, hS⟩
  · intro h c
    obtain ⟨p, hS⟩ := h c
    refine ⟨_, ⟨p, rfl⟩, ?_⟩
    rw [compScript_evalWith]
    exact hS

end ReadOffGraph

/-! ### With all answers empty, the output is empty -/

section Null

variable {V W : Type} [Fintype V] [Fintype W] {q R : ℕ}

theorem layerLoop_null_succ (X : LG V q) (Y : LG W q) (f r : ℕ) (A : Subgroup (Perm V))
    (τ : V → W) : layerLoop Oracle.null X Y (f + 1) r A τ = none := by
  have h : readStep X Y r τ (Oracle.null _ _ .solve (layerState X Y A τ r)) = none := by
    unfold readStep Oracle.null
    exact dif_neg (by simp)
  show (readStep X Y r τ (Oracle.null _ _ .solve (layerState X Y A τ r))).bind _ = none
  rw [h]
  rfl

theorem rootedOff_null (X : LG V q) (Y : LG W q) (f₀ : V → W) (hR : 1 ≤ R) :
    rootedOff Oracle.null X Y f₀ R = ∅ := by
  obtain ⟨f, rfl⟩ : ∃ f, R = f + 1 := ⟨R - 1, by omega⟩
  unfold rootedOff
  rw [layerLoop_null_succ]

variable {X : SimpleGraph V} {Y : SimpleGraph W}

theorem candOff_null (hX : X.Connected) (hY : Y.Connected)
    (hXd : ∀ l, Nat.card (X.neighborSet l) ≤ q) (hYd : ∀ l, Nat.card (Y.neighborSet l) ≤ q)
    (u v : V) (hR : 1 ≤ R) (p : W × W) :
    candOff Oracle.null hX hY hXd hYd u v R p = ∅ := by
  unfold candOff
  split_ifs
  · exact rootedOff_null _ _ _ hR
  · rfl

theorem connOff_null (hX : X.Connected) (hY : Y.Connected)
    (hXd : ∀ l, Nat.card (X.neighborSet l) ≤ q) (hYd : ∀ l, Nat.card (Y.neighborSet l) ≤ q)
    (u v : V) (hR : 1 ≤ R) : connOff Oracle.null hX hY hXd hYd u v R = ∅ := by
  unfold connOff
  rw [Set.iUnion_eq_empty]
  exact candOff_null hX hY hXd hYd u v hR

theorem anyOff_null (hX : X.Connected) (hY : Y.Connected)
    (hXd : ∀ l, Nat.card (X.neighborSet l) ≤ q) (hYd : ∀ l, Nat.card (Y.neighborSet l) ≤ q)
    (hR : 1 ≤ R) : anyOff Oracle.null hX hY hXd hYd R = ∅ := by
  unfold anyOff
  split_ifs <;> exact connOff_null _ _ _ _ _ _ hR

end Null

/-! ### The queries -/

section Queries

/-- A query of the connected reduction of `X, Y`: the layer instance `layerState` of the slot graphs
`mkLG` of `X, Y`, for some root, image of the root, level and coset data. -/
inductive LayerFrom {V W : Type} [Finite V] [Finite W] (X : SimpleGraph V) (Y : SimpleGraph W)
    (q : ℕ) : ∀ {Ω C : Type}, Mode → State Ω C → Prop
  | mk (hX : X.Connected) (hY : Y.Connected) (hXd : ∀ l, Nat.card (X.neighborSet l) ≤ q)
      (hYd : ∀ l, Nat.card (Y.neighborSet l) ≤ q) (u v : V) (p : W × W)
      (A : Subgroup (Perm V)) (τ : V → W) (r : ℕ) :
      LayerFrom X Y q .solve
        (layerState (mkLG X hX u v q hXd) (mkLG Y hY p.1 p.2 q hYd) A τ r)

/-- A query of the reduction of `X, Y`: the layer instance of a pair of connected components. -/
def LuksQuery {n : ℕ} (X Y : SimpleGraph (Fin n)) (q : ℕ) {Ω C : Type} (m : Mode)
    (T : State Ω C) : Prop :=
  ∃ (c : X.ConnectedComponent) (c' : Y.ConnectedComponent),
    LayerFrom c.toSimpleGraph c'.toSimpleGraph q m T

variable {V W : Type} [Fintype V] [Fintype W] {q R : ℕ}

theorem layersScript_allCalls {X : LG V q} {Y : LG W q}
    {p : ∀ {Ω' C' : Type}, Mode → State Ω' C' → Prop}
    (hp : ∀ A τ r, p .solve (layerState X Y A τ r)) (f : ℕ) :
    ∀ (r : ℕ) (A : Subgroup (Perm V)) (τ : V → W), (layersScript X Y f r A τ).AllCalls p := by
  induction f with
  | zero => intro r A τ; trivial
  | succ f ih =>
    intro r A τ
    refine ⟨hp A τ r, fun ans => ?_⟩
    show (match readStep X Y r τ ans with
      | none => Script.done none
      | some d' => layersScript X Y f (r + 1) d'.1 d'.2).AllCalls p
    split
    · trivial
    · exact ih _ _ _

variable {X : SimpleGraph V} {Y : SimpleGraph W}

theorem connScript_allCalls (hX : X.Connected) (hY : Y.Connected)
    (hXd : ∀ l, Nat.card (X.neighborSet l) ≤ q) (hYd : ∀ l, Nat.card (Y.neighborSet l) ≤ q)
    (u v : V) (R : ℕ) :
    (connScript hX hY hXd hYd u v R).AllCalls (LayerFrom X Y q) := by
  refine Script.AllCalls.bind (Script.AllCalls.seqList fun s hs => ?_) fun _ => trivial
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hs
  unfold candScript
  split_ifs
  · refine Script.AllCalls.bind (layersScript_allCalls (fun A τ r => ?_) _ _ _ _) fun _ => trivial
    exact LayerFrom.mk hX hY hXd hYd u v p A τ r
  · trivial

theorem anyScript_allCalls (hX : X.Connected) (hY : Y.Connected)
    (hXd : ∀ l, Nat.card (X.neighborSet l) ≤ q) (hYd : ∀ l, Nat.card (Y.neighborSet l) ≤ q)
    (R : ℕ) : (anyScript hX hY hXd hYd R).AllCalls (LayerFrom X Y q) := by
  unfold anyScript
  split_ifs <;> exact connScript_allCalls _ _ _ _ _ _ _

variable {n : ℕ} {X' Y' : SimpleGraph (Fin n)}

theorem compScript_allCalls (hXd : ∀ l, Nat.card (X'.neighborSet l) ≤ q)
    (hYd : ∀ l, Nat.card (Y'.neighborSet l) ≤ q)
    (p : X'.ConnectedComponent × Y'.ConnectedComponent) :
    (compScript hXd hYd p).AllCalls (LuksQuery X' Y' q) := by
  refine Script.AllCalls.bind ?_ fun _ => trivial
  exact (anyScript_allCalls _ _ _ _ _).mono fun m T h => ⟨p.1, p.2, h⟩

theorem graphScript_allCalls [Fintype X'.ConnectedComponent] [Fintype Y'.ConnectedComponent]
    (hXd : ∀ l, Nat.card (X'.neighborSet l) ≤ q)
    (hYd : ∀ l, Nat.card (Y'.neighborSet l) ≤ q) :
    (graphScript hXd hYd).AllCalls (LuksQuery X' Y' q) := by
  refine Script.AllCalls.bind (Script.AllCalls.seqList fun s hs => ?_) fun _ => trivial
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hs
  exact compScript_allCalls hXd hYd p

end Queries

/-! ### The statement -/

section Statement

variable {n d : ℕ} {X Y : SimpleGraph (Fin n)}

/-- **The explicit read-off of the named reduction**: the output of `luksScript` as a function
of the oracle (`luksScript_evalWith`). -/
noncomputable def luksOff (hX : ∀ v, Nat.card (X.neighborSet v) ≤ d)
    (hY : ∀ v, Nat.card (Y.neighborSet v) ≤ d) (o : Oracle) : Set (Perm (Fin n)) :=
  graphOff o (fun l => le_min (hX l) (card_neighborSet_le_n X l))
    (fun l => le_min (hY l) (card_neighborSet_le_n Y l))

variable (hX : ∀ v, Nat.card (X.neighborSet v) ≤ d) (hY : ∀ v, Nat.card (Y.neighborSet v) ≤ d)

theorem luksScript_evalWith (o : Oracle) :
    (luksScript hX hY).evalWith o = luksOff hX hY o := by
  letI : Fintype X.ConnectedComponent := Fintype.ofFinite _
  letI : Fintype Y.ConnectedComponent := Fintype.ofFinite _
  exact graphScript_evalWith o _ _

theorem luksScript_allCalls : (luksScript hX hY).AllCalls (LuksQuery X Y (min d n)) := by
  letI : Fintype X.ConnectedComponent := Fintype.ofFinite _
  letI : Fintype Y.ConnectedComponent := Fintype.ofFinite _
  exact graphScript_allCalls _ _

/-- With all answers empty, the output of the read-off is empty (`n ≥ 1`). -/
theorem luksOff_null (hn : 1 ≤ n) : luksOff hX hY Oracle.null = ∅ := by
  unfold luksOff graphOff
  haveI : NeZero n := ⟨by omega⟩
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall]
  refine ⟨X.connectedComponentMk 0, fun h => ?_⟩
  obtain ⟨p, hp⟩ := h
  unfold compOff at hp
  rw [anyOff_null _ _ _ _ hn] at hp
  simp at hp

/-- **The theorem's notion of reduction.** A script `s` for the pair `X, Y` is a reduction when
  * for **every** oracle, its output is the explicit read-off `luksOff` of the oracle's answers
    (so `s` behaves as a fixed function of the answers, on right and wrong answers alike);
  * every query it can make, on any branch, is the layer instance of a pair of components;
  * along the exact answers its calls are `Solve` calls in `Γ̂_d` on at most `3 n⁴` positions,
    and it makes at most `n⁵` of them;
  * its value on the exact answers is the isomorphism set. -/
structure IsLuksReduction (s : Script (Set (Perm (Fin n)))) : Prop where
  readOff : ∀ o : Oracle, s.evalWith o = luksOff hX hY o
  layered : s.AllCalls (LuksQuery X Y (min d n))
  calls : s.CallsExact fun {_ _} m T => m = .solve ∧ GammaHat d T.G ∧ (T.size : ℝ) ≤ 3 * (n : ℝ) ^ 4
  numCalls : s.numCalls ≤ n ^ 5
  exact : s.evalExact = isoSet X Y

/-- `luksScript` is a reduction. -/
theorem luksScript_isLuksReduction : IsLuksReduction hX hY (luksScript hX hY) where
  readOff := luksScript_evalWith hX hY
  layered := luksScript_allCalls hX hY
  calls := (luksScript_spec hX hY).1.mono fun m T ⟨hm, _, hg, hs⟩ =>
    ⟨hm, hg, le_trans (by exact_mod_cast hs) (bOm_le (min_le_right _ _))⟩
  numCalls := (luksScript_spec hX hY).2.1
  exact := (luksScript_spec hX hY).2.2

/-- An isomorphism gives an element of `isoSet`. -/
theorem isoSet_nonempty (e : X ≃g Y) : (isoSet X Y).Nonempty :=
  ⟨e.toEquiv, fun _ _ => e.map_rel_iff.symm⟩

variable {hX hY}

/-- The output of a reduction with all answers empty is empty. -/
theorem IsLuksReduction.evalWith_null {s : Script (Set (Perm (Fin n)))}
    (h : IsLuksReduction hX hY s) (hn : 1 ≤ n) : s.evalWith Oracle.null = ∅ := by
  rw [h.readOff, luksOff_null hX hY hn]

/-- A script that returns anything nonempty when all answers are empty is not a reduction. -/
theorem not_isLuksReduction_of_null_nonempty {s : Script (Set (Perm (Fin n)))} (hn : 1 ≤ n)
    (hs : (s.evalWith Oracle.null).Nonempty) : ¬ IsLuksReduction hX hY s := by
  intro h
  rw [h.evalWith_null hn] at hs
  exact Set.not_nonempty_empty hs

/-- **The trivial witness fails.** For isomorphic graphs on `n ≥ 1` vertices, the script that returns
the isomorphism set without asking is not a reduction. -/
theorem not_isLuksReduction_done (hn : 1 ≤ n) (e : X ≃g Y) :
    ¬ IsLuksReduction hX hY (Script.done (isoSet X Y)) :=
  not_isLuksReduction_of_null_nonempty hn (isoSet_nonempty e)

/-- The answers matter: for isomorphic graphs on `n ≥ 1` vertices, the output with all answers empty
differs from the output on the exact answers. -/
theorem luksScript_answers_matter (hn : 1 ≤ n) (e : X ≃g Y) :
    (luksScript hX hY).evalWith Oracle.null ≠ (luksScript hX hY).evalExact := by
  rw [luksScript_evalWith, luksOff_null hX hY hn, (luksScript_spec hX hY).2.2]
  exact (isoSet_nonempty e).ne_empty.symm

/-- A script that asks any number of useless questions and then returns the isomorphism set is
not a reduction. -/
theorem not_isLuksReduction_useless (hn : 1 ≤ n) (e : X ≃g Y) {Ω C : Type} (m : Mode)
    (S : State Ω C) (k : Set (Perm Ω) → Script (Set (Perm (Fin n))))
    (hk : ∀ A, (k A).evalWith Oracle.null = isoSet X Y) :
    ¬ IsLuksReduction hX hY (Script.ask m S k) :=
  not_isLuksReduction_of_null_nonempty hn (by
    rw [Script.evalWith_ask, hk]
    exact isoSet_nonempty e)

end Statement

/-! ### The theorems -/

open GI.DegreeD.M in
/-- **GI of maximum degree `d`, as a reduction to string isomorphism.** From the Stage-1
conclusion: there is a constant `C` such that for all graphs `X, Y` on `Fin n` of maximum degree at
most `d`, the named script `luksScript` is a reduction of `X, Y` (`IsLuksReduction`: on every oracle
it computes the explicit read-off `luksOff` of the answers, every query on every branch is a layer
instance of a pair of components, along exact answers the queries are in `Γ̂_d` on at most `3 n⁴`
positions, and the exact output is the isomorphism set), and it has a run, with value the isomorphism set, of total weight at most `exp(C log(d+2) log(n+2))`. -/
theorem graphIso_reduction_general {P : Params} {w : M.Node P → ℝ} (h : Stage1Conclusion P w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n d : ℕ) (X Y : SimpleGraph (Fin n))
      (hX : ∀ v, Nat.card (X.neighborSet v) ≤ d) (hY : ∀ v, Nat.card (Y.neighborSet v) ≤ d),
      IsLuksReduction hX hY (luksScript hX hY) ∧
      ∃ e : M.Exec P (luksScript hX hY) (isoSet X Y),
        e.total w ≤ Real.exp (C * (Real.log ((d : ℝ) + 2) * Real.log ((n : ℝ) + 2))) := by
  obtain ⟨C, hC, hexec⟩ := luksScript_exec h
  refine ⟨C, hC, fun n d X Y hX hY => ⟨luksScript_isLuksReduction hX hY, ?_⟩⟩
  obtain ⟨e, he⟩ := hexec n d X Y hX hY
  have key : ∀ a, (luksScript hX hY).evalExact = a →
      ∃ e : M.Exec P (luksScript hX hY) a,
        e.total w ≤ Real.exp (C * (Real.log ((d : ℝ) + 2) * Real.log ((n : ℝ) + 2))) := by
    rintro _ rfl
    exact ⟨e, he⟩
  exact key _ (luksScript_spec hX hY).2.2

/-- **GI of maximum degree `d`, as a reduction, from the cited results.** With the cited results
of HJ's aggregation and of Theorem A.9, and the axioms `bcp`, `gnsPrimitive`: there are parameters
`P` and a constant `C` such that for all graphs `X, Y` on `Fin n` of maximum degree at most `d`,
`luksScript hX hY` is a reduction (`IsLuksReduction`) and has a run with value the isomorphism set and at
most `exp(C log(d+2) log(n+2))` nodes. -/
theorem graphIso_reduction (hcite : GI.Cited.TransitiveAffected)
    (hK : GI.Cited.KaryCoherentRefinement) (h6 : GI.Cited.SixTransitiveContainsAlt)
    (hDL : GI.Cited.DesignLemma) (hAut : GI.Cited.AutCardLeSq)
    (hLie : GI.Cited.SimpleValuationDegree) :
    ∃ (P : Params) (C : ℝ), 0 ≤ C ∧ ∀ (n d : ℕ) (X Y : SimpleGraph (Fin n))
      (hX : ∀ v, Nat.card (X.neighborSet v) ≤ d) (hY : ∀ v, Nat.card (Y.neighborSet v) ≤ d),
      IsLuksReduction hX hY (luksScript hX hY) ∧
      ∃ e : M.Exec P (luksScript hX hY) (isoSet X Y),
        e.total (fun _ => (1 : ℝ)) ≤ Real.exp (C * (Real.log ((d : ℝ) + 2) * Real.log ((n : ℝ) + 2))) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hG⟩ := M.gnsPrimitive
  obtain ⟨P, cc, hP, hκ, hc, hαγ, hbase, h4, hab, hq, hcc, hA, hT, hγ, hPa, ha198⟩ :=
    M.params_full hcite c₁ c₂
  have h5 : (5 : ℝ) ≤ P.a := by rw [hPa]; linarith
  have h197 : (0 : ℝ) ≤ P.a := by linarith
  refine ⟨P, ?_⟩
  exact graphIso_reduction_general (M.degreeD_stage1_cited hcite hK h6 hDL hAut hLie hP hA hT hκ hc hαγ
    hbase h4 hab M.bcp hG hc₁ hc₂ hcc hq (M.nodeBoundD_one h5) le_rfl h197
    (by rw [hPa]; linarith) hγ)

/-- Every run of the named script, however it was obtained, returns the isomorphism set. -/
theorem luksScript_exec_value {P : Params} {n d : ℕ} {X Y : SimpleGraph (Fin n)}
    (hX : ∀ v, Nat.card (X.neighborSet v) ≤ d) (hY : ∀ v, Nat.card (Y.neighborSet v) ≤ d)
    {a : Set (Perm (Fin n))} (e : M.Exec P (luksScript hX hY) a) : a = isoSet X Y := by
  rw [M.Exec.exact e]
  exact (luksScript_spec hX hY).2.2

end GI.DegreeD.Luks
