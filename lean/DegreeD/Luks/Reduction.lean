import DegreeD.Luks.Step
import DegreeD.M.Supply

/-!
# Luks's reduction as a script of `Solve` calls

`layersScript`: the layer-by-layer script: at each level the instance `layerState` is asked as a
`Solve` call and the next coset is read off its answer (`readStep`). `rootedScript` runs the layers
from a rooted base and returns the set of rooted isomorphisms of the whole graph. Correctness:
`layersScript_spec`, `rootedScript_spec`: the script returns exactly the isomorphisms when every call
receives its exact answer. `exec_of_calls` and `Exec.total_le`: runs of the script from
`exists_run_solve`, and the sum of the costs of the calls.
-/

namespace GI.DegreeD.Luks

open Equiv Equiv.Perm GI.Algorithm
open scoped Classical

set_option linter.unusedSectionVars false

variable {V W : Type} {q : ℕ}

/-- The layers `r, r+1, …` of the reduction: `f` calls, starting from the level `r` data `(A, τ)`.
The result is `some` of the data at level `r + f` or `none` if an empty answer stops the
loop. -/
noncomputable def layersScript (X : LG V q) (Y : LG W q) :
    ℕ → ℕ → Subgroup (Perm V) → (V → W) → Script (Option (Subgroup (Perm V) × (V → W)))
  | 0, _, A, τ => Script.done (some (A, τ))
  | f + 1, r, A, τ => Script.ask .solve (layerState X Y A τ r) fun ans =>
      match readStep X Y r τ ans with
      | none => Script.done none
      | some d' => layersScript X Y f (r + 1) d'.1 d'.2

/-- The properties of a call of the scripts: a `Solve` call, on a finite set, in `Γ̂_q`, with
at most `B` positions. -/
def CallOK (q : ℕ) (B : ℕ) {Ω' C' : Type} (m : Mode) (T : State Ω' C') : Prop :=
  m = .solve ∧ Finite Ω' ∧ GammaHat q T.G ∧ T.size ≤ B

theorem layerState_size [Finite V] (X : LG V q) (Y : LG W q) (A : Subgroup (Perm V)) (τ : V → W)
    (r : ℕ) : (layerState X Y A τ r).size = Nat.card (Om V q) := by
  show Nat.card (Set.univ : Set (Om V q)) = _
  exact Nat.card_congr (Equiv.Set.univ _)

theorem layersScript_spec [Finite V] {X : LG V q} {Y : LG W q} {f₀ : V → W} (f : ℕ) :
    ∀ (r : ℕ) (τ : V → W), IsIso X Y f₀ r τ →
      (layersScript X Y f r (X.aut r) τ).CallsExact (CallOK q (Nat.card (Om V q))) ∧
      (layersScript X Y f r (X.aut r) τ).numCalls ≤ f ∧
      (match (layersScript X Y f r (X.aut r) τ).evalExact with
       | some d' => d'.1 = X.aut (r + f) ∧ IsIso X Y f₀ (r + f) d'.2
       | none => ¬ ∃ g, IsIso X Y f₀ (r + f) g) := by
  induction f with
  | zero =>
    intro r τ hτ
    refine ⟨trivial, by simp [layersScript, Script.numCalls], ?_⟩
    exact ⟨rfl, hτ⟩
  | succ f ih =>
    intro r τ hτ
    have hcall : CallOK q (Nat.card (Om V q)) .solve (layerState X Y (X.aut r) τ r) :=
      ⟨rfl, inferInstance, gammaHat_wreath _ (X.gammaHat_aut r), (layerState_size _ _ _ _ _).le⟩
    have hle : r + (f + 1) = r + 1 + f := by omega
    rcases hread : readStep X Y r τ (layerState X Y (X.aut r) τ r).answer with _ | ⟨A', τ'⟩
    · refine ⟨⟨hcall, ?_⟩, ?_, ?_⟩
      · show (match readStep X Y r τ (layerState X Y (X.aut r) τ r).answer with
              | none => Script.done none
              | some d' => layersScript X Y f (r + 1) d'.1 d'.2).CallsExact _
        rw [hread]
        exact trivial
      · show 1 + (match readStep X Y r τ (layerState X Y (X.aut r) τ r).answer with
              | none => Script.done none
              | some d' => layersScript X Y f (r + 1) d'.1 d'.2).numCalls ≤ f + 1
        rw [hread]
        simp [Script.numCalls]
      · show match (match readStep X Y r τ (layerState X Y (X.aut r) τ r).answer with
              | none => Script.done none
              | some d' => layersScript X Y f (r + 1) d'.1 d'.2).evalExact with
            | some d' => d'.1 = X.aut (r + (f + 1)) ∧ IsIso X Y f₀ (r + (f + 1)) d'.2
            | none => ¬ ∃ g, IsIso X Y f₀ (r + (f + 1)) g
        rw [hread]
        show ¬ ∃ g, IsIso X Y f₀ (r + (f + 1)) g
        rintro ⟨g, hg⟩
        exact readStep_none hτ hread ⟨g, hg.mono (by omega)⟩
    · obtain ⟨hA', hτ'⟩ := readStep_some hτ hread
      subst hA'
      obtain ⟨h1, h2, h3⟩ := ih (r + 1) τ' hτ'
      refine ⟨⟨hcall, ?_⟩, ?_, ?_⟩
      · show (match readStep X Y r τ (layerState X Y (X.aut r) τ r).answer with
              | none => Script.done none
              | some d' => layersScript X Y f (r + 1) d'.1 d'.2).CallsExact _
        rw [hread]
        exact h1
      · show 1 + (match readStep X Y r τ (layerState X Y (X.aut r) τ r).answer with
              | none => Script.done none
              | some d' => layersScript X Y f (r + 1) d'.1 d'.2).numCalls ≤ f + 1
        rw [hread]
        show 1 + (layersScript X Y f (r + 1) (X.aut (r + 1)) τ').numCalls ≤ f + 1
        omega
      · show match (match readStep X Y r τ (layerState X Y (X.aut r) τ r).answer with
              | none => Script.done none
              | some d' => layersScript X Y f (r + 1) d'.1 d'.2).evalExact with
            | some d' => d'.1 = X.aut (r + (f + 1)) ∧ IsIso X Y f₀ (r + (f + 1)) d'.2
            | none => ¬ ∃ g, IsIso X Y f₀ (r + (f + 1)) g
        rw [hread, hle]
        exact h3

/-- **The rooted script**: the layers from the base data `(⊥, f₀)` up to level `R`, returning the
isomorphisms as functions. -/
noncomputable def rootedScript (X : LG V q) (Y : LG W q) (f₀ : V → W) (R : ℕ) :
    Script (Set (V → W)) :=
  (layersScript X Y R 0 ⊥ f₀).bind fun o =>
    Script.done (match o with
      | none => ∅
      | some d => {f | ∃ a ∈ d.1, f = fun w => d.2 (a w)})

/-- At level `0` the automorphism group is trivial. -/
theorem LG.aut_zero (X : LG V q) : X.aut 0 = ⊥ := by
  ext a
  simp only [Subgroup.mem_bot]
  constructor
  · intro h
    obtain ⟨h1, h2, -, -⟩ := LG.mem_aut.1 h
    ext w
    by_cases hw : X.lvl w = 0
    · rw [h2 w hw]; rfl
    · rw [h1 w (by omega)]; rfl
  · rintro rfl
    exact (X.aut 0).one_mem

/-- **The rooted script is exact.** If `f₀` is an isomorphism of the level-`0` balls and all levels
of both graphs are at most `R`, the script returns exactly the isomorphisms extending `f₀`
(`f₀` is only used on level `0`), and its calls satisfy `CallOK`, with at most `R` calls. -/
theorem rootedScript_spec [Finite V] {X : LG V q} {Y : LG W q} {f₀ : V → W} {R : ℕ}
    (h₀ : IsIso X Y f₀ 0 f₀) (hX : ∀ w, X.lvl w ≤ R) :
    (rootedScript X Y f₀ R).CallsExact (CallOK q (Nat.card (Om V q))) ∧
      (rootedScript X Y f₀ R).numCalls ≤ R ∧
      (rootedScript X Y f₀ R).evalExact = {f | IsIso X Y f₀ R f} := by
  obtain ⟨h1, h2, h3⟩ := layersScript_spec (X := X) (Y := Y) (f₀ := f₀) R 0 f₀ h₀
  rw [X.aut_zero] at h1 h2 h3
  simp only [zero_add] at h3
  refine ⟨?_, ?_, ?_⟩
  · exact Script.callsExact_bind _ _ h1 trivial
  · unfold rootedScript
    rw [Script.numCalls_bind]
    simp only [Script.numCalls, add_zero]
    exact h2
  · unfold rootedScript
    rw [Script.evalExact_bind]
    show (match (layersScript X Y R 0 ⊥ f₀).evalExact with
      | none => (∅ : Set (V → W))
      | some d => {f | ∃ a ∈ d.1, f = fun w => d.2 (a w)}) = _
    revert h3
    generalize (layersScript X Y R 0 ⊥ f₀).evalExact = o
    intro h3
    cases o with
    | none =>
      ext f
      constructor
      · intro hf; exact absurd hf (by simp)
      · intro hf; exact absurd ⟨f, hf⟩ h3
    | some d =>
      obtain ⟨hd1, hd2⟩ := h3
      ext f
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨a, ha, rfl⟩
        rw [hd1] at ha
        exact hd2.comp_aut ha
      · intro hf
        obtain ⟨a, ha, hfa⟩ := hd2.exists_aut hf
        rw [hd1]
        exact ⟨a, ha, funext fun w => (hfa w (hX w)).symm⟩

/-! ### Exact runs of the script -/

section Exec

variable {P : Params}

/-- **Every script of `Solve` calls in the class has a run with root bounds**, with its exact
value. -/
theorem exec_of_calls {cσ : ℝ} {d D : ℕ} (hdD : d ≤ D)
    (hcalls : ∀ {Ω C : Type} [Finite Ω] (S : State Ω C),
      GammaHat d S.G → ∃ r : M.Run P .solve S none S.answer, r.RootsOK cσ D)
    {α : Type} (s : Script α) (B : ℕ)
    (h : s.CallsExact (CallOK d B)) :
    ∃ e : M.Exec P s s.evalExact, e.RootsOK cσ D := by
  refine M.Exec.exists_exact s (h.mono fun m T hT => ?_)
  obtain ⟨rfl, hfin, hg, -⟩ := hT
  haveI := hfin
  exact ⟨fun _ => ⟨hfin, hg.mono hdD⟩, hcalls T hg⟩

/-- The sum of the costs of the calls of a script run. -/
theorem exec_total_le {w : M.Node P → ℝ} {cσ : ℝ} {D : ℕ} {K : ℝ}
    {p : ∀ {Ω' C' : Type}, Mode → State Ω' C' → Prop}
    (hb : ∀ {Ω' C' : Type} {m : Mode} {T : State Ω' C'} (r : M.Run P m T none T.answer),
      p m T → r.RootsOK cσ D → r.total w ≤ K) :
    ∀ {α : Type} (s : Script α) {a : α} (e : M.Exec P s a), e.RootsOK cσ D →
      s.CallsExact p → e.total w ≤ s.numCalls * K := by
  intro α s
  induction s with
  | done a =>
    intro a' e _ _
    cases e
    simp [M.Exec.total_done, Script.numCalls]
  | ask m T k ih =>
    intro a' e he hs
    cases e with
    | @ask _ Ω' C' m' S' k' A a'' r e' =>
      have hA : A = T.answer := r.exact
      subst hA
      obtain ⟨-, hr, he'⟩ := he
      have h1 := hb r hs.1 hr
      have h2 := ih T.answer e' he' hs.2
      rw [M.Exec.total_ask]
      show _ ≤ ((1 + (k T.answer).numCalls : ℕ) : ℝ) * K
      push_cast
      nlinarith

end Exec

end GI.DegreeD.Luks
