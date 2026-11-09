import DegreeD.M.Main
import DegreeD.M.Existence
import Workspace.Paper.ScriptCalls

/-!
# `NodeBoundD` is inhabited

The red-team of the Stage-1 theorem (`docs/redteam-lean-stage1.md`, appendix A) proved this as a
scratch check; it is kept here. For the constant weight `1` (so `r.total 1` is the number of nodes
of the run), `NodeBoundD` holds with `cw = 0`, `af = P.a` when `5 ≤ P.a`. The only nontrivial
field is `calls`, ported from HJ's `Run.scriptCalls_le` to `M.Run`.
-/

namespace GI.DegreeD.M

open Equiv Equiv.Perm GI.Algorithm GI.Paper
open scoped Pointwise

variable {P : Params}

/-- `M`-version of `GI.Algorithm.Exec.calls_length`. -/
theorem Exec.calls_length' {α : Type} {s : Script α} {a : α} (e : Exec P s a) :
    e.calls.length = s.numCalls := by
  refine Exec.rec (motive_1 := fun _ {_ _} _ _ _ _ => True)
    (motive_2 := fun s _ e => e.calls.length = s.numCalls)
    (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    ?done ?ask e
  case done => intro α a; rfl
  case ask =>
    intro α Ω' C' m S k A a r e' _ ih
    have hA : A = S.answer := r.exact
    subst hA
    change (e'.calls.length + 1) = 1 + (k S.answer).numCalls
    omega

/-- `M`-version of `GI.Algorithm.Run.scriptCalls_le`: the `calls` field of `NodeBoundD` is a
theorem, for `af = P.a` and `5 ≤ P.a`. -/
theorem Run.scriptCalls_le' (ha : 5 ≤ P.a) {m : Mode} {Ω C : Type} {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)} (r : Run P m S L A)
    (hsz : S.size ≤ S.N) :
    (r.scriptCalls.length : ℝ) ≤ (S.N : ℝ) ^ P.a := by
  have h0 : (0 : ℝ) ≤ (S.N : ℝ) ^ P.a := Real.rpow_nonneg (Nat.cast_nonneg _) _
  cases r with
  | rowTerminal hs _ L _ I e =>
    change (e.calls.length : ℝ) ≤ _
    rw [Exec.calls_length', I.numCalls_eq]
    have hN2 := two_le_N_of_large hs hsz
    have hq : L.q ≤ S.N := (I.q_le_size (size_pos_of_large' hs)).trans hsz
    have hN2' : (2 : ℝ) ≤ S.N := by exact_mod_cast hN2
    have hqR : (L.q : ℝ) ≤ S.N := by exact_mod_cast hq
    have hq0 : (0 : ℝ) ≤ L.q := Nat.cast_nonneg _
    have h5 : (5 : ℝ) * L.q ^ 2 ≤ (S.N : ℝ) ^ (5 : ℕ) := by
      have h1 : (L.q : ℝ) ^ 2 ≤ (S.N : ℝ) ^ 2 := pow_le_pow_left₀ hq0 hqR 2
      have h2 : (5 : ℝ) ≤ (S.N : ℝ) ^ 3 := by nlinarith
      calc (5 : ℝ) * L.q ^ 2 ≤ (S.N : ℝ) ^ 3 * (S.N : ℝ) ^ 2 :=
            mul_le_mul h2 h1 (by positivity) (by positivity)
        _ = (S.N : ℝ) ^ (5 : ℕ) := by ring
    push_cast
    calc (5 : ℝ) * L.q ^ 2 ≤ (S.N : ℝ) ^ (5 : ℕ) := h5
      _ = (S.N : ℝ) ^ ((5 : ℕ) : ℝ) := by rw [Real.rpow_natCast]
      _ ≤ (S.N : ℝ) ^ P.a :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; exact ha)
  | aggregate _ _ _ _ _ I _ _ b e =>
    change (e.calls.length : ℝ) ≤ _
    rw [Exec.calls_length']
    exact I.calls_count'
  | direct => simpa [Run.scriptCalls] using h0
  | fresh => simpa [Run.scriptCalls] using h0
  | threshold => simpa [Run.scriptCalls] using h0
  | orbitStop => simpa [Run.scriptCalls] using h0
  | orbitChain => simpa [Run.scriptCalls] using h0
  | floorReset => simpa [Run.scriptCalls] using h0
  | dispatch => simpa [Run.scriptCalls] using h0
  | normalize => simpa [Run.scriptCalls] using h0
  | rowColumns => simpa [Run.scriptCalls] using h0

/-- **`NodeBoundD` is inhabited**: the constant weight `1` (so `r.total 1` is the number of
nodes of the run) satisfies it with `cw = 0`, `af = P.a`, `5 ≤ P.a`. -/
theorem nodeBoundD_one (ha : 5 ≤ P.a) :
    NodeBoundD (P := P) (fun _ => (1 : ℝ)) 0 P.a where
  nonneg _ := zero_le_one
  work nd _ _ _ := by
    have h : (0 : ℝ) ≤ (nd.run.fanout : ℝ) := Nat.cast_nonneg _
    simp only [Real.rpow_zero, mul_one]; linarith
  rowTerminal nd _ _ _ := by
    simp [expLogSq]
  solve nd _ := by simp
  calls nd _ hsz := Run.scriptCalls_le' ha nd.run hsz

end GI.DegreeD.M
