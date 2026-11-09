import Mathlib

/-!
# Theorem H of `docs/w45-quartic.md` §4, for top forms over `𝔽₂`

Definitions and the statements proved in `QuarticH/Main.lean`. Nothing in this file is proved
except `contr3_apply`, which only unfolds a definition. Each statement is a `Prop`; `Main.lean`
contains `theorem … : QuarticH.<Name>` for each of them and prints its axioms.

Setting. `V d = 𝔽₂^d = Fin d → ZMod 2`, and `τ : AltForm4 d` is an alternating 4-linear form on
`V d` (an element of `Λ⁴ V*`, the top form of a quartic). We write `τ ![a, b, c, x]` for
`τ(a, b, c, x)`. For a quartic `f` with `f ∘ L = g`, the top forms satisfy
`τ_g(x₁,…,x₄) = τ_f(Lx₁,…,Lx₄)`, i.e. `τ_f.compLinearMap L = τ_g`. Only top forms are treated;
see `docs/w55-lean-h.md` for what this leaves out.
-/

namespace QuarticH

/-- The space `V = 𝔽₂^d`. -/
abbrev V (d : ℕ) := Fin d → ZMod 2

/-- Alternating 4-linear forms on `𝔽₂^d`. -/
abbrev AltForm4 (d : ℕ) := V d [⋀^Fin 4]→ₗ[ZMod 2] ZMod 2

variable {d : ℕ}

/-- The matrix of the pair contraction `τ(w, l, ·, ·)` in the standard basis:
entry `(i, j)` is `τ(w, l, eᵢ, eⱼ)`. -/
def pairMatrix (τ : AltForm4 d) (w l : V d) : Matrix (Fin d) (Fin d) (ZMod 2) :=
  Matrix.of fun i j => τ ![w, l, Pi.single i 1, Pi.single j 1]

/-- `s(τ)`: the minimum rank of the pair contraction `τ(w, l, ·, ·)` over linearly
independent `w, l`. (For `d ≤ 1` there is no such pair and `sInf ∅ = 0`.) -/
noncomputable def sInv (τ : AltForm4 d) : ℕ :=
  sInf {r | ∃ w l : V d, LinearIndependent (ZMod 2) ![w, l] ∧ (pairMatrix τ w l).rank = r}

/-- The functional `x ↦ τ(a, b, c, x)`, as an element of the dual space `V*`. -/
def contr3 (τ : AltForm4 d) (a b c : V d) : Module.Dual (ZMod 2) (V d) :=
  τ.toMultilinearMap.toLinearMap ![a, b, c, 0] 3

theorem contr3_apply (τ : AltForm4 d) (a b c x : V d) : contr3 τ a b c x = τ ![a, b, c, x] := by
  have h : Function.update ![a, b, c, 0] 3 x = ![a, b, c, x] := by
    funext i; fin_cases i <;> rfl
  simp only [contr3, MultilinearMap.toLinearMap_apply, h, AlternatingMap.coe_multilinearMap]

/-- A tuple `(u₁,…,u_{2m}, b₁,…,b_b)` is *good* for `τ` if the functionals
`τ(u_j, u_k, b_i, ·)`, `j < k`, span `V*`. -/
def IsGood (τ : AltForm4 d) {m b : ℕ} (u : Fin (2 * m) → V d) (bv : Fin b → V d) : Prop :=
  Submodule.span (ZMod 2) {φ | ∃ j k i, j < k ∧ φ = contr3 τ (u j) (u k) (bv i)} = ⊤

/-- Isomorphisms from `τ` to `τ'`: linear automorphisms `L` with
`τ'(x₁,…,x₄) = τ(Lx₁,…,Lx₄)` (the top-form shadow of `f ∘ L = g`). -/
def Iso (τ τ' : AltForm4 d) : Set (V d ≃ₗ[ZMod 2] V d) :=
  {L | τ.compLinearMap (L : V d →ₗ[ZMod 2] V d) = τ'}

/-! ### The parameters of Theorem H, as printed in w45 -/

/-- `s' = min(s, d/2)`; `d/2` is rounded down (natural-number division). -/
def sPrime (s d : ℕ) : ℕ := min s (d / 2)

/-- `R = ⌈√(s'/2)⌉`. -/
noncomputable def RParam (s' : ℕ) : ℕ := ⌈Real.sqrt ((s' : ℝ) / 2)⌉₊

/-- `m = ⌈(R d + 4)/(s' − 1)⌉`. -/
noncomputable def mParam (s' R d : ℕ) : ℕ := ⌈((R * d + 4 : ℕ) : ℝ) / ((s' : ℝ) - 1)⌉₊

/-- `b = ⌈(d + 2)/R⌉`. -/
noncomputable def bParam (R d : ℕ) : ℕ := ⌈((d + 2 : ℕ) : ℝ) / (R : ℝ)⌉₊

/-- `m` and `b` as functions of `(s, d)` with the printed `s'` and `R`. -/
noncomputable def mP (s d : ℕ) : ℕ := mParam (sPrime s d) (RParam (sPrime s d)) d
noncomputable def bP (s d : ℕ) : ℕ := bParam (RParam (sPrime s d)) d

/-- `t = 2m + b`. -/
noncomputable def tP (s d : ℕ) : ℕ := 2 * mP s d + bP s d

/-! ### Part 1: determination -/

/-- If `(u, b)` is good for `τ`, any linear `M` with `τ = τ' ∘ (M,M,M,M)` is determined by the
images of the `2m + b` vectors. (`M` is not assumed invertible.) -/
def Determination : Prop :=
  ∀ (d m b : ℕ) (τ τ' : AltForm4 d) (u : Fin (2 * m) → V d) (bv : Fin b → V d)
    (M₁ M₂ : V d →ₗ[ZMod 2] V d),
    IsGood τ u bv → τ = τ'.compLinearMap M₁ → τ = τ'.compLinearMap M₂ →
    (∀ j, M₁ (u j) = M₂ (u j)) → (∀ i, M₁ (bv i) = M₂ (bv i)) → M₁ = M₂

/-! ### Part 3: existence of a good tuple -/

/-- Existence for any parameters satisfying the inequalities used by the proof
(`2^{Rd}·2^{(1−s')m} < 1` in Step 1, `2^{d−Rb} ≤ 1` in Step 2, and `R + s' ≤ d` for the
pair-rank lemma). -/
def ExistsGood : Prop :=
  ∀ (d s s' R m b : ℕ) (τ : AltForm4 d),
    s ≤ sInv τ → s' ≤ s → 1 ≤ R → R + s' ≤ d → R * d + m ≤ s' * m → d ≤ R * b →
    ∃ (u : Fin (2 * m) → V d) (bv : Fin b → V d), IsGood τ u bv

/-- Existence with the printed parameters, under `s(τ) ≥ s ≥ 2`. -/
def ExistsGoodPrinted : Prop :=
  ∀ (d s : ℕ) (τ : AltForm4 d), 2 ≤ s → s ≤ sInv τ →
    ∃ (u : Fin (2 * mP s d) → V d) (bv : Fin (bP s d) → V d), IsGood τ u bv

/-! ### Part 4: assembled -/

/-- **Theorem H (top forms, no running time).** If `s(τ) ≥ s ≥ 2` there is a good tuple
`x = (u, b)` of `t = 2m + b` vectors, and for every `τ'` the map `L ↦ (L⁻¹ x₁, …, L⁻¹ x_t)`
from the isomorphisms `τ → τ'` to `V^t` is injective. Hence there are at most `2^{td}` of them. -/
def MainTheorem : Prop :=
  ∀ (d s : ℕ) (τ : AltForm4 d), 2 ≤ s → s ≤ sInv τ →
    ∃ (u : Fin (2 * mP s d) → V d) (bv : Fin (bP s d) → V d), IsGood τ u bv ∧
      ∀ τ' : AltForm4 d,
        Function.Injective (fun L : Iso τ τ' => fun i : Fin (tP s d) =>
          (L : V d ≃ₗ[ZMod 2] V d).symm (Fin.append u bv i)) ∧
        Nat.card (Iso τ τ') ≤ 2 ^ (tP s d * d)

/-! ### Part 2: threshold arithmetic (`t < d/4` iff the bound `2^{td}` beats `2^{d²/4}`) -/

/-- With the printed parameters, `t < d/4` for every `s ≥ 132` and every `d ≥ 2097`. -/
def BeatsQuarter : Prop := ∀ s d : ℕ, 132 ≤ s → 2097 ≤ d → 4 * tP s d < d

/-- `2097` cannot be lowered: at `s = 132, d = 2096`, `t = d/4` exactly. -/
def SharpAt2096 : Prop := 4 * tP 132 2096 = 2096

/-- With the printed parameters, `t > d/4` for every `s ≤ 130` and every `d`
(in particular at `s = 128` and `s = 130`). -/
def NeverBeatsLe130 : Prop := ∀ s d : ℕ, 2 ≤ s → s ≤ 130 → 4 ≤ d → d < 4 * tP s d

/-- The limit of `t/d` as `d → ∞` at fixed `s'` is `2R/(s'−1) + 1/R`; it is below `1/4` exactly
for `s' ≥ 131`. -/
def LimitThreshold : Prop :=
  ∀ s' : ℕ, 2 ≤ s' →
    ((2 * RParam s' / ((s' : ℝ) - 1) + 1 / RParam s' < 1 / 4) ↔ 131 ≤ s')

/-- The printed `R` at `s' = 128, 130`, and the two limits. -/
def RValues : Prop :=
  RParam 128 = 8 ∧ RParam 130 = 9 ∧
    (2 * 8 / (127 : ℝ) + 1 / 8 > 1 / 4) ∧ (2 * 9 / (129 : ℝ) + 1 / 9 > 1 / 4) ∧
    (2 * 8 / (129 : ℝ) + 1 / 8 < 1 / 4)

/-- The red-team repair: with `R = 8` chosen by hand at `s' = 130`, a good tuple with
`t = 2m + b < d/4` exists for `s(τ) ≥ 130` and `d ≥ 3145`. -/
def Repaired130 : Prop :=
  ∀ (d : ℕ) (τ : AltForm4 d), 130 ≤ sInv τ → 3145 ≤ d →
    ∃ (u : Fin (2 * mParam 130 8 d) → V d) (bv : Fin (bParam 8 d) → V d),
      IsGood τ u bv ∧ 4 * (2 * mParam 130 8 d + bParam 8 d) < d

/-- `3145` is the least `d` from which the `R = 8` parameters stay below `d/4`. -/
def SharpAt3144 : Prop := 3144 ≤ 4 * (2 * mParam 130 8 3144 + bParam 8 3144)

/-! ### Non-vacuity -/

/-- `s(τ) ≥ 2` forces `d ≥ 4`. -/
def FourLeD : Prop := ∀ (d : ℕ) (τ : AltForm4 d), 2 ≤ sInv τ → 4 ≤ d

/-- The hypothesis `s(τ) ≥ 2` is satisfiable: the determinant on `𝔽₂⁴` has `s(τ) ≥ 2`. -/
def DetHasS2 : Prop := 2 ≤ sInv (Matrix.detRowAlternating : AltForm4 4)

end QuarticH
