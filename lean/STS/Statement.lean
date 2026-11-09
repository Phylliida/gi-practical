import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi

/-!
# T2 of `docs/w30-sts.md` §6: the statement

This file contains every definition a reader has to check and the two claims, stated as
propositions `T2_sts` and `T2_iso`.  It imports only Mathlib.  The proofs are in other files;
`STS/Main.lean` proves `theorem t2_sts : T2_sts` and `theorem t2_iso : T2_iso` and prints their axioms.
`STS/Sanity.lean` has the non-vacuity checks.

Conventions (as in the memo): `V = 𝔽₂^d`, `Z = 𝔽₂^3`, a colouring is `χ : V ∖ 0 → {0,1}`.
Here a colouring is a function `V d → Bool` whose value at `0` is never used (`false` = colour 0).
-/

namespace STS

/-! ## Standard notions -/

/-- A **Steiner triple system** on the type `P`: a set of 3-element subsets of `P` (the blocks)
such that any two distinct points lie in exactly one block. -/
def IsSTS {P : Type*} (blocks : Set (Finset P)) : Prop :=
  (∀ B ∈ blocks, B.card = 3) ∧
  ∀ x y : P, x ≠ y → ∃! B : Finset P, B ∈ blocks ∧ x ∈ B ∧ y ∈ B

/-- Two block systems are **isomorphic** if some bijection of the points maps every block to a
block and every non-block to a non-block. -/
def Isomorphic {P P' : Type*} [DecidableEq P'] (blocks : Set (Finset P))
    (blocks' : Set (Finset P')) : Prop :=
  ∃ e : P ≃ P', ∀ B : Finset P, B ∈ blocks ↔ B.image e ∈ blocks'

/-- `V d = 𝔽₂^d`. -/
abbrev V (d : ℕ) := Fin d → ZMod 2

/-- Two colourings of `V d ∖ 0` are **linearly equivalent** if `χ' ∘ A = χ` on `V d ∖ 0` for some
`A ∈ GL(V)` (the memo's form). -/
def LinearlyEquivalent {d : ℕ} (χ χ' : V d → Bool) : Prop :=
  ∃ A : V d ≃ₗ[ZMod 2] V d, ∀ c : V d, c ≠ 0 → χ' (A c) = χ c

/-- `χ` is **non-constant** on `V d ∖ 0`. -/
def NonConstant {d : ℕ} (χ : V d → Bool) : Prop :=
  ∃ c₀ c₁ : V d, c₀ ≠ 0 ∧ c₁ ≠ 0 ∧ χ c₀ ≠ χ c₁

/-! ## The construction `X_χ` (memo §6) -/

/-- `Z = 𝔽₂³`, its elements written `0, …, 7` in binary; addition is bitwise xor `^^^`.
(This is the encoding the memo's table uses.) -/
abbrev Z := Fin 8

/-- The memo's 1-factorization `F¹` of the complete graph on `Z`: `F1 z` lists the four pairs
of the factor `F¹_z`, copied from the memo's table. -/
def F1 (z : Z) : List (Z × Z) :=
  match z.val with
  | 1 => [(0, 5), (1, 2), (3, 4), (6, 7)]
  | 2 => [(0, 2), (1, 6), (3, 7), (4, 5)]
  | 3 => [(0, 7), (1, 5), (2, 4), (3, 6)]
  | 4 => [(0, 4), (1, 7), (2, 3), (5, 6)]
  | 5 => [(0, 1), (2, 7), (3, 5), (4, 6)]
  | 6 => [(0, 6), (1, 3), (2, 5), (4, 7)]
  | 7 => [(0, 3), (1, 4), (2, 6), (5, 7)]
  | _ => []

/-- `InFactor col z a b` says `{a, b} ∈ F^col_z`, where `F⁰_z = {{a, a + z}}` and `F¹_z` is the
table `F1`. -/
def InFactor : Bool → Z → Z → Z → Prop
  | false, z, a, b => b = a ^^^ z
  | true,  z, a, b => (a, b) ∈ F1 z ∨ (b, a) ∈ F1 z

/-- The point set `(Z ∖ 0) ⊔ (V ∖ 0) × Z` of `X_χ`. -/
abbrev Point (d : ℕ) := {z : Z // z ≠ 0} ⊕ ({c : V d // c ≠ 0} × Z)

/-- The blocks of `X_χ`, the three kinds of the memo:
(i) the lines `{z₁, z₂, z₃}` of the Fano plane on `Z ∖ 0`;
(ii) `{z, (c,a), (c,b)}` for `{a, b} ∈ F^{χ(c)}_z`;
(iii) `{(c₁,a), (c₂,b), (c₃,a+b)}` for lines `{c₁, c₂, c₃}` of `PG(V)`.
(Three nonzero vectors with sum `0` are automatically distinct, so "sum zero" is "line".) -/
def X {d : ℕ} (χ : V d → Bool) : Set (Finset (Point d)) :=
  { B | (∃ z₁ z₂ z₃ : {z : Z // z ≠ 0}, z₁.1 ^^^ z₂.1 ^^^ z₃.1 = 0 ∧
            B = {.inl z₁, .inl z₂, .inl z₃}) ∨
        (∃ (z : {z : Z // z ≠ 0}) (c : {c : V d // c ≠ 0}) (a b : Z), InFactor (χ c) z a b ∧
            B = {.inl z, .inr (c, a), .inr (c, b)}) ∨
        (∃ (c₁ c₂ c₃ : {c : V d // c ≠ 0}) (a b : Z), c₁.1 + c₂.1 + c₃.1 = 0 ∧
            B = {.inr (c₁, a), .inr (c₂, b), .inr (c₃, a ^^^ b)}) }

/-! ## The claims -/

/-- **T2, part 1.** `X_χ` is a Steiner triple system on `n = 2^(d+3) - 1` points
(for every `d` and every colouring). -/
def T2_sts : Prop :=
  ∀ (d : ℕ) (χ : V d → Bool), IsSTS (X χ) ∧ Fintype.card (Point d) = 2 ^ (d + 3) - 1

/-- **T2, part 2.** For non-constant `χ, χ'`: `X_χ ≅ X_χ'` iff `χ' ∘ A = χ` for some `A ∈ GL(V)`.
(Non-constancy forces `d ≥ 2`, so no separate hypothesis on `d` is needed.) -/
def T2_iso : Prop :=
  ∀ (d : ℕ) (χ χ' : V d → Bool), NonConstant χ → NonConstant χ' →
    (Isomorphic (X χ) (X χ') ↔ LinearlyEquivalent χ χ')

end STS
