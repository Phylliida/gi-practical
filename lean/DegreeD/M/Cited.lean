import DegreeD.GammaHat
import Workspace.Algorithm.Dispatch

/-!
# The cited results of the degree-`d` analysis

These are the literature results that the Stage-1 degree-`d` theorem uses, stated as definitions
(the pattern of `Workspace/Cited/`). They enter the theorems as hypotheses; the file
`DegreeD/M/Axioms.lean` adds them as axioms, for the final `#print axioms`.

We use exactly two results.

## Babai–Cameron–Pálfy

BCP82, Lemma 2.2, as quoted by GNS (Grohe, Neuen, Schweitzer, *An improved isomorphism test for
graphs of small maximum degree*, arXiv:1802.04659v3, Lemma 2.2): "Suppose `d ≥ 6`. Let `G` be a
permutation group of degree `n` such that `G` has no composition factor isomorphic to an
alternating group `A_k` of degree `k > d`. Then `|G| ≤ d^{n-1}`."

Our `BCP` is implied by this statement, and is weaker: we assume `G ∈ Γ̂_d`, and a group in `Γ̂_d`
has no composition factor `A_k` with `k > d` (`GI.DegreeD.le_of_embedsSym_alt`: an embedding
`A_k ≤ S_d` forces `k ≤ d`, by comparing orders). Two independent restatements of the source
result are in Maróti (*On the orders of primitive groups*, J. Algebra 2002, Cor. 1.5) and
Burness–Shalev (arXiv:2012.12818, Lemma 2.2).

Why it is true: induction on the orbit and block structure reduces to primitive groups, and for
primitive groups the bound is the classical bound of BCP itself (via the Praeger–Saxl and
Liebeck type estimates; for our purposes we only need it for the top group `K ≤ S_k` of a
product action).

## Grohe–Neuen–Schweitzer Theorem 3.13

GNS Theorem 3.13: "Let `G ≤ Sym(Ω)` be a primitive `Γ̂_d`-group. Then one of the following holds:
(1) `|G| ≤ n^{c₁ log d + c₂}` for some absolute constants `c₁, c₂`, or (2) for the normal subgroup
`N = Soc(G) ≤ G` there is a sequence of partitions `{Ω} = B₁ ≻ ⋯ ≻ B_k = {{α} : α ∈ Ω}` such that:
(a) `|G:N| ≤ n^{1 + log d}`, (b) `B_i` is `N`-invariant for every `i`, and (c) there are `m ≤ d` and
`t ≤ m/2` with `m > 4 log s`, where `s = binom(m,t)`, such that for all `i` and `B ∈ B_i` the group
`N_B^{B_{i+1}[B]}` is permutationally equivalent to `A_m^{(t)}`."

`GNSPrimitive` states option (2) in the product form established by the proof of Theorem 3.13
(Lemma 3.9, Types II and IV, and the construction of the partitions from
`G ≤ P ≀ K` in product action with `Soc(P)` permutationally equivalent to `A_m^{(t)}`): there is a
bijection `e : Ω ≃ (r-tuples of t-subsets of [m])` such that `G` acts through coordinate-wise
`S_m`-permutations and a permutation of the coordinates, and `G` contains the coordinate-wise
`A_m^r`. This is the form HJ's product refinement and normalization consume
(`PrimitiveQuotient.ProductStructure`). Since `m > 4 log₂ s ≥ 4 log₂ m` forces `m ≥ 17`, the
automorphism `Aut(A_m^{(t)}) = S_m` issue does not arise.

**Status of this citation.** The text of option (2) in the theorem statement is about the
partitions; the product form used here is in its proof. We state the axiom in the product form
that the proof establishes, because that is what the algorithm consumes, and flag this: the axiom is
what the *proof* of GNS 3.13 shows, not the literal statement.

**Why the constants are absolute and unspecified.** They come from Liebeck–Shalev base bounds,
GSS98 and Maróti, through the proof of the theorem; the file does not assume more than existence.
-/

namespace GI.DegreeD.M

open Equiv Equiv.Perm GI.Algorithm

/-- The BCP bound on the order of permutation groups in `Γ̂_d` (GNS Lemma 2.2; see the module
docstring). -/
def BCP : Prop :=
  ∀ (d : ℕ), 6 ≤ d → ∀ (n : ℕ) (G : Subgroup (Perm (Fin n))), GammaHat d G →
    Nat.card G ≤ d ^ (n - 1)

/-- The product-action shape of option (2) of GNS Theorem 3.13. Same statement as
`PrimitiveQuotient.ProductStructure`, for a subgroup of `Sym(n)`. -/
def ProductForm {n : ℕ} (G : Subgroup (Perm (Fin n))) (m k r : ℕ)
    (e : Fin n ≃ (Fin r → Product.KSet m k)) : Prop :=
  (∀ g ∈ G, ∃ σ h, Product.IsProd e g σ h) ∧
  (∀ h : Fin r → Perm (Fin m), (∀ i, h i ∈ alternatingGroup (Fin m)) →
    (e.trans ((Equiv.piCongrRight fun i => GI.Cited.kSetPerm (h i)).trans e.symm) :
      Perm (Fin n)) ∈ G)

/-- GNS Theorem 3.13 (with its option 2 in the product form established by its proof), with the
constants `c₁, c₂` made explicit. Here `log = log₂`. -/
def GNSPrimitive (c₁ c₂ : ℝ) : Prop :=
  ∀ (d n : ℕ), 2 ≤ d → 2 ≤ n → ∀ (G : Subgroup (Perm (Fin n))),
    MulAction.IsPreprimitive G (Fin n) → GammaHat d G →
    ((Nat.card G : ℕ) : ℝ) ≤ (n : ℝ) ^ (c₁ * Real.logb 2 d + c₂) ∨
    ∃ (m k r : ℕ) (e : Fin n ≃ (Fin r → Product.KSet m k)), ProductForm G m k r e ∧
      m ≤ d ∧ 2 * k ≤ m ∧ 4 * Real.logb 2 (m.choose k) < m

end GI.DegreeD.M
