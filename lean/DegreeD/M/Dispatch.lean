import Workspace.Algorithm.Procedure
import Workspace.Algorithm.DispatchKeep
import Workspace.Algorithm.NormLabels

/-!
# The dispatcher `(M′)`, at the abstract level

HJ's dispatcher (`GI.Algorithm.DispatchStep`) enumerates a primitive quotient only under the order
test `Q.Small P.a`, and normalizes a single factor only when the integer test `Q.SmallZ` fails.
Those tests are not compatible with the degree-`d` analysis (`docs/verify-theorem-R.md` §2.3,
`docs/redteam-theorem-R.md` §9(b)): the dispatcher must decide on the structure of the quotient.

**The structural test** (`Structural`). A primitive quotient `Q` of degree `d'` is *structural* when
`ρ(G)` lies in `S_m ≀ S_r` in its product action on the `r`-tuples of `k`-subsets of `[m]`, with
`2 k ≤ m`, contains `Alt(m)^r`, and `m > q₀`, `m > 4 log₂ C(m,k)`. Otherwise `Q` is enumerated. The
rule needs no knowledge of the class parameter `d`. In the regime `d ≤ N^α` this is what
Theorem R* uses, and in every regime it is a correct dispatcher, since enumeration and product
refinement are both exact reductions.

This file sets up the structural test and the step `M.DispatchStep`, whose enumeration case carries
`¬ Structural` in place of `Small`. A `Structural` quotient is handled by the normalization or
the product refinement of `GI.Algorithm`, unchanged; only the guards change.

## Reduction and facts

`M.Reduction`, `M.DispatchFacts` are `GI.Algorithm.Reduction`, `DispatchFacts` with the
enumeration index bound removed: the index is whatever it is (`|ρ(G)|`), and it is bounded *for
`Γ̂_d` groups* by the cited structure theorem (`DegreeD.Cited`), in the analysis only.
-/

namespace GI.DegreeD.M

open Equiv Equiv.Perm GI.Algorithm
open scoped Pointwise

variable {Ω C : Type}

/-- **The structural test of `(M′)`** (`docs/redteam-theorem-R.md` §9(b)): the quotient is a product
action of `S_m ≀ S_r` on `r`-tuples of `k`-subsets of `[m]`, containing `Alt(m)^r`, with `2 k ≤ m`,
`m > q₀` and `m > 4 log₂ C(m,k)`. -/
def Structural (P : Params) {S : State Ω C} (Q : PrimitiveQuotient S) : Prop :=
  ∃ (m k r : ℕ) (e : Fin Q.d ≃ (Fin r → Product.KSet m k)), Q.ProductStructure m k r e ∧
    2 * k ≤ m ∧ P.q₀ < m ∧ 4 * Real.logb 2 (m.choose k) < m

/-- **The exposed hierarchy of a quotient comes from splitting one interval.** Algorithm 5:
"Expose the next primitive quotient"; Section 7.1: "Splitting or restricting intervals also cannot
increase `Q`". The stored hierarchy is `pre₀ ++ J :: post₀`; the quotient `Q` keeps `pre₀`, adds an
interval of ratio `c₁` when `c₁ ≠ 1`, then `top` of ratio `d`, then `post₀`, with `c₁ d ≤ ratio J` and
with caps at most the cap of `J`. `State.expose` satisfies it (`DegreeD.M.exposed_split`). This
is what makes the clipped cap moment `hierQd` monotone (`ExposedSplit.Qd_le`). -/
structure ExposedSplit {S : State Ω C} (Q : PrimitiveQuotient S) : Prop where
  out : ∃ (pre₀ post₀ : List (Interval Ω)) (J : Interval Ω) (c₁ : ℕ),
    S.hier = pre₀ ++ J :: post₀ ∧ 1 ≤ c₁ ∧ c₁ * Q.d ≤ J.ratio ∧ Q.post = post₀ ∧ Q.top.cap ≤ J.cap ∧
    ((c₁ = 1 ∧ Q.pre = pre₀) ∨ (∃ mid : Interval Ω, Q.pre = pre₀ ++ [mid] ∧ mid.ratio = c₁ ∧ mid.cap ≤ J.cap))

/-- The facts of a dispatcher reduction: `GI.Algorithm.DispatchFacts` without the enumeration
index bound. -/
def DispatchFacts (S : State Ω C) (K : Subgroup (Perm Ω)) (n : ℕ)
    (hier' : List (Interval Ω)) : DispatchKind → Prop
  | .enumeration d => 2 ≤ d ∧ d ≤ S.size ∧
      State.hierRho hier' ≤ State.hierRho S.hier ∧ ∀ v ∈ S.dom, d * Nat.card (orb K v) ≤ S.size
  | .product r => 2 ≤ r ∧ (r : ℝ) ≤ Real.logb 2 S.size ∧ n ≤ 2 ^ r * r.factorial ∧
      State.hierRho hier' + ((r : ℝ) - 1) ≤ State.hierRho S.hier

/-- `GI.Algorithm.Reduction`, with the facts of `M.DispatchFacts`. -/
structure Reduction (S : State Ω C) where
  kind : DispatchKind
  blocks : Setoid Ω
  blocks_inv : ∀ g ∈ S.G, ∀ v w, blocks.r (g v) (g w) ↔ blocks.r v w
  K : Subgroup (Perm Ω)
  K_le : K ≤ S.G
  n : ℕ
  τ : Fin n → Perm Ω
  τ_mem : ∀ j, τ j ∈ S.G
  cover : (S.G : Set (Perm Ω)) ⊆ ⋃ j, τ j • (K : Set (Perm Ω))
  hier' : List (Interval Ω)
  Q_le : State.hierQ hier' ≤ State.hierQ S.hier
  facts : DispatchFacts S K n hier' kind

/-- A reduction with other coset representatives of its child group. -/
noncomputable def Reduction.withReps {S : State Ω C} (R : Reduction S)
    (hn : R.n = (R.K.subgroupOf S.G).index) (c : CosetReps S.G R.K) : Reduction S :=
  { R with
    τ := fun j => c.τ (Fin.cast hn j)
    τ_mem := fun j => c.mem _
    cover := fun g hg => by
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (c.cover hg)
      exact Set.mem_iUnion.2 ⟨Fin.cast hn.symm j, by simpa using hj⟩ }

/-- The enumeration reduction of a primitive quotient, for any index: `Reduction.ofEnumeration`
without the index bound. -/
noncomputable def enumerationRed [Finite Ω] {S : State Ω C} (Q : PrimitiveQuotient S)
    (htr : S.Transitive) : Reduction S where
  kind := .enumeration Q.d
  blocks := Q.blocks
  blocks_inv := Q.blocks_inv
  K := Q.kernel
  K_le := Q.kernel_le
  n := (Q.kernel.subgroupOf S.G).index
  τ := (CitedInstances.exists_coset_cover S.G Q.kernel).choose
  τ_mem := (CitedInstances.exists_coset_cover S.G Q.kernel).choose_spec.1
  cover := (CitedInstances.exists_coset_cover S.G Q.kernel).choose_spec.2
  hier' := Q.pre ++ Q.top :: Q.post
  Q_le := Q.Q_le
  facts := ⟨Q.two_le, Q.d_le_size, Q.rho_le, Q.kernel_orbit htr⟩

/-- The product reduction of `GI.Algorithm.PrimitiveQuotient.productRed`, as an `M.Reduction`. -/
noncomputable def productRed [Finite Ω] (P : Params) {S : State Ω C} (Q : PrimitiveQuotient S)
    (c : Q.ProductChoice) : Reduction S :=
  let R := Q.productRed P c
  { kind := R.kind
    blocks := R.blocks
    blocks_inv := R.blocks_inv
    K := R.K
    K_le := R.K_le
    n := R.n
    τ := R.τ
    τ_mem := R.τ_mem
    cover := R.cover
    hier' := R.hier'
    Q_le := R.Q_le
    facts := by
      have hf := R.facts
      show DispatchFacts S R.K R.n R.hier' R.kind
      revert hf
      generalize R.kind = k
      intro hf
      cases k with
      | enumeration d =>
        obtain ⟨hd2, hds, -, hρ', horb⟩ := hf
        exact ⟨hd2, hds, hρ', horb⟩
      | product r =>
        exact hf }

/-- **The dispatcher step of `(M′)`.** `Q` is the primitive quotient of the state. Enumeration
happens only for quotients that are not structural (`Structural`), with no order test.
Product refinement is the same as in HJ. -/
inductive DispatchStep (P : Params) {Ω C : Type} (S : State Ω C) : Type
  | enumeration (Q : PrimitiveQuotient S) (fin : Finite Ω) (htr : S.Transitive)
      (hns : ¬ Structural P Q ∧ ExposedSplit Q) (reps : CosetReps S.G Q.kernel)
      (hkeep : CarrierOK Q.kernel S.dom S.rows (Q.pre ++ Q.top :: Q.post))
  | product (Q : PrimitiveQuotient S) (fin : Finite Ω)
      (c : Q.ProductChoice) (reps : CosetReps S.G (Q.productRed P c).K)
      (hkeep : CarrierOK (Q.productRed P c).K S.dom S.rows (Q.productRed P c).hier' ∧ ExposedSplit Q)

namespace DispatchStep

variable {P : Params} {S : State Ω C} (I : DispatchStep P S)

/-- The primitive quotient of the step. -/
def quotient : PrimitiveQuotient S :=
  match I with
  | .enumeration Q _ _ _ _ _ => Q
  | .product Q _ _ _ _ => Q

/-- **The reduction of the step**, computed from its primitive quotient. -/
noncomputable def red : Reduction S :=
  match I with
  | .enumeration Q _ htr _ reps _ => (enumerationRed Q htr).withReps rfl reps
  | .product Q _ c reps _ => (productRed P Q c).withReps rfl reps

noncomputable def kind : DispatchKind := I.red.kind
noncomputable def K : Subgroup (Perm Ω) := I.red.K
theorem K_le : I.K ≤ S.G := I.red.K_le
noncomputable def n : ℕ := I.red.n
noncomputable def τ : Fin I.n → Perm Ω := I.red.τ
theorem τ_mem (j : Fin I.n) : I.τ j ∈ S.G := I.red.τ_mem j
theorem cover : (S.G : Set (Perm Ω)) ⊆ ⋃ j, I.τ j • (I.K : Set (Perm Ω)) := I.red.cover
noncomputable def hier' : List (Interval Ω) := I.red.hier'
theorem Q_le : State.hierQ I.hier' ≤ State.hierQ S.hier := I.red.Q_le
theorem facts : DispatchFacts S I.K I.n I.hier' I.kind := I.red.facts

/-- **The step is determined by its quotient.** -/
theorem K_hier'_eq :
    (∃ Q fin htr hs reps hk, I = .enumeration Q fin htr hs reps hk ∧ I.K = Q.kernel ∧
      I.hier' = Q.pre ++ Q.top :: Q.post) ∨
    (∃ Q fin c reps hk, I = .product Q fin c reps hk ∧
      ∃ (m k r : ℕ) (e : Fin Q.d ≃ (Fin r → Product.KSet m k))
        (hS : Q.ProductStructure m k r e) (hb : 2 ≤ m.choose k), 2 ≤ r ∧
        I.K = Q.coordinateGroup e hS hb ∧
        I.hier' = Q.pre ++ Q.coordHier e ++ Q.post) := by
  cases I with
  | enumeration Q fin htr hs reps hk => exact Or.inl ⟨Q, fin, htr, hs, reps, hk, rfl, rfl, rfl⟩
  | product Q fin c reps hk =>
    exact Or.inr ⟨Q, fin, c, reps, hk, rfl, _, _, _, c.e, c.hS, Q.two_le_choose c.e, c.hr, rfl, rfl⟩

/-- Every dispatcher step is proper. -/
theorem exists_not_mem_K : ∃ g ∈ S.G, g ∉ I.K := by
  cases I with
  | enumeration Q fin htr hs reps _ => exact Q.exists_not_mem_kernel
  | product Q fin c reps _ =>
    exact Q.exists_not_mem_coordinateGroup _ c.hS (Q.two_le_choose c.e) c.hr

/-- **The child group keeps the carrier** of the retained rows with the new hierarchy. -/
theorem keeps : CarrierOK I.K S.dom S.rows I.hier' := by
  cases I with
  | enumeration Q fin htr hs reps hk => exact hk
  | product Q fin c reps hk => exact hk.1

end DispatchStep

end GI.DegreeD.M
