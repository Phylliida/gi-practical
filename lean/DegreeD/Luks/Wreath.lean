import DegreeD.GammaHat

/-!
# The group of a Luks step

The string-isomorphism instance of one layer of Luks's reduction lives on
`[V] ⊔ (V × [q]) ⊔ (V × [q])²`: the vertices (to keep the action faithful), the slots
(half-edges), and pairs of slots. The group is `S_q ≀_V A`: an element `a ∈ A ≤ Sym(V)` and, for
each vertex `l`, a permutation `s_l` of its `q` slots, acting by `(l, i) ↦ (a l, s_l i)` on
slots and coordinatewise on pairs of slots.

Main results: `wreath A : Subgroup (Perm (Om V q))`, the closure of `Γ̂_q` under this
construction (`gammaHat_wreath`), `gammaHat_pi`.
-/

namespace GI.DegreeD.Luks

open Equiv Equiv.Perm

/-! ### General closure facts -/

section Closure

variable {d : ℕ}

/-- `Γ̂_d` is closed under the extension given by a homomorphism with kernel and image in the
class. -/
theorem gammaHat_of_hom {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y] (f : X →* Y)
    (hker : GammaHat d f.ker) (hrange : GammaHat d f.range) : GammaHat d X := by
  refine GammaHat.extension f.ker hker ?_
  haveI : Finite (X ⧸ f.ker) := inferInstance
  exact GammaHat.of_injective (QuotientGroup.quotientKerEquivRange f).toMonoidHom
    (QuotientGroup.quotientKerEquivRange f).injective hrange

/-- A finite product of groups in `Γ̂_d` is in `Γ̂_d`. -/
theorem gammaHat_piDep (ι : Type) [Finite ι] :
    ∀ (H : ι → Type) [∀ i, Group (H i)] [∀ i, Finite (H i)], (∀ i, GammaHat d (H i)) →
      GammaHat d (∀ i, H i) := by
  refine Finite.induction_empty_option
    (P := fun ι : Type => Finite ι → ∀ (H : ι → Type) [∀ i, Group (H i)] [∀ i, Finite (H i)],
      (∀ i, GammaHat d (H i)) → GammaHat d (∀ i, H i)) ?_ ?_ ?_ ι ‹_›
  · intro α β e h hβ H _ _ hH
    haveI : Finite β := hβ
    haveI : Finite α := Finite.of_equiv β e.symm
    refine GammaHat.of_injective
      ({ toFun := fun f a => f (e a)
         map_one' := rfl
         map_mul' := fun _ _ => rfl } : (∀ b, H b) →* ∀ a, H (e a)) ?_
      (h inferInstance (fun a => H (e a)) fun a => hH (e a))
    intro f g hfg
    funext b
    obtain ⟨a, rfl⟩ := e.surjective b
    exact congrFun hfg a
  · intro _ H _ _ _
    haveI : Subsingleton (∀ i, H i) := ⟨fun f g => funext fun a => a.elim⟩
    exact GammaHat.trivial _
  · intro α _ h _ H _ _ hH
    have h' := h inferInstance (fun a => H (some a)) fun a => hH (some a)
    let ev : (∀ o, H o) →* H none :=
      { toFun := fun f => f none
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine gammaHat_of_hom ev ?_ ((hH none).subgroup _)
    let ι' : ev.ker →* (∀ a, H (some a)) :=
      { toFun := fun f a => (f : ∀ o, H o) (some a)
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine GammaHat.of_injective ι' ?_ h'
    intro f g hfg
    apply Subtype.ext
    funext o
    cases o with
    | none =>
      have hf : (f : ∀ o, H o) none = 1 := f.2
      have hg : (g : ∀ o, H o) none = 1 := g.2
      rw [hf, hg]
    | some a => exact congrFun hfg a

/-- A finite power of a group in `Γ̂_d` is in `Γ̂_d`. -/
theorem gammaHat_pi {H : Type} [Group H] [Finite H] (hH : GammaHat d H) (ι : Type) [Finite ι] :
    GammaHat d (ι → H) :=
  gammaHat_piDep ι (fun _ => H) fun _ => hH

end Closure

/-! ### The action -/

variable {V : Type} {q : ℕ}

/-- The slots: `q` slots at each vertex. -/
abbrev Sl (V : Type) (q : ℕ) : Type := V × Fin q

/-- The domain of a Luks instance: vertices, slots and pairs of slots. -/
abbrev Om (V : Type) (q : ℕ) : Type := V ⊕ (Sl V q ⊕ Sl V q × Sl V q)

/-- The action on slots of `(a, s)`. -/
def slotAct (a : Perm V) (s : V → Perm (Fin q)) : Perm (Sl V q) := Equiv.prodShear a s

@[simp] theorem slotAct_apply (a : Perm V) (s : V → Perm (Fin q)) (p : Sl V q) :
    slotAct a s p = (a p.1, s p.1 p.2) := rfl

/-- The action of `(a, s)` on `V ⊔ Sl ⊔ Sl²`. -/
def act (a : Perm V) (s : V → Perm (Fin q)) : Perm (Om V q) :=
  Equiv.sumCongr a (Equiv.sumCongr (slotAct a s) (Equiv.prodCongr (slotAct a s) (slotAct a s)))

@[simp] theorem act_inl (a : Perm V) (s : V → Perm (Fin q)) (v : V) :
    act a s (Sum.inl v) = Sum.inl (a v) := rfl

@[simp] theorem act_slot (a : Perm V) (s : V → Perm (Fin q)) (p : Sl V q) :
    act a s (Sum.inr (Sum.inl p)) = Sum.inr (Sum.inl (a p.1, s p.1 p.2)) := rfl

@[simp] theorem act_pair (a : Perm V) (s : V → Perm (Fin q)) (p p' : Sl V q) :
    act a s (Sum.inr (Sum.inr (p, p'))) =
      Sum.inr (Sum.inr ((a p.1, s p.1 p.2), (a p'.1, s p'.1 p'.2))) := rfl

theorem act_mul (a b : Perm V) (s t : V → Perm (Fin q)) :
    act a s * act b t = act (a * b) (fun l => s (b l) * t l) := by
  ext ω
  rcases ω with v | p | ⟨p, p'⟩
  · simp [Perm.mul_apply]
  · simp [Perm.mul_apply]
  · simp [Perm.mul_apply]

theorem act_one : act (1 : Perm V) (fun _ => (1 : Perm (Fin q))) = 1 := by
  ext ω
  rcases ω with v | p | ⟨p, p'⟩ <;> simp

theorem act_inv (a : Perm V) (s : V → Perm (Fin q)) :
    (act a s)⁻¹ = act a⁻¹ (fun l => (s (a⁻¹ l))⁻¹) := by
  rw [inv_eq_iff_mul_eq_one, act_mul]
  have h : (fun l => s (a⁻¹ l) * (s (a⁻¹ l))⁻¹) = fun _ => (1 : Perm (Fin q)) := by
    funext l; simp
  rw [h, mul_inv_cancel]
  exact act_one

theorem act_injective {a a' : Perm V} {s s' : V → Perm (Fin q)} (h : act a s = act a' s') :
    a = a' ∧ s = s' := by
  constructor
  · ext v
    have := congrArg (fun g : Perm (Om V q) => g (Sum.inl v)) h
    simpa using this
  · funext l
    ext i
    have := congrArg (fun g : Perm (Om V q) => g (Sum.inr (Sum.inl (l, i)))) h
    simp only [act_slot, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at this
    exact congrArg Fin.val this.2

/-- `S_q ≀_V A`: the elements `act a s` with `a ∈ A`. -/
def wreath (A : Subgroup (Perm V)) : Subgroup (Perm (Om V q)) where
  carrier := {g | ∃ a ∈ A, ∃ s : V → Perm (Fin q), g = act a s}
  mul_mem' := by
    rintro _ _ ⟨a, ha, s, rfl⟩ ⟨b, hb, t, rfl⟩
    exact ⟨a * b, A.mul_mem ha hb, _, act_mul a b s t⟩
  one_mem' := ⟨1, A.one_mem, fun _ => 1, act_one.symm⟩
  inv_mem' := by
    rintro _ ⟨a, ha, s, rfl⟩
    exact ⟨a⁻¹, A.inv_mem ha, _, act_inv a s⟩

theorem mem_wreath {A : Subgroup (Perm V)} {g : Perm (Om V q)} :
    g ∈ wreath A ↔ ∃ a ∈ A, ∃ s : V → Perm (Fin q), g = act a s := Iff.rfl

theorem act_mem_wreath {A : Subgroup (Perm V)} {a : Perm V} (ha : a ∈ A)
    (s : V → Perm (Fin q)) : act a s ∈ wreath A := ⟨a, ha, s, rfl⟩

section GammaHat

variable (A : Subgroup (Perm V))

/-- The `A`-component of an element of the wreath product. -/
noncomputable def wreathA (g : wreath (q := q) A) : Perm V := g.2.choose

theorem wreathA_mem (g : wreath (q := q) A) : wreathA A g ∈ A := g.2.choose_spec.1

/-- The slot component of an element of the wreath product. -/
noncomputable def wreathS (g : wreath (q := q) A) : V → Perm (Fin q) :=
  g.2.choose_spec.2.choose

theorem wreathA_spec (g : wreath (q := q) A) :
    (g : Perm (Om V q)) = act (wreathA A g) (wreathS A g) := g.2.choose_spec.2.choose_spec

/-- The projection `S_q ≀_V A → A`. -/
noncomputable def wreathHom : wreath (q := q) A →* A where
  toFun g := ⟨wreathA A g, wreathA_mem A g⟩
  map_one' := by
    apply Subtype.ext
    have h := wreathA_spec A (1 : wreath (q := q) A)
    change (1 : Perm (Om V q)) = _ at h
    rw [← act_one] at h
    exact (act_injective h).1.symm
  map_mul' g h := by
    apply Subtype.ext
    have h1 := wreathA_spec A (g * h)
    change (g : Perm (Om V q)) * h = _ at h1
    rw [wreathA_spec A g, wreathA_spec A h, act_mul] at h1
    exact (act_injective h1).1.symm

/-- The kernel of the projection embeds in `∏_V S_q`. -/
theorem wreath_ker_gammaHat [Finite V] : GammaHat q (wreathHom (q := q) A).ker := by
  have hS : GammaHat q (V → Perm (Fin q)) :=
    gammaHat_pi (gammaHat_perm (MonoidHom.id _) Function.injective_id (by simp)) V
  have hone : ∀ g : (wreathHom (q := q) A).ker, wreathA A g.1 = 1 := fun g => by
    have := g.2
    rw [MonoidHom.mem_ker] at this
    exact congrArg Subtype.val this
  let ψ : (wreathHom (q := q) A).ker →* (V → Perm (Fin q)) :=
    { toFun := fun g => wreathS A g.1
      map_one' := by
        have h := wreathA_spec A ((1 : (wreathHom (q := q) A).ker) : wreath (q := q) A)
        rw [show ((1 : (wreathHom (q := q) A).ker) : wreath (q := q) A) = 1 from rfl] at h
        change (1 : Perm (Om V q)) = _ at h
        rw [← act_one] at h
        exact (act_injective h).2.symm
      map_mul' := fun g h => by
        have h1 := wreathA_spec A (g.1 * h.1)
        change (g.1 : Perm (Om V q)) * h.1 = _ at h1
        rw [wreathA_spec A g.1, wreathA_spec A h.1, act_mul, hone g, hone h] at h1
        have := (act_injective h1).2.symm
        funext l
        exact congrFun this l }
  refine GammaHat.of_injective ψ ?_ hS
  intro g h hgh
  apply Subtype.ext
  apply Subtype.ext
  rw [wreathA_spec A g.1, wreathA_spec A h.1, hone g, hone h]
  show act 1 (ψ g) = act 1 (ψ h)
  rw [hgh]

/-- **`S_q ≀_V A ∈ Γ̂_q`** when `A ∈ Γ̂_q`. -/
theorem gammaHat_wreath [Finite V] (hA : GammaHat q A) : GammaHat q (wreath (q := q) A) :=
  gammaHat_of_hom (wreathHom A) (wreath_ker_gammaHat A) (hA.subgroup _)

end GammaHat

end GI.DegreeD.Luks
