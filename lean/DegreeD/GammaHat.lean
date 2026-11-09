import Workspace.CompositionFactors
import Workspace.AlternatingSections
import Mathlib.GroupTheory.Perm.ViaEmbedding

/-!
# The class `Γ̂_d` and its closure

GNS (Grohe, Neuen, Schweitzer, arXiv:1802.04659v3), Definition 2.3: "For `d ≥ 2` let `Γ̂_d` denote
the class of all groups `G` for which every composition factor of `G` is isomorphic to a subgroup
of `S_d`." `GammaHat d X` is this class, defined by recursion on the top of a composition
series, as `GI.Cited.CompositionProducts` is: `X` is trivial, or it has a normal subgroup `K`
with `X/K` simple and embedding in `S_d`, and `K ∈ Γ̂_d`.

The closure (GNS Lemma 2.4, Luks) goes through the equivalent characterization `SectionsEmbed d X`:
every simple quotient of every subgroup of `X` embeds in `S_d`. For finite groups the two agree
(`gammaHat_iff_sectionsEmbed`). `SectionsEmbed` is closed under subgroups and quotients by
construction, and under extensions by a short argument.

The one non-formal input is `embeds_of_simple_quotient`: a simple quotient `T` of a permutation
group on `n` points embeds in `S_n`. The proof is elementary and short (no CFSG, no Schreier):
if the point stabilizer of `v` surjects onto `T` we remove the point `v`; otherwise its image `A`
is a proper subgroup and `T` acts faithfully on the cosets of `A`, of which there are at most
`n`.

## Main results

* `GammaHat`, `SectionsEmbed`, `gammaHat_iff_sectionsEmbed`.
* `GammaHat.subgroup`, `GammaHat.of_surjective`, `GammaHat.of_injective`,
  `GammaHat.extension`, `GammaHat.mono`, `gammaHat_perm`.
* `q_le_of_surjective`: a group in `Γ̂_d` with a surjection onto `Alt(q)` (`q ≥ 5`) has `q ≤ d`.
* `GammaHat.cap`: `Γ̂_d` has alternating-section cap `d` (the `GI.SectionCaps.Cap` of HJ).
-/

namespace GI.DegreeD

open Equiv Equiv.Perm

/-- `T` is isomorphic to a subgroup of `S_d`. -/
def EmbedsSym (d : ℕ) (T : Type*) [Group T] : Prop :=
  ∃ f : T →* Perm (Fin d), Function.Injective f

theorem EmbedsSym.mono {d d' : ℕ} (h : d ≤ d') {T : Type*} [Group T] (hT : EmbedsSym d T) :
    EmbedsSym d' T := by
  obtain ⟨f, hf⟩ := hT
  let ι : Fin d ↪ Fin d' := Fin.castLEEmb h
  exact ⟨(viaEmbeddingHom ι).comp f, (viaEmbeddingHom_injective ι).comp hf⟩

/-- A group that acts faithfully on a finite set of at most `d` points embeds in `S_d`. -/
theorem embedsSym_of_card_le {V : Type*} [Finite V] {T : Type*} [Group T] (f : T →* Perm V)
    (hf : Function.Injective f) {d : ℕ} (hV : Nat.card V ≤ d) : EmbedsSym d T := by
  classical
  have e : V ≃ Fin (Nat.card V) := Finite.equivFin V
  have h1 : EmbedsSym (Nat.card V) T := by
    refine ⟨(Equiv.permCongrHom e).toMonoidHom.comp f, ?_⟩
    exact (Equiv.permCongrHom e).injective.comp hf
  exact h1.mono hV

/-! ### Simple quotients of permutation groups -/

/-- **A simple quotient of a permutation group on `n` points embeds in `S_n`.** Let `G` act
faithfully on `n` points and let `φ : G → T` be onto a simple group. Either a point stabilizer
surjects onto `T`, and we remove the point (induction on `n`), or the image `A` of a point
stabilizer is proper, and `T` acts faithfully on the at most `n` cosets of `A`. -/
theorem embeds_of_simple_quotient :
    ∀ (n : ℕ) (X : Type) [Fintype X], Fintype.card X = n →
      ∀ (G : Type) [Group G] (ι : G →* Perm X), Function.Injective ι →
      ∀ (T : Type) [Group T] [IsSimpleGroup T] (φ : G →* T), Function.Surjective φ →
        EmbedsSym n T := by
  intro n
  induction n with
  | zero =>
    intro X _ hX G _ ι hι T _ _ φ hφ
    have hemp : IsEmpty X := Fintype.card_eq_zero_iff.mp hX
    have hG : Subsingleton G := by
      refine ⟨fun a b => hι ?_⟩
      ext x
      exact (IsEmpty.false x).elim
    obtain ⟨t₁, t₂, ht⟩ := exists_pair_ne T
    obtain ⟨a, rfl⟩ := hφ t₁
    obtain ⟨b, rfl⟩ := hφ t₂
    exact (ht (by rw [Subsingleton.elim a b])).elim
  | succ n ih =>
    intro X _ hX G _ ι hι T _ _ φ hφ
    classical
    haveI hGfin : Finite G := Finite.of_injective ι hι
    have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨v⟩ := hne
    set Hv : Subgroup G := (MulAction.stabilizer (Perm X) v).comap ι with hHv
    have hmem : ∀ g : G, g ∈ Hv ↔ ι g v = v := fun g => by
      rw [hHv, Subgroup.mem_comap, MulAction.mem_stabilizer_iff]; rfl
    by_cases hA : Hv.map φ = ⊤
    · -- the stabilizer of `v` surjects onto `T`: remove the point `v`
      have hpi : ∀ g : Hv, ∀ x, ((ι g.1) x ≠ v) ↔ x ≠ v := by
        intro g x
        have hgv : ι g.1 v = v := (hmem g.1).1 g.2
        constructor
        · rintro hne rfl; exact hne hgv
        · intro hne heq
          apply hne
          apply (ι g.1).injective
          rw [heq, hgv]
      let ι' : Hv →* Perm {x : X // x ≠ v} :=
        { toFun := fun g => (ι g.1).subtypePerm (hpi g)
          map_one' := by ext x; simp
          map_mul' := fun a b => by ext x; simp }
      have hι' : Function.Injective ι' := by
        intro a b hab
        apply Subtype.ext
        apply hι
        ext x
        by_cases hx : x = v
        · subst hx
          rw [(hmem a.1).1 a.2, (hmem b.1).1 b.2]
        · have := congrArg (fun p : Perm {y : X // y ≠ v} => (p ⟨x, hx⟩ : X)) hab
          simpa [ι'] using this
      have hφ' : Function.Surjective (φ.comp Hv.subtype) := by
        intro t
        have ht : t ∈ Hv.map φ := by rw [hA]; trivial
        obtain ⟨g, hg, rfl⟩ := ht
        exact ⟨⟨g, hg⟩, rfl⟩
      have hcard : Fintype.card {x : X // x ≠ v} = n := by
        rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hX]; omega
      exact (ih _ hcard Hv ι' hι' T (φ.comp Hv.subtype) hφ').mono (Nat.le_succ n)
    · -- the image of the stabilizer is proper: act on its cosets
      set A : Subgroup T := Hv.map φ with hAdef
      let f : T →* Perm (T ⧸ A) := MulAction.toPermHom T (T ⧸ A)
      have hker : f.ker = ⊥ := by
        rcases (IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker inferInstance) with h | h
        · exact h
        · exfalso
          apply hA
          refine eq_top_iff.mpr fun t _ => ?_
          have ht : f t = 1 := MonoidHom.mem_ker.mp (by rw [h]; trivial)
          have h1 : f t ((1 : T) : T ⧸ A) = ((1 : T) : T ⧸ A) := by rw [ht]; rfl
          have h2 : ((t * 1 : T) : T ⧸ A) = ((1 : T) : T ⧸ A) := h1
          have h3 : (1 : T)⁻¹ * (t * 1) ∈ A := QuotientGroup.eq.mp h2.symm
          simpa using h3
      have hf : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
      -- the number of cosets of `A` is at most the number of points
      have hidx : A.index ≤ Hv.index := by
        have := Subgroup.index_map_dvd (H := Hv) hφ
        exact Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)) this
      have hidx2 : Hv.index ≤ Nat.card X := by
        let qq : G ⧸ Hv → X := Quotient.lift (fun g => ι g v) (by
          intro a b hab
          have h1 : a⁻¹ * b ∈ Hv := QuotientGroup.leftRel_apply.mp hab
          have h2 := (hmem _).1 h1
          simp only [map_mul, map_inv, Perm.mul_apply] at h2
          exact ((ι a).symm_apply_eq.mp h2).symm)
        have hqq : Function.Injective qq := by
          intro a b
          induction a using QuotientGroup.induction_on
          induction b using QuotientGroup.induction_on
          rename_i a b
          intro h
          have h' : ι a v = ι b v := h
          apply QuotientGroup.eq.mpr
          rw [hmem]
          simp only [map_mul, map_inv, Perm.mul_apply]
          rw [← h']
          exact (ι a).symm_apply_apply v
        exact Nat.card_le_card_of_injective qq hqq
      have hcoset : Nat.card (T ⧸ A) ≤ n + 1 := by
        change A.index ≤ n + 1
        rw [← hX, ← Nat.card_eq_fintype_card]
        exact hidx.trans hidx2
      haveI : Finite T := Finite.of_surjective φ hφ
      exact embedsSym_of_card_le f hf hcoset

/-- The form of `embeds_of_simple_quotient` that the closure lemmas use. -/
theorem EmbedsSym.of_quotient {d : ℕ} {U : Type} [Group U] (hU : EmbedsSym d U) {T : Type}
    [Group T] [IsSimpleGroup T] (φ : U →* T) (hφ : Function.Surjective φ) : EmbedsSym d T := by
  obtain ⟨f, hf⟩ := hU
  have := embeds_of_simple_quotient d (Fin d) (by simp) U f hf T φ hφ
  exact this

/-! ### The class -/

/-- **The class `Γ̂_d`** (GNS, Definition 2.3): `X` has a composition series whose factors all
embed in `S_d`. For finite `X` this does not depend on the series (`gammaHat_iff_sectionsEmbed`). -/
inductive GammaHat (d : ℕ) : (X : Type) → [Group X] → Prop
  /-- The trivial group has the empty series. -/
  | trivial (X : Type) [Group X] [Subsingleton X] : GammaHat d X
  /-- A simple top factor `X/K` embedding in `S_d`. -/
  | top (X : Type) [Group X] (K : Subgroup X) [K.Normal] (hs : IsSimpleGroup (X ⧸ K))
      (he : EmbedsSym d (X ⧸ K)) (hK : GammaHat d K) : GammaHat d X

/-- Every simple quotient of every subgroup of `X` embeds in `S_d`. For finite `X` this is `Γ̂_d`
(`gammaHat_iff_sectionsEmbed`). -/
def SectionsEmbed (d : ℕ) (X : Type) [Group X] : Prop :=
  ∀ (U : Type) [Group U] (ι : U →* X), Function.Injective ι →
    ∀ (T : Type) [Group T] [IsSimpleGroup T] (φ : U →* T), Function.Surjective φ → EmbedsSym d T

section Closure

variable {d : ℕ} {X Y : Type} [Group X] [Group Y]

theorem SectionsEmbed.of_injective (f : Y →* X) (hf : Function.Injective f)
    (h : SectionsEmbed d X) : SectionsEmbed d Y := fun U _ ι hι T _ _ φ hφ =>
  h U (f.comp ι) (hf.comp hι) T φ hφ

theorem SectionsEmbed.subgroup (h : SectionsEmbed d X) (H : Subgroup X) :
    SectionsEmbed d H := h.of_injective H.subtype Subtype.val_injective

/-- Quotients: pull the section back to the preimage of the subgroup. -/
theorem SectionsEmbed.of_surjective (π : X →* Y) (hπ : Function.Surjective π)
    (h : SectionsEmbed d X) : SectionsEmbed d Y := by
  intro U _ ι hι T _ _ φ hφ
  let U' : Subgroup X := (ι.range).comap π
  let ψ : U' →* U :=
    ((MonoidHom.ofInjective hι).symm.toMonoidHom).comp
      ((π.comp U'.subtype).codRestrict ι.range (fun g => g.2))
  refine h U' U'.subtype Subtype.val_injective T (φ.comp ψ) ?_
  intro t
  obtain ⟨u, rfl⟩ := hφ t
  obtain ⟨x, hx⟩ := hπ (ι u)
  refine ⟨⟨x, ⟨u, hx.symm⟩⟩, ?_⟩
  change φ ((MonoidHom.ofInjective hι).symm _) = _
  congr 1
  apply (MonoidHom.ofInjective hι).symm_apply_eq.mpr
  exact Subtype.ext hx

/-- Extensions (GNS, after Lemma 2.4): a section of `X` either comes from `X/K`, or from `K`. -/
theorem SectionsEmbed.extension (K : Subgroup X) [K.Normal] (hK : SectionsEmbed d K)
    (hQ : SectionsEmbed d (X ⧸ K)) : SectionsEmbed d X := by
  intro U _ ι hι T _ _ φ hφ
  let K' : Subgroup U := K.comap ι
  haveI : K'.Normal := inferInstanceAs (K.comap ι).Normal
  rcases (IsSimpleGroup.eq_bot_or_eq_top_of_normal (K'.map φ) (Subgroup.Normal.map inferInstance φ hφ))
    with hbot | htop
  · -- `φ` kills `K'`: it factors through `U/K'`, which embeds in `X/K`
    have hkill : ∀ u ∈ K', φ u = 1 := fun u hu => by
      have : φ u ∈ K'.map φ := ⟨u, hu, rfl⟩
      rw [hbot] at this
      simpa using this
    let ι₂ : U ⧸ K' →* X ⧸ K := QuotientGroup.map K' K ι (fun u hu => hu)
    have hι₂ : Function.Injective ι₂ := by
      refine (MonoidHom.ker_eq_bot_iff ι₂).mp ?_
      refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective K' x
      have h2 : ι₂ (QuotientGroup.mk' K' u) = 1 := hx
      have h3 : ((ι u : X) : X ⧸ K) = 1 := h2
      have h4 : ι u ∈ K := (QuotientGroup.eq_one_iff _).mp h3
      exact (QuotientGroup.eq_one_iff _).mpr h4
    let φ₂ : U ⧸ K' →* T := QuotientGroup.lift K' φ hkill
    have hφ₂ : Function.Surjective φ₂ := by
      intro t
      obtain ⟨u, rfl⟩ := hφ t
      exact ⟨QuotientGroup.mk' K' u, rfl⟩
    exact hQ (U ⧸ K') ι₂ hι₂ T φ₂ hφ₂
  · -- `K'` surjects onto `T`, and `K'` embeds in `K`
    let ι₂ : K' →* K :=
      { toFun := fun u => ⟨ι u.1, u.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by simp) }
    have hι₂ : Function.Injective ι₂ := by
      intro a b hab
      apply Subtype.ext
      apply hι
      exact congrArg Subtype.val hab
    have hφ₂ : Function.Surjective (φ.comp K'.subtype) := by
      intro t
      have ht : t ∈ K'.map φ := by rw [htop]; trivial
      obtain ⟨u, hu, rfl⟩ := ht
      exact ⟨⟨u, hu⟩, rfl⟩
    exact hK K' ι₂ hι₂ T (φ.comp K'.subtype) hφ₂

/-- A group that embeds in `S_d` has all its sections embedding in `S_d`
(`embeds_of_simple_quotient`). -/
theorem EmbedsSym.sectionsEmbed (h : EmbedsSym d X) : SectionsEmbed d X := by
  intro U _ ι hι T _ _ φ hφ
  obtain ⟨f, hf⟩ := h
  have hU : EmbedsSym d U := ⟨f.comp ι, hf.comp hι⟩
  exact hU.of_quotient φ hφ

end Closure

/-! ### The two definitions agree on finite groups -/

theorem GammaHat.sectionsEmbed {d : ℕ} {X : Type} [Group X] (h : GammaHat d X) :
    SectionsEmbed d X := by
  induction h with
  | trivial X =>
    intro U _ ι hι T _ _ φ hφ
    have hU : Subsingleton U := by
      refine ⟨fun a b => hι (Subsingleton.elim _ _)⟩
    obtain ⟨t₁, t₂, ht⟩ := exists_pair_ne T
    obtain ⟨a, rfl⟩ := hφ t₁
    obtain ⟨b, rfl⟩ := hφ t₂
    exact (ht (by rw [Subsingleton.elim a b])).elim
  | top X K hs he hK ih =>
    exact SectionsEmbed.extension K ih he.sectionsEmbed

theorem SectionsEmbed.gammaHat {d : ℕ} :
    ∀ (n : ℕ) (X : Type) [Group X] [Finite X], Nat.card X = n → SectionsEmbed d X →
      GammaHat d X := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ hn h
  by_cases hsub : Subsingleton X
  · exact GammaHat.trivial X
  rw [not_subsingleton_iff_nontrivial] at hsub
  haveI : Finite (Subgroup X) :=
    Finite.of_injective (fun H : Subgroup X => (H : Set X)) SetLike.coe_injective
  let C : Set (Subgroup X) := {K | K.Normal ∧ K ≠ ⊤}
  have hC : C.Nonempty := ⟨⊥, inferInstance, bot_ne_top⟩
  obtain ⟨K, hK, hmax'⟩ := Set.Finite.exists_maximalFor id C (Set.toFinite C) hC
  haveI : K.Normal := hK.1
  have hmax : ∀ M : Subgroup X, M.Normal → K ≤ M → M = K ∨ M = ⊤ := by
    intro M hM hKM
    by_cases htop : M = ⊤
    · exact Or.inr htop
    · exact Or.inl (le_antisymm (hmax' ⟨hM, htop⟩ hKM) hKM)
  have hs : IsSimpleGroup (X ⧸ K) := GI.Composition.isSimpleGroup_quotient hK.2 hmax
  have hlt : Nat.card K < n := hn ▸ GI.Composition.card_lt_of_ne_top hK.2
  have he : EmbedsSym d (X ⧸ K) :=
    h X (MonoidHom.id X) Function.injective_id (X ⧸ K) (QuotientGroup.mk' K)
      (QuotientGroup.mk'_surjective K)
  exact GammaHat.top X K hs he (ih _ hlt K rfl (h.subgroup K))

/-- **`Γ̂_d` is determined by the simple sections**, for finite groups. -/
theorem gammaHat_iff_sectionsEmbed {d : ℕ} {X : Type} [Group X] [Finite X] :
    GammaHat d X ↔ SectionsEmbed d X :=
  ⟨GammaHat.sectionsEmbed, SectionsEmbed.gammaHat _ X rfl⟩

section Corollaries

variable {d d' : ℕ} {X Y : Type} [Group X] [Group Y]

theorem GammaHat.mono [Finite X] (h : GammaHat d X) (hd : d ≤ d') : GammaHat d' X := by
  rw [gammaHat_iff_sectionsEmbed] at h ⊢
  exact fun U _ ι hι T _ _ φ hφ => (h U ι hι T φ hφ).mono hd

/-- `Γ̂_d` is closed under subgroups (GNS Lemma 2.4). -/
theorem GammaHat.subgroup [Finite X] (h : GammaHat d X) (H : Subgroup X) : GammaHat d H := by
  rw [gammaHat_iff_sectionsEmbed] at h ⊢
  exact h.subgroup H

/-- `Γ̂_d` is closed under isomorphic copies and injective homomorphic images pulled back. -/
theorem GammaHat.of_injective [Finite X] [Finite Y] (f : Y →* X) (hf : Function.Injective f)
    (h : GammaHat d X) : GammaHat d Y := by
  rw [gammaHat_iff_sectionsEmbed] at h ⊢
  exact h.of_injective f hf

/-- `Γ̂_d` is closed under quotients (GNS Lemma 2.4). -/
theorem GammaHat.of_surjective [Finite X] [Finite Y] (π : X →* Y) (hπ : Function.Surjective π)
    (h : GammaHat d X) : GammaHat d Y := by
  rw [gammaHat_iff_sectionsEmbed] at h ⊢
  exact h.of_surjective π hπ

/-- The image of a homomorphism from a group in `Γ̂_d` is in `Γ̂_d`. -/
theorem GammaHat.range [Finite X] [Finite Y] (f : X →* Y) (h : GammaHat d X) :
    GammaHat d f.range :=
  h.of_surjective f.rangeRestrict f.rangeRestrict_surjective

/-- `Γ̂_d` is closed under extensions (GNS, after Lemma 2.4). -/
theorem GammaHat.extension [Finite X] (K : Subgroup X) [K.Normal] (hK : GammaHat d K)
    (hQ : GammaHat d (X ⧸ K)) : GammaHat d X := by
  rw [gammaHat_iff_sectionsEmbed] at hK hQ ⊢
  exact SectionsEmbed.extension K hK hQ

/-- A subgroup of `S_n` with `n ≤ d` is in `Γ̂_d`. -/
theorem gammaHat_perm [Finite X] {V : Type} [Finite V] (f : X →* Perm V)
    (hf : Function.Injective f) (hV : Nat.card V ≤ d) : GammaHat d X := by
  rw [gammaHat_iff_sectionsEmbed]
  exact (embedsSym_of_card_le f hf hV).sectionsEmbed

theorem gammaHat_of_subgroup_perm {V : Type} [Finite V] (H : Subgroup (Perm V))
    (hV : Nat.card V ≤ d) : GammaHat d H :=
  gammaHat_perm H.subtype Subtype.val_injective hV

end Corollaries

/-! ### `q ≤ d` at the giant steps -/

/-- `q ≥ 5`, `q! ≤ 2 d!` imply `q ≤ d`. -/
theorem le_of_factorial_le {q d : ℕ} (hq : 5 ≤ q) (h : q.factorial ≤ 2 * d.factorial) :
    q ≤ d := by
  by_contra hlt
  push Not at hlt
  have h1 : (d + 1).factorial ≤ q.factorial := Nat.factorial_le hlt
  rw [Nat.factorial_succ] at h1
  have hdpos : 0 < d.factorial := Nat.factorial_pos d
  have h2 : (d + 1) * d.factorial ≤ 2 * d.factorial := h1.trans h
  have hd : d + 1 ≤ 2 := Nat.le_of_mul_le_mul_right h2 hdpos
  have hd' : d ≤ 1 := by omega
  have hdf : d.factorial = 1 := by
    interval_cases d <;> rfl
  rw [hdf] at h
  have h5 : Nat.factorial 5 ≤ q.factorial := Nat.factorial_le hq
  have : (5 : ℕ).factorial = 120 := rfl
  omega

/-- **`q ≤ d` from the embedding `Alt(q) ≤ S_d`.** Comparing orders: `q!/2 ≤ d!` and `q ≥ 5` force
`q ≤ d`. (No fact about the minimal degree of `Alt(q)` is needed.) -/
theorem le_of_embedsSym_alt {q d : ℕ} (hq : 5 ≤ q) (h : EmbedsSym d (alternatingGroup (Fin q))) :
    q ≤ d := by
  classical
  obtain ⟨f, hf⟩ := h
  have hcard : Nat.card (alternatingGroup (Fin q)) ≤ Nat.card (Perm (Fin d)) :=
    Nat.card_le_card_of_injective f hf
  rw [Nat.card_perm, Nat.card_fin] at hcard
  haveI : Nontrivial (Fin q) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have h2 : 2 * Nat.card (alternatingGroup (Fin q)) = q.factorial := by
    rw [two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_fin]
  exact le_of_factorial_le hq (by omega)

/-- **Every alternating quotient of a `Γ̂_d` group has degree at most `d`** (`q ≥ 5`). -/
theorem q_le_of_surjective {q d : ℕ} {X : Type} [Group X] (hq : 5 ≤ q) (hX : SectionsEmbed d X)
    (π : X →* alternatingGroup (Fin q)) (hπ : Function.Surjective π) : q ≤ d := by
  haveI : IsSimpleGroup (alternatingGroup (Fin q)) := GI.AlternatingSimple.isSimple_fin hq
  exact le_of_embedsSym_alt hq
    (hX X (MonoidHom.id X) Function.injective_id _ π hπ)

/-- `Γ̂_d` bounds the alternating width by `d` (HJ's `GI.SectionCaps.Cap`, in terms of sections).
The only input is the characterization `SectionsEmbed`. -/
theorem SectionsEmbed.cap {d : ℕ} {X : Type} [Group X] (hX : SectionsEmbed d X) :
    GI.SectionCaps.Cap X d := by
  intro U k hk q onto
  exact q_le_of_surjective hk (hX.subgroup U) q onto

theorem GammaHat.cap {d : ℕ} {X : Type} [Group X] (hX : GammaHat d X) :
    GI.SectionCaps.Cap X d :=
  hX.sectionsEmbed.cap

end GI.DegreeD
