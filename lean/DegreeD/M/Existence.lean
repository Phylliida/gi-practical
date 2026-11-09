import DegreeD.M.Main
import Workspace.Algorithm.SupplyBuild
import Workspace.Paper.RootBounds

/-!
# Every `Γ̂_d` state has a run of `M.Run`

Non-vacuity of `degreeD_stage1`. Given the subroutine data of the recursion (`M.Supply`, the
analogue of HJ's `GI.Algorithm.Supply`), every state whose group lies in `Γ̂_D` has a run of `Solve`
with the exact answer and with root bounds (`Run.RootsOK`). The termination argument is the same
lexicographic GI.Algorithm.measure as `GI.Algorithm.exists_run_aux`; the dispatcher is `(M′)`:

* if the exposed primitive quotient is structural, normalize (single factor) or refine the
  product (`r ≥ 2`);
* otherwise enumerate the block kernel.

The cases are exhaustive *for every group*: the structural test is a test, not a theorem.
Its role as a cost bound (the cited structure theorem) is used only in the analysis
(`DegreeD/M/Bounds.lean`). The class `Γ̂_D` is preserved by the recursion (the children lie in
subgroups or quotients), which is what `GiantCase`, a copy of HJ's `GI.Algorithm.GiantCase`,
needs: the `Solve` calls of an aggregation round are on `Γ̂_D` groups (`GiantCase.aggregate`, `cls`).
-/

namespace GI.DegreeD.M

open Equiv Equiv.Perm GI.Algorithm GI.Paper
open scoped Pointwise

variable {P : Params} {Ω C : Type}

/-! ### The hierarchy invariant of a dispatcher step -/

section HierInv

variable {S : State Ω C}

theorem DispatchStep.hierInv [Finite Ω] (I : DispatchStep P S) : HierInv I.K S.dom I.hier' := by
  rcases I.K_hier'_eq with ⟨Q, _, _, _, _, _, -, hK, hh⟩ |
    ⟨Q, _, _, _, _, -, m, k, r, e, hS, hb, hr, hK, hh⟩
  · rw [hK, hh]
    exact Q.tower.mono Q.kernel_le subset_rfl
  · rw [hK, hh]
    have hKG : Q.coordinateGroup e hS hb ≤ S.G := Subgroup.map_subtype_le _
    obtain ⟨hpre, -, -, -, -, hpost⟩ := chain_append.1 Q.tower.chain
    -- The block partition is "all coordinates agree".
    have h0 : ∀ v ∈ S.dom, ∀ w ∈ S.dom, (fineEnd ⊥ Q.pre).r v w ↔ (Q.coordPart e 0).r v w := by
      intro v hv w hw
      rw [Q.fine_eq v hv w hw]
      constructor
      · intro h
        exact Or.inl ⟨hv, hw, fun j _ => by rw [h]⟩
      · rintro (⟨-, -, h⟩ | ⟨h, -⟩)
        · exact e.injective (funext fun j => h j (Nat.zero_le _))
        · exact absurd hv h
    -- The last coordinate partition holds the domain, as the coarse end of `top` does.
    have hr0 : 1 ≤ r := by omega
    have hfe : fineEnd (fineEnd ⊥ Q.pre) (Q.coordHier e) = Q.coordPart e r := by
      rw [Q.coordHier_eq, Q.fineEnd_coordFrom e _ 0 r hr0, zero_add]
    have htop : ∀ v ∈ S.dom, ∀ w ∈ S.dom, Q.top.part.r v w ↔ (Q.coordPart e r).r v w := by
      intro v hv w hw
      refine ⟨fun _ => Or.inl ⟨hv, hw, fun j hj => absurd j.2 (by omega)⟩,
        fun _ => Q.top_univ v hv w hw⟩
    have hDK : Invariant (Q.coordinateGroup e hS hb) S.dom := S.dom_inv.mono hKG
    refine ⟨?_, ?_, ?_⟩
    · rw [chain_append, chain_append, fineEnd_append, hfe]
      refine ⟨⟨hpre.mono hKG subset_rfl, ?_⟩, ?_⟩
      · rw [chain_congr h0, Q.coordHier_eq]
        exact Q.chain_coordFrom e hS hb 0 r (by omega)
      · rw [← chain_congr htop]
        exact hpost.mono hKG subset_rfl
    · have ht := Q.tower.top.mono hKG subset_rfl
      rw [fineEnd_append, fineEnd_cons] at ht
      rw [fineEnd_append, fineEnd_append, hfe]
      intro a ha w hw hwa
      exact (fineEnd_congr htop Q.post a ha w hw).1 (ht a ha w hw hwa)
    · obtain ⟨hcpre, hctop, hcpost⟩ := caps_append.1 Q.tower.caps
      rw [caps_append, caps_append, fineEnd_append, hfe]
      refine ⟨⟨hcpre.mono hKG subset_rfl, ?_⟩, ?_⟩
      · rw [caps_congr hDK h0, Q.coordHier_eq]
        refine Q.caps_coordFrom e hS hb (fun a ha => ?_) 0 r (by omega)
        exact (capAt_congr S.dom_inv h0).1 (hctop a ha)
      · rw [← caps_congr hDK htop]
        exact hcpost.mono hKG subset_rfl

end HierInv

/-! ### The exposed quotient, with the split of its interval -/

section Expose

/-- **The exposed quotient with its split** (the `State.expose` of HJ, with the content
`ExposedSplit`, which is what `hierQd` needs). -/
theorem exists_primitiveQuotient_split [Finite Ω] (S : State Ω C) (htr : S.Transitive)
    (hinv : S.HierInv) (h2 : ¬ UnivOn S.dom ⊥) :
    ∃ Q : PrimitiveQuotient S, Q.AboveCols ∧ Q.KeepsLevels ∧ ExposedSplit Q := by
  classical
  have htr' : ∀ v ∈ S.dom, ∀ w ∈ S.dom, w ∈ orb S.G v := fun v hv w hw => htr v hv w hw
  obtain ⟨pre, J, post, hl, hpre, hJ⟩ := exists_split htr' ⊥ S.hier hinv.top h2
  set f := fineEnd ⊥ pre with hfdef
  have hch := hinv.chain
  unfold State.HierInv at hinv
  rw [hl] at hch
  obtain ⟨hchpre, -, -, hJcount, -, -⟩ := chain_append.1 hch
  have hfinv := Chain.fineEnd_inv hchpre (bot_inv _ _)
  have hfc : IsCand S.G S.dom f f := ⟨hfinv, fun _ _ _ _ h => h, hpre⟩
  -- The candidates above the retained columns, if there is one; else all candidates.
  let p : Setoid Ω → Prop := fun M =>
    (∃ M₀, IsCand S.G S.dom f M₀ ∧ AboveCols S M₀) → AboveCols S M
  have hp_mono : ∀ M M', p M → (∀ v ∈ S.dom, ∀ w ∈ S.dom, M.r v w → M'.r v w) → p M' :=
    fun M M' hM hle hex c hc v hv w hw h => hle v hv w hw (hM hex c hc v hv w hw h)
  obtain ⟨M, hMc, hpM, hmax⟩ : ∃ M, IsCand S.G S.dom f M ∧ p M ∧
      ∀ M', IsCand S.G S.dom f M' → p M' → pairCount S.dom M' ≤ pairCount S.dom M := by
    by_cases hex : ∃ M₀, IsCand S.G S.dom f M₀ ∧ AboveCols S M₀
    · obtain ⟨M₀, h₀, hA⟩ := hex
      exact exists_maxCand_of p h₀ fun _ => hA
    · exact exists_maxCand_of p hfc fun h => absurd h hex
  -- No candidate is strictly coarser than `M`: it would relate more pairs.
  have hmaxM : ∀ M', IsCand S.G S.dom f M' → (∀ v ∈ S.dom, ∀ w ∈ S.dom, M.r v w → M'.r v w) →
      ∀ v ∈ S.dom, ∀ w ∈ S.dom, M'.r v w → M.r v w := by
    intro M' h1 h2
    have hle := hmax M' h1 (hp_mono M M' hpM h2)
    have hsub : {q : Ω × Ω | q.1 ∈ S.dom ∧ q.2 ∈ S.dom ∧ M.r q.1 q.2} ⊆
        {q : Ω × Ω | q.1 ∈ S.dom ∧ q.2 ∈ S.dom ∧ M'.r q.1 q.2} :=
      fun q ⟨hv, hw, h⟩ => ⟨hv, hw, h2 _ hv _ hw h⟩
    have heq := Set.eq_of_subset_of_ncard_le hsub hle (Set.toFinite _)
    intro v hv w hw h
    have : (v, w) ∈ {q : Ω × Ω | q.1 ∈ S.dom ∧ q.2 ∈ S.dom ∧ M.r q.1 q.2} := by
      rw [heq]; exact ⟨hv, hw, h⟩
    exact this.2.2
  -- `M` is above every comparable column partition coarser than `f`.
  have hcols : ∀ c, S.retainedCols = some c → ColsComparable S c →
      (∀ v ∈ S.dom, ∀ w ∈ S.dom, f.r v w → c.r v w) →
      ∀ v ∈ S.dom, ∀ w ∈ S.dom, c.r v w → M.r v w := by
    intro c hc hcc hfc' v hv w hw hvw
    have hcand : IsCand S.G S.dom f c := ⟨hcc.inv, hfc', hcc.proper⟩
    have hA : AboveCols S c := fun c' hc' => by
      rw [hc] at hc'
      cases hc'
      exact fun _ _ _ _ h => h
    exact hpM ⟨c, hcand, hA⟩ c hc v hv w hw hvw
  have hinv' : S.HierInv := hinv
  obtain ⟨Q, -, hab, hkl, c₁, hc₁d, hQpre, hQtop, hQpost⟩ :=
    exists_primitiveQuotient_of_cand S htr hinv' pre J post hl hJ M hMc hmaxM hcols
  refine ⟨Q, hab, hkl, ?_⟩
  -- the count `c₁ d ≤ ratio J`
  have hne : S.dom.Nonempty := by
    by_contra hemp
    apply h2
    intro v hv
    exact absurd ⟨v, hv⟩ hemp
  obtain ⟨a₀, ha₀⟩ := hne
  have hJall : classIn S.G S.dom J.part a₀ = S.dom := by
    ext w
    exact ⟨fun h => h.1, fun hw => ⟨hw, htr' a₀ ha₀ w hw, hJ a₀ ha₀ w hw⟩⟩
  have hcount : classCount (fineEnd ⊥ pre) S.dom ≤ J.ratio := by
    have := hJcount a₀ ha₀
    rwa [hJall] at this
  have hc₁cd : c₁ * Q.d ≤ J.ratio := by
    rw [hc₁d]; exact hcount
  have hc₁1 : 1 ≤ c₁ := by
    have hdiv : 0 < c₁ * Q.d := by
      rw [hc₁d]
      exact one_le_classCount _ ⟨a₀, ha₀⟩
    rcases Nat.eq_zero_or_pos c₁ with h | h
    · simp [h] at hdiv
    · exact h
  refine ⟨⟨pre, post, J, c₁, hl, hc₁1, hc₁cd, hQpost, ?_, ?_⟩⟩
  · rw [hQtop]; exact min_le_left _ _
  · by_cases hc1 : c₁ = 1
    · exact Or.inl ⟨hc1, by rw [hQpre, if_pos hc1]⟩
    · refine Or.inr ⟨⟨M, c₁, min J.cap c₁, J.origin⟩, by rw [hQpre, if_neg hc1], rfl, min_le_left _ _⟩

/-- The exposed quotient with the split (`exists_primitiveQuotient_split`). -/
noncomputable def exposeS [Finite Ω] (S : State Ω C) (htr : S.Transitive)
    (hinv : S.HierInv) (h2 : ¬ UnivOn S.dom ⊥) : PrimitiveQuotient S :=
  Classical.choose (exists_primitiveQuotient_split S htr hinv h2)

theorem exposeS_spec [Finite Ω] (S : State Ω C) (htr : S.Transitive)
    (hinv : S.HierInv) (h2 : ¬ UnivOn S.dom ⊥) :
    (exposeS S htr hinv h2).AboveCols ∧ (exposeS S htr hinv h2).KeepsLevels ∧
      ExposedSplit (exposeS S htr hinv h2) :=
  Classical.choose_spec (exists_primitiveQuotient_split S htr hinv h2)

end Expose

/-! ### The subroutine data of the recursion `M.Run` -/

/-- The case data of a transitive `Continue` state above the threshold, off the floor: the
exposed primitive quotient. `exposeS` provides one (`M.contCase`). -/
structure ContData (S : State Ω C) where
  Q : PrimitiveQuotient S
  hkc : Q.KillsCols
  hkl : Q.KeepsLevels
  hxs : ExposedSplit Q

/-- The case data of a transitive `GiantStep` state, as HJ's `GI.Algorithm.GiantCase`, with one new
requirement on an aggregation round: its fresh `Solve` calls are on `Γ̂_D` groups. -/
inductive GiantCase (P : Params) (D : ℕ) {Ω C : Type} (S : State Ω C) (L : SuppliedLabels S) : Type 1
  | terminal (hrow : RowCase P.α S L.toGiantLabels) (I : RowTerminal P S L.toGiantLabels)
  | columns (hrow : RowCase P.α S L.toGiantLabels) (I : ColumnStep S L.toGiantLabels)
      (hinv : HierInv S.G S.dom I.hier')
  | aggregate (hnot : ¬ RowCase P.α S L.toGiantLabels) (I : Aggregation P S L.toGiantLabels)
      (hsel : I.sel.val = L.sel.val) (hcon : I.con = L.con)
      (fin : I.script.CallsExact fun {Ω' _} _ _ => Finite Ω')
      (cls : I.script.CallsExact fun {Ω' _} m T => m = .solve → GammaHat D T.G)

/-- **The subroutine data of `M.Run`**, for the class parameter `D`. -/
structure Supply (P : Params) (D : ℕ) : Type 1 where
  cont : ∀ {Ω C : Type} [Finite Ω] (S : State Ω C), S.HierInv → P.N₀ < S.N → S.size ≤ S.N →
    S.Transitive → (S.N : ℝ) ^ P.γ < S.size → ¬ S.FloorEntered → ContData S
  giant : ∀ {Ω C : Type} [Finite Ω] (S : State Ω C), S.HierInv → P.N₀ < S.N → S.size ≤ S.N →
    S.Transitive → (S.N : ℝ) ^ P.γ < S.size → (L : SuppliedLabels S) → P.q₀ < L.q →
    GammaHat D S.G → GiantCase P D S L

section Cont

/-- The continuation data is built from the exposure, unconditionally. -/
noncomputable def contData (hP : P.Terminating) (hγ : 0 ≤ P.γ) [Finite Ω] (S : State Ω C)
    (hinv : S.HierInv) (hN : P.N₀ < S.N) (htr : S.Transitive) (hs : (S.N : ℝ) ^ P.γ < S.size) :
    ContData S :=
  let h2 := not_univOn_bot_of_large hP hγ hN hs
  ⟨exposeS S htr hinv h2,
    (exposeS S htr hinv h2).killsCols_of (exposeS_spec S htr hinv h2).1 hinv,
    (exposeS_spec S htr hinv h2).2.1, (exposeS_spec S htr hinv h2).2.2⟩

end Cont

/-! ### Scripts -/

/-- Transport a run along an equality of answers. -/
theorem Run.exists_cast {cσ : ℝ} {D : ℕ} {m : Mode} {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A B : Set (Perm Ω)} (h : A = B) {r : Run P m S L A}
    (hr : r.RootsOK cσ D) : ∃ r' : Run P m S L B, r'.RootsOK cσ D := by
  subst h; exact ⟨r, hr⟩

/-- A run with its root bounds. -/
theorem Run.rootsOK_answer {cσ : ℝ} {D : ℕ} {m : Mode} {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)} (r : Run P m S L A) (h : r.RootsOK cσ D) :
    ∃ r' : Run P m S L S.answer, r'.RootsOK cσ D := by
  have hA : A = S.answer := r.exact
  subst hA
  exact ⟨r, h⟩

/-- A script runs, with root bounds and its exact value, when each of its calls along the exact
answers has such a run, and its `Solve` calls are in `Γ̂_D`. -/
theorem Exec.exists_exact {cσ : ℝ} {D : ℕ} {α : Type} :
    ∀ (s : Script α), s.CallsExact (fun {Ω' _} m T => (m = .solve → Finite Ω' ∧ GammaHat D T.G) ∧
        ∃ r : Run P m T none T.answer, r.RootsOK cσ D) →
      ∃ e : Exec P s s.evalExact, e.RootsOK cσ D
  | .done a, _ => ⟨Exec.done a, trivial⟩
  | .ask _ T k, h => by
    obtain ⟨⟨hs, r, hr⟩, hk⟩ := h
    obtain ⟨e, he⟩ := Exec.exists_exact (k T.answer) hk
    exact ⟨Exec.ask r e, hs, hr, he⟩


/-! ### The row terminal stays in the class -/

section RowClass

variable {D : ℕ} {S : State Ω C} {L : GiantLabels S}

/-- The groups of the row terminal's fresh calls are in `Γ̂_D`: they are sections of the
domain group. -/
theorem rowTerminal_groups [Finite Ω] (hg : GammaHat D S.G) (I : RowTerminal P S L) :
    GammaHat D I.Hb ∧ GammaHat D I.Nb := by
  classical
  haveI : Fintype I.B := I.fin
  have hdom : GammaHat D S.domGroup := GammaHat.range S.domHom hg
  have hcomap : GammaHat D ((S.domGroup).comap (cleanRowPerm I.e)) := by
    let f : ((S.domGroup).comap (cleanRowPerm I.e)) →* S.domGroup :=
      ((cleanRowPerm I.e).comp (Subgroup.subtype _)).codRestrict _ (fun g => g.2)
    refine hdom.of_injective f ?_
    intro a b hab
    apply Subtype.ext
    funext i
    ext b'
    have h := congrArg (fun z : S.domGroup => (z : Perm S.dom) (I.e (b', i))) hab
    simp only [f, MonoidHom.codRestrict_apply, MonoidHom.comp_apply, Subgroup.subtype_apply,
      cleanRowPerm_apply] at h
    have h2 := I.e.injective h
    exact congrArg Prod.fst h2
  have hHb : GammaHat D ((S.domGroup.comap (cleanRowPerm I.e)).map (rowEval I.i0)) :=
    hcomap.of_surjective ((rowEval I.i0).subgroupMap (S.domGroup.comap (cleanRowPerm I.e)))
      ((rowEval I.i0).subgroupMap_surjective (S.domGroup.comap (cleanRowPerm I.e)))
  have hHb' : GammaHat D I.Hb := hHb
  exact ⟨hHb', GammaHat.of_le (Ω := I.B) hHb' I.Nb_le⟩

/-- The fresh calls of the row terminal are in the class. -/
theorem rowTerminal_calls_class [Finite Ω] (hg : GammaHat D S.G) (I : RowTerminal P S L) :
    I.script.CallsExact fun {Ω' _} m T => m = .solve → GammaHat D T.G := by
  obtain ⟨hHb, hNb⟩ := rowTerminal_groups hg I
  refine Script.callsExact_bind _ _ (Script.callsExact_table _ _ (fun ac _ => ?_) _) ?_
  · exact hNb
  refine Script.callsExact_bind _ _ (Script.callsExact_table _ _ (fun ij _ => ?_) _) trivial
  exact hHb

/-- The configuration calls of HJ's aggregation (`pairState`, the group `Sym(n)` acting diagonally
on pairs) are in `Γ̂_D` as soon as `n ≤ D`. This is the case the field `GiantCase.aggregate.cls`
is meant for, with `n ≤ q ≤ D`. -/
theorem pairState_class {C' : Type} {n : ℕ} (hn : n ≤ D) (x y : Fin n × Fin n → C') :
    GammaHat D (pairState n x y).G := by
  have h : GammaHat D (Perm (Fin n)) :=
    gammaHat_perm (MonoidHom.id _) Function.injective_id (by simpa using hn)
  exact GammaHat.range (diagHom n) h

end RowClass

/-! ### Existence of runs -/

section Exists

variable {D : ℕ} {cσ : ℝ}

/-- What a call needs in the recursion: HJ's conditions (`GI.Algorithm.GoodL`), the class `Γ̂_D`. -/
def GoodL (P : Params) (D : ℕ) {Ω C : Type} : (m : Mode) → (S : State Ω C) →
    Option (SuppliedLabels S) → Prop
  | .solve, S, L => L = none ∧ GammaHat D S.G
  | .cont, S, L => L = none ∧ P.N₀ < S.N ∧ S.size ≤ S.N ∧ S.HierInv ∧ GammaHat D S.G
  | .giant, S, L => P.N₀ < S.N ∧ S.size ≤ S.N ∧ S.Transitive ∧ (S.N : ℝ) ^ P.γ < S.size ∧
      S.HierInv ∧ GammaHat D S.G ∧ ∃ L' : SuppliedLabels S, L = some L' ∧ P.q₀ < L'.q

/-- **The recursion terminates and has root bounds, for `Γ̂_D` states.** -/
theorem exists_run_aux (hP : P.Terminating)
    (hσ : ∀ (V : Type) [Fintype V] (H : Subgroup (Perm V)) (v : V),
      (GI.sigma P.κ v H : ℝ) ≤ cσ * Real.log (Fintype.card V))
    (hcσ : 0 ≤ cσ) (Su : Supply P D) :
    ∀ k, ∀ {Ω C : Type} [Finite Ω] (m : Mode) (S : State Ω C) (L : Option (SuppliedLabels S)),
      GoodL P D m S L → GI.Algorithm.measure P m S = k → ∃ r : Run P m S L S.answer, r.RootsOK cσ D := by
  intro k
  induction k using MLt_wf.induction with
  | _ k ih =>
  intro Ω C _ m S L hgood hk
  subst hk
  have IH : ∀ {Ω' C' : Type} [Finite Ω'] (m' : Mode) (T : State Ω' C')
      (L' : Option (SuppliedLabels T)), GoodL P D m' T L' →
      MLt (GI.Algorithm.measure P m' T) (GI.Algorithm.measure P m S) → ∃ r : Run P m' T L' T.answer, r.RootsOK cσ D :=
    fun m' T L' hg hlt => ih _ hlt m' T L' hg rfl
  have hκ := hP.κ_five
  cases m with
  | solve =>
    obtain ⟨rfl, hgS⟩ := hgood
    by_cases hs : S.size ≤ P.N₀
    · exact ⟨Run.direct S hs, trivial⟩
    · push Not at hs
      have hne : S.dom.Nonempty := by
        have h0 : 0 < Nat.card S.dom := by change 0 < S.size; omega
        obtain ⟨⟨v, hv⟩⟩ := Nat.card_pos_iff.1 h0 |>.1
        exact ⟨v, hv⟩
      obtain ⟨M, hT, hH⟩ := exists_orbitHier S.domGroup (D := Set.univ) (fun _ _ _ => by simp) (by
        obtain ⟨v, hv⟩ := hne
        exact ⟨⟨v, hv⟩, trivial⟩)
      let S' : State S.dom C := S.freshOn (orbitHier S.domGroup M)
      have hS' : S.FreshOf S' := S.freshOn_freshOf hT hH
      have hN' : S'.N = S.size := rfl
      have hsz' : S'.size = S.size := hS'.size_eq
      have hgS' : GammaHat D S'.G := by
        rw [hS'.G_eq]; exact GammaHat.range S.domHom hgS
      have hrb := GI.Paper.freshOf_rootBounds hσ hcσ hs hS'
      obtain ⟨r, hr⟩ := IH .cont S' none ⟨rfl, show P.N₀ < S'.N from hN' ▸ hs, by omega,
        hS'.hierInv, hgS'⟩ (by
        rw [mlt_iff]
        simp only [GI.Algorithm.measure, major, solveInd]
        omega)
      exact Run.rootsOK_answer (Run.fresh hs hS' r) ⟨hrb.1, hrb.2, hr⟩
  | cont =>
    obtain ⟨rfl, hN, hsN, hhi, hgS⟩ := hgood
    have hN2 : 2 ≤ S.N := by have := hP.N₀_pos; omega
    by_cases hth : (S.size : ℝ) ≤ (S.N : ℝ) ^ P.γ
    · have hlt := size_lt_of_rpow hN2 hP.γ_lt hth
      obtain ⟨r, hr⟩ := IH .solve S none ⟨rfl, hgS⟩ (by mlt_tac)
      exact ⟨Run.threshold hth r, hr⟩
    push Not at hth
    have hpos := size_pos_of_large hth
    by_cases htr : S.Transitive
    swap
    · -- The orbit chain.
      obtain ⟨D₁, hD₁⟩ := exists_largestOrbit S (dom_nonempty_of_large hth)
      let S₁ := S.inherit S.G D₁ hD₁.invariant S.x S.y
      have hsz₁ : S₁.size < S.size := LargestOrbit.size_lt htr hD₁ (State.inherit_dom _ _ _ _ _ _)
      have hN₁ : S₁.N = S.N := State.inherit_N _ _ _ _ _ _
      have hinv₁ : S₁.HierInv := by
        show HierInv S₁.G S₁.dom S₁.hier
        rw [State.inherit_G, State.inherit_dom, State.inherit_hier]
        exact HierInv.mono hhi le_rfl hD₁.subset
      have hg₁ : GammaHat D S₁.G := by
        show GammaHat D (S.inherit S.G D₁ hD₁.invariant S.x S.y).G
        rw [State.inherit_G]; exact hgS
      obtain ⟨r₁, hr₁⟩ := IH .cont S₁ none ⟨rfl, hN₁ ▸ hN, by omega, hinv₁, hg₁⟩ (by mlt_tac)
      have hb₁ : S₁.book = S.orbitBook D₁ :=
        S.inherit_book hD₁.invariant hD₁.subset hD₁.nonempty _ _
      by_cases hA : S₁.answer = ∅
      · obtain ⟨r₁', hr₁'⟩ := Run.exists_cast hA hr₁
        exact Run.rootsOK_answer (Run.orbitStop hth htr hD₁ (S.inherit_inst _ _ _ _ _) hN₁
          (State.inherit_hier _ _ _ _ _ _) hb₁ r₁') hr₁'
      · obtain ⟨t, ht⟩ := Set.nonempty_iff_ne_empty.2 hA
        have hinv : Invariant (autGroup S.G D₁ hD₁.invariant S.x) (S.dom \ D₁) :=
          (S.dom_inv.diff hD₁.invariant).mono (autGroup_le _ _ _ _)
        let S₂ := S.resetChild (autGroup S.G D₁ hD₁.invariant S.x) (S.dom \ D₁) hinv S.x (S.y ∘ t)
        have hsz := orbitChain_sizes (S₁ := S₁) (S₂ := S₂) htr hD₁
          (State.inherit_dom _ _ _ _ _ _) rfl
        have hN₂ : S₂.N = S.N := rfl
        have hinv₂ : S₂.HierInv := by
          show HierInv (autGroup S.G D₁ hD₁.invariant S.x) (S.dom \ D₁) S.hier
          exact HierInv.mono hhi (autGroup_le _ _ _ _) Set.diff_subset
        have hg₂ : GammaHat D S₂.G :=
          GammaHat.of_le hgS (autGroup_le S.G D₁ hD₁.invariant S.x)
        obtain ⟨r₂, hr₂⟩ := IH .cont S₂ none ⟨rfl, hN₂ ▸ hN, by omega, hinv₂, hg₂⟩ (by mlt_tac)
        exact Run.rootsOK_answer (Run.orbitChain hth htr hD₁ (S.inherit_inst _ _ _ _ _) hN₁
          (State.inherit_hier _ _ _ _ _ _) hb₁ r₁ t ht (S.resetChild_inst _ _ _ _ _) hN₂
          rfl rfl r₂) ⟨hr₁, hr₂⟩
    have htr1 := trInd_of S htr
    by_cases hfl : S.FloorEntered
    · let S' : State Ω C := S.floorCleared
      have hfl1 : flInd S = 1 := by simp [flInd, hfl.1]
      have hfl0 : flInd S' = 0 := by simp [flInd, S', State.floorCleared]
      have htr' : trInd S' = 1 := trInd_of S' htr
      have hh := S.h_le
      have h1 : S'.N = S.N := rfl
      have h2 : S'.size = S.size := rfl
      have h3 : S'.sigma P.κ = S.sigma P.κ := rfl
      have h4 : rhoNat S'.hier = rhoNat S.hier := rfl
      have h5 : S'.h = 2 := rfl
      obtain ⟨r, hr⟩ := IH .cont S' none ⟨rfl, hN, hsN, hhi, hgS⟩ (by mlt_tac)
      exact ⟨Run.floorReset (S' := S') hth htr hfl ⟨rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl r, hr⟩
    -- a dispatcher step
    have hdispatch : ∀ I : DispatchStep P S, ∃ r : Run P .cont S none S.answer, r.RootsOK cσ D := by
      intro I
      let child : Fin I.n → State Ω C := fun j =>
        S.restrict I.K I.K_le S.x (S.y ∘ I.τ j) I.hier'
      have hdrop : ∀ j, MLt (GI.Algorithm.measure P .cont (child j)) (GI.Algorithm.measure P .cont S) := by
        intro j
        have hσ : (child j).sigma P.κ ≤ S.sigma P.κ := State.sigma_le_of hκ I.K_le le_rfl
        have htrj := trInd_le (child j)
        have hsz : (child j).size = S.size := rfl
        have hNj : (child j).N = S.N := rfl
        rw [mlt_iff]
        simp only [GI.Algorithm.measure, major, solveInd, stageInd, true_and, lt_self_iff_false, false_or]
        cases hkind : I.kind with
        | enumeration d =>
          have hf := I.facts
          rw [hkind] at hf
          obtain ⟨hd2, -, -, hdorb⟩ := hf
          have hnt : ¬ (child j).Transitive := by
            intro htj
            obtain ⟨v, hv⟩ := dom_nonempty_of_large hth
            have h1 := size_le_orb htj hv
            have h2 := hdorb v hv
            change S.size ≤ Nat.card (orb I.K v) at h1
            have : 2 * S.size ≤ S.size :=
              (Nat.mul_le_mul hd2 h1).trans h2
            omega
          have := trInd_of_not _ hnt
          omega
        | product r =>
          have hf := I.facts
          rw [hkind] at hf
          obtain ⟨hr2, -, -, hρ⟩ := hf
          have hρ' : rhoNat I.hier' + 1 ≤ rhoNat S.hier := by
            have h1 : (rhoNat I.hier' : ℝ) + 1 ≤ rhoNat S.hier := by
              rw [rhoNat_cast, rhoNat_cast]
              have : (2 : ℝ) ≤ r := by exact_mod_cast hr2
              linarith
            exact_mod_cast h1
          change rhoNat I.hier' + 1 ≤ rhoNat S.hier at hρ'
          have : rhoNat (child j).hier = rhoNat I.hier' := rfl
          omega
      have hK := I.K_le
      have r : ∀ j, ∃ r : Run P .cont (child j) none (child j).answer, r.RootsOK cσ D :=
        fun j => IH .cont (child j) none ⟨rfl, hN, hsN, I.hierInv,
          GammaHat.of_le hgS hK⟩ (hdrop j)
      have hbk : ∀ j, (child j).book = S.book := fun j => by
        simp only [child, State.book, State.restrict_rows_of _ _ _ _ _ _ I.keeps,
          State.restrict_floor_of _ _ _ _ _ _ I.keeps, State.restrict_h_of _ _ _ _ _ _ I.keeps]
      choose r' hr' using r
      exact Run.rootsOK_answer (Run.dispatch hth htr hfl I child (fun j => ⟨rfl, rfl, rfl, rfl⟩)
        (fun _ => rfl) (fun _ => rfl) hbk _ r') hr'
    -- the normalization
    have hnormalize : ∀ (Q : PrimitiveQuotient S) (hxs : ExposedSplit Q) (c : Q.NormChoice)
        (hq : P.q₀ < (Q.normalizationOf c).q) (hkc : Q.KillsCols) (hkl : Q.KeepsLevels)
        (hst : Structural P Q),
        ∃ r : Run P .cont S none S.answer, r.RootsOK cσ D := by
      intro Q hxs c hq hkc hkl hst
      let N := Q.normAboveOf c htr hq hkc hkl
      let I := N.I
      let child : Fin I.k → State Ω C := fun j => N.child j
      have hsm : Structural P Q ∧ ExposedSplit Q := ⟨hst, hxs⟩
      have hρI : rhoNat I.hier' ≤ rhoNat S.hier := by
        have h1 : (rhoNat I.hier' : ℝ) ≤ rhoNat S.hier := by
          rw [rhoNat_cast, rhoNat_cast]; exact I.rho_le
        exact_mod_cast h1
      have hdropI : rhoNat I.hier' < rhoNat S.hier ∨ capSum I.hier' ≤ capSum S.hier := by
        rcases I.drop with h | h
        · left
          have h1 : (rhoNat I.hier' : ℝ) < rhoNat S.hier := by
            rw [rhoNat_cast, rhoNat_cast]; exact h
          exact_mod_cast h1
        · exact Or.inr h
      have hσ : ∀ j, (child j).sigma P.κ ≤ S.sigma P.κ := fun j =>
        State.sigma_le_of hκ I.le le_rfl
      have hgchild : ∀ j, GammaHat D (child j).G := fun j => GammaHat.of_le hgS I.le
      by_cases hT' : ∀ v ∈ S.dom, ∀ w ∈ S.dom, ∃ g ∈ I.G', g v = w
      · have hdrop : ∀ j, MLt (GI.Algorithm.measure P .giant (child j)) (GI.Algorithm.measure P .cont S) := by
          intro j
          have htrj : trInd (child j) = 1 := trInd_of _ hT'
          have hσj := hσ j
          rw [mlt_iff]
          simp only [GI.Algorithm.measure, major, solveInd, stageInd, true_and, lt_self_iff_false, false_or]
          have h1 : (child j).size = S.size := rfl
          have hNj : (child j).N = S.N := rfl
          have h2 : rhoNat (child j).hier = rhoNat I.hier' := rfl
          have hfl : (child j).floor = S.floor := State.restrict_floor_of _ _ _ _ _ _ N.keeps
          have h3 : flInd (child j) = flInd S := by simp only [flInd, hfl]
          have h4 : (child j).h = S.h := State.restrict_h_of _ _ _ _ _ _ N.keeps
          have h5 : capSum (child j).hier = capSum I.hier' := rfl
          omega
        have r : ∀ j, ∃ r : Run P .giant (child j) (some (N.childLabels j)) (child j).answer,
            r.RootsOK cσ D :=
          fun j => IH .giant (child j) _ ⟨hN, hsN, hT', hth, N.tower, hgchild j, N.childLabels j,
            rfl, N.q_large⟩ (hdrop j)
        choose r' hr' using r
        exact Run.rootsOK_answer (Run.normalize hth htr hfl Q hsm c hq hkc hkl N rfl .giant
          (fun _ => Or.inr ⟨rfl, hT'⟩) _ r') hr'
      · have hdrop : ∀ j, MLt (GI.Algorithm.measure P .cont (child j)) (GI.Algorithm.measure P .cont S) := by
          intro j
          have htrj : trInd (child j) = 0 := trInd_of_not _ hT'
          rw [mlt_iff]
          simp only [GI.Algorithm.measure, major, solveInd, stageInd, true_and, lt_self_iff_false, false_or]
          have h1 : (child j).size = S.size := rfl
          have hNj : (child j).N = S.N := rfl
          omega
        have r : ∀ j, ∃ r : Run P .cont (child j) none (child j).answer, r.RootsOK cσ D :=
          fun j => IH .cont (child j) none ⟨rfl, hN, hsN, N.tower, hgchild j⟩ (hdrop j)
        choose r' hr' using r
        exact Run.rootsOK_answer (Run.normalize hth htr hfl Q hsm c hq hkc hkl N rfl .cont
          (fun _ => Or.inl ⟨rfl, hT'⟩) _ r') hr'
    -- `(M′)`: the structural test
    obtain ⟨Q, hkc, hkl, hxs⟩ := Su.cont S hhi hN hsN htr hth hfl
    by_cases hst : Structural P Q
    · obtain ⟨m, k, r, e, hS, h2k, hqm, hlog⟩ := id hst
      have hdk := Q.card_kset_pow e
      have hr1 : 1 ≤ r := by
        by_contra h0
        have h0' : r = 0 := by omega
        rw [h0', pow_zero] at hdk
        have := Q.two_le
        omega
      by_cases hr2 : r = 1
      · subst hr2
        -- a single factor: normalize, with the structural witness
        let cc : Q.NormChoice :=
          ⟨m, k, e, hS, (CitedInstances.exists_coset_cover S.G (Q.normGroup e hS)).choose,
            (CitedInstances.exists_coset_cover S.G (Q.normGroup e hS)).choose_spec.1,
            (CitedInstances.exists_coset_cover S.G (Q.normGroup e hS)).choose_spec.2⟩
        exact hnormalize Q hxs cc hqm hkc hkl hst
      · -- a product with `r ≥ 2`
        have hr' : 2 ≤ r := by omega
        let c' : Q.ProductChoice := ⟨m, k, r, e, hS, hr'⟩
        exact hdispatch (.product Q ‹_› c' (CosetReps.default _ _)
          ⟨Q.productRed_keeps P hkc hkl c', hxs⟩)
    · exact hdispatch (.enumeration Q ‹_› htr ⟨hst, hxs⟩ (CosetReps.default _ _)
        (Q.kernel_keeps hkc hkl))
  | giant =>
    obtain ⟨hN, hsN, htr, hth, hhi, hgS, L, rfl, hLq⟩ := hgood
    have hN2 : 2 ≤ S.N := by have := hP.N₀_pos; omega
    have hpos := size_pos_of_large hth
    have htr1 := trInd_of S htr
    match Su.giant S hhi hN hsN htr hth L hLq hgS with
    | .terminal hrow I =>
      have hcls := rowTerminal_calls_class hgS I
      have hcalls := Script.CallsExact.and (Script.CallsExact.and I.calls I.calls_finite) hcls
      have he := Exec.exists_exact (P := P) (cσ := cσ) (D := D) I.script (hcalls.mono fun m' T hT => by
        obtain ⟨⟨⟨rfl, hsz⟩, hfinT⟩, hclT⟩ := hT
        have hlt := size_lt_of_rpow hN2 (by linarith [hP.α_pos]) hsz
        exact ⟨fun _ => ⟨hfinT, hclT rfl⟩, IH .solve T none ⟨rfl, hclT rfl⟩ (by mlt_tac)⟩)
      obtain ⟨e, he⟩ := he
      exact Run.rootsOK_answer (Run.rowTerminal hth htr L hrow I e) he
    | .columns hrow I hinv' =>
      obtain ⟨hh1, hcnt⟩ := column_step_counter hP.third_lt_α S htr hsN L hrow I
      let S' : State Ω C := ⟨S.G, S.dom, S.dom_inv, S.x, S.y, dropTriv I.hier',
        some ⟨L.q, I.rowPart, some I.cols⟩, S.floor, S.h - 1, by have := S.h_le; omega, S.N,
        hcnt, CarrierOK.dropTriv S.dom_inv htr hinv' I.carrierOK⟩
      have hρ : rhoNat (dropTriv I.hier') ≤ rhoNat S.hier := by
        have h1 : (rhoNat (dropTriv I.hier') : ℝ) ≤ rhoNat S.hier := by
          rw [rhoNat_cast, rhoNat_cast, hierRho_dropTriv]; exact I.rho_le
        exact_mod_cast h1
      have htr' : trInd S' = 1 := trInd_of S' htr
      obtain ⟨r, hr⟩ := IH .cont S' none ⟨rfl, hN, hsN, HierInv.dropTriv S.dom_inv hinv', hgS⟩ (by
        rw [mlt_iff]; simp only [GI.Algorithm.measure, major, solveInd, stageInd, true_and, lt_self_iff_false, false_or]
        have h1 : S'.size = S.size := rfl
        have hNj : S'.N = S.N := rfl
        have h2 : S'.sigma P.κ = S.sigma P.κ := rfl
        have h3 : flInd S' = flInd S := rfl
        have h4 : S'.h = S.h - 1 := rfl
        have h5 : rhoNat S'.hier = rhoNat (dropTriv I.hier') := rfl
        omega)
      exact ⟨Run.rowColumns (S' := S') hth htr L hrow I ⟨rfl, rfl, rfl, rfl⟩ rfl hh1 rfl rfl rfl r, hr⟩
    | .aggregate hnot I hsel hcon hfin hcls =>
      have hq₀ : P.q₀ ≤ L.q := hLq.le
      have hcalls := Script.CallsExact.and (Script.CallsExact.and I.calls hfin) hcls
      have he := Exec.exists_exact (P := P) (cσ := cσ) (D := D) I.script (hcalls.mono fun m' T hT => by
        obtain ⟨⟨hT, hfinT⟩, hclT⟩ := hT
        rcases hT with ⟨rfl, hsz⟩ | ⟨rfl, e, hch⟩
        · have hlt := size_lt_of_rpow hN2 hP.two_α_lt hsz
          exact ⟨fun _ => ⟨hfinT, hclT rfl⟩, IH .solve T none ⟨rfl, hclT rfl⟩ (by mlt_tac)⟩
        · subst e
          replace hch : ChargedCall P S T := hch
          have hTN : T.N = S.N := hch.N_eq
          have hsz : T.size ≤ S.size := size_le_of_subset hch.sub
          have key : T.size < S.size ∨ trInd T = 0 ∨ T.sigma P.κ < S.sigma P.κ := by
            by_cases hlt : T.size < S.size
            · exact Or.inl hlt
            by_cases htrT : T.Transitive
            · right; right
              have heq : T.size = S.size := by omega
              obtain ⟨v, hv⟩ : T.dom.Nonempty := by
                have : 0 < T.size := heq ▸ hpos
                exact Set.nonempty_coe_sort.1 (Nat.card_pos_iff.1 this).1
              rcases hch.types v hv with horb | hσ
              · exfalso
                have h1 := size_le_orb htrT hv
                have h2 : (T.size : ℝ) ≤ P.θ * S.size :=
                  (by exact_mod_cast h1 : (T.size : ℝ) ≤ (Nat.card (orb T.G v) : ℝ)).trans horb
                rw [heq] at h2
                have h3 : (0 : ℝ) < S.size := by exact_mod_cast hpos
                nlinarith [hP.θ_lt]
              · rw [State.sigma_eq_point P.κ htrT hv]
                omega
            · exact Or.inr (Or.inl (trInd_of_not _ htrT))
          have htrT := trInd_le T
          have hinvT : T.HierInv := by
            show HierInv T.G T.dom T.hier
            rw [hch.hier_eq]
            exact HierInv.mono hhi hch.le hch.sub
          have hgT : GammaHat D T.G := GammaHat.of_le hgS hch.le
          exact ⟨fun h => absurd h (by decide),
            IH .cont T none ⟨rfl, show P.N₀ < T.N by omega, by omega, hinvT, hgT⟩ (by mlt_tac)⟩)
      obtain ⟨e, he⟩ := he
      let b := I.script.evalExact
      let child : Fin b.overs.length → State Ω C := fun j =>
        S.restrict (b.overs.get j).2 (I.covers.overs_le j) S.x
          (S.y ∘ (b.overs.get j).1) (I.newHier (b.overs.get j))
      have hdrop : ∀ j, MLt (GI.Algorithm.measure P .cont (child j)) (GI.Algorithm.measure P .giant S) := by
        intro j
        have hcu := I.capUpdate (b.overs.get j) (List.get_mem _ _)
        have hσ : (child j).sigma P.κ ≤ S.sigma P.κ :=
          State.sigma_le_of hκ (I.covers.overs_le j) le_rfl
        have hρ : rhoNat (I.newHier (b.overs.get j)) = rhoNat S.hier := by
          have h1 : (rhoNat (I.newHier (b.overs.get j)) : ℝ) = rhoNat S.hier := by
            rw [rhoNat_cast, rhoNat_cast]; exact CapUpdate.rho_eq hcu
          exact_mod_cast h1
        have hc := hcu.capSum_lt hP.β_lt (hP.q₀_pos.trans hq₀)
        have htrj := trInd_le (child j)
        rw [mlt_iff]
        simp only [GI.Algorithm.measure, major, solveInd, stageInd, true_and, lt_self_iff_false, false_or]
        have h1 : (child j).size = S.size := rfl
        have hNj : (child j).N = S.N := rfl
        have h2 : rhoNat (child j).hier = rhoNat (I.newHier (b.overs.get j)) := rfl
        have hk := I.overs_keep (b.overs.get j) (List.get_mem _ _)
        have hfl : (child j).floor = S.floor := State.restrict_floor_of _ _ _ _ _ _ hk
        have h3 : flInd (child j) = flInd S := by simp only [flInd, hfl]
        have h4 : (child j).h = S.h := State.restrict_h_of _ _ _ _ _ _ hk
        have h5 : capSum (child j).hier = capSum (I.newHier (b.overs.get j)) := rfl
        omega
      have hrc : ∀ j, ∃ r : Run P .cont (child j) none (child j).answer, r.RootsOK cσ D :=
        fun j => IH .cont (child j) none ⟨rfl, hN, hsN,
          I.child_hierInv hsel hhi (List.get_mem _ _),
          GammaHat.of_le hgS (I.covers.overs_le j)⟩ (hdrop j)
      choose r' hr' using hrc
      have hbk : ∀ j, (child j).book = S.book := fun j => by
        have hk := I.overs_keep (b.overs.get j) (List.get_mem _ _)
        simp only [State.book, child, State.restrict_rows_of _ _ _ _ _ _ hk,
          State.restrict_floor_of _ _ _ _ _ _ hk, State.restrict_h_of _ _ _ _ _ _ hk]
      exact Run.rootsOK_answer (Run.aggregate hth htr L hnot hq₀ I hsel hcon b e
        (fun j => (b.overs.get j).1)
        (fun j => ⟨1, (b.overs.get j).2.one_mem, mul_one _⟩) child (fun j => ⟨rfl, rfl, rfl, rfl⟩)
        (fun _ => rfl) (fun _ => rfl) hbk _ r') ⟨he, hr'⟩

/-- **Every `Γ̂_D` state has a run of `Solve`, with the exact answer and root bounds.** -/
theorem exists_run_solve (hP : P.Terminating)
    (hσ : ∀ (V : Type) [Fintype V] (H : Subgroup (Perm V)) (v : V),
      (GI.sigma P.κ v H : ℝ) ≤ cσ * Real.log (Fintype.card V))
    (hcσ : 0 ≤ cσ) (Su : Supply P D) {Ω C : Type} [Finite Ω] (S : State Ω C)
    (hg : GammaHat D S.G) :
    ∃ r : Run P .solve S none S.answer, r.RootsOK cσ D :=
  exists_run_aux hP hσ hcσ Su _ .solve S none ⟨rfl, hg⟩ rfl

end Exists

end GI.DegreeD.M
