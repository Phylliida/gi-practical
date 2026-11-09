import DegreeD.M.Closure

/-!
# The clipped cap moment `Q_d`

`hierQd D l = Σ_i log d_i · log max(min(c_i, D), 2)` is the cap moment of Theorem R*, an
analysis-only function of the hierarchy (the caps the algorithm stores are HJ's): with `D = max(d,6)`,
the root value is at most `(log s)(log D) ≤ Λ log s` (`RootBoundsL`), while HJ's `Q` can be `(log s)²`.

This file proves the row clauses (`qClause`) of `phaseTreeOn_hypL` for `Qf = hierQd D` in
the regime `max(d,6) ≤ N^α`, where no row event occurs (`q ≤ d ≤ N^α` contradicts the row case
`q > N^α`): each child has clipped moment at most the parent's, and an aggregation continuation
drops it by `c_β log q` (`CapUpdate.Qd_drop`). The one input beyond the facts of the runs is that
exposure splits one interval (`ExposedSplit`).
-/

namespace GI.DegreeD.M

open Equiv Equiv.Perm GI.Algorithm GI.Paper
open scoped Pointwise

variable {P : Params} {Ω C : Type}

/-- The clipped cap moment `Σ log d_i · log max(min(c_i, D), 2)`. -/
noncomputable def hierQd (D : ℕ) {Ω : Type} (l : List (Interval Ω)) : ℝ :=
  (l.map fun I => Real.log I.ratio * Real.log (max (min I.cap D) 2 : ℕ)).sum

theorem hierQd_nonneg (D : ℕ) {Ω : Type} (l : List (Interval Ω)) : 0 ≤ hierQd D l := by
  unfold hierQd
  apply List.sum_nonneg
  intro r hr
  obtain ⟨I, -, rfl⟩ := List.mem_map.1 hr
  exact mul_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)

theorem hierQd_append (D : ℕ) {Ω : Type} (l l' : List (Interval Ω)) :
    hierQd D (l ++ l') = hierQd D l + hierQd D l' := by
  simp [hierQd]

@[simp] theorem hierQd_nil (D : ℕ) {Ω : Type} : hierQd D ([] : List (Interval Ω)) = 0 := by
  simp [hierQd]

theorem hierQd_cons (D : ℕ) {Ω : Type} (I : Interval Ω) (l : List (Interval Ω)) :
    hierQd D (I :: l) =
      Real.log I.ratio * Real.log (max (min I.cap D) 2 : ℕ) + hierQd D l := by
  simp [hierQd]

/-- **The cap payment survives clipping**: a cap update with `q ≤ D` drops the clipped moment
by at least `c_β log q` (eq. `main-cap-payment` for the caps `min(c, D)`). -/
theorem capUpdate_Qd_drop {l l' : List (Interval Ω)} {q D : ℕ} (hqD : q ≤ D)
    (h : CapUpdate P l q l') (hβ0 : 0 < P.β) (hβ1 : P.β < 1) (hβq : 2 ≤ P.β * q) :
    hierQd D l' + GI.Paper.cBeta P.β * Real.log q ≤ hierQd D l := by
  obtain ⟨i, hqc, hcd, rfl⟩ := h
  have hset := sum_map_set (fun I : Interval Ω => Real.log I.ratio * Real.log (max (min I.cap D) 2 : ℕ))
    l i i.2 ⟨l[i].part, l[i].ratio, min l[i].cap ⌊P.β * q⌋₊, l[i].origin⟩
  have hq' : (q : ℝ) ≤ (min l[i].cap D : ℕ) := by exact_mod_cast (le_min hqc hqD)
  have hcd' : ((min l[i].cap D : ℕ) : ℝ) ≤ l[i].ratio := by
    exact_mod_cast (min_le_left _ _).trans hcd
  have hnew : ((min (min l[i].cap ⌊P.β * q⌋₊) D : ℕ) : ℝ) ≤ P.β * q := by
    have h1 : ((min (min l[i].cap ⌊P.β * q⌋₊) D : ℕ) : ℝ) ≤ (⌊P.β * q⌋₊ : ℕ) := by
      exact_mod_cast (min_le_left _ _).trans (min_le_right _ _)
    exact h1.trans (Nat.floor_le (by linarith))
  obtain ⟨h1, h2⟩ := GI.Paper.eq_main_cap_payment hβ0 hβ1 hβq hq' hcd' hnew
  have hmax : ∀ c : ℕ, max (c : ℝ) 2 = ((max c 2 : ℕ) : ℝ) := fun c => by push_cast; rfl
  rw [hmax, hmax] at h1
  unfold hierQd GI.Paper.cBeta
  simp only [Fin.getElem_fin] at hset h1 h2 ⊢
  linarith

/-- The one-interval split inequality, with clipped caps. -/
theorem split_term_le {c d e capA capB capJ D : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d) (hcde : c * d ≤ e)
    (hA : capA ≤ capJ) (hB : capB ≤ capJ) :
    Real.log c * Real.log (max (min capA D) 2 : ℕ) + Real.log d * Real.log (max (min capB D) 2 : ℕ) ≤
      Real.log e * Real.log (max (min capJ D) 2 : ℕ) := by
  have hL : ∀ x : ℕ, x ≤ capJ → Real.log (max (min x D) 2 : ℕ) ≤ Real.log (max (min capJ D) 2 : ℕ) := by
    intro x hx
    apply Real.log_le_log (by positivity)
    exact_mod_cast max_le_max (min_le_min_right _ hx) le_rfl
  have hL0 : 0 ≤ Real.log (max (min capJ D) 2 : ℕ) := Real.log_natCast_nonneg _
  have hc0 := Real.log_natCast_nonneg c
  have hd0 := Real.log_natCast_nonneg d
  have hsum : Real.log c + Real.log d ≤ Real.log e := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    apply Real.log_le_log (by positivity)
    exact_mod_cast hcde
  have h1 := mul_le_mul_of_nonneg_left (hL capA hA) hc0
  have h2 := mul_le_mul_of_nonneg_left (hL capB hB) hd0
  have h3 := mul_le_mul_of_nonneg_right hsum hL0
  nlinarith

namespace ExposedSplit

variable {S : State Ω C} {Q : PrimitiveQuotient S}

/-- **The exposure does not increase the clipped moment.** -/
theorem Qd_le (h : ExposedSplit Q) (D : ℕ) :
    hierQd D (Q.pre ++ Q.top :: Q.post) ≤ hierQd D S.hier := by
  obtain ⟨pre₀, post₀, J, c₁, hl, hc₁, hcd, hpost, hcap, hpre⟩ := h.out
  have hd1 : 1 ≤ Q.d := by have := Q.two_le; omega
  have ht : Q.top.ratio = Q.d := Q.ratio_eq
  rw [hl, hierQd_append, hierQd_append, hierQd_cons, hierQd_cons, hpost]
  rcases hpre with ⟨h1, h2⟩ | ⟨mid, h2, hmr, hmc⟩
  · rw [h2]
    have hs := split_term_le (c := 1) (d := Q.d) (e := J.ratio) (capA := 0) (capB := Q.top.cap)
      (capJ := J.cap) (D := D) le_rfl hd1 (by rw [one_mul]; rw [h1] at hcd; simpa using hcd)
      (Nat.zero_le _) hcap
    simp only [Nat.cast_one, Real.log_one, zero_mul, zero_add] at hs
    rw [ht]
    linarith
  · rw [h2, hierQd_append]
    have hs := split_term_le (c := c₁) (d := Q.d) (e := J.ratio) (capA := mid.cap) (capB := Q.top.cap)
      (capJ := J.cap) (D := D) hc₁ hd1 hcd hmc hcap
    have hmid : hierQd D [mid] = Real.log mid.ratio * Real.log (max (min mid.cap D) 2 : ℕ) := by
      simp [hierQd]
    rw [hmid, hmr, ht]
    linarith

end ExposedSplit

/-- The coordinate intervals of a product refinement have clipped moment at most that of `top`. -/
theorem coordHier_Qd_le {S : State Ω C} (Q : PrimitiveQuotient S) {m k r : ℕ}
    (e : Fin Q.d ≃ (Fin r → Product.KSet m k)) (D : ℕ) :
    hierQd D (Q.coordHier e) ≤ hierQd D [Q.top] := by
  have hd := Q.card_kset_pow e
  have ht : Q.top.ratio = Q.d := Q.ratio_eq
  simp only [PrimitiveQuotient.coordHier, hierQd]
  rw [List.map_map]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  -- each term is at most `log C · log max(min(top.cap, D), 2)`
  set a := Real.log (m.choose k) with ha
  set b := Real.log (max (min Q.top.cap D) 2 : ℕ) with hb
  have ha0 : 0 ≤ a := Real.log_natCast_nonneg _
  have hb0 : 0 ≤ b := Real.log_natCast_nonneg _
  have hterm : ∀ i ∈ List.range r, (fun I : Interval Ω =>
      Real.log I.ratio * Real.log (max (min I.cap D) 2 : ℕ)) ((fun i : ℕ =>
        (⟨Q.coordPart e (i + 1), m.choose k, min Q.top.cap (m.choose k), Q.top.origin⟩ : Interval Ω)) i) ≤ a * b := by
    intro i _
    show a * Real.log (max (min (min Q.top.cap (m.choose k)) D) 2 : ℕ) ≤ a * b
    apply mul_le_mul_of_nonneg_left _ ha0
    apply Real.log_le_log (by positivity)
    exact_mod_cast max_le_max (min_le_min_right _ (min_le_left _ _)) le_rfl
  have hsum : ((List.range r).map ((fun I : Interval Ω =>
      Real.log I.ratio * Real.log (max (min I.cap D) 2 : ℕ)) ∘ fun i : ℕ =>
        (⟨Q.coordPart e (i + 1), m.choose k, min Q.top.cap (m.choose k), Q.top.origin⟩ : Interval Ω))).sum ≤
      (r : ℝ) * (a * b) := by
    have hb' := List.sum_le_card_nsmul
      ((List.range r).map ((fun I : Interval Ω => Real.log I.ratio * Real.log (max (min I.cap D) 2 : ℕ)) ∘
        fun i : ℕ => (⟨Q.coordPart e (i + 1), m.choose k, min Q.top.cap (m.choose k), Q.top.origin⟩ : Interval Ω)))
      (a * b) (by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
        exact hterm i hi)
    simp only [List.length_map, List.length_range, nsmul_eq_mul] at hb'
    exact hb'
  have hlogd : Real.log (Q.d : ℝ) = (r : ℝ) * a := by
    rw [hd, Nat.cast_pow, Real.log_pow]
  have hgoal : (r : ℝ) * (a * b) = Real.log (Q.top.ratio : ℝ) * b := by
    rw [ht, hlogd]; ring
  exact hsum.trans (le_of_eq hgoal)

section Clause

variable {cc : ChargingConstants}

theorem qClause_mono {R : Row} {qX qX' qU : ℝ} (h : qClause cc qX qU R) (hX : qX ≤ qX') :
    qClause cc qX' qU R := by
  cases R <;> simp only [qClause] at * <;> linarith

/-- **The row clauses of `Q_d` at a giant step.** (`D = max(d,6)`.) -/
theorem giantClasses_q [Finite Ω] (hc : Compat P cc) {d : ℕ} {m : Mode} {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)} (r : Run P m S L A)
    (hg : GammaHat d S.G) (hR1 : ((max d 6 : ℕ) : ℝ) ≤ (S.N : ℝ) ^ P.α)
    {c : ChildClass (PNode P)} (hc' : c ∈ giantClasses r) {b : List (PNode P)}
    (hb : b ∈ c.branches) {u : PNode P} (hu : u ∈ b) :
    qClause cc (hierQd (max d 6) S.hier) (hierQd (max d 6) u.leaf.S.hier) c.row := by
  cases r with
  | rowColumns hs htr L hrow I hcore hR hh1 hh hN hhier r' =>
    exfalso
    have h1 : (S.N : ℝ) ^ P.α < L.q := hrow.1
    have h2 : L.q ≤ max d 6 := labels_q_le hg L
    have h3 : ((L.q : ℕ) : ℝ) ≤ (max d 6 : ℕ) := by exact_mod_cast h2
    linarith
  | aggregate hs htr L hnot hq₀ I _ _ b' e τ hτ child hchild hN hhier hbk A' r' =>
    have hbe := e.exact
    subst hbe
    have hβ1 : P.β < 1 := lt_of_le_of_lt hc.β_le cc.β_lt_one
    have hβq : 2 ≤ P.β * L.q :=
      hc.βq₀.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hq₀) hc.β_pos.le)
    have hqD : L.q ≤ max d 6 := labels_q_le hg L
    simp only [giantClasses, List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl
    · obtain ⟨C', T, hT, -, hus⟩ := callBranches_spec e I.calls _ _ b hb
      obtain ⟨ℓ, rfl, hℓ, -, -⟩ := hus u hu
      simp only [qClause]
      have : ℓ.S.hier = S.hier := hℓ.hier_eq.trans hT.hier_eq
      show hierQd (max d 6) ℓ.S.hier ≤ hierQd (max d 6) S.hier
      rw [this]
    · obtain ⟨C', T, hT, -, hus⟩ := callBranches_spec e I.calls _ _ b hb
      obtain ⟨ℓ, rfl, hℓ, -, -⟩ := hus u hu
      simp only [qClause]
      have : ℓ.S.hier = S.hier := hℓ.hier_eq.trans hT.hier_eq
      show hierQd (max d 6) ℓ.S.hier ≤ hierQd (max d 6) S.hier
      rw [this]
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hb
      obtain ⟨ℓ, -, rfl, hℓ, -, -⟩ := forestP_branch (r' j) (by simp) ((hN j).trans rfl) u hu
      have hhierℓ : ℓ.S.hier = I.newHier (I.script.evalExact.overs.get j) :=
        hℓ.hier_eq.trans (hhier j)
      have hcap := I.capUpdate _ (List.get_mem _ j)
      have hdrop := capUpdate_Qd_drop hqD hcap hc.β_pos hβ1 hβq
      have hcβ : GI.Paper.cBeta cc.β ≤ GI.Paper.cBeta P.β := by
        unfold GI.Paper.cBeta
        apply Real.log_le_log (by have := cc.β_lt_one; have := cc.half_lt_β; positivity)
        exact one_div_le_one_div_of_le hc.β_pos hc.β_le
      have hlogq : 0 ≤ Real.log L.q := Real.log_natCast_nonneg _
      simp only [qClause]
      show hierQd (max d 6) ℓ.S.hier ≤
        hierQd (max d 6) S.hier - GI.Paper.cBeta cc.β * Real.log L.q
      rw [hhierℓ]
      have := mul_le_mul_of_nonneg_right hcβ hlogq
      linarith
  | _ => simp [giantClasses] at hc'

/-- **The row clauses of `Q_d` at a vertex.** The domain sizes are not used. -/
theorem runKind_q [Finite Ω] (hc : Compat P cc) {d : ℕ} {m : Mode} {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)} (r : Run P m S L A)
    (hg : GammaHat d S.G) (hR1 : ((max d 6 : ℕ) : ℝ) ≤ (S.N : ℝ) ^ P.α)
    {cls : List (ChildClass (PNode P))} (hk : runKind r = .charged cls)
    {c : ChildClass (PNode P)} (hc' : c ∈ cls) {b : List (PNode P)} (hb : b ∈ c.branches)
    {u : PNode P} (hu : u ∈ b) :
    qClause cc (hierQd (max d 6) S.hier) (hierQd (max d 6) u.leaf.S.hier) c.row := by
  cases r with
  | direct => simp [runKind] at hk
  | fresh => simp [runKind] at hk
  | threshold => simp [runKind] at hk
  | orbitStop => simp [runKind] at hk
  | orbitChain => simp [runKind] at hk
  | floorReset => simp only [runKind, NodeKind.charged.injEq] at hk; subst hk; simp at hc'
  | rowTerminal =>
    simp only [runKind, NodeKind.charged.injEq] at hk; subst hk
    exact giantClasses_q hc _ hg hR1 hc' hb hu
  | rowColumns =>
    simp only [runKind, NodeKind.charged.injEq] at hk; subst hk
    exact giantClasses_q hc _ hg hR1 hc' hb hu
  | aggregate =>
    simp only [runKind, NodeKind.charged.injEq] at hk; subst hk
    exact giantClasses_q hc _ hg hR1 hc' hb hu
  | dispatch hs htr hfl I child hchild hN hhier hbk A' r' =>
    simp only [runKind, NodeKind.charged.injEq] at hk; subst hk
    simp only [List.mem_singleton] at hc'
    subst hc'
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hb
    obtain ⟨ℓ, -, rfl, hℓ, -, -⟩ := forestP_branch (r' j) (by simp) (hN j) u hu
    have hhierℓ : ℓ.S.hier = I.hier' := hℓ.hier_eq.trans (hhier j)
    have hle : hierQd (max d 6) I.hier' ≤ hierQd (max d 6) S.hier := by
      rcases I.K_hier'_eq with ⟨Q, fin, htr', hs', reps, hk', hI, hK, hh⟩ |
        ⟨Q, fin, c', reps, hk', hI, m', k, r, e, hS, hb', hr, hK, hh⟩
      · rw [hh]
        exact hs'.2.Qd_le _
      · rw [hh, List.append_assoc, hierQd_append, hierQd_append]
        have h1 := coordHier_Qd_le Q e (max d 6)
        have h2 := hk'.2.Qd_le (max d 6)
        rw [hierQd_append] at h2
        have h3 : hierQd (max d 6) (Q.top :: Q.post) = hierQd (max d 6) [Q.top] + hierQd (max d 6) Q.post := by
          rw [show (Q.top :: Q.post) = [Q.top] ++ Q.post from rfl, hierQd_append]
        rw [h3] at h2
        linarith
    have hclause : qClause cc (hierQd (max d 6) S.hier) (hierQd (max d 6) ℓ.S.hier) (kindRow I.kind) := by
      generalize I.kind = k
      cases k <;> simp only [kindRow, qClause] <;> (rw [hhierℓ]; exact hle)
    exact hclause
  | normalize hs htr hfl Q hsm c' hq hkc hkl NA hNA m' hmode A' r' =>
    subst hNA
    have hhier : ∀ j, ((Q.normAboveOf c' htr hq hkc hkl).child j).hier = Q.pre ++ Q.top :: Q.post :=
      fun j => rfl
    have hle : hierQd (max d 6) (Q.pre ++ Q.top :: Q.post) ≤ hierQd (max d 6) S.hier :=
      hsm.2.Qd_le _
    simp only [runKind] at hk
    split_ifs at hk with hm'
    · simp only [NodeKind.charged.injEq] at hk; subst hk
      simp only [List.mem_singleton] at hc'
      subst hc'
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hb
      subst hm'
      obtain ⟨ℓ, -, rfl, hℓ, -, -⟩ := forestP_branch (r' j) (by simp) rfl u hu
      show hierQd (max d 6) ℓ.S.hier ≤ hierQd (max d 6) S.hier
      rw [hℓ.hier_eq, hhier j]
      exact hle
    · simp only [NodeKind.charged.injEq] at hk; subst hk
      obtain ⟨l, hl, hcl⟩ := List.mem_flatten.1 hc'
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hl
      have hsub : GammaHat d ((Q.normAboveOf c' htr hq hkc hkl).child j).G :=
        GammaHat.of_le hg (Q.normAboveOf c' htr hq hkc hkl).I.le
      have hRj : ((max d 6 : ℕ) : ℝ) ≤ (((Q.normAboveOf c' htr hq hkc hkl).child j).N : ℝ) ^ P.α := hR1
      have h := giantClasses_q hc (r' j) hsub hRj hcl hb hu
      refine qClause_mono h ?_
      rw [hhier j]
      exact hle

/-- The clause for the orbit children: they have the same hierarchy. -/
theorem runKind_orbit_q [Finite Ω] {D : ℕ} {m : Mode} {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)} (r : Run P m S L A)
    (hm : m ≠ .solve) {cs : List (PNode P)} (hk : runKind r = .orbit cs) {u : PNode P}
    (hu : u ∈ cs) : hierQd D u.leaf.S.hier ≤ hierQd D S.hier := by
  have hfor : ∃ (r₀ : Run P .cont S L A), m = .cont ∧ HEq r r₀ ∧ u ∈ r₀.forestP := by
    cases r with
    | orbitStop hs hint hD₁ h₁ hN₁ hhier₁ hb₁ r₁ =>
      simp only [runKind, NodeKind.orbit.injEq] at hk
      subst hk
      exact ⟨_, rfl, HEq.rfl, hu⟩
    | orbitChain hs hint hD₁ h₁ hN₁ hhier₁ hb₁ r₁ t ht h₂ hN₂ hhier₂ hb₂ r₂ =>
      simp only [runKind, NodeKind.orbit.injEq] at hk
      subst hk
      exact ⟨_, rfl, HEq.rfl, hu⟩
    | normalize =>
      simp only [runKind] at hk
      split_ifs at hk <;> simp at hk
    | direct => simp [runKind] at hk
    | fresh => simp [runKind] at hk
    | threshold => simp [runKind] at hk
    | floorReset => simp [runKind] at hk
    | dispatch => simp [runKind] at hk
    | rowTerminal => simp [runKind] at hk
    | rowColumns => simp [runKind] at hk
    | aggregate => simp [runKind] at hk
  obtain ⟨r₀, rfl, hre, hfor⟩ := hfor
  obtain rfl : r = r₀ := eq_of_heq hre
  obtain ⟨ℓ, -, rfl, hℓ, -, -⟩ := forestP_branch r (by simp) rfl u hfor
  show hierQd D ℓ.S.hier ≤ hierQd D S.hier
  rw [hℓ.hier_eq]

/-- **The packaged clauses of `Q_d`**, for `Good = VClass d`, `D = max(d,6)`, in the regime
`max(d,6) ≤ N^α`. -/
theorem clipped_clauses (hc : Compat P cc) {d N : ℕ}
    (hR1 : ((max d 6 : ℕ) : ℝ) ≤ (N : ℝ) ^ P.α) :
    (∀ v : PNode P, v.Inv N → VClass d v → v.leaf.pt = none → ∀ cls,
      runKind v.leaf.run = .charged cls → ∀ c ∈ cls, ∀ b ∈ c.branches, ∀ u ∈ b,
        qClause cc (hierQd (max d 6) v.leaf.S.hier) (hierQd (max d 6) u.leaf.S.hier) c.row) ∧
    (∀ v : PNode P, v.Inv N → VClass d v → v.leaf.pt = none → ∀ cs,
      runKind v.leaf.run = .orbit cs → ∀ u ∈ cs,
        hierQd (max d 6) u.leaf.S.hier ≤ hierQd (max d 6) v.leaf.S.hier) := by
  refine ⟨?_, ?_⟩
  · intro v hv hg hpt cls hk c hc' b hb u hu
    obtain ⟨Ω', m, C', S, L, A, r, pt⟩ := v
    simp only at hpt
    subst hpt
    haveI := hv.fin
    have hN : S.N = N := hv.N_eq
    exact runKind_q hc r hg (by rw [hN]; exact hR1) hk hc' hb hu
  · intro v hv hg hpt cs hk u hu
    obtain ⟨Ω', m, C', S, L, A, r, pt⟩ := v
    simp only at hpt
    subst hpt
    haveI := hv.fin
    have hm : m ≠ .solve := hv.mode
    exact runKind_orbit_q r hm hk hu

end Clause

end GI.DegreeD.M
