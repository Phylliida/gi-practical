import Mathlib.Data.List.Basic
import Mathlib.Data.List.Zip
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic

/-!
# Families of list entries

`ListFam L M B`: the entries of a list `L : List ℕ` are labelled by `M` labels so that, for every
label, the entries with that label sum to at most `B`. This is the combinatorial content of the
regrouping (H2): many calls, few families, each family a disjoint-domain family (sizes summing to
at most the domain size `B`).

Labellings are represented by a list of labels, zipped with `L`; sums over a label use
`List.filter`. `toFin` converts a labelling to a function on `Fin L.length`, the form used in
`DegreeD/Induction.lean`.
-/

namespace GI.DegreeD

open List

variable {β γ : Type*}

/-- Sum of the entries of `L` whose label satisfies `p`. -/
def zsum (L : List ℕ) (labs : List β) (p : β → Bool) : ℕ :=
  (((L.zip labs).filter (fun x => p x.2)).map (·.1)).sum

theorem zsum_nil_left (labs : List β) (p : β → Bool) : zsum [] labs p = 0 := by
  simp [zsum]

theorem zsum_cons (a : ℕ) (L : List ℕ) (b : β) (labs : List β) (p : β → Bool) :
    zsum (a :: L) (b :: labs) p = (if p b then a else 0) + zsum L labs p := by
  unfold zsum
  rw [List.zip_cons_cons, List.filter_cons]
  split_ifs with h <;> simp [h]

theorem zsum_le_of_forall_false (L : List ℕ) (labs : List β) (p : β → Bool)
    (h : ∀ l ∈ labs, p l = false) : zsum L labs p = 0 := by
  induction L generalizing labs with
  | nil => simp [zsum]
  | cons a L ih =>
    cases labs with
    | nil => simp [zsum]
    | cons b labs =>
      rw [zsum_cons, ih labs (fun l hl => h l (by simp [hl]))]
      simp [h b (by simp)]

theorem zsum_map (L : List ℕ) (labs : List β) (f : β → γ) (p : γ → Bool) :
    zsum L (labs.map f) p = zsum L labs (fun b => p (f b)) := by
  induction L generalizing labs with
  | nil => simp [zsum]
  | cons a L ih =>
    cases labs with
    | nil => simp [zsum]
    | cons b labs =>
      simp only [List.map_cons]
      rw [zsum_cons, zsum_cons, ih labs]

theorem zsum_append {L₁ L₂ : List ℕ} {labs₁ labs₂ : List β} (p : β → Bool)
    (h : L₁.length = labs₁.length) :
    zsum (L₁ ++ L₂) (labs₁ ++ labs₂) p = zsum L₁ labs₁ p + zsum L₂ labs₂ p := by
  unfold zsum
  rw [List.zip_append h, List.filter_append, List.map_append, List.sum_append]

/-- `ListFam L M B`: the entries of `L` can be labelled by `Fin M` with each label's sum `≤ B`. -/
def ListFam (L : List ℕ) (M B : ℕ) : Prop :=
  ∃ labs : List (Fin M), labs.length = L.length ∧
    ∀ j : Fin M, zsum L labs (fun l => decide (l = j)) ≤ B

namespace ListFam

theorem nil (M B : ℕ) : ListFam [] M B :=
  ⟨[], rfl, fun j => by simp [zsum]⟩

theorem append {L₁ L₂ : List ℕ} {M₁ M₂ B : ℕ} (h₁ : ListFam L₁ M₁ B) (h₂ : ListFam L₂ M₂ B) :
    ListFam (L₁ ++ L₂) (M₁ + M₂) B := by
  obtain ⟨l₁, hl₁, h1⟩ := h₁
  obtain ⟨l₂, hl₂, h2⟩ := h₂
  refine ⟨l₁.map (Fin.castAdd M₂) ++ l₂.map (Fin.natAdd M₁), by simp [hl₁, hl₂], fun j => ?_⟩
  rw [zsum_append _ (by simp [hl₁]), zsum_map, zsum_map]
  by_cases hj : (j : ℕ) < M₁
  · -- the label `j` lies in the first block
    have e1 : (fun b => decide (Fin.castAdd M₂ b = j)) =
        (fun b => decide (b = (⟨j, hj⟩ : Fin M₁))) := by
      ext b
      simp only [decide_eq_decide]
      constructor
      · intro h; exact Fin.ext (by have := congrArg Fin.val h; simpa using this)
      · intro h; subst h; exact Fin.ext (by simp)
    have e2 : ∀ b ∈ l₂, decide (Fin.natAdd M₁ b = j) = false := by
      intro b _
      simp only [decide_eq_false_iff_not]
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_natAdd] at this
      omega
    rw [e1, zsum_le_of_forall_false _ _ _ e2]
    simpa using h1 ⟨j, hj⟩
  · -- the label `j` lies in the second block
    have hj' : (j : ℕ) - M₁ < M₂ := by have := j.2; omega
    have e1 : ∀ b ∈ l₁, decide (Fin.castAdd M₂ b = j) = false := by
      intro b _
      simp only [decide_eq_false_iff_not]
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castAdd] at this
      omega
    have e2 : (fun b => decide (Fin.natAdd M₁ b = j)) =
        (fun b => decide (b = (⟨j - M₁, hj'⟩ : Fin M₂))) := by
      ext b
      simp only [decide_eq_decide]
      constructor
      · intro h
        apply Fin.ext
        have := congrArg Fin.val h
        simp only [Fin.val_natAdd] at this
        show (b : ℕ) = (j : ℕ) - M₁
        omega
      · intro h
        subst h
        apply Fin.ext
        simp only [Fin.val_natAdd]
        omega
    rw [zsum_le_of_forall_false _ _ _ e1, e2]
    simpa using h2 ⟨j - M₁, hj'⟩

theorem mono {L : List ℕ} {M M' B : ℕ} (h : ListFam L M B) (hM : M ≤ M') : ListFam L M' B := by
  obtain ⟨labs, hl, h1⟩ := h
  refine ⟨labs.map (Fin.castLE hM), by simp [hl], fun j => ?_⟩
  rw [zsum_map]
  by_cases hj : (j : ℕ) < M
  · have e1 : (fun b => decide (Fin.castLE hM b = j)) =
        (fun b => decide (b = (⟨j, hj⟩ : Fin M))) := by
      ext b
      simp only [decide_eq_decide]
      constructor
      · intro h; exact Fin.ext (by have := congrArg Fin.val h; simpa using this)
      · intro h; subst h; exact Fin.ext (by simp)
    rw [e1]
    simpa using h1 ⟨j, hj⟩
  · have e2 : ∀ b ∈ labs, decide (Fin.castLE hM b = j) = false := by
      intro b _
      simp only [decide_eq_false_iff_not]
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castLE] at this
      have hb := b.2
      omega
    rw [zsum_le_of_forall_false _ _ _ e2]
    exact Nat.zero_le _

theorem mono_B {L : List ℕ} {M B B' : ℕ} (h : ListFam L M B) (hB : B ≤ B') : ListFam L M B' := by
  obtain ⟨labs, hl, h1⟩ := h
  exact ⟨labs, hl, fun j => (h1 j).trans hB⟩

/-- A single entry `≤ B`, in one family. -/
theorem single {x B : ℕ} (hx : x ≤ B) : ListFam [x] 1 B := by
  refine ⟨[0], rfl, fun j => ?_⟩
  have hj : j = 0 := Fin.ext (by have := j.2; omega)
  subst hj
  simpa [zsum] using hx

/-- Each entry in its own family: `L.length` families, if each entry is `≤ B`. -/
theorem singletons {L : List ℕ} {B : ℕ} (h : ∀ x ∈ L, x ≤ B) : ListFam L L.length B := by
  induction L with
  | nil => exact nil 0 B
  | cons a L ih =>
    have h1 := single (x := a) (B := B) (h a (by simp))
    have h2 := ih (fun x hx => h x (by simp [hx]))
    have := append h1 h2
    refine this.mono ?_
    simp [Nat.add_comm]

/-- Flattening a list of lists, each with `m` families. -/
theorem flatten {ls : List (List ℕ)} {m B : ℕ} (h : ∀ l ∈ ls, ListFam l m B) :
    ListFam ls.flatten (ls.length * m) B := by
  induction ls with
  | nil => simpa using nil 0 B
  | cons l ls ih =>
    have h1 := h l (by simp)
    have h2 := ih (fun x hx => h x (by simp [hx]))
    have := append h1 h2
    refine this.mono ?_
    simp only [List.length_cons]
    nlinarith

/-- A flat map over a list. -/
theorem flatMap {α : Type*} (l : List α) (f : α → List ℕ) {m B : ℕ}
    (h : ∀ a ∈ l, ListFam (f a) m B) : ListFam (l.flatMap f) (l.length * m) B := by
  have := @flatten (l.map f) m B (by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact h a ha)
  simpa [List.flatMap, Function.comp_def] using this

/-- The entries of a labelling are at most their old versions (pointwise): same families work.
Used to replace a list of sizes by a list of smaller sizes. -/
theorem mono_entries {L L' : List ℕ} {M B : ℕ} (h : ListFam L M B)
    (hlen : L'.length = L.length) (hle : ∀ i (hi : i < L'.length), L'[i] ≤ L[i]) :
    ListFam L' M B := by
  obtain ⟨labs, hl, h1⟩ := h
  refine ⟨labs, hl.trans hlen.symm, fun j => le_trans ?_ (h1 j)⟩
  -- an auxiliary statement by induction, comparing zsums entrywise
  have key : ∀ (L L' : List ℕ) (labs : List (Fin M)) (_hlen : L'.length = L.length),
      (∀ i (hi : i < L'.length), L'[i] ≤ L[i]'(by omega)) →
      zsum L' labs (fun l => decide (l = j)) ≤ zsum L labs (fun l => decide (l = j)) := by
    intro L L' labs
    induction L generalizing L' labs with
    | nil =>
      intro hlen' _
      cases L' with
      | nil => exact le_refl _
      | cons a L' => simp at hlen'
    | cons a L ih =>
      intro hlen' hle'
      cases L' with
      | nil => simp at hlen'
      | cons b L' =>
        cases labs with
        | nil => simp [zsum]
        | cons l labs =>
          rw [zsum_cons, zsum_cons]
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen'
          have h0 := hle' 0 (by simp)
          have hrest := ih L' labs hlen' (fun i hi => by
            have := hle' (i + 1) (by simpa using hi)
            simpa using this)
          simp only [List.getElem_cons_zero] at h0
          split_ifs <;> omega
  exact key L L' labs hlen hle

/-- **Layers**: if `L` is a concatenation of blocks `replicate (r t) (v t)` for `t < n`, with
each `r t ≤ Q`, then `L` has `Q` families, each of total at most `Σ_t v t`. This is the merge
across updates: take one call from each update (each update repeats the same size at most `Q`
times), the window sizes of one label add up to at most `Σ_t v_t`. -/
theorem layers (n Q : ℕ) (r v : ℕ → ℕ) (hr : ∀ t, r t ≤ Q) :
    ListFam ((List.range n).flatMap fun t => List.replicate (r t) (v t)) Q
      (∑ t ∈ Finset.range n, v t) := by
  induction n with
  | zero => simpa using nil Q 0
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, Finset.sum_range_succ]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    obtain ⟨labs, hl, h1⟩ := ih
    refine ⟨labs ++ (List.finRange (r n)).map (Fin.castLE (hr n)),
      by simp [hl], fun j => ?_⟩
    rw [zsum_append _ hl.symm]
    have hsecond : zsum (List.replicate (r n) (v n)) ((List.finRange (r n)).map (Fin.castLE (hr n)))
        (fun l => decide (l = j)) ≤ v n := by
      -- the new labels are distinct, so at most one entry has label `j`
      have aux : ∀ (ls : List (Fin Q)), ls.Nodup →
          zsum (List.replicate ls.length (v n)) ls (fun l => decide (l = j)) ≤ v n := by
        intro ls hnd
        induction ls with
        | nil => simp [zsum]
        | cons b ls ih =>
          simp only [List.length_cons, List.replicate_succ]
          rw [zsum_cons]
          rw [List.nodup_cons] at hnd
          have hrest := ih hnd.2
          split_ifs with hb
          · -- `b = j`: the rest has no label `j`
            have hb' : b = j := by simpa using hb
            have hzero : zsum (List.replicate ls.length (v n)) ls (fun l => decide (l = j)) = 0 := by
              apply zsum_le_of_forall_false
              intro l hl
              simp only [decide_eq_false_iff_not]
              rintro rfl
              exact hnd.1 (hb' ▸ hl)
            rw [hzero]; simp
          · simpa using hrest
      have hnd : ((List.finRange (r n)).map (Fin.castLE (hr n))).Nodup :=
        (List.nodup_finRange _).map (Fin.castLE_injective (hr n))
      have hlen : ((List.finRange (r n)).map (Fin.castLE (hr n))).length = r n := by simp
      have := aux _ hnd
      rwa [hlen] at this
    have hfirst := h1 j
    omega

/-- A labelling as a function on indices. -/
theorem toFin {L : List ℕ} {M B : ℕ} (h : ListFam L M B) :
    ∃ fam : Fin L.length → Fin M, ∀ j : Fin M,
      ∑ i ∈ Finset.univ.filter (fun i => fam i = j), L.get i ≤ B := by
  classical
  obtain ⟨labs, hl, h1⟩ := h
  refine ⟨fun i => labs[(i : ℕ)]'(by rw [hl]; exact i.2), fun j => le_trans ?_ (h1 j)⟩
  apply le_of_eq
  -- the sum over the filter equals the zipped sum
  have key : ∀ (L : List ℕ) (labs : List (Fin M)) (hl : labs.length = L.length),
      ∑ i ∈ Finset.univ.filter
          (fun i : Fin L.length => (labs[(i : ℕ)]'(by rw [hl]; exact i.2)) = j), L.get i =
        zsum L labs (fun l => decide (l = j)) := by
    intro L labs hl
    induction L generalizing labs with
    | nil => simp [zsum]
    | cons a L ih =>
      cases labs with
      | nil => simp at hl
      | cons b labs =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
        rw [Finset.sum_filter]
        refine (Fin.sum_univ_succ _).trans ?_
        rw [zsum_cons, ← ih labs hl, Finset.sum_filter]
        simp only [Fin.val_zero, List.getElem_cons_zero, List.get_cons_zero, Fin.val_succ,
          List.getElem_cons_succ, List.get_cons_succ]
        by_cases hb : b = j <;> simp [hb]
  exact key L labs hl

/-- `toFin` for a list given as a `map`: a labelling of the indices of `bs`. -/
theorem toFin_map {β : Type*} (bs : List β) (f : β → ℕ) {M B : ℕ} (h : ListFam (bs.map f) M B) :
    ∃ fam : Fin bs.length → Fin M, ∀ j : Fin M,
      ∑ i ∈ Finset.univ.filter (fun i => fam i = j), f (bs.get i) ≤ B := by
  classical
  obtain ⟨labs, hl, h1⟩ := h
  have hlen : labs.length = bs.length := by simpa using hl
  refine ⟨fun i => labs[(i : ℕ)]'(by rw [hlen]; exact i.2), fun j => le_trans ?_ (h1 j)⟩
  apply le_of_eq
  have key : ∀ (bs : List β) (labs : List (Fin M)) (hl : labs.length = bs.length),
      ∑ i ∈ Finset.univ.filter
          (fun i : Fin bs.length => (labs[(i : ℕ)]'(by rw [hl]; exact i.2)) = j), f (bs.get i) =
        zsum (bs.map f) labs (fun l => decide (l = j)) := by
    intro bs labs hl
    induction bs generalizing labs with
    | nil => simp [zsum]
    | cons a bs ih =>
      cases labs with
      | nil => simp at hl
      | cons l labs =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
        rw [Finset.sum_filter]
        refine (Fin.sum_univ_succ _).trans ?_
        rw [List.map_cons, zsum_cons, ← ih labs hl, Finset.sum_filter]
        simp only [Fin.val_zero, List.getElem_cons_zero, List.get_cons_zero, Fin.val_succ,
          List.getElem_cons_succ, List.get_cons_succ]
        by_cases hb : l = j <;> simp [hb]
  exact key bs labs hlen

end ListFam

end GI.DegreeD
