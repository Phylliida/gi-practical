import STS.Gadget
import STS.Steiner

/-!
# The Steiner quasigroup of `X_χ`

`third χ x y` is the third point of the block of `X_χ` through `x ≠ y`.  We prove the Steiner
quasigroup laws and `X χ = blocksOf (third χ)`.  (`third` is a proof device; it uses choice to name
partners in the fixed 8-point gadget, which is harmless: `X χ` itself is defined without it.)
-/

namespace STS

abbrev Zn := {z : Z // z ≠ 0}
abbrev Vn (d : ℕ) := {c : V d // c ≠ 0}

variable {d : ℕ}

/-! ## Arithmetic in `V d` -/

theorem V.add_self (c : V d) : c + c = 0 := by
  funext i; simp only [Pi.add_apply, Pi.zero_apply]; generalize c i = x; revert x; decide

theorem V.add_eq_zero_iff (c c' : V d) : c + c' = 0 ↔ c = c' := by
  constructor
  · intro h; funext i
    have := congrFun h i
    simp only [Pi.add_apply, Pi.zero_apply] at this
    revert this; generalize c i = x; generalize c' i = y; revert x y; decide
  · rintro rfl; exact V.add_self c

theorem V.add_cancel_left (c c' : V d) : c + (c + c') = c' := by
  rw [← add_assoc, V.add_self, zero_add]

/-! ## Sums of distinct nonzero elements -/

theorem zxor_ne_zero {z w : Zn} (h : z ≠ w) : z.1 ^^^ w.1 ≠ 0 := by
  rw [Ne, xor_eq_zero_iff]; exact fun e => h (Subtype.ext e)

def zxor (z w : Zn) (h : z ≠ w) : Zn := ⟨z.1 ^^^ w.1, zxor_ne_zero h⟩

theorem vadd_ne_zero {c c' : Vn d} (h : c ≠ c') : c.1 + c'.1 ≠ 0 := by
  rw [Ne, V.add_eq_zero_iff]; exact fun e => h (Subtype.ext e)

def vadd (c c' : Vn d) (h : c ≠ c') : Vn d := ⟨c.1 + c'.1, vadd_ne_zero h⟩

/-! ## Partners and labels in the gadget -/

/-- The partner of `a` in the matching `F^col_z`. -/
noncomputable def partner (col : Bool) (z : Zn) (a : Z) : Z :=
  Classical.choose (inFactor_exists col z.1 z.2 a)

theorem partner_spec (col : Bool) (z : Zn) (a : Z) : InFactor col z.1 a (partner col z a) :=
  Classical.choose_spec (inFactor_exists col z.1 z.2 a)

theorem eq_partner {col : Bool} {z : Zn} {a b : Z} (h : InFactor col z.1 a b) :
    b = partner col z a :=
  inFactor_unique col z.1 a b _ h (partner_spec col z a)

theorem partner_false (z : Zn) (a : Z) : partner false z a = a ^^^ z.1 :=
  (eq_partner (col := false) (rfl : a ^^^ z.1 = a ^^^ z.1)).symm

theorem partner_partner (col : Bool) (z : Zn) (a : Z) : partner col z (partner col z a) = a :=
  (eq_partner (inFactor_symm _ _ _ _ (partner_spec col z a))).symm

theorem partner_ne (col : Bool) (z : Zn) (a : Z) : partner col z a ≠ a :=
  (inFactor_ne col z.1 a _ z.2 (partner_spec col z a)).symm

/-- The label `z` of the factor containing `{a, b}`. -/
noncomputable def label (col : Bool) (a b : Z) (h : a ≠ b) : Zn :=
  ⟨Classical.choose (inFactor_cover col a b h), (Classical.choose_spec (inFactor_cover col a b h)).1⟩

theorem label_spec (col : Bool) (a b : Z) (h : a ≠ b) : InFactor col (label col a b h).1 a b :=
  (Classical.choose_spec (inFactor_cover col a b h)).2

theorem eq_label {col : Bool} {z : Zn} {a b : Z} (h : InFactor col z.1 a b) (hab : a ≠ b) :
    z = label col a b hab :=
  Subtype.ext (inFactor_label_unique col _ _ a b h (label_spec col a b hab))

/-! ## The third point -/

/-- The third point of the block through `x` and `y` (and `x` itself when `x = y`). -/
noncomputable def third (χ : V d → Bool) : Point d → Point d → Point d
  | .inl z, .inl w => if h : z = w then .inl z else .inl (zxor z w h)
  | .inl z, .inr (c, a) => .inr (c, partner (χ c.1) z a)
  | .inr (c, a), .inl z => .inr (c, partner (χ c.1) z a)
  | .inr (c, a), .inr (c', b) =>
      if h : c = c' then (if hab : a = b then .inr (c, a) else .inl (label (χ c.1) a b hab))
      else .inr (vadd c c' h, a ^^^ b)

variable (χ : V d → Bool)

theorem third_inl_inl {z w : Zn} (h : z ≠ w) : third χ (.inl z) (.inl w) = .inl (zxor z w h) := by
  simp [third, h]

theorem third_inl_inr (z : Zn) (c : Vn d) (a : Z) :
    third χ (.inl z) (.inr (c, a)) = .inr (c, partner (χ c.1) z a) := rfl

theorem third_inr_inl (z : Zn) (c : Vn d) (a : Z) :
    third χ (.inr (c, a)) (.inl z) = .inr (c, partner (χ c.1) z a) := rfl

theorem third_inr_inr_same (c : Vn d) {a b : Z} (hab : a ≠ b) :
    third χ (.inr (c, a)) (.inr (c, b)) = .inl (label (χ c.1) a b hab) := by
  simp [third, hab]

theorem third_inr_inr_ne {c c' : Vn d} (h : c ≠ c') (a b : Z) :
    third χ (.inr (c, a)) (.inr (c', b)) = .inr (vadd c c' h, a ^^^ b) := by
  simp [third, h]

/-! ## Steiner quasigroup laws -/

theorem isSQ_third : IsSQ (third χ) where
  ne_left := by
    rintro (z | ⟨c, a⟩) (w | ⟨c', b⟩) hxy
    · have h : z ≠ w := fun e => hxy (e ▸ rfl)
      rw [third_inl_inl χ h]; intro e
      have := congrArg Subtype.val (Sum.inl.inj e)
      exact xor_ne_self z.1 w.1 w.2 this
    · rw [third_inl_inr]; exact Sum.inr_ne_inl
    · rw [third_inr_inl]; intro e
      exact partner_ne _ _ _ (congrArg Prod.snd (Sum.inr.inj e))
    · by_cases h : c = c'
      · subst h
        have hab : a ≠ b := fun e => hxy (e ▸ rfl)
        rw [third_inr_inr_same χ c hab]; exact Sum.inl_ne_inr
      · rw [third_inr_inr_ne χ h]; intro e
        have := congrArg Subtype.val (congrArg Prod.fst (Sum.inr.inj e))
        simp only [vadd] at this
        exact c'.2 (by simpa using this)
  ne_right := by
    rintro (z | ⟨c, a⟩) (w | ⟨c', b⟩) hxy
    · have h : z ≠ w := fun e => hxy (e ▸ rfl)
      rw [third_inl_inl χ h]; intro e
      have := congrArg Subtype.val (Sum.inl.inj e)
      simp only [zxor] at this
      rw [xor_comm'] at this
      exact xor_ne_self w.1 z.1 z.2 this
    · rw [third_inl_inr]; intro e
      exact partner_ne _ _ _ (congrArg Prod.snd (Sum.inr.inj e))
    · rw [third_inr_inl]; exact Sum.inr_ne_inl
    · by_cases h : c = c'
      · subst h
        have hab : a ≠ b := fun e => hxy (e ▸ rfl)
        rw [third_inr_inr_same χ c hab]; exact Sum.inl_ne_inr
      · rw [third_inr_inr_ne χ h]; intro e
        have := congrArg Subtype.val (congrArg Prod.fst (Sum.inr.inj e))
        simp only [vadd] at this
        rw [add_comm] at this
        exact c.2 (by simpa using this)
  comm := by
    rintro (z | ⟨c, a⟩) (w | ⟨c', b⟩) hxy
    · have h : z ≠ w := fun e => hxy (e ▸ rfl)
      rw [third_inl_inl χ h, third_inl_inl χ (Ne.symm h)]
      congr 1; exact Subtype.ext (xor_comm' _ _)
    · rfl
    · rfl
    · by_cases h : c = c'
      · subst h
        have hab : a ≠ b := fun e => hxy (e ▸ rfl)
        rw [third_inr_inr_same χ c hab, third_inr_inr_same χ c (Ne.symm hab)]
        congr 1
        exact eq_label (inFactor_symm _ _ _ _ (label_spec _ _ _ _)) _
      · rw [third_inr_inr_ne χ h, third_inr_inr_ne χ (Ne.symm h)]
        congr 2
        · exact Subtype.ext (add_comm _ _)
        · exact xor_comm' _ _
  cancel := by
    rintro (z | ⟨c, a⟩) (w | ⟨c', b⟩) hxy
    · have h : z ≠ w := fun e => hxy (e ▸ rfl)
      have h2 : z ≠ zxor z w h := by
        intro e; have := congrArg Subtype.val e; simp only [zxor] at this
        exact xor_ne_self z.1 w.1 w.2 this.symm
      rw [third_inl_inl χ h, third_inl_inl χ h2]
      congr 1; exact Subtype.ext (xor_cancel_left _ _)
    · rw [third_inl_inr, third_inl_inr, partner_partner]
    · rw [third_inr_inl, third_inr_inr_same χ c (partner_ne _ _ _).symm]
      congr 1
      exact (eq_label (partner_spec _ _ _) _).symm
    · by_cases h : c = c'
      · subst h
        have hab : a ≠ b := fun e => hxy (e ▸ rfl)
        rw [third_inr_inr_same χ c hab, third_inr_inl]
        congr 2
        exact (eq_partner (label_spec _ _ _ _)).symm
      · have h2 : c ≠ vadd c c' h := by
          intro e; have := congrArg Subtype.val e; simp only [vadd] at this
          exact c'.2 (by simpa using this.symm)
        rw [third_inr_inr_ne χ h, third_inr_inr_ne χ h2]
        congr 2
        · exact Subtype.ext (V.add_cancel_left _ _)
        · exact xor_cancel_left _ _

/-! ## `X χ` is the block system of `third χ` -/

theorem X_eq_blocksOf : X χ = blocksOf (third χ) := by
  ext B
  constructor
  · rintro (⟨z₁, z₂, z₃, hs, rfl⟩ | ⟨z, c, a, b, hf, rfl⟩ | ⟨c₁, c₂, c₃, a, b, hs, rfl⟩)
    · have h : z₁ ≠ z₂ := by
        rintro rfl; rw [xor_self', zero_xor'] at hs; exact z₃.2 hs
      refine ⟨.inl z₁, .inl z₂, fun e => h (Sum.inl.inj e), ?_⟩
      rw [third_inl_inl χ h]
      have e : z₃ = zxor z₁ z₂ h := by
        apply Subtype.ext; simp only [zxor]
        exact xor_solve _ _ _ hs
      rw [e]
    · refine ⟨.inl z, .inr (c, a), Sum.inl_ne_inr, ?_⟩
      rw [third_inl_inr, ← eq_partner hf]
    · have h : c₁ ≠ c₂ := by
        rintro rfl; rw [V.add_self, zero_add] at hs; exact c₃.2 hs
      refine ⟨.inr (c₁, a), .inr (c₂, b), fun e => h (congrArg Prod.fst (Sum.inr.inj e)), ?_⟩
      rw [third_inr_inr_ne χ h]
      have e : c₃ = vadd c₁ c₂ h := by
        apply Subtype.ext; simp only [vadd]
        exact ((V.add_eq_zero_iff _ _).1 hs).symm
      rw [e]
  · rintro ⟨x, y, hxy, rfl⟩
    rcases x with z | ⟨c, a⟩ <;> rcases y with w | ⟨c', b⟩
    · have h : z ≠ w := fun e => hxy (e ▸ rfl)
      rw [third_inl_inl χ h]
      refine Or.inl ⟨z, w, zxor z w h, ?_, rfl⟩
      simp only [zxor]; exact xor_three _ _
    · rw [third_inl_inr]
      exact Or.inr (Or.inl ⟨z, c', b, _, partner_spec _ _ _, rfl⟩)
    · rw [third_inr_inl]
      refine Or.inr (Or.inl ⟨w, c, a, _, partner_spec _ _ _, ?_⟩)
      ext p; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    · by_cases h : c = c'
      · subst h
        have hab : a ≠ b := fun e => hxy (e ▸ rfl)
        rw [third_inr_inr_same χ c hab]
        refine Or.inr (Or.inl ⟨label (χ c.1) a b hab, c, a, b, label_spec _ _ _ hab, ?_⟩)
        ext p; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
      · rw [third_inr_inr_ne χ h]
        refine Or.inr (Or.inr ⟨c, c', vadd c c' h, a, b, ?_, rfl⟩)
        exact V.add_self _

end STS
