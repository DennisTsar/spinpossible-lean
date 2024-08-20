import Spinpossible.Definitions
import Mathlib.Tactic

def Spin.IsSpinAbout (s : Spin m n) (r : Rectangle m n) : Prop :=
  s = r.toSpin

def IsLowercaseSpin (s : Spin m n) : Prop :=
  ∃ (r : Rectangle m n), s.IsSpinAbout r

lemma rect_spin_mul_eq_chain : ((Rectangle.toSpin r1) * (Rectangle.toSpin r2)).actionOnBoard b =
    r2.toSpin.actionOnBoard (r1.toSpin.actionOnBoard b) := by
  simp_rw [HMul.hMul, Mul.mul, Spin.mul, HMul.hMul, Mul.mul, perm.actionRight]
  unfold Rectangle.toSpin Spin.actionOnBoard
  funext i j
  by_cases h1 : Point.IsInside ⟨i, j⟩ r2
  · simp only [to2d_to1d_inverse, h1, ite_true, add_left_eq_self, ite_eq_right_iff, one_ne_zero,
      imp_false, Equiv.symm_trans_apply, Equiv.coe_fn_symm_mk, ite_eq_left_iff, zero_ne_one]
    split <;> simp
  · simp [h1]

-- proposition 1

theorem spin_is_own_inverse : performSpin r (performSpin r b) = b := by
  funext i j
  unfold performSpin Rectangle.toSpin Spin.actionOnBoard
  by_cases h : Point.IsInside ⟨i, j⟩ r
  · simp [h, spin_stays_inside, rotate180_self_inverse, orientation.other_self]
  · simp [h]

theorem spin_is_own_inverse' (h : Spin.IsSpinAbout s r) :
    s.actionOnBoard (s.actionOnBoard b) = b := by
  rw [h, ←performSpin, ←performSpin, spin_is_own_inverse]

theorem spin_is_own_inverse'' (h : Spin.IsSpinAbout s r) : (s * s).actionOnBoard b = b := by
  have h1 : (s * s).actionOnBoard b = s.actionOnBoard (s.actionOnBoard b) := by
    rw [h, rect_spin_mul_eq_chain]
  simp only [h1, spin_is_own_inverse' h]

theorem spin_inverse_props (h : Spin.IsSpinAbout s r) :
    (s * s).α.toFun = id ∧ (s * s).u = fun _ => 0 := by
  rw [h]
  dsimp only [HMul.hMul, Mul.mul, Spin.mul]
  unfold Rectangle.toSpin perm.actionRight
  simp_rw [Nat.mul_eq, Equiv.toFun_as_coe, Equiv.coe_trans, Equiv.coe_fn_mk]
  apply And.intro
  · funext p
    by_cases h1 : (to2d p).IsInside r
    · simp [h1, spin_stays_inside]
    · simp [h1]
  · funext p
    by_cases h1 : (to2d p).IsInside r
    · simp [h1, spin_stays_inside]
    · simp [h1]

-- proposition 2

lemma rectangle_flips_min_one_tile (r : Rectangle m n) :
    ∃ p, r.toSpin.u p = 1 := by
  let p := r.topLeft
  use to1d p
  have h : p.IsInside r := by
    simp_rw [Point.IsInside, le_refl, true_and]
    exact ⟨r.validRow, r.validCol⟩
  simp_rw [Rectangle.toSpin, to2d_to1d_inverse, h, ite_true]

theorem spin_inverse_is_not_spin (h : Spin.IsSpinAbout s r) : ¬(s * s).IsSpinAbout r2 := by
  rw [Spin.IsSpinAbout]
  intro h1
  have h2 : ∃ p, (s * s).u p = 1 := by simp_rw [h1, rectangle_flips_min_one_tile r2]
  simp_rw [spin_inverse_props h, exists_const, zero_ne_one] at h2

def CommonCenter (r1 r2 : Rectangle m n) : Prop :=
  r1.topLeft.row.val + r1.bottomRight.row.val = r2.topLeft.row.val + r2.bottomRight.row.val ∧
  r1.topLeft.col.val + r1.bottomRight.col.val = r2.topLeft.col.val + r2.bottomRight.col.val

lemma commonCenter_rotate (h : CommonCenter r1 r2) :
    ∀ p : Point .., (p.IsInside r1 ∧ p.IsInside r2) → (rotate180 p r2 = rotate180 p r1) := by
  dsimp only [CommonCenter, Point.IsInside] at *
  simp [rotate180, rotateCalc]
  omega

lemma commonCenter_trans (h1 : CommonCenter r1 r2) (h2 : CommonCenter r2 r3)
    : CommonCenter r1 r3 := by
  dsimp only [CommonCenter] at *
  omega

lemma commonCenter_comm : CommonCenter r1 r2 ↔ CommonCenter r2 r1 := by
  dsimp only [CommonCenter]
  omega

lemma rect_commonCenter
    (h : ∀ p : Point .., (p.IsInside r1 ∧ p.IsInside r2) → (rotate180 p r2 = rotate180 p r1))
    (h2 : ∃ p : Point .., p.IsInside r1 ∧ p.IsInside r2) : CommonCenter r1 r2 := by
  simp only [CommonCenter] at *
  obtain ⟨p, h3⟩ := h2
  have a7 : rotate180 p r2 = rotate180 p r1 := h p h3
  dsimp [rotate180, rotateCalc] at a7
  simp [Point.IsInside] at *
  omega

lemma rotate_calc_helper {a b c d e : Nat} (h : d - (e - c) = b - (e - a))
    (h4 : e ≤ b) (h5 : e ≤ d) (h6 : a ≤ e) (h7 : c ≤ e) :
    ∀ x, (x ≤ b ∧ x ≤ d ∧ a ≤ x ∧ c ≤ x) → d - (x - c) = b - (x - a) := by omega

lemma rect_commonCenter_if_rotate_eq (h1 : Point.IsInside p r1) (h2 : Point.IsInside p r2)
    (h3 : rotate180 p r2 = rotate180 p r1) : CommonCenter r1 r2 := by
  apply rect_commonCenter ?_ (by use p)
  intro p2 a
  simp only [rotate180, rotateCalc, Point.mk.injEq, Fin.mk.injEq] at h3
  let h11 := h1.right.right
  let h22 := h2.right.right
  have hp1 := rotate_calc_helper h3.left h1.right.left h2.right.left h1.left h2.left
    p2.row ⟨a.left.right.left, a.right.right.left, a.left.left, a.right.left⟩
  have hp2 := rotate_calc_helper h3.right h11.right h22.right h11.left h22.left
    p2.col ⟨a.left.right.right.right, a.right.right.right.right,
      a.left.right.right.left, a.right.right.right.left⟩
  simp only [rotate180, rotateCalc, hp1, hp2]

-- "r1 contains r2"
def Rectangle.Contains (r1 r2 : Rectangle m n) : Prop :=
  ∀ p, Point.IsInside p r2 → Point.IsInside p r1

lemma s1_eq_s2_of_r1_eq_r2 (h_s1 : Spin.IsSpinAbout s1 r1) (h_s2 : s2.IsSpinAbout r2)
    (h : r1 = r2) : s1 = s2 := by
  calc
    s1 = r1.toSpin := h_s1
    _  = r2.toSpin := by rw [h]
    _  = s2        := h_s2.symm

lemma to1d_injective : Function.Injective (to1d: Point m n -> _)
  | p1, p2, h => by simpa only [to2d_to1d_inverse] using congr(to2d $h)

@[simp]
lemma to1d_inj : to1d p1 = to1d p2 ↔ p1 = p2 :=to1d_injective.eq_iff

lemma Rectangle.corners_inside (r : Rectangle m n) : r.topLeft.IsInside r ∧ r.bottomRight.IsInside r := by
  dsimp [Point.IsInside]
  have : _ ∧ _ := ⟨r.validRow, r.validCol⟩
  omega

lemma Rectangle.corners_rotate (r: Rectangle m n) :
    rotate180 r.topLeft r = r.bottomRight ∧ rotate180 r.bottomRight r = r.topLeft := by
  simp [rotate180, rotateCalc]
  have : _ ∧ _ := ⟨r.validCol, r.validRow⟩
  ext <;> (apply Nat.sub_sub_self; omega)

lemma s1s2_not_spin.aux1 {r1 r2 r3 : Rectangle m n} {s1 s2 : Spin m n} {p: Point m n}
    (p_in_r1 : p.IsInside r1) (p_not_in_r2 : ¬p.IsInside r2)
    (h_s1 : s1.IsSpinAbout r1) (h_s2 : s2.IsSpinAbout r2)
    (h_s1s2_r3 : (s1 * s2).IsSpinAbout r3)
    (r2_in_r1 : ∀ (p : Point m n), p.IsInside r2 → p.IsInside r1)
    -- This args is only needed for the final parts
    (p_is_corner : p = r1.topLeft ∨ p = r1.bottomRight)
    : False := by
  dsimp [Spin.IsSpinAbout, Rectangle.toSpin] at h_s1s2_r3 h_s1 h_s2
  dsimp only [HMul.hMul, Mul.mul, Spin.mul, perm.actionRight] at h_s1s2_r3
  simp [h_s1, h_s2] at h_s1s2_r3
  obtain ⟨h_s1s2_r3_perm, h_s1s2_r3_orient⟩ := h_s1s2_r3
  clear h_s1 h_s2

  have : p.IsInside r3 ∧ (rotate180 p r1).IsInside r3 := by
    apply And.intro
    · by_contra! h
      have app := congrFun h_s1s2_r3_orient (to1d p)
      simp [p_not_in_r2, p_in_r1, h] at app
    · by_contra! h
      have r1_bot_in_r2 : (rotate180 p r1).IsInside r2 := by
        by_contra! h2
        have app := congrFun h_s1s2_r3_orient (to1d (rotate180 p r1))
        simp [h2, spin_stays_inside p_in_r1, h] at app
      have app := congr($h_s1s2_r3_perm (to1d (rotate180 p r1)))
      simp only [Equiv.trans_apply, Equiv.coe_fn_mk, to2d_to1d_inverse, r1_bot_in_r2, r2_in_r1,
        reduceIte, p_in_r1, rotate180_self_inverse, p_not_in_r2, h, to1d_inj] at app
      rw [app] at p_not_in_r2
      contradiction

  have ⟨r1_top_in_r3, r1_bot_in_r3⟩ : r1.topLeft.IsInside r3 ∧ r1.bottomRight.IsInside r3 := by
    rcases p_is_corner with a1 | a1
    · simp_all [r1.corners_rotate]
    · simp_all [r1.corners_rotate]

  have r3_eq_r1 : r3 = r1 := by
    ext : 1
    · have app := congrFun h_s1s2_r3_orient (to1d r3.topLeft)
      ext
      all_goals
        by_contra
        have : ¬r3.topLeft.IsInside r1 := by dsimp [Point.IsInside] at r1_top_in_r3 ⊢; omega
        simp [this, mt (r2_in_r1 r3.topLeft) this, r3.corners_inside] at app
    · have app := congrFun h_s1s2_r3_orient (to1d r3.bottomRight)
      ext
      all_goals
        by_contra
        have : ¬r3.bottomRight.IsInside r1 := by dsimp [Point.IsInside] at r1_bot_in_r3 ⊢; omega
        simp [this, mt (r2_in_r1 r3.bottomRight) this, r3.corners_inside] at app
  have app_orient := congrFun h_s1s2_r3_orient (to1d r2.topLeft)
  simp [r2.corners_inside, r3_eq_r1, r2_in_r1] at app_orient
  have := r2_in_r1 r2.bottomRight r2.corners_inside.2
  dsimp [Point.IsInside, rotate180, rotateCalc] at app_orient this
  omega

lemma s1s2_not_spin.aux2 {r1 r2 r3 : Rectangle m n} {s1 s2 : Spin m n} {p: Point m n}
    -- This is implied by the last arg, but most of the proof needs only this weaker
    -- assumption, so we leave it to show intention
    (p_in_r2 : p.IsInside r2)
    (h_s1 : s1.IsSpinAbout r1) (h_s2 : s2.IsSpinAbout r2)
    (h_s1s2_r3 : (s1 * s2).IsSpinAbout r3)
    (r1_in_r2 : ∀ (p : Point m n), p.IsInside r1 → p.IsInside r2)
    (p_rot_not_in_r1 : ¬(rotate180 p r2).IsInside r1)
    (p_is_corner: p = r2.topLeft ∨ p = r2.bottomRight)
    : False := by
  dsimp only [Spin.IsSpinAbout, Rectangle.toSpin] at h_s1s2_r3 h_s1 h_s2
  dsimp only [HMul.hMul, Mul.mul, Spin.mul, perm.actionRight] at h_s1s2_r3
  simp [h_s1, h_s2] at h_s1s2_r3
  obtain ⟨h_s1s2_r3_perm, h_s1s2_r3_orient⟩ := h_s1s2_r3
  clear h_s1 h_s2

  have r3_top_in_r2 : r3.topLeft.IsInside r2 := by
    by_contra! h
    have app := congrFun h_s1s2_r3_orient (to1d r3.topLeft)
    simp [r3.corners_inside, h] at app
    exact h (r1_in_r2 r3.topLeft app)

  have r3_bot_in_r2 : r3.bottomRight.IsInside r2 := by
    by_contra! h
    have app := congrFun h_s1s2_r3_orient (to1d r3.bottomRight)
    simp [r3.corners_inside, h] at app
    exact h (r1_in_r2 r3.bottomRight app)

  have r2_bot_in_r3 : p.IsInside r3 := by
    by_contra! h
    have app := congr($h_s1s2_r3_orient (to1d p))
    simp [p_rot_not_in_r1, h, p_in_r2] at app

  have r2_top_not_in_r3 : ¬(rotate180 p r2).IsInside r3 := by
    by_contra! h
    have r2_eq_r3 : r2 = r3 := by
      dsimp [Point.IsInside, rotate180, rotateCalc] at r3_top_in_r2 r3_bot_in_r2 r2_bot_in_r3 h
      rcases p_is_corner with rfl | rfl <;> ext <;> omega
    have app := congrFun h_s1s2_r3_orient (to1d (rotate180 r1.bottomRight r2))
    have r1_bot_in_r3 : r1.bottomRight.IsInside r3 := by
      rw [← r2_eq_r3]
      exact r1_in_r2 r1.bottomRight r1.corners_inside.2
    simp [r1_bot_in_r3, spin_stays_inside, r2_eq_r3, r1.corners_inside] at app

  have app := congr($h_s1s2_r3_perm (to1d (rotate180 p r2)))
  simp only [Equiv.trans_apply, Equiv.coe_fn_mk, to2d_to1d_inverse, p_rot_not_in_r1, reduceIte,
    p_in_r2, spin_stays_inside, rotate180_self_inverse, r2_top_not_in_r3, to1d_inj] at app
  rw [app, rotate180_self_inverse p_in_r2] at r2_top_not_in_r3
  contradiction

lemma s1s2_not_spin.aux3 {r1 r2: Rectangle m n} (h1: r1.Contains r2) (h_r1_ne_r2 : r1 ≠ r2)
    : ¬r1.topLeft.IsInside r2 ∨ ¬r1.bottomRight.IsInside r2 := by
  have r2_in_r1 : r2.topLeft.IsInside r1 ∧ r2.bottomRight.IsInside r1 :=
    ⟨h1 r2.topLeft r2.corners_inside.1, h1 r2.bottomRight r2.corners_inside.2⟩
  have : ∃ p : Point .., p.IsInside r1 ∧ ¬p.IsInside r2 := by
    by_contra! h
    apply h_r1_ne_r2
    have a1 : r1.topLeft.IsInside r2 := h r1.topLeft r1.corners_inside.1
    have b1 : r1.bottomRight.IsInside r2 := h r1.bottomRight r1.corners_inside.2
    dsimp only [Point.IsInside] at a1 b1 r2_in_r1
    ext <;> omega
  by_contra! h
  have : ∀ (p : Point m n), p.IsInside r1 → p.IsInside r2 := by
    dsimp [Point.IsInside] at h ⊢
    omega
  aesop

theorem s1s2_not_spin {s1 s2 : Spin m n} (h_s1 : s1.IsSpinAbout r1) (h_s2 : s2.IsSpinAbout r2) :
    ¬IsLowercaseSpin (s1 * s2) := by
  intro ⟨r3, h_s1s2_r3⟩

  have h_r1_ne_r2 : r1 ≠ r2 := by -- feels like there should be a simpler way to do this
    intro h1
    absurd (s1_eq_s2_of_r1_eq_r2 h_s1 h_s2 h1)
    intro h2
    rw [h2] at h_s1s2_r3
    exact spin_inverse_is_not_spin h_s2 h_s1s2_r3

  let exists_p1_p2 :=
    (∃ p1 : Point .., p1.IsInside r1 ∧ ¬p1.IsInside r2) ∧
    (∃ p2 : Point .., p2.IsInside r2 ∧ ¬p2.IsInside r1)

  by_cases h_exists_p1_p2 : exists_p1_p2
  · dsimp [Spin.IsSpinAbout, Rectangle.toSpin] at h_s1s2_r3 h_s1 h_s2
    dsimp only [HMul.hMul, Mul.mul, Spin.mul, perm.actionRight] at h_s1s2_r3
    simp [h_s1, h_s2] at h_s1s2_r3
    obtain ⟨h_s1s2_r3_perm, h_s1s2_r3_orient⟩ := h_s1s2_r3
    clear h_s1 h_s2

    obtain ⟨p1, h_p1_r1, h_p1_not_r2⟩ := h_exists_p1_p2.left
    obtain ⟨p2, h_p2_r2, h_p2_not_r1⟩ := h_exists_p1_p2.right

    have r2_r3_commonCenter : CommonCenter r2 r3 := by
      have app := congr($h_s1s2_r3_perm (to1d p2))
      simp [h_p2_r2, h_p2_not_r1] at app
      have : p2.IsInside r3 := by
        by_contra h
        have app_2 := congrFun h_s1s2_r3_orient (to1d (rotate180 p2 r2))
        simp [spin_stays_inside, h_p2_r2, h_p2_not_r1, h, app] at app_2
      refine rect_commonCenter_if_rotate_eq h_p2_r2 this ?_
      simp_rw [this, reduceIte, to1d_inj] at app
      rw [← app]

    have r1_r3_commonCenter : CommonCenter r1 r3 := by
      have app := congr($h_s1s2_r3_perm (to1d (rotate180 p1 r1)))
      simp [spin_stays_inside, h_p1_r1, h_p1_not_r2] at app
      have : (rotate180 p1 r1).IsInside r3 := by
        by_contra h
        simp [h] at app
        rw [← app] at h
        have app_2 := congrFun h_s1s2_r3_orient (to1d p1)
        simp [h, app.symm, h_p1_r1, h_p1_not_r2] at app_2
      refine rect_commonCenter_if_rotate_eq (spin_stays_inside h_p1_r1) this ?_
      simp_rw [this, reduceIte, to1d_inj] at app
      rw [← app, rotate180_self_inverse h_p1_r1]

    dsimp [CommonCenter] at r1_r3_commonCenter r2_r3_commonCenter

    have r1_top_not_in_r2 : ¬r1.topLeft.IsInside r2 := by
      by_contra! h
      dsimp [Point.IsInside] at h h_p1_r1 h_p1_not_r2
      omega

    have r1_top_in_r3 : r1.topLeft.IsInside r3 := by
      by_contra! h
      have app := congrFun h_s1s2_r3_orient (to1d r1.topLeft)
      simp [r1.corners_inside, r1_top_not_in_r2, h] at app
    have r3_top_in_r1 : r3.topLeft.IsInside r1 := by
      have r3_top_not_in_r2 : ¬r3.topLeft.IsInside r2 := by
        dsimp [Point.IsInside] at r1_top_not_in_r2 r1_top_in_r3 ⊢
        omega
      have app := congrFun h_s1s2_r3_orient (to1d r3.topLeft)
      simpa [r3.corners_inside, r3_top_not_in_r2] using app

    have r1_eq_r3 : r1 = r3 := by
      ext : 1
      · dsimp [Point.IsInside] at r3_top_in_r1 r1_top_in_r3
        ext <;> omega
      · have r3_bot_in_r1 : r3.bottomRight.IsInside r1 := by
          dsimp [Point.IsInside] at r3_top_in_r1 ⊢
          omega
        have r1_bot_in_r3 : r1.bottomRight.IsInside r3 := by
          dsimp [Point.IsInside] at r1_top_in_r3 ⊢
          omega
        dsimp [Point.IsInside] at r3_bot_in_r1 r1_bot_in_r3
        ext <;> omega

    have r2_top_not_in_r3 : ¬r2.topLeft.IsInside r3 := by
      dsimp [Point.IsInside] at h_p2_r2 h_p2_not_r1 r3_top_in_r1 ⊢
      omega
    have r2_bot_in_r3 : r2.bottomRight.IsInside r3 := by
      by_contra! h
      have app_orient := congrFun h_s1s2_r3_orient (to1d r2.topLeft)
      simp [h, r2_top_not_in_r3, r2.corners_rotate, r2.corners_inside, r1_eq_r3] at app_orient

    dsimp [Point.IsInside] at r2_bot_in_r3 r2_top_not_in_r3
    omega
  · have r1_contains_r2_or_r2_contains_r1 : r1.Contains r2 ∨ r2.Contains r1 := by
      by_contra! h
      simp [exists_p1_p2] at h_exists_p1_p2
      simp [Rectangle.Contains] at h
      obtain ⟨p1, h_p1⟩ := h.left
      obtain ⟨p2, h_p2⟩ := h.right
      absurd h_p1.right
      exact h_exists_p1_p2 p2 h_p2.left h_p2.right p1 h_p1.left

    rcases r1_contains_r2_or_r2_contains_r1 with h | h
    · rcases s1s2_not_spin.aux3 h h_r1_ne_r2 with h_corner | h_corner
      · exact s1s2_not_spin.aux1 r1.corners_inside.1 h_corner h_s1 h_s2 h_s1s2_r3 h (Or.inl rfl)
      · exact s1s2_not_spin.aux1 r1.corners_inside.2 h_corner h_s1 h_s2 h_s1s2_r3 h (Or.inr rfl)
    · rcases s1s2_not_spin.aux3 h h_r1_ne_r2.symm with h_corner | h_corner
      · apply s1s2_not_spin.aux2 r2.corners_inside.2 h_s1 h_s2 h_s1s2_r3 h
        simp [r2.corners_rotate, h_corner]; exact Or.inr rfl
      · apply s1s2_not_spin.aux2 r2.corners_inside.1  h_s1 h_s2 h_s1s2_r3 h
        simp [r2.corners_rotate, h_corner]; exact Or.inl rfl

-- proposition 3
def DisjointRect (r1 r2 : Rectangle m n) : Prop :=
  ∀ p : Point .., p.IsInside r1 → ¬p.IsInside r2

lemma rect_disjoint_eq : DisjointRect r1 r2 ↔
    (r1.bottomRight.row < r2.topLeft.row ∨ r1.bottomRight.col < r2.topLeft.col ∨
    r2.bottomRight.row < r1.topLeft.row ∨ r2.bottomRight.col < r1.topLeft.col) := by
  unfold DisjointRect Point.IsInside
  apply Iff.intro
  · intro a
    contrapose! a
    have : _ ∧ _ ∧ _ ∧ _ := ⟨r1.validRow, r1.validCol, r2.validRow, r2.validCol⟩
    by_cases h1 : r2.topLeft.row ≤ r1.topLeft.row
    · by_cases h2 : r2.topLeft.col ≤ r1.topLeft.col
      · use ⟨r1.topLeft.row, r1.topLeft.col⟩
        simp only [true_and]; omega
      · use ⟨r1.topLeft.row, r2.topLeft.col⟩
        simp only [true_and]; omega
    · by_cases h2 : r2.topLeft.col ≤ r1.topLeft.col
      · use ⟨r2.topLeft.row, r1.topLeft.col⟩
        simp only [true_and]; omega
      · use ⟨r2.topLeft.row, r2.topLeft.col⟩
        simp only [true_and]; omega
  · omega

lemma rect_disjoint_comm : DisjointRect r1 r2 ↔ DisjointRect r2 r1 := by
  simp only [rect_disjoint_eq]
  omega

lemma spin_stays_outside_disj (h1 : Point.IsInside p r2) (h2 : DisjointRect r1 r2) :
    ¬(rotate180 p r2).IsInside r1 := by
  rw [rect_disjoint_comm] at h2
  exact h2 _ (spin_stays_inside h1)

lemma spin_stays_outside_cent (h1 : CommonCenter r1 r2) (h2 : ¬Point.IsInside p r1)
    (h3 : Point.IsInside p r2) : ¬(rotate180 p r2).IsInside r1 := by
  have h1 := commonCenter_rotate h1
  contrapose! h1
  use (rotate180 p r2)
  simp_rw [spin_stays_inside h3, h1, true_and]
  by_contra a
  absurd h2
  rw [rotate180_self_inverse h3] at a
  rw [a]
  exact spin_stays_inside h1

lemma spin_stays_inside_cent {p : Point m n} (h1 : CommonCenter r1 r2) (h2 : Point.IsInside p r1)
    (h3 : Point.IsInside p r2) : (rotate180 p r2).IsInside r1 := by
  rw [commonCenter_rotate h1 _ ⟨h2, h3⟩]
  exact spin_stays_inside h2

lemma calc_for_rotate {a b c d e : Nat} (h : d - (b - (e - a) - c) = b - (d - (e - c) - a))
    (_ : a ≤ e) (_ : c ≤ e) (_ : e ≤ b) (_ : e ≤ d) : d - (e - c) = b - (e - a) := by omega

lemma rotate_eq_if_comm (h1 : rotate180 (rotate180 p r1) r2 = rotate180 (rotate180 p r2) r1)
    (h2 : p.IsInside r1) (h3 : p.IsInside r2) :
    rotate180 p r2 = rotate180 p r1 := by
  simp only [rotate180, rotateCalc, Point.mk.injEq, Fin.mk.injEq] at h1 ⊢
  apply And.intro
  · rw [calc_for_rotate h1.left h2.left h3.left h2.right.left h3.right.left]
  · have h4 := h2.right.right
    have h5 := h3.right.right
    rw [calc_for_rotate h1.right h4.left h5.left h4.right h5.right]

lemma spin_not_comm_if_outside (h_s1 : Spin.IsSpinAbout s1 r1) (h_s2 : Spin.IsSpinAbout s2 r2)
    (h3 : Point.IsInside p r1) (h4 : Point.IsInside p r2)
    (h6 : ¬(rotate180 p r2).IsInside r1) :
    (fun i ↦ s1.u (s2.α.symm i) + s2.u i) ≠ (fun i ↦ s2.u (s1.α.symm i) + s1.u i) := by
  by_contra a
  rw [h_s1, h_s2, Function.funext_iff] at a
  specialize a (to1d (rotate180 p r2))
  simp [Rectangle.toSpin, h3, h4, h6, spin_stays_inside] at a

theorem s1s2_eq_s2s1_iff {s1 s2 : Spin m n} (h_s1 : s1.IsSpinAbout r1) (h_s2 : s2.IsSpinAbout r2) :
    s1 * s2 = s2 * s1 ↔ (DisjointRect r1 r2 ∨ CommonCenter r1 r2) := by
  apply Iff.intro
  · intro h
    dsimp only [HMul.hMul, Mul.mul, Spin.mul, perm.actionRight] at h
    simp_rw [Equiv.invFun_as_coe, Spin.mk.injEq] at h
    by_cases h1 : DisjointRect r1 r2
    · exact Or.inl h1
    · apply Or.inr
      apply rect_commonCenter ?_ (by simpa [DisjointRect] using h1)
      intro p a
      have hp : s1.α.trans s2.α (to1d p) = s2.α.trans s1.α (to1d p) := by simp_rw [h]

      rw [h_s1, h_s2] at hp
      simp_rw [Equiv.trans_apply, Rectangle.toSpin, Equiv.coe_fn_mk, to2d_to1d_inverse,
        a, ite_true, to2d_to1d_inverse] at hp

      by_cases h1 : (rotate180 p r1).IsInside r2
      · by_cases h2 : (rotate180 p r2).IsInside r1
        · simp_rw [h1, h2, ite_true, to1d_inj] at hp
          exact rotate_eq_if_comm hp a.left a.right
        · absurd h.right
          exact spin_not_comm_if_outside h_s1 h_s2 a.left a.right h2
      · by_cases h2 : (rotate180 p r2).IsInside r1
        · absurd h.right
          exact (spin_not_comm_if_outside h_s2 h_s1 a.right a.left h1).symm
        · simp_rw [h1, h2, ite_false, to1d_inj] at hp
          exact hp.symm
  · intro h
    rw [h_s1, h_s2]
    dsimp only [HMul.hMul, Mul.mul, Spin.mul, perm.actionRight]
    simp_rw [Equiv.invFun_as_coe, Spin.mk.injEq, Nat.mul_eq, Rectangle.toSpin, Equiv.coe_fn_symm_mk]
    rcases h with a | a
    · apply And.intro
      · apply Equiv.ext
        intro p
        simp_rw [Equiv.trans_apply, Equiv.coe_fn_mk]
        by_cases h1 : (to2d p).IsInside r1
        · by_cases h2 : (to2d p).IsInside r2
          · exact (a (to2d p) h1 h2).elim
          · have h3 := spin_stays_outside_disj h1 (rect_disjoint_comm.mp a)
            simp_rw [h2, ite_false, h1, ite_true, to2d_to1d_inverse, h3, ite_false]
        · by_cases h2 : (to2d p).IsInside r2
          · have h3 := spin_stays_outside_disj h2 a
            simp_rw [h1, ite_false, h2, ite_true, to2d_to1d_inverse, h3, ite_false]
          · simp_rw [h1, h2, ite_false, h1, h2, ite_false]
      · funext p
        by_cases h1 : (to2d p).IsInside r1
        · by_cases h2 : (to2d p).IsInside r2
          · exact (a (to2d p) h1 h2).elim
          · have h3 := spin_stays_outside_disj h1 (rect_disjoint_comm.mp a)
            simp_rw [h2, ite_false, h1, ite_true, to2d_to1d_inverse, h3, ite_false, add_comm]
        · by_cases h2 : (to2d p).IsInside r2
          · have h3 := spin_stays_outside_disj h2 a
            simp_rw [h1, ite_false, h2, ite_true, to2d_to1d_inverse, h3, ite_false, add_comm]
          · simp_rw [h1, h2, ite_false, h1, h2]
    · apply And.intro
      · apply Equiv.ext
        intro p
        simp_rw [Equiv.trans_apply, Equiv.coe_fn_mk]
        by_cases h1 : (to2d p).IsInside r1
        · by_cases h2 : (to2d p).IsInside r2
          · have h3 := spin_stays_inside_cent a h1 h2
            have h4 := spin_stays_inside_cent (commonCenter_comm.mp a) h2 h1
            simp_rw [h1, h2, ite_true, to2d_to1d_inverse, h4, ite_true, h3]
            congr 1
            simp only [spin_stays_inside h1, h4, and_self, commonCenter_rotate a, h1, h2]
          · simp_rw [h2, ite_false, h1, ite_true, to2d_to1d_inverse, ite_eq_right_iff]
            intro h3
            absurd h2
            have h4 := spin_stays_inside_cent (commonCenter_comm.mp a) h3 (spin_stays_inside h1)
            simpa only [rotate180_self_inverse h1] using h4
        · by_cases h2 : (to2d p).IsInside r2
          · have h3 := spin_stays_outside_cent a h1 h2
            simp_rw [h1, ite_false, h2, ite_true, to2d_to1d_inverse, h3, ite_false]
          · simp_rw [h2, h1, ite_false, h2, h1, ite_false]
      · funext p
        by_cases h1 : (to2d p).IsInside r1
        · by_cases h2 : (to2d p).IsInside r2
          · have h3 := spin_stays_inside_cent a h1 h2
            have h4 := spin_stays_inside_cent (commonCenter_comm.mp a) h2 h1
            simp_rw [h1, h2, ite_true, to2d_to1d_inverse, h4, h3]
          · have h3 := spin_stays_outside_cent (commonCenter_comm.mp a) h2 h1
            simp_rw [h2, ite_false, h1, ite_true, to2d_to1d_inverse, h3, ite_false, add_comm]
        · by_cases h2 : (to2d p).IsInside r2
          · have h3 := spin_stays_outside_cent a h1 h2
            simp_rw [h1, ite_false, h2, ite_true, to2d_to1d_inverse, h3, ite_false, add_comm]
          · simp_rw [h2, h1, ite_false, h2, h1]

-- proposition 4

def SameShape (r1 r2 : Rectangle m n) : Prop :=
  (r1.bottomRight.row - r1.topLeft.row) = (r2.bottomRight.row - r2.topLeft.row) ∧
  (r1.bottomRight.col - r1.topLeft.col) = (r2.bottomRight.col - r2.topLeft.col)

theorem s1s2s1_is_spin_iff {s1 s2 : Spin m n} (h_s1 : s1.IsSpinAbout r1) (h_s2 : s2.IsSpinAbout r2) :
  (∃ r3 : Rectangle m n, (s1 * s2 * s1).IsSpinAbout r3 ∧ SameShape r3 r2) ↔
  (s1 * s2 = s2 * s1 ∨ r1.Contains r2) := by
  apply Iff.intro
  · sorry
  · sorry
  -- sorry
