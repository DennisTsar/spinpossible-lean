import Spinpossible.Definitions
import Mathlib.Tactic

open scoped CharTwo -- useful since orient is in `ZMod 2` (specifically `CharTwo.two_eq_zero`)

def Spin.IsSpinAbout (s : Spin m n) (r : Rectangle m n) : Prop :=
  s = r.toSpin

/-- We say that an element of `Spin m n` is a *spin* if it is a spin about some rectangle `r` -/
def IsLowercaseSpin (s : Spin m n) : Prop :=
  ∃ (r : Rectangle m n), s.IsSpinAbout r

lemma rect_spin_mul_eq_chain : ((Rectangle.toSpin r1) * (Rectangle.toSpin r2)).actionOnBoard b =
    r2.toSpin.actionOnBoard (r1.toSpin.actionOnBoard b) := by
  simp only [Spin.mul_def, perm.mul_def, Rectangle.toSpin]
  unfold Spin.actionOnBoard
  funext i j
  by_cases h1 : Point.IsInside ⟨i, j⟩ r2
  · simp only [to2d_to1d_inverse, h1, ite_true, add_left_eq_self, ite_eq_right_iff, one_ne_zero,
      imp_false, Equiv.symm_trans_apply, Equiv.coe_fn_symm_mk, ite_eq_left_iff, zero_ne_one]
    split <;> simp
  · simp [h1]

/-- **Proposition 1.1**: A spin about a rectangle is its own inverse -/
theorem spin_is_own_inverse : performSpin r (performSpin r b) = b := by
  funext i j
  unfold performSpin Rectangle.toSpin Spin.actionOnBoard
  by_cases h : Point.IsInside ⟨i, j⟩ r
  · simp [h, spin_stays_inside, rotate180_self_inverse, orientation.other_self]
  · simp [h]

/-- **Proposition 1.1**: A spin about a rectangle is its own inverse -/
theorem spin_is_own_inverse' (h : Spin.IsSpinAbout s r) :
    s.actionOnBoard (s.actionOnBoard b) = b := by
  rw [h, ←performSpin, ←performSpin, spin_is_own_inverse]

/-- **Proposition 1.1**: A spin about a rectangle is its own inverse -/
theorem spin_is_own_inverse'' (h : Spin.IsSpinAbout s r) : (s * s).actionOnBoard b = b := by
  have h1 : (s * s).actionOnBoard b = s.actionOnBoard (s.actionOnBoard b) := by
    rw [h, rect_spin_mul_eq_chain]
  simp only [h1, spin_is_own_inverse' h]

/-- **Proposition 1.1**: A spin about a rectangle is its own inverse -/
theorem spin_inverse_props (h : Spin.IsSpinAbout s r) :
    (s * s).α.toFun = id ∧ (s * s).u = fun _ => 0 := by
  rw [h]
  simp only [Spin.mul_def, perm.mul_def, Rectangle.toSpin]
  apply And.intro
  · funext p
    by_cases h1 : (to2d p).IsInside r
    · simp [h1, spin_stays_inside]
    · simp [h1]
  · funext p
    by_cases h1 : (to2d p).IsInside r
    · simp [h1, spin_stays_inside]
    · simp [h1]

lemma Rectangle.corners_inside (r : Rectangle m n) :
    r.topLeft.IsInside r ∧ r.bottomRight.IsInside r := by
  simp [Point.IsInside, r.validRow, r.validCol]

lemma Rectangle.corners_rotate (r : Rectangle m n) :
    rotate180 r.topLeft r = r.bottomRight ∧ rotate180 r.bottomRight r = r.topLeft := by
  have : _ ∧ _ := ⟨r.validCol, r.validRow⟩
  constructor <;> ext <;> (simp only [rotate180, Nat.sub_sub_self]; omega)

lemma rectangle_flips_min_one_tile (r : Rectangle m n) :
    ∃ p, r.toSpin.u p = 1 := by
  use to1d r.topLeft
  simp_rw [Rectangle.toSpin, to2d_to1d_inverse, r.corners_inside, ite_true]

lemma spin_inverse_is_not_spin (h : Spin.IsSpinAbout s r) : ¬(s * s).IsSpinAbout r2 := by
  rw [Spin.IsSpinAbout]
  intro h1
  have h2 : ∃ p, (s * s).u p = 1 := by simp_rw [h1, rectangle_flips_min_one_tile r2]
  simp_rw [spin_inverse_props h, exists_const, zero_ne_one] at h2

def CommonCenter (r1 r2 : Rectangle m n) : Prop :=
  r1.topLeft.row.val + r1.bottomRight.row.val = r2.topLeft.row.val + r2.bottomRight.row.val ∧
  r1.topLeft.col.val + r1.bottomRight.col.val = r2.topLeft.col.val + r2.bottomRight.col.val

lemma CommonCenter.rotate_eq (h : CommonCenter r1 r2) :
    ∀ p : Point .., (p.IsInside r1 ∧ p.IsInside r2) → (rotate180 p r2 = rotate180 p r1) := by
  dsimp only [CommonCenter, Point.IsInside] at *
  simp [rotate180]
  omega

lemma CommonCenter.trans (h1 : CommonCenter r1 r2) (h2 : CommonCenter r2 r3) :
    CommonCenter r1 r3 := by dsimp only [CommonCenter] at *; omega

lemma CommonCenter.symm (h : CommonCenter r1 r2) : CommonCenter r2 r1 := by
  dsimp only [CommonCenter] at *; omega

lemma commonCenter_if_rotate_eq (h1 : p.IsInside  r1) (h2 : p.IsInside r2)
    (h3 : rotate180 p r2 = rotate180 p r1) : CommonCenter r1 r2 := by
  dsimp [CommonCenter, Point.IsInside, rotate180] at *
  simp only [Point.mk.injEq, Fin.mk.injEq] at h3
  omega

/-- `r1` contains `r2` -/
def Rectangle.Contains (r1 r2 : Rectangle m n) : Prop :=
  ∀ p : Point .., p.IsInside r2 → p.IsInside r1

lemma s1_eq_s2_of_r1_eq_r2 (h_s1 : Spin.IsSpinAbout s1 r1) (h_s2 : s2.IsSpinAbout r2)
    (h : r1 = r2) : s1 = s2 := by
  calc
    s1 = r1.toSpin := h_s1
    _  = r2.toSpin := by rw [h]
    _  = s2        := h_s2.symm

lemma to1d_injective : Function.Injective (to1d : Point m n -> _)
  | p1, p2, h => by simpa only [to2d_to1d_inverse] using congr(to2d $h)

@[simp]
lemma to1d_inj : to1d p1 = to1d p2 ↔ p1 = p2 := to1d_injective.eq_iff

lemma rect_eq_if_corners_inside {r1 r2 : Rectangle m n}
    (_ : r1.topLeft.IsInside r2)
    (_ : r2.topLeft.IsInside r1)
    (_ : r1.bottomRight.IsInside r2)
    (_ : r2.bottomRight.IsInside r1)
    : r1 = r2 := by dsimp [Point.IsInside] at *; ext <;> omega

lemma s1s2_not_spin.aux1 {r1 r2 r3 : Rectangle m n} {s1 s2 : Spin m n} {p : Point m n}
    (p_in_r1 : p.IsInside r1) (p_not_in_r2 : ¬p.IsInside r2)
    (h_s1 : s1.IsSpinAbout r1) (h_s2 : s2.IsSpinAbout r2)
    (h_s1s2_r3 : (s1 * s2).IsSpinAbout r3)
    (r2_in_r1 : ∀ (p : Point m n), p.IsInside r2 → p.IsInside r1)
    -- This arg is only needed for the final parts
    (p_is_corner : p = r1.topLeft ∨ p = r1.bottomRight)
    : False := by
  dsimp only [Spin.IsSpinAbout, Rectangle.toSpin] at h_s1s2_r3 h_s1 h_s2
  simp only [h_s1, h_s2, Spin.mul_def, perm.mul_def, Spin.mk.injEq] at h_s1s2_r3
  obtain ⟨h_s1s2_r3_perm, h_s1s2_r3_orient⟩ := h_s1s2_r3
  clear h_s1 h_s2

  have : p.IsInside r3 := by
    by_contra! h
    have app := congrFun h_s1s2_r3_orient (to1d p)
    simp [p_not_in_r2, p_in_r1, h] at app
  have r2_bot_in_r3 : (rotate180 p r1).IsInside r3 := by
    by_contra! h
    have r1_bot_in_r2 : (rotate180 p r1).IsInside r2 := by
      by_contra! h2
      have app := congrFun h_s1s2_r3_orient (to1d (rotate180 p r1))
      simp [h2, spin_stays_inside p_in_r1, h] at app
    have app := congr($h_s1s2_r3_perm (to1d (rotate180 p r1)))
    simp only [Equiv.trans_apply, Equiv.coe_fn_mk, to2d_to1d_inverse, r1_bot_in_r2, r2_in_r1,
      reduceIte, p_in_r1, rotate180_self_inverse, p_not_in_r2, h, to1d_inj] at app
    exact (app ▸ p_not_in_r2) r1_bot_in_r2

  have ⟨r1_top_in_r3, r1_bot_in_r3⟩ : r1.topLeft.IsInside r3 ∧ r1.bottomRight.IsInside r3 := by
    cases p_is_corner <;> simp_all [r1.corners_rotate]

  have r3_eq_r1 : r3 = r1 := by
    apply rect_eq_if_corners_inside ?_ r1_top_in_r3 ?_ r1_bot_in_r3
    · by_contra h
      have app := congrFun h_s1s2_r3_orient (to1d r3.topLeft)
      simp [h, (r2_in_r1 r3.topLeft).mt, r3.corners_inside] at app
    · by_contra h
      have app := congrFun h_s1s2_r3_orient (to1d r3.bottomRight)
      simp [h, (r2_in_r1 r3.bottomRight).mt h, r3.corners_inside] at app
  have app_orient := congrFun h_s1s2_r3_orient (to1d r2.topLeft)
  simp [r2.corners_inside, r2.corners_rotate, r2_in_r1, r3_eq_r1] at app_orient

lemma s1s2_not_spin.aux2 {s1 s2 : Spin m n}
    -- This is implied by the last arg, but most of the proof needs only this weaker
    -- assumption, so we leave it to show intention
    (p_in_r2 : p.IsInside r2)
    (h_s1 : s1.IsSpinAbout r1) (h_s2 : s2.IsSpinAbout r2)
    (h_s1s2_r3 : (s1 * s2).IsSpinAbout r3)
    (r1_in_r2 : ∀ (p : Point m n), p.IsInside r1 → p.IsInside r2)
    (p_rot_not_in_r1 : ¬(rotate180 p r2).IsInside r1)
    (p_is_corner : p = r2.topLeft ∨ p = r2.bottomRight)
    : False := by
  dsimp only [Spin.IsSpinAbout, Rectangle.toSpin] at h_s1s2_r3 h_s1 h_s2
  simp only [h_s1, h_s2, Spin.mul_def, perm.mul_def, Spin.mk.injEq] at h_s1s2_r3
  obtain ⟨h_s1s2_r3_perm, h_s1s2_r3_orient⟩ := h_s1s2_r3
  clear h_s1 h_s2

  have r3_top_in_r2 : r3.topLeft.IsInside r2 := by
    by_contra! h
    have app := congrFun h_s1s2_r3_orient (to1d r3.topLeft)
    simp_all [r3.corners_inside, h]

  have r3_bot_in_r2 : r3.bottomRight.IsInside r2 := by
    by_contra! h
    have app := congrFun h_s1s2_r3_orient (to1d r3.bottomRight)
    simp_all [r3.corners_inside, h]

  have r2_bot_in_r3 : p.IsInside r3 := by
    by_contra! h
    have app := congr($h_s1s2_r3_orient (to1d p))
    simp [p_rot_not_in_r1, h, p_in_r2] at app

  have r2_top_not_in_r3 : ¬(rotate180 p r2).IsInside r3 := by
    by_contra! h
    have r2_eq_r3 : r2 = r3 := by
      refine rect_eq_if_corners_inside ?top r3_top_in_r2 ?bot r3_bot_in_r2 <;>
      rcases p_is_corner with rfl | rfl
      case bot.inr | top.inl => exact r2_bot_in_r3
      case bot.inl | top.inr => simpa [r2.corners_rotate] using h
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

lemma s1s2_not_spin.aux3 {r1 r2 : Rectangle m n}
    (h_contains : r1.Contains r2) (h_r1_ne_r2 : r1 ≠ r2) :
    ¬r1.topLeft.IsInside r2 ∨ ¬r1.bottomRight.IsInside r2 := by
  let ⟨_, _, _⟩ : ∃ p : Point .., p.IsInside r1 ∧ ¬p.IsInside r2 := by
    by_contra! h
    apply h_r1_ne_r2
    apply rect_eq_if_corners_inside
    · exact h r1.topLeft r1.corners_inside.1
    · exact h_contains r2.topLeft r2.corners_inside.1
    · exact h r1.bottomRight r1.corners_inside.2
    · exact h_contains r2.bottomRight r2.corners_inside.2
  dsimp [Point.IsInside] at *
  omega

/-- **Proposition 1.2**: Let `s1` and `s2` be spins about rectangles `r1` and `r2` respectively.
    `s1 * s2` is not a spin. -/
theorem s1s2_not_spin {s1 s2 : Spin m n} (h_s1 : s1.IsSpinAbout r1) (h_s2 : s2.IsSpinAbout r2) :
    ¬IsLowercaseSpin (s1 * s2) := by
  intro ⟨r3, h_s1s2_r3⟩

  have h_r1_ne_r2 : r1 ≠ r2 := by
    intro h1
    have := s1_eq_s2_of_r1_eq_r2 h_s1 h_s2 h1
    exact spin_inverse_is_not_spin h_s2 (this ▸ h_s1s2_r3)

  let exists_p1_p2 :=
    (∃ p1 p2 : Point .., p1.IsInside r1 ∧ ¬p1.IsInside r2 ∧ p2.IsInside r2 ∧ ¬p2.IsInside r1)

  by_cases h_exists_p1_p2 : exists_p1_p2
  · dsimp only [Spin.IsSpinAbout, Rectangle.toSpin] at h_s1s2_r3 h_s1 h_s2
    simp only [h_s1, h_s2, Spin.mul_def, perm.mul_def, Spin.mk.injEq] at h_s1s2_r3
    obtain ⟨h_s1s2_r3_perm, h_s1s2_r3_orient⟩ := h_s1s2_r3
    clear h_s1 h_s2

    obtain ⟨p1, p2, h_p1_r1, h_p1_not_r2, h_p2_r2, h_p2_not_r1⟩ := h_exists_p1_p2

    have r2_r3_commonCenter : CommonCenter r2 r3 := by
      have app := congr($h_s1s2_r3_perm (to1d p2))
      simp [h_p2_r2, h_p2_not_r1] at app
      have : p2.IsInside r3 := by
        by_contra h
        have app_2 := congrFun h_s1s2_r3_orient (to1d p2)
        simp [h_p2_r2, h_p2_not_r1, h, app] at app_2
      apply commonCenter_if_rotate_eq h_p2_r2 this
      simp_rw [this, reduceIte, to1d_inj] at app
      rw [← app]

    have r1_r3_commonCenter : CommonCenter r1 r3 := by
      have app := congr($h_s1s2_r3_perm (to1d (rotate180 p1 r1)))
      simp [spin_stays_inside, h_p1_r1, h_p1_not_r2] at app
      have : (rotate180 p1 r1).IsInside r3 := by
        by_contra h
        simp only [h, reduceIte, to1d_inj] at app
        rw [← app] at h
        have app_2 := congrFun h_s1s2_r3_orient (to1d p1)
        simp [h_p1_not_r2, h_p1_r1, h] at app_2
      apply commonCenter_if_rotate_eq (spin_stays_inside h_p1_r1) this
      simp_rw [this, reduceIte, to1d_inj] at app
      rw [← app, rotate180_self_inverse h_p1_r1]

    clear h_s1s2_r3_perm
    dsimp [CommonCenter] at r1_r3_commonCenter r2_r3_commonCenter

    have r1_top_not_in_r2 : ¬r1.topLeft.IsInside r2 := by
      dsimp [Point.IsInside] at h_p1_r1 h_p1_not_r2 ⊢
      omega

    have r1_top_in_r3 : r1.topLeft.IsInside r3 := by
      by_contra! h
      have app := congr($h_s1s2_r3_orient (to1d r1.topLeft))
      simp [r1.corners_inside, r1_top_not_in_r2, h] at app
    have r3_top_in_r1 : r3.topLeft.IsInside r1 := by
      have : ¬r3.topLeft.IsInside r2 := by
        dsimp [Point.IsInside] at r1_top_not_in_r2 r1_top_in_r3 ⊢
        omega
      have app := congrFun h_s1s2_r3_orient (to1d r3.topLeft)
      simpa [r3.corners_inside, this] using app

    have r1_eq_r3 : r1 = r3 := by
      apply rect_eq_if_corners_inside r1_top_in_r3 r3_top_in_r1 <;>
      dsimp [Point.IsInside] at r1_top_in_r3 r3_top_in_r1 ⊢ <;> omega

    have r2_top_not_in_r3 : ¬r2.topLeft.IsInside r3 := by
      dsimp [Point.IsInside] at h_p2_r2 h_p2_not_r1 r3_top_in_r1 ⊢
      omega
    have r2_bot_in_r3 : r2.bottomRight.IsInside r3 := by
      by_contra! h
      have app := congrFun h_s1s2_r3_orient (to1d r2.topLeft)
      simp [h, r2_top_not_in_r3, r2.corners_rotate, r2.corners_inside, r1_eq_r3] at app

    dsimp [Point.IsInside] at r2_bot_in_r3 r2_top_not_in_r3
    omega
  · have r1_contains_r2_or_r2_contains_r1 : r1.Contains r2 ∨ r2.Contains r1 := by
      by_contra! h
      simp [exists_p1_p2] at h_exists_p1_p2
      simp [Rectangle.Contains] at h
      obtain ⟨⟨p1, h_p1⟩, ⟨p2, h_p2⟩⟩ := h
      exact h_p1.2 <| h_exists_p1_p2 p2 h_p2.1 h_p2.2 p1 h_p1.1

    rcases r1_contains_r2_or_r2_contains_r1 with h | h
    · rcases s1s2_not_spin.aux3 h h_r1_ne_r2 with h_corner | h_corner
      · exact s1s2_not_spin.aux1 r1.corners_inside.1 h_corner h_s1 h_s2 h_s1s2_r3 h (Or.inl rfl)
      · exact s1s2_not_spin.aux1 r1.corners_inside.2 h_corner h_s1 h_s2 h_s1s2_r3 h (Or.inr rfl)
    · rcases s1s2_not_spin.aux3 h h_r1_ne_r2.symm with h_corner | h_corner
      · apply s1s2_not_spin.aux2 r2.corners_inside.2 h_s1 h_s2 h_s1s2_r3 h
        simp [r2.corners_rotate, h_corner]; exact Or.inr rfl
      · apply s1s2_not_spin.aux2 r2.corners_inside.1  h_s1 h_s2 h_s1s2_r3 h
        simp [r2.corners_rotate, h_corner]; exact Or.inl rfl

def DisjointRect (r1 r2 : Rectangle m n) : Prop :=
  ∀ p : Point .., p.IsInside r1 → ¬p.IsInside r2

lemma DisjointRect.symm (h : DisjointRect r1 r2) : DisjointRect r2 r1 := by
  dsimp [DisjointRect, Point.IsInside] at *
  by_cases h1 : r2.topLeft.row ≤ r1.topLeft.row
  · by_cases h2 : r2.topLeft.col ≤ r1.topLeft.col
    · specialize h r1.topLeft; omega
    · specialize h ⟨r1.topLeft.row, r2.topLeft.col⟩; fin_omega
  · by_cases h2 : r2.topLeft.col ≤ r1.topLeft.col
    · specialize h ⟨r2.topLeft.row, r1.topLeft.col⟩; fin_omega
    · specialize h r2.topLeft; omega

lemma spin_stays_outside_disj (h1 : DisjointRect r1 r2) (h2 : p.IsInside r2) :
    ¬(rotate180 p r2).IsInside r1 := h1.symm _ (spin_stays_inside h2)

lemma spin_stays_outside_cent (h1 : CommonCenter r1 r2) (h2 : ¬p.IsInside r1)
    (h3 : p.IsInside r2) : ¬(rotate180 p r2).IsInside r1 := by
  by_contra h5
  have h4 := h1.rotate_eq (rotate180 p r2)
  simp_rw [spin_stays_inside h3, and_true, h5, true_implies, rotate180_self_inverse h3] at h4
  exact h4 ▸ h2 <| spin_stays_inside h5

lemma spin_stays_inside_cent (h1 : CommonCenter r1 r2) (h2 : p.IsInside r1)
    (h3 : p.IsInside r2) : (rotate180 p r2).IsInside r1 := by
  rw [h1.rotate_eq _ ⟨h2, h3⟩]
  exact spin_stays_inside h2

lemma rotate_eq_if_comm.aux1 {a b c d e : Nat} (h : d - (b - (e - a) - c) = b - (d - (e - c) - a))
    (_ : a ≤ e) (_ : c ≤ e) (_ : e ≤ b) (_ : e ≤ d) : d - (e - c) = b - (e - a) := by omega

lemma rotate_eq_if_comm (h1 : rotate180 (rotate180 p r1) r2 = rotate180 (rotate180 p r2) r1)
    (h2 : p.IsInside r1) (h3 : p.IsInside r2) :
    rotate180 p r2 = rotate180 p r1 := by
  simp only [rotate180, Point.mk.injEq, Fin.mk.injEq] at h1 ⊢
  apply And.intro
  · rw [rotate_eq_if_comm.aux1 h1.1 h2.1 h3.1 h2.2.1 h3.2.1]
  · rw [rotate_eq_if_comm.aux1 h1.2 h2.2.2.1 h3.2.2.1 h2.2.2.2 h3.2.2.2]

lemma spin_not_comm_if_outside (h_s1 : Spin.IsSpinAbout s1 r1) (h_s2 : Spin.IsSpinAbout s2 r2)
    (h3 : p.IsInside r1) (h4 : p.IsInside r2)
    (h6 : ¬(rotate180 p r2).IsInside r1) :
    (fun i ↦ s1.u (s2.α.symm i) + s2.u i) ≠ (fun i ↦ s2.u (s1.α.symm i) + s1.u i) := by
  rw [h_s1, h_s2]
  refine Function.ne_iff.mpr ?_
  use (to1d (rotate180 p r2))
  simp [Rectangle.toSpin, h3, h4, h6, spin_stays_inside]

/-- **Proposition 1.3**: Let `s1` and `s2` be spins about rectangles `r1` and `r2` respectively.
    `s1 * s2 = s2 * s1` if and only if `r1` and `r2` are disjoint or have a common center. -/
theorem s1s2_eq_s2s1_iff {s1 s2 : Spin m n} (h_s1 : s1.IsSpinAbout r1) (h_s2 : s2.IsSpinAbout r2) :
    s1 * s2 = s2 * s1 ↔ (DisjointRect r1 r2 ∨ CommonCenter r1 r2) := by
  apply Iff.intro
  · intro h
    simp only [Spin.mul_def, perm.mul_def, Spin.mk.injEq] at h
    by_cases h1 : DisjointRect r1 r2
    · exact Or.inl h1
    · apply Or.inr
      simp only [DisjointRect, not_forall, not_not] at h1
      obtain ⟨p, hp_r1, hp_r2⟩ := h1
      apply commonCenter_if_rotate_eq hp_r1 hp_r2

      have h1 : (rotate180 p r1).IsInside r2 := by
        by_contra h1
        exact (spin_not_comm_if_outside h_s2 h_s1 hp_r2 hp_r1 h1).symm h.2
      have h2 : (rotate180 p r2).IsInside r1 := by
        by_contra h2
        exact (spin_not_comm_if_outside h_s1 h_s2 hp_r1 hp_r2 h2) h.2

      have hp : s1.α.trans s2.α (to1d p) = s2.α.trans s1.α (to1d p) := by simp_rw [h]
      rw [h_s1, h_s2] at hp
      simp_rw [Equiv.trans_apply, Rectangle.toSpin, Equiv.coe_fn_mk, to2d_to1d_inverse,
        hp_r1, hp_r2, ite_true, to2d_to1d_inverse, h1, h2, ite_true, to1d_inj] at hp
      exact rotate_eq_if_comm hp hp_r1 hp_r2
  · intro h
    rw [h_s1, h_s2]
    simp only [Spin.mul_def, perm.mul_def, Spin.mk.injEq, Rectangle.toSpin]
    rcases h with a | a
    · apply And.intro
      · apply Equiv.ext
        intro p
        simp_rw [Equiv.trans_apply, Equiv.coe_fn_mk]
        by_cases h1 : (to2d p).IsInside r1
        · by_cases h2 : (to2d p).IsInside r2
          · exact (a (to2d p) h1 h2).elim
          · have h3 := spin_stays_outside_disj a.symm h1
            simp_rw [h2, ite_false, h1, ite_true, to2d_to1d_inverse, h3, ite_false]
        · by_cases h2 : (to2d p).IsInside r2
          · have h3 := spin_stays_outside_disj a h2
            simp_rw [h1, ite_false, h2, ite_true, to2d_to1d_inverse, h3, ite_false]
          · simp_rw [h1, h2, ite_false, h1, h2, ite_false]
      · funext p
        by_cases h1 : (to2d p).IsInside r1
        · by_cases h2 : (to2d p).IsInside r2
          · exact (a (to2d p) h1 h2).elim
          · have h3 := spin_stays_outside_disj a.symm h1
            simp_rw [h2, ite_false, h1, ite_true, to2d_to1d_inverse, h3, ite_false, add_comm]
        · by_cases h2 : (to2d p).IsInside r2
          · have h3 := spin_stays_outside_disj a h2
            simp_rw [h1, ite_false, h2, ite_true, to2d_to1d_inverse, h3, ite_false, add_comm]
          · simp_rw [h1, h2, ite_false, h1, h2]
    · apply And.intro
      · apply Equiv.ext
        intro p
        simp_rw [Equiv.trans_apply, Equiv.coe_fn_mk]
        by_cases h1 : (to2d p).IsInside r1
        · by_cases h2 : (to2d p).IsInside r2
          · have h3 := spin_stays_inside_cent a h1 h2
            have h4 := spin_stays_inside_cent a.symm h2 h1
            simp_rw [h1, h2, ite_true, to2d_to1d_inverse, h4, ite_true, h3]
            congr 1
            simp only [spin_stays_inside h1, h4, and_self, a.rotate_eq, h1, h2]
          · simp_rw [h2, ite_false, h1, ite_true, to2d_to1d_inverse, ite_eq_right_iff]
            intro h3
            absurd h2
            have h4 := spin_stays_inside_cent a.symm h3 (spin_stays_inside h1)
            simpa only [rotate180_self_inverse h1] using h4
        · by_cases h2 : (to2d p).IsInside r2
          · have h3 := spin_stays_outside_cent a h1 h2
            simp_rw [h1, ite_false, h2, ite_true, to2d_to1d_inverse, h3, ite_false]
          · simp_rw [h2, h1, ite_false, h2, h1, ite_false]
      · funext p
        by_cases h1 : (to2d p).IsInside r1
        · by_cases h2 : (to2d p).IsInside r2
          · have h3 := spin_stays_inside_cent a h1 h2
            have h4 := spin_stays_inside_cent a.symm h2 h1
            simp_rw [h1, h2, ite_true, to2d_to1d_inverse, h4, h3]
          · have h3 := spin_stays_outside_cent a.symm h2 h1
            simp_rw [h2, ite_false, h1, ite_true, to2d_to1d_inverse, h3, ite_false, add_comm]
        · by_cases h2 : (to2d p).IsInside r2
          · have h3 := spin_stays_outside_cent a h1 h2
            simp_rw [h1, ite_false, h2, ite_true, to2d_to1d_inverse, h3, ite_false, add_comm]
          · simp_rw [h2, h1, ite_false, h2, h1]

def SameShape (r1 r2 : Rectangle m n) : Prop :=
  (r1.bottomRight.row.val - r1.topLeft.row.val) = (r2.bottomRight.row.val - r2.topLeft.row.val) ∧
  (r1.bottomRight.col.val - r1.topLeft.col.val) = (r2.bottomRight.col.val - r2.topLeft.col.val)

lemma s1s2s1_is_spin_iff.aux1 {r1t r1b r2t r2b p : Fin x}
  (_ : r2t ≤ r2b) (_ : r1t ≤ r2t) (_ : r1b ≥ r2b)
  (_ : r1b - (r2b - r1t) ≤ p.val)
  (_ : p.val ≤ r1b - (r2t - r1t))
  : r1b.val - (r2b.val - (r1b.val - (p.val - r1t.val) - r2t.val) - r1t.val) =
    r1b.val - (r2t.val - r1t.val) - (p.val - (r1b.val - (r2b.val - r1t.val))) := by
  omega

lemma s1s2s1_is_spin_iff.aux2 {r1 r2 r3 : Rectangle m n} (h : r1.Contains r2)
    (h_r3 : r3.topLeft = rotate180 r2.bottomRight r1 ∧ r3.bottomRight = rotate180 r2.topLeft r1) :
    ∀ (p : Point m n), p.IsInside r1 → (p.IsInside r3 ↔ (rotate180 p r1).IsInside r2) := by
  intro p p_in_r1
  have : _ ∧ _ := ⟨r2.validRow, r2.validCol⟩
  have : r2.topLeft.IsInside r1 := h r2.topLeft r2.corners_inside.1
  apply Iff.intro <;>
  · dsimp [Point.IsInside, rotate180] at *
    simp only [h_r3]
    omega

/-- **Proposition 1.4**: Let `s1` and `s2` be spins about rectangles `r1` and `r2` respectively.
    `s1 * s2 * s1` is a spin `s3` if and only if either `s1` and `s2` commute or `r1` contains `r2`.
    The rectangle of `s3` has the same shape as `r2`. -/
theorem s1s2s1_is_spin_iff {s1 s2 : Spin m n} (h_s1 : s1.IsSpinAbout r1) (h_s2 : s2.IsSpinAbout r2) :
  (∃ r3 : Rectangle m n, (s1 * s2 * s1).IsSpinAbout r3 ∧ SameShape r3 r2) ↔
  (s1 * s2 = s2 * s1 ∨ r1.Contains r2) := by
  apply Iff.intro
  · by_cases h1 : r1.Contains r2
    · exact fun _ => Or.inr h1
    intro h
    apply Or.inl
    rw [(s1s2_eq_s2s1_iff h_s1 h_s2).mpr]
    by_cases h2 : DisjointRect r1 r2
    · exact Or.inl h2
    apply Or.inr
    have r2_corner_not_in_r1 : ¬r2.topLeft.IsInside r1 ∨ ¬r2.bottomRight.IsInside r1 := by
      by_contra! h
      have : ∀ (p : Point m n), p.IsInside r2 → p.IsInside r1 := by
        dsimp [Point.IsInside] at h ⊢
        omega
      exact h1 this

    obtain ⟨r3, h3, -⟩ := h
    dsimp only [Spin.IsSpinAbout, Rectangle.toSpin] at h_s1 h_s2 h3
    simp only [h_s1, h_s2, Spin.mul_def, perm.mul_def, Spin.mk.injEq] at h3
    clear h_s1 h_s2
    obtain ⟨h_perm, h_orient⟩ := h3
    rw [Equiv.ext_iff] at h_perm
    rw [Function.funext_iff] at h_orient

    simp [DisjointRect] at h2
    obtain ⟨p, h_p⟩ := h2

    have ⟨r2_r3_commonCenter, p_in_r3⟩ : CommonCenter r3 r2 ∧ p.IsInside r3 := by
      rcases r2_corner_not_in_r1 with r2_top_r1 | r2_bot_r1
      · specialize h_perm (to1d r2.topLeft)
        specialize h_orient (to1d r2.topLeft)
        simp [r2_top_r1, r2.corners_inside] at h_perm h_orient
        have : ¬(rotate180 r2.topLeft r2).IsInside r1 := by
          by_contra! h
          simp [h, apply_ite] at h_perm h_orient
          rw [if_neg h_orient] at h_perm
          exact r2_top_r1 (h_perm ▸ spin_stays_inside h)
        simp [this, apply_ite] at h_perm h_orient
        rw [if_pos h_orient] at h_perm
        have : CommonCenter r3 r2 :=
          commonCenter_if_rotate_eq h_orient r2.corners_inside.1 h_perm
        refine ⟨this, ?_⟩
        dsimp [Point.IsInside, CommonCenter] at *
        omega
      · specialize h_perm (to1d r2.bottomRight)
        specialize h_orient (to1d r2.bottomRight)
        simp [r2_bot_r1, r2.corners_inside] at h_perm h_orient
        have : ¬(rotate180 r2.bottomRight r2).IsInside r1 := by
          by_contra! h
          simp [h, apply_ite] at h_perm h_orient
          rw [if_neg h_orient] at h_perm
          exact r2_bot_r1 (h_perm ▸ spin_stays_inside h)
        simp [this, apply_ite] at h_perm h_orient
        rw [if_pos h_orient] at h_perm
        have : CommonCenter r3 r2 :=
          commonCenter_if_rotate_eq h_orient r2.corners_inside.2 h_perm
        refine ⟨this, ?_⟩
        dsimp [Point.IsInside, CommonCenter] at *
        omega

    specialize h_perm (to1d p)
    specialize h_orient (to1d p)

    by_cases this : (rotate180 p r1).IsInside r2
    swap
    · simp [this, h_p, p_in_r3] at h_orient h_perm
      simp [h_orient] at h_perm
      have : CommonCenter r1 r3 := commonCenter_if_rotate_eq h_p.1 p_in_r3 h_perm.symm
      exact this.trans r2_r3_commonCenter
    simp [this, h_p] at h_perm h_orient

    have hx : (rotate180 (rotate180 p r1) r2).IsInside r1 := by
      by_contra! hx
      simp [hx, apply_ite] at h_perm h_orient
      simp [h_orient] at h_perm
      exact (h_perm ▸ hx) h_p.1
    simp [hx, apply_ite] at h_perm h_orient
    simp [h_orient] at h_perm
    have := r2_r3_commonCenter.rotate_eq p ⟨h_orient, h_p.2⟩
    have := rotate180_self_inverse hx ▸ congr(rotate180 $(this ▸ h_perm) r1)
    have := rotate_eq_if_comm this h_p.1 h_p.2
    exact commonCenter_if_rotate_eq h_p.1 h_p.2 this
  · intro h
    rcases h with h | h
    · use r2
      simp only [SameShape, and_self, and_true]
      ext
      · -- would be nice for these first steps to be shorter
        -- also can I use `Equiv.toFun_as_coe` + `funext`?
        rw [Equiv.ext_iff]
        intro p
        rw [← to1d_to2d_inverse (p := p)] -- can I do this (and below) without the explicit `p`?
        set p := to2d p -- can I combine this with the `intro` step?
        by_contra! h_p
        have h_p2 : (s2 * s1 * s1).α.toFun (to1d p) ≠ r2.toSpin.α.toFun (to1d p) := h ▸ h_p
        dsimp only [Spin.IsSpinAbout, Rectangle.toSpin] at h_s1 h_s2 h_p h_p2
        simp only [h_s1, h_s2, Spin.mul_def, perm.mul_def, Equiv.trans_apply, Equiv.coe_fn_mk,
          to2d_to1d_inverse, ne_eq, Equiv.toFun_as_coe] at h_p h_p2
        clear h_s1 h_s2
        split_ifs at h_p2 <;> simp_all [spin_stays_inside]
      · funext p
        rw [← to1d_to2d_inverse (p := p)]
        set p := to2d p
        by_contra! h_p
        have h_p2 : (s2 * s1 * s1).u (to1d p) ≠ r2.toSpin.u (to1d p) := by rwa [h] at h_p
        dsimp only [Spin.IsSpinAbout, Rectangle.toSpin] at h_s1 h_s2 h_p h_p2
        simp only [h_s1, h_s2, Spin.mul_def, to2d_to1d_inverse, ne_eq] at h_p h_p2
        clear h_s1 h_s2
        split_ifs at h_p <;> simp_all [spin_stays_inside]
    · let r3 : Rectangle m n := ⟨
        rotate180 r2.bottomRight r1,
        rotate180 r2.topLeft r1,
        by dsimp [rotate180]; have := r2.validCol; fin_omega,
        by dsimp [rotate180]; have := r2.validRow; fin_omega,
      ⟩
      have r2_top_in_r1 := h r2.topLeft ⟨Nat.le_refl _, r2.validRow, Nat.le_refl _, r2.validCol⟩
      have r2_bot_in_r1 := h r2.bottomRight ⟨r2.validRow, Nat.le_refl _, r2.validCol, Nat.le_refl _⟩
      -- the `p.IsInside r1` is kinda superfluous, but easier to accept it than fight it
      have x : ∀ p, p.IsInside r1 → (p.IsInside r3 ↔ (rotate180 p r1).IsInside r2) :=
        s1s2s1_is_spin_iff.aux2 h ⟨rfl, rfl⟩
      have r3_in_r1 : r1.Contains r3 := by
        intro p h_p
        dsimp [Point.IsInside, rotate180] at r2_bot_in_r1 h_p ⊢
        omega
      use r3
      · apply And.intro
        · dsimp only [Spin.IsSpinAbout, Rectangle.toSpin] at h_s1 h_s2 ⊢
          simp only [h_s1, h_s2, Spin.mul_def, perm.mul_def, Spin.mk.injEq]
          clear h_s1 h_s2
          constructor
          · rw [Equiv.ext_iff]
            intro p
            simp only [Equiv.trans_apply, Equiv.coe_fn_mk]
            rw [← to1d_to2d_inverse (p := p)] -- weird that this is needed
            split_ifs <;> simp_all [spin_stays_inside, Rectangle.Contains]
            · dsimp [Point.IsInside, rotate180] at *
              simp only [Point.mk.injEq, Fin.mk.injEq]
              constructor <;> apply s1s2s1_is_spin_iff.aux1 <;> omega
          · funext p
            rw [← to1d_to2d_inverse (p := p)] -- weird that this is needed
            clear r2_bot_in_r1 r2_top_in_r1
            split_ifs <;>
            simp_all only [spin_stays_inside, Rectangle.Contains, to2d_to1d_inverse, to1d_inj,
              zero_add, CharTwo.add_self_eq_zero, zero_ne_one, not_true_eq_false, add_zero]
        · dsimp only [SameShape, Point.IsInside, rotate180] at r2_bot_in_r1 r2_top_in_r1 ⊢
          omega
