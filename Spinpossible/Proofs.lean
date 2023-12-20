import Spinpossible.Definitions

def Spin.isSpinAbout {m n : PNat} (s : Spin m n) (R : Rectangle m n) : Prop :=
  s = createRectangleSpin R

def isLowercaseSpin {m n : PNat} (s : Spin m n) : Prop :=
  ∃ (r : Rectangle m n), s.isSpinAbout r

theorem rect_spin_mul_eq_chain : ((createRectangleSpin r1) * (createRectangleSpin r2)).actionOnBoard b =
    (createRectangleSpin r2).actionOnBoard ((createRectangleSpin r1).actionOnBoard b) := by
  simp_rw [HMul.hMul, Mul.mul, Spin.mul, HMul.hMul, Mul.mul, perm.actionRight]
  unfold createRectangleSpin Spin.actionOnBoard
  funext i j
  by_cases h1 : isInsideRectangle ⟨i, j⟩ r2
  · simp only [h1, to2d_to1d_inverse, ite_true, add_left_eq_self, ite_eq_right_iff,
      one_ne_zero, imp_false, Bool.not_eq_true, Equiv.symm_trans_apply,
      Equiv.coe_fn_symm_mk, ite_eq_left_iff, zero_ne_one, Bool.not_eq_false]
    by_cases h2 : isInsideRectangle (rotate180 ⟨i, j⟩ r2) r1
    · simp_rw [h2, ite_false, ite_true, point_eq, h2, ite_true, orientation.other_self]
    · simp_rw [h2, ite_false, ite_true, point_eq, h2, ite_false]
  · simp [h1]

-- proposition 1

theorem spin_is_own_inverse : performSpin r (performSpin r b) = b := by
  funext i j
  unfold performSpin createRectangleSpin Spin.actionOnBoard
  by_cases h : isInsideRectangle ⟨i, j⟩ r
  · simp [h, spin_stays_inside, rotate180_self_inverse, orientation.other_self]
  · simp [h]

theorem spin_is_own_inverse' (h : Spin.isSpinAbout s r) :
    s.actionOnBoard (s.actionOnBoard b) = b := by
  rw [h, ←performSpin, ←performSpin, spin_is_own_inverse]

theorem spin_is_own_inverse'' (h : Spin.isSpinAbout s r) : (s * s).actionOnBoard b = b := by
  have h1 : (s * s).actionOnBoard b = s.actionOnBoard (s.actionOnBoard b) := by
    rw [h, rect_spin_mul_eq_chain]
  simp only [h1, spin_is_own_inverse' h]

theorem spin_inverse_props (h : Spin.isSpinAbout s r) :
    (s * s).α.toFun = id ∧ (s * s).u = fun _ => 0 := by
  rw [h]
  dsimp only [HMul.hMul, Mul.mul, Spin.mul]
  unfold createRectangleSpin perm.actionRight
  simp_rw [Nat.mul_eq, Equiv.toFun_as_coe, Equiv.coe_trans, Equiv.coe_fn_mk]
  apply And.intro
  . funext p
    by_cases h1 : isInsideRectangle (to2d p) r
    · simp_rw [Function.comp_apply, h1, ite_true, to2d_to1d_inverse, spin_stays_inside h1,
        ite_true, rotate180_self_inverse h1, to1d_to2d_inverse, id_eq]
    · simp [h1]
  . funext p
    by_cases h1 : isInsideRectangle (to2d p) r
    · simp_rw [h1, ite_true, to2d_to1d_inverse, spin_stays_inside h1, ite_true]; rfl
    · simp [h1]

-- proposition 2

lemma rectangle_flips_min_one_tile (R : Rectangle m n) :
    ∃ p, (createRectangleSpin R).u p = 1 := by
  let p := R.topLeft
  use to1d p
  have h : isInsideRectangle p R := by
    simp_rw [isInsideRectangle, le_refl, true_and, decide_eq_true_eq]
    exact ⟨R.validRow, R.validCol⟩
  simp_rw [createRectangleSpin, to2d_to1d_inverse, h, ite_true]

theorem spin_inverse_is_not_spin (h : Spin.isSpinAbout s r) : ¬(s * s).isSpinAbout r2 := by
  rw [Spin.isSpinAbout]
  intro h1
  have h2 : ∃ p, (s * s).u p = 1 := by simp_rw [h1, rectangle_flips_min_one_tile r2]
  simp_rw [spin_inverse_props h, exists_const, zero_ne_one] at h2

variable {m n : PNat} (s1 s2 : Spin m n) (R1 R2 : Rectangle m n)
  (h_s1 : s1.isSpinAbout R1) (h_s2 : s2.isSpinAbout R2)

def moves_tile (s : Spin m n) (p : Fin (m * n)) (R : Rectangle m n) : Prop :=
  let newPos := s.α.symm (to1d (to2d p))
  newPos ≠ p ∧ isInsideRectangle (to2d newPos) R

def common_center (R1 R2 : Rectangle m n) : Prop :=
  -- technically center * 2 but we don't care
  let center1 := (R1.topLeft.row + R1.bottomRight.row, R1.topLeft.col + R1.bottomRight.col)
  let center2 := (R2.topLeft.row + R2.bottomRight.row, R2.topLeft.col + R2.bottomRight.col)
  center1 = center2

lemma s1_eq_s2_of_R1_eq_R2 (h_R1_eq_R2 : R1 = R2) : s1 = s2 := by
  -- Since s1 is a spin about R1 and s2 is a spin about R2, and R1 = R2
  -- it follows that s1 and s2 are both spins about the same rectangle (R1 or R2)
  calc
    s1 = createRectangleSpin R1 := by rw [h_s1]
    _  = createRectangleSpin R2 := by rw [h_R1_eq_R2]
    _  = s2                     := by rw [h_s2.symm]

-- Assuming that s1 and s2 are spins about R1 and R2, respectively
-- and that s1 ≠ s2
lemma R1_ne_R2_of_s1_ne_s2 (h_s1_ne_s2 : s1 ≠ s2) : R1 ≠ R2 := by
  by_contra h
  have h_s1_eq_s2 : s1 = s2 := s1_eq_s2_of_R1_eq_R2 _ _ _ _ h_s1 h_s2 h
  contradiction

theorem s1s2_not_spin : ¬isLowercaseSpin (s1 * s2) := by
  rintro ⟨R3, h_s1s2_R3⟩

  have h_R1_ne_R2 : R1 ≠ R2 := R1_ne_R2_of_s1_ne_s2 _ _ _ _ h_s1 h_s2 sorry

  -- Handling the existence of p1 and p2
  obtain ⟨p1, h_p1_in_R1, h_p1_not_in_R2⟩ :
    ∃ p1, isInsideRectangle p1 R1 ∧ ¬isInsideRectangle p1 R2 := by sorry
  obtain ⟨p2, h_p2_in_R2, h_p2_not_in_R1⟩ :
    ∃ p2, isInsideRectangle p2 R2 ∧ ¬isInsideRectangle p2 R1 := by sorry

  have h_s1s2_moves_p1 : moves_tile (s1 * s2) (to1d p1) R3 := by sorry
  have h_s1s2_moves_p2 : moves_tile (s1 * s2) (to1d p2) R3 := by sorry

  have h_common_center_R1_R3 : common_center R1 R3 := by sorry
  have h_common_center_R2_R3 : common_center R2 R3 := by sorry

  sorry

-- proposition 3
def rectangles_disjoint (R1 R2 : Rectangle m n) : Prop :=
  R1.bottomRight.row < R2.topLeft.row ∨ R1.bottomRight.col < R2.topLeft.col ∨
  R2.bottomRight.row < R1.topLeft.row ∨ R2.bottomRight.col < R1.topLeft.col

-- def apply_spin {m n : PosNat} (s : Spin m n) (p : Point m n) (orient : orientation) :=
--   let newPos := to_2d (s.α.symm (to_1d p))
--   let newOrient := if s.u (to_1d p) = 1 then flipOrientation orient else orient
--   (newPos, newOrient)


theorem s1s2_eq_s2s1_iff : s1 * s2 = s2 * s1 ↔ (rectangles_disjoint R1 R2 ∨ common_center R1 R2) := by
  apply Iff.intro

  -- Forward direction
  intro h
  by_contra
  have h_not_disjoint : ¬rectangles_disjoint R1 R2 := by sorry  -- Proof needed
  have h_not_common_center : ¬common_center R1 R2 := by sorry  -- Proof needed
  sorry -- Derive a contradiction from these conditions and h: s1 * s2 = s2 * s1

  -- Reverse direction
  intro h
  cases h
  -- Case 1: R1 and R2 are disjoint
  sorry -- Proof that s1s2 = s2s1 when R1 and R2 are disjoint
  -- Case 2: R1 and R2 have a common center
  sorry -- Proof that s1s2 = s2s1 when R1 and R2 have a common center


-- proposition 4

def rectangle_contains (R1 R2 : Rectangle m n) : Prop :=
  isInsideRectangle R2.topLeft R1 ∧ isInsideRectangle R2.bottomRight R1

def same_shape (R1 R2 : Rectangle m n) : Prop :=
  (R1.bottomRight.row - R1.topLeft.row) = (R2.bottomRight.row - R2.topLeft.row) ∧
  (R1.bottomRight.col - R1.topLeft.col) = (R2.bottomRight.col - R2.topLeft.col)

theorem s1s2s1_is_spin_iff :
  (∃ R3 : Rectangle m n, (s1 * s2 * s1).isSpinAbout R3 ∧ same_shape R3 R2) ↔
  (s1 * s2 = s2 * s1 ∨ rectangle_contains R1 R2) := by
  apply Iff.intro

  -- Forward direction
  intro h
  -- Extract the existence of R3 and its properties
  obtain ⟨R3, h_s3_R3, h_shape_R3_R2⟩ := h
  -- Now, use h_s3_R3 and h_shape_R3_R2 to prove the right-hand side of the equivalence
  sorry

  -- Reverse direction
  intro h
  cases h
  -- Case 1: s1 and s2 commute
  sorry
  -- Case 2: R1 contains R2
  -- Prove the existence of R3 that is a spin s3 and has the same shape as R2
  sorry
