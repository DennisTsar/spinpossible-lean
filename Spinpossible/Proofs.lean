import Spinpossible.Definitions

def Spin.isSpinAbout (s : Spin m n) (R : Rectangle m n) : Prop :=
  s = createRectangleSpin R

def isLowercaseSpin (s : Spin m n) : Prop :=
  ∃ (r : Rectangle m n), s.isSpinAbout r

theorem rect_spin_mul_eq_chain : ((createRectangleSpin r1) * (createRectangleSpin r2)).actionOnBoard b =
    (createRectangleSpin r2).actionOnBoard ((createRectangleSpin r1).actionOnBoard b) := by
  simp_rw [HMul.hMul, Mul.mul, Spin.mul, HMul.hMul, Mul.mul, perm.actionRight]
  unfold createRectangleSpin Spin.actionOnBoard
  funext i j
  by_cases h1 : isInsideRectangle ⟨i, j⟩ r2
  · simp only [to2d_to1d_inverse, h1, ite_true, add_left_eq_self, ite_eq_right_iff, one_ne_zero,
      imp_false, Bool.not_eq_true, Equiv.symm_trans_apply, Equiv.coe_fn_symm_mk, ite_eq_left_iff,
      zero_ne_one, Bool.not_eq_false]
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

def moves_tile (s : Spin m n) (p : Fin (m * n)) (R : Rectangle m n) :=
  let newPos := s.α.symm (to1d (to2d p))
  newPos ≠ p ∧ isInsideRectangle (to2d newPos) R

def common_center (R1 R2 : Rectangle m n) :=
  -- technically center * 2 but we don't care
  let center1 := (R1.topLeft.row + R1.bottomRight.row, R1.topLeft.col + R1.bottomRight.col)
  let center2 := (R2.topLeft.row + R2.bottomRight.row, R2.topLeft.col + R2.bottomRight.col)
  center1 = center2

def rectangle_contains (R1 R2 : Rectangle m n) :=
  ∀ p, isInsideRectangle p R1 → isInsideRectangle p R2

-- def rectangle_contains2 (R1 R2 : Rectangle m n) : Prop :=
--   isInsideRectangle R2.topLeft R1 ∧ isInsideRectangle R2.bottomRight R1

lemma s1_eq_s2_of_R1_eq_R2 (h_s1 : Spin.isSpinAbout s1 r1) (h_s2 : s2.isSpinAbout r2)
    (h : r1 = r2) : s1 = s2 := by
  calc
    s1 = createRectangleSpin r1 := by rw [h_s1]
    _  = createRectangleSpin r2 := by rw [h]
    _  = s2                     := by rw [h_s2.symm]

lemma point_outside_unaffected (h1 : s1.isSpinAbout r1) (h2 : s2.isSpinAbout r2)
    (h3 : Spin.isSpinAbout (s1 * s2) r3)
    (h4 : isInsideRectangle p r1 ∧ ¬isInsideRectangle p r2) :
    (performSpin r1 b) p.row p.col = (performSpin r3 b) p.row p.col := by
  let a := performSpin r1 b
  have x : (performSpin r3 b) p.row p.col = (performSpin r2 a) p.row p.col := by
    dsimp only [performSpin]
    have x2 : (createRectangleSpin r3).actionOnBoard b = (s1 * s2).actionOnBoard b := by
      rw [h3]
    have x3 : (s1 * s2).actionOnBoard b =
        (createRectangleSpin r2).actionOnBoard ((createRectangleSpin r1).actionOnBoard b) := by
      rw [h1, h2, rect_spin_mul_eq_chain]
    simp only [x2, x3]
  have y : (performSpin r2 a) p.row p.col = a p.row p.col := by
    dsimp only [performSpin, createRectangleSpin, Spin.actionOnBoard]
    simp [h4.right, to2d_to1d_inverse]
  rw [x, y]

lemma point_outside_rect_unchanged (h : ¬isInsideRectangle p r) :
    (performSpin r b) p.row p.col = b p.row p.col := by
  simp [performSpin, createRectangleSpin, Spin.actionOnBoard, h]

theorem s1s2_not_spin {s1 s2 : Spin m n} (h_s1 : s1.isSpinAbout R1) (h_s2 : s2.isSpinAbout R2)
    : ¬isLowercaseSpin (s1 * s2) := by
  intro ⟨R3, h_s1s2_R3⟩

  have h_R1_ne_R2 : R1 ≠ R2 := by -- feels like there should be a simpler way to do this
    intro h
    have := s1_eq_s2_of_R1_eq_R2 h_s1 h_s2 h
    have s1_ne_s2 : s1 ≠ s2 := by
      intro h
      rw [h] at h_s1s2_R3
      exact spin_inverse_is_not_spin h_s2 h_s1s2_R3
    contradiction

  let exists_p1_p2 :=
    (∃ p1, isInsideRectangle p1 R1 ∧ ¬isInsideRectangle p1 R2) ∧
    (∃ p2, isInsideRectangle p2 R2 ∧ ¬isInsideRectangle p2 R1)

  by_cases h_exists_p1_p2 : exists_p1_p2
  . obtain ⟨p1, h_p1_R1, h_p1_not_R2⟩ := h_exists_p1_p2.left
    obtain ⟨p2, h_p2_R2, h_p2_not_R1⟩ := h_exists_p1_p2.right
    have a1 : (b : board m n) → (performSpin R1 b) p1.row p1.col = (performSpin R3 b) p1.row p1.col := by
      intro b
      exact point_outside_unaffected h_s1 h_s2 h_s1s2_R3 ⟨h_p1_R1, h_p1_not_R2⟩
    have a2 : (b : board m n) → (performSpin R1 b) p2.row p2.col = b p2.row p2.col := by
      intro b
      exact point_outside_rect_unchanged h_p2_not_R1
    have a3 : (createRectangleSpin R2).α.toFun (to1d p2) = (createRectangleSpin R3).α.toFun (to1d p2) := by
      have a3_2 : (createRectangleSpin R3).α.toFun (to1d p2) = (s1 * s2).α.toFun (to1d p2) := by
        rw [h_s1s2_R3]
      have a3_4 : (createRectangleSpin R2).α.toFun (to1d p2) = (s1 * s2).α.toFun (to1d p2) := by
        have a3_3 : (createRectangleSpin R1).α.toFun (to1d p2) = to1d p2 := by
          simp only [Equiv.toFun_as_coe, createRectangleSpin]
          simp_all only [ne_eq, Bool.not_eq_true, Equiv.toFun_as_coe, Equiv.coe_fn_mk, to2d_to1d_inverse, ite_false]
        rw [Equiv.toFun_as_coe, h_s1, h_s2]
        dsimp only [HMul.hMul, Mul.mul, Spin.mul]
        exact congrArg ((createRectangleSpin R2).α.toFun) (id a3_3.symm)
      simp only [a3_2, a3_4, Equiv.toFun_as_coe]

    have a4 : isInsideRectangle p1 R3 := by
      simp [isInsideRectangle, le_refl, true_and, decide_eq_true_eq]
      sorry

    have q1 : ∃ p, isInsideRectangle p R1 ∧ isInsideRectangle p R2 ∧ isInsideRectangle p R3 := by
      sorry
    sorry
  . have R1_contains_R2_or_R2_contains_R1 : rectangle_contains R1 R3 ∨ rectangle_contains R2 R3 := by
      by_contra h
      push_neg at h
      sorry
    sorry

-- proposition 3
def rectangles_disjoint (R1 R2 : Rectangle m n) : Prop :=
  R1.bottomRight.row < R2.topLeft.row ∨ R1.bottomRight.col < R2.topLeft.col ∨
  R2.bottomRight.row < R1.topLeft.row ∨ R2.bottomRight.col < R1.topLeft.col

def rectangles_disjoint2 (R1 R2 : Rectangle m n) :=
  ∀ p, isInsideRectangle p R1 → ¬isInsideRectangle p R2

lemma rect_disjoint_eq : rectangles_disjoint r1 r2 ↔ rectangles_disjoint2 r1 r2 := by
  apply Iff.intro
  · unfold rectangles_disjoint2 rectangles_disjoint isInsideRectangle
    intro h p
    aesop
    · have h1 : p.row < r2.topLeft.row := by calc
        p.row ≤ r1.bottomRight.row := left_1
        _ < r2.topLeft.row := h
      exfalso
      exact (Fin.not_le.mpr h1) a_1
    · have h1 : p.col < r2.topLeft.col := by calc
        p.col ≤ r1.bottomRight.col := by exact right
        _ < r2.topLeft.col := by exact h
      exfalso
      exact (Fin.not_le.mpr h1) (a_3)
    · have h1 : p.row < r1.topLeft.row := by calc
        p.row ≤ r2.bottomRight.row := by exact a_2
        _ < r1.topLeft.row := by exact h
      exfalso
      exact (Fin.not_le.mpr h1) (left)
    · calc
        r2.bottomRight.col < r1.topLeft.col := h
        _ ≤ p.col := left_2
  · unfold rectangles_disjoint2 rectangles_disjoint isInsideRectangle
    have a1 : r1.topLeft.col ≤ r1.bottomRight.col := r1.validCol
    have a3 : r1.topLeft.row ≤ r1.bottomRight.row := r1.validRow
    have a4 : r2.topLeft.row ≤ r2.bottomRight.row := r2.validRow
    have a5 : r2.topLeft.col ≤ r2.bottomRight.col := r2.validCol
    aesop
    contrapose a
    aesop
    push_neg at a
    aesop
    by_cases h1 : r2.topLeft.row ≤ r1.topLeft.row
    · by_cases h2 : r2.topLeft.col ≤ r1.topLeft.col
      · use (Point.mk r1.topLeft.row r1.topLeft.col)
      · use (Point.mk r1.topLeft.row r2.topLeft.col)
        aesop
        exact le_of_lt h2
    · by_cases h2 : r2.topLeft.col ≤ r1.topLeft.col
      · use (Point.mk r2.topLeft.row r1.topLeft.col)
        aesop
        exact le_of_lt h1
      · use (Point.mk r2.topLeft.row r2.topLeft.col)
        aesop
        · exact le_of_lt h2
        · exact le_of_lt h1

lemma rect_common_center_eq : common_center r1 r2 ↔ common_center r2 r1 := by
  unfold common_center
  apply Iff.intro
  · intro a
    simp_all only [and_self]
  · intro a
    simp_all only [and_self]

-- BEING USED
lemma spin_stays_outside2 (h1 : ¬isInsideRectangle p r1) (h2 : rectangles_disjoint2 r1 r2) :
    ¬isInsideRectangle (rotate180 p r2) r1 := by
  sorry

-- BEING USED
lemma spin_stays_outside3 (h1 : ¬isInsideRectangle p r1) (h2 : common_center r1 r2) :
    ¬isInsideRectangle (rotate180 p r2) r1 := by
  sorry

-- BEING USED
lemma spin_stays_inside3 (h1 : isInsideRectangle p r1) (h2 : common_center r1 r2) :
    isInsideRectangle (rotate180 p r2) r1 := by
  unfold common_center isInsideRectangle rotate180 rotateCalc at *
  aesop
  · sorry
  · sorry
  · sorry
  · sorry

lemma rect_disjoint_comm : rectangles_disjoint r1 r2 ↔ rectangles_disjoint r2 r1 := by
  simp [rectangles_disjoint]
  aesop

lemma rect_disjoint_comm2 : rectangles_disjoint2 r1 r2 ↔ rectangles_disjoint2 r2 r1 := by
  have x : rectangles_disjoint2 r1 r2 ↔ rectangles_disjoint r1 r2 := by rw [rect_disjoint_eq]
  have y : rectangles_disjoint2 r2 r1 ↔ rectangles_disjoint r2 r1 := by rw [rect_disjoint_eq]
  rw [x, y, rect_disjoint_comm]

theorem s1s2_eq_s2s1_iff {s1 s2 : Spin m n} (h_s1 : s1.isSpinAbout R1) (h_s2 : s2.isSpinAbout R2) :
    s1 * s2 = s2 * s1 ↔ (rectangles_disjoint2 R1 R2 ∨ common_center R1 R2) := by
  apply Iff.intro
  · intro h
    -- unfold rectangles_disjoint2 common_center at *
    -- exfalso
    -- aesop
    sorry
  · intro h
    dsimp only [HMul.hMul, Mul.mul, Spin.mul]
    unfold perm.actionRight
    aesop
    · unfold rectangles_disjoint2 at h
      -- unfold Spin.isSpinAbout createRectangleSpin at *
      have q : (p : Point m n) → (s1.α.trans s2.α) (to1d p) = (s2.α.trans s1.α) (to1d p) := by
        intro p
        have q1 : isInsideRectangle p R1 → ¬isInsideRectangle p R2 := by
          exact h p
        unfold Spin.isSpinAbout createRectangleSpin at *
        sorry
      sorry
    · let a := h
      unfold rectangles_disjoint2 at a
      simp_all [Spin.isSpinAbout, createRectangleSpin]
      funext p
      by_cases q4 : isInsideRectangle (to2d p) R1
      . aesop
        have q9 : ¬isInsideRectangle (rotate180 (to2d p) R1) R2 := by
          rw [@Bool.eq_iff_iff] at q4
          apply spin_stays_outside2
          . simp [q4]; simp_all only [iff_true]
          . exact rect_disjoint_comm2.mpr h
        exact Bool.eq_false_iff.mpr q9
      . aesop
        have q1234 : ¬isInsideRectangle (to2d p) R1 = true := by
          simp [q4]
        have q56 : ¬isInsideRectangle (rotate180 (to2d p) R2) R1 := by
          simp_rw [spin_stays_outside2 q1234 h, not_false_eq_true]
        simp [q56]
    · sorry
    · let a := h
      unfold rectangles_disjoint2 at a
      simp_all [Spin.isSpinAbout, createRectangleSpin]
      funext p
      by_cases q4 : isInsideRectangle (to2d p) R1
      · aesop
        · rename_i a1 a2 a3
          have x : common_center R2 R1 := by
            simp [rect_common_center_eq.mpr h]
          have y : isInsideRectangle (rotate180 (to2d p) R1) R2 := by
            exact spin_stays_inside3 a1 x
          simp_all only
        · rename_i a1 a2 a3
          have y : isInsideRectangle (rotate180 (to2d p) R2) R1 := by
            exact spin_stays_inside3 q4 h
          simp_all only
        · rename_i a1
          have x : ¬isInsideRectangle (to2d p) R2 := Bool.eq_false_iff.mp a1
          simp [spin_stays_outside3 x (rect_common_center_eq.mpr h)]
      · aesop
        rename_i a1
        have x : ¬isInsideRectangle (to2d p) R1 := by simp [q4]
        simp [spin_stays_outside3 x h]

-- proposition 4

def same_shape (R1 R2 : Rectangle m n) : Prop :=
  (R1.bottomRight.row - R1.topLeft.row) = (R2.bottomRight.row - R2.topLeft.row) ∧
  (R1.bottomRight.col - R1.topLeft.col) = (R2.bottomRight.col - R2.topLeft.col)

theorem s1s2s1_is_spin_iff {s1 s2 : Spin m n} (h_s1 : s1.isSpinAbout R1) (h_s2 : s2.isSpinAbout R2) :
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
