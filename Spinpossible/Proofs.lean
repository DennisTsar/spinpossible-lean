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
      imp_false, Equiv.symm_trans_apply, Equiv.coe_fn_symm_mk, ite_eq_left_iff, zero_ne_one]
    by_cases h2 : isInsideRectangle (rotate180 ⟨i, j⟩ r2) r1
    · simp_rw [h2, not_true_eq_false, ite_false, point_eq, h2, not_not, ite_true, orientation.other_self]
    · simp_rw [h2, not_false_eq_true, not_not, ite_true, point_eq, h2, ite_false]
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
    simp_rw [isInsideRectangle, le_refl, true_and]
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
  ∀ p, (isInsideRectangle p R1 ∧ isInsideRectangle p R2) → (rotate180 p R2 = rotate180 p R1)
  -- technically center * 2 but we don't care
  -- let center1 := (R1.topLeft.row + R1.bottomRight.row, R1.topLeft.col + R1.bottomRight.col)
  -- let center2 := (R2.topLeft.row + R2.bottomRight.row, R2.topLeft.col + R2.bottomRight.col)
  -- center1 = center2

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
    (h3 : Spin.isSpinAbout (s1 * s2) r3) (h4 : ¬isInsideRectangle p r2) :
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
    simp [h4, to2d_to1d_inverse]
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
      exact point_outside_unaffected h_s1 h_s2 h_s1s2_R3 h_p1_not_R2
    have a2 : (b : board m n) → (performSpin R1 b) p2.row p2.col = b p2.row p2.col := by
      intro b
      exact point_outside_rect_unchanged h_p2_not_R1
    have a3 : (createRectangleSpin R2).α.toFun (to1d p2) = (createRectangleSpin R3).α.toFun (to1d p2) := by
      have a3_2 : (createRectangleSpin R3).α.toFun (to1d p2) = (s1 * s2).α.toFun (to1d p2) := by
        rw [h_s1s2_R3]
      have a3_4 : (createRectangleSpin R2).α.toFun (to1d p2) = (s1 * s2).α.toFun (to1d p2) := by
        have a3_3 : (createRectangleSpin R1).α.toFun (to1d p2) = to1d p2 := by
          simp_all only [createRectangleSpin, to2d_to1d_inverse, ite_false]
        rw [h_s1, h_s2]
        dsimp only [HMul.hMul, Mul.mul, Spin.mul]
        exact congrArg ((createRectangleSpin R2).α.toFun) (id a3_3.symm)
      simp only [a3_2, a3_4]

    have a4 : isInsideRectangle p1 R3 := by
      simp only [isInsideRectangle, Fin.val_fin_le]
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
def rectangles_disjoint (R1 R2 : Rectangle m n) :=
  ∀ p, isInsideRectangle p R1 → ¬isInsideRectangle p R2

lemma rect_disjoint_eq : rectangles_disjoint r1 r2 ↔
    (r1.bottomRight.row < r2.topLeft.row ∨ r1.bottomRight.col < r2.topLeft.col ∨
    r2.bottomRight.row < r1.topLeft.row ∨ r2.bottomRight.col < r1.topLeft.col) := by
  unfold rectangles_disjoint isInsideRectangle
  apply Iff.intro
  · intro a
    contrapose a
    push_neg at a
    simp only [Fin.val_fin_le, not_not, and_imp, not_forall, exists_prop] at *
    by_cases h1 : r2.topLeft.row ≤ r1.topLeft.row
    · by_cases h2 : r2.topLeft.col ≤ r1.topLeft.col
      · use ⟨r1.topLeft.row, r1.topLeft.col⟩
        simp_rw [le_refl, r1.validRow, r1.validCol, h1, a, h2, and_self]
      · use ⟨r1.topLeft.row, r2.topLeft.col⟩
        rw [not_le] at h2
        simp_rw [le_refl, r1.validRow, a, h1, le_of_lt h2, r2.validCol, true_and]
    · by_cases h2 : r2.topLeft.col ≤ r1.topLeft.col
      · use ⟨r2.topLeft.row, r1.topLeft.col⟩
        rw [not_le] at h1
        simp_rw [a, le_refl, r1.validCol, h2, le_of_lt h1, r2.validRow, and_true]
      · use ⟨r2.topLeft.row, r2.topLeft.col⟩
        rw [not_le] at h1 h2
        simp_rw [a, le_refl, le_of_lt h1, le_of_lt h2, r2.validRow, r2.validCol, true_and]
  · intro h p a
    simp_rw [Fin.val_fin_le, not_and, not_le] at *
    intro a1 a2 a3
    rcases h with h1 | h1 | h1 | h1
    · absurd h1
      exact not_lt.mpr (le_trans a1 a.right.left)
    · absurd h1
      exact not_lt.mpr (le_trans a3 a.right.right.right)
    · absurd h1
      exact not_lt.mpr (le_trans a.left a2)
    · calc
        r2.bottomRight.col < r1.topLeft.col := h1
        _ ≤ p.col := a.right.right.left


lemma rect_common_center_eq : common_center r1 r2 ↔ common_center r2 r1 := by
  unfold common_center
  aesop

lemma rect_disjoint_comm : rectangles_disjoint r1 r2 ↔ rectangles_disjoint r2 r1 := by
  simp_rw [rect_disjoint_eq]
  aesop

lemma spin_stays_outside_disj (h1 : isInsideRectangle p r2) (h2 : rectangles_disjoint r1 r2) :
    ¬isInsideRectangle (rotate180 p r2) r1 := by
  have x : isInsideRectangle (rotate180 p r2) r2 := by simp [spin_stays_inside h1]
  simp [rect_disjoint_comm] at h2
  exact h2 (rotate180 p r2) x

lemma spin_stays_outside_cent (h1 : common_center r1 r2) (h2 : ¬isInsideRectangle p r1)
    (h3 : isInsideRectangle p r2) : ¬isInsideRectangle (rotate180 p r2) r1 := by
  unfold common_center at h1
  contrapose h1
  push_neg
  use (rotate180 p r2)
  simp_all only [not_not, spin_stays_inside]
  apply And.intro
  · simp [spin_stays_inside h3]
  · intro a
    absurd h2
    rw [rotate180_self_inverse h3] at a
    rw [a]
    simp_rw [spin_stays_inside h1]

lemma spin_stays_inside_cent (h1 : common_center r1 r2) (h2 : isInsideRectangle p r1)
    (h3 : isInsideRectangle p r2) : isInsideRectangle (rotate180 p r2) r1 := by
  unfold common_center at h1
  simp_all only [and_imp, spin_stays_inside, h2, h3]

lemma other_lemma5 (h1 : rotate180 (rotate180 p r1) r2 = rotate180 (rotate180 p r2) r1)
    (h2 : isInsideRectangle p r1) (h3 : isInsideRectangle p r2)
    (h4: isInsideRectangle (rotate180 p r1) r2)
    (h5: isInsideRectangle (rotate180 p r2) r1)
    : rotate180 p r2 = rotate180 p r1 := by
  unfold rotate180 rotateCalc at h1
  unfold rotate180 rotateCalc

  have a1 : r1.topLeft.row ≤ r1.bottomRight.row := r1.validRow
  have a2 : r1.topLeft.col ≤ r1.bottomRight.col := r1.validCol
  have a3 : r2.topLeft.row ≤ r2.bottomRight.row := r2.validRow
  have a4 : r2.topLeft.col ≤ r2.bottomRight.col := r2.validCol

  simp_all only [Point.mk.injEq, Fin.mk.injEq]
  with_reducible aesop_destruct_products
  rename_i left right
  apply And.intro
  ·
    have e1_1 : p.row.val ≤ r2.bottomRight.row.val := by
      unfold isInsideRectangle at h3
      simp_all only
    have e1_2 : p.row.val ≥ r2.topLeft.row.val := by
      unfold isInsideRectangle at h3
      simp_all only
    rw [tsub_tsub_assoc e1_1 e1_2]
    -- clear e1 e2
    have e2_1 : p.row.val ≤ r1.bottomRight.row.val := by
      unfold isInsideRectangle at h2
      simp_all only
    have e2_2 : p.row.val ≥ r1.topLeft.row.val := by
      unfold isInsideRectangle at h2
      simp_all only
    rw [tsub_tsub_assoc e2_1 e2_2]
    -- clear e1 e2
    rw [tsub_add_eq_add_tsub e1_1, tsub_add_eq_add_tsub e2_1]
    have e3_1 : p.row.val ≤ r2.bottomRight.row.val + r2.topLeft.row.val := by
      calc
        p.row.val ≤ r2.bottomRight.row.val := e1_1
        _ ≤ r2.bottomRight.row.val + r2.topLeft.row.val := by apply Nat.le_add_right
    have e3_2 : p.row.val ≤ r1.bottomRight.row.val + r1.topLeft.row.val := by
      calc
        p.row.val ≤ r1.bottomRight.row.val := e2_1
        _ ≤ r1.bottomRight.row.val + r1.topLeft.row.val := by apply Nat.le_add_right
    rw [tsub_left_inj e3_1 e3_2]

    omega
  · have e1_1 : p.col.val ≤ r2.bottomRight.col.val := by
      unfold isInsideRectangle at h3
      simp_all only
    have e1_2 : p.col.val ≥ r2.topLeft.col.val := by
      unfold isInsideRectangle at h3
      simp_all only
    rw [tsub_tsub_assoc e1_1 e1_2]
    -- clear e1 e2
    have e2_1 : p.col.val ≤ r1.bottomRight.col.val := by
      unfold isInsideRectangle at h2
      simp_all only
    have e2_2 : p.col.val ≥ r1.topLeft.col.val := by
      unfold isInsideRectangle at h2
      simp_all only
    rw [tsub_tsub_assoc e2_1 e2_2]
    -- clear e1 e2
    rw [tsub_add_eq_add_tsub e1_1, tsub_add_eq_add_tsub e2_1]
    have e3_1 : p.col.val ≤ r2.bottomRight.col.val + r2.topLeft.col.val := by
      calc
        p.col.val ≤ r2.bottomRight.col.val := e1_1
        _ ≤ r2.bottomRight.col.val + r2.topLeft.col.val := by apply Nat.le_add_right
    have e3_2 : p.col.val ≤ r1.bottomRight.col.val + r1.topLeft.col.val := by
      calc
        p.col.val ≤ r1.bottomRight.col.val := e2_1
        _ ≤ r1.bottomRight.col.val + r1.topLeft.col.val := by apply Nat.le_add_right
    rw [tsub_left_inj e3_1 e3_2]

    omega

-- technically h3 isn't needed
lemma important_lemma (h_s1 : s1.isSpinAbout R1) (h_s2 : s2.isSpinAbout R2)
    (h3 : isInsideRectangle p R1) (h4 : isInsideRectangle p R2)
    (h5 : isInsideRectangle (rotate180 p R1) R2) (h6 : ¬isInsideRectangle (rotate180 p R2) R1) :
    (fun i ↦ Spin.u s1 (s2.α.symm i) + Spin.u s2 i) ≠ (fun i ↦ Spin.u s2 (s1.α.symm i) + Spin.u s1 i) := by
  rw [h_s1, h_s2, createRectangleSpin]
  by_contra a
  rw [Function.funext_iff] at a
  specialize a (to1d (rotate180 p R2))
  unfold createRectangleSpin at a
  simp_all only [Equiv.coe_fn_symm_mk, to2d_to1d_inverse, ite_false, add_zero, add_left_eq_self, ite_eq_right_iff,
    one_ne_zero, imp_false]
  have x : isInsideRectangle (rotate180 p R2) R2 := by simp [spin_stays_inside h4]
  simp [rotate180_self_inverse h4, x] at a
  contradiction


theorem s1s2_eq_s2s1_iff {s1 s2 : Spin m n} (h_s1 : s1.isSpinAbout R1) (h_s2 : s2.isSpinAbout R2) :
    s1 * s2 = s2 * s1 ↔ (rectangles_disjoint R1 R2 ∨ common_center R1 R2) := by
  apply Iff.intro
  · intro h
    dsimp only [HMul.hMul, Mul.mul, Spin.mul, perm.actionRight] at h
    simp only [Equiv.invFun_as_coe, Spin.mk.injEq] at h
    by_cases h1 : rectangles_disjoint R1 R2
    · exact Or.inl h1
    ·
      have h2 : common_center R1 R2 := by
        unfold common_center at *
        intro p a
        have left := a.left
        have right := a.right

        have q : s1.α.trans s2.α (to1d p) = s2.α.trans s1.α (to1d p) := by
          simp_all only [left, Equiv.trans_apply, Nat.mul_eq]

        have x : s1 = createRectangleSpin R1 := by rw [h_s1]
        have y : s2 = createRectangleSpin R2 := by rw [h_s2]
        rw [x, y] at q
        unfold createRectangleSpin at q
        simp [left] at q
        simp [right] at q
        by_cases h3 : isInsideRectangle (rotate180 p R1) R2
        · simp [h3] at q
          by_cases h4 : isInsideRectangle (rotate180 p R2) R1
          . simp [h4] at q
            have z2 : rotate180 (rotate180 p R1) R2 = rotate180 (rotate180 p R2) R1 := by
              have z1 : to2d (to1d (rotate180 (rotate180 p R1) R2)) = to2d (to1d (rotate180 (rotate180 p R2) R1)) := by
                rw [q]
              simpa [to2d_to1d_inverse] using z1
            simp [other_lemma5 z2 left right h3 h4]
          . have x := important_lemma h_s1 h_s2 left right h3 h4
            simp_all only [and_self, ite_true, Nat.mul_eq, ne_eq, not_true_eq_false]
        · simp [h3] at q
          by_cases h4 : isInsideRectangle (rotate180 p R2) R1
          . have x := important_lemma h_s2 h_s1 right left h4 h3
            simp_all only [and_self, ite_true, Nat.mul_eq, ne_eq, not_true_eq_false]
          . simp [h4] at q
            have z1 : to2d (to1d (rotate180 p R1)) = to2d (to1d (rotate180 p R2)) := by
                rw [q]
            simp [to2d_to1d_inverse, Eq.symm] at z1
            exact z1.symm
      exact Or.inr h2
  · intro h
    dsimp only [HMul.hMul, Mul.mul, Spin.mul, perm.actionRight]
    simp only [Equiv.invFun_as_coe, Spin.mk.injEq]
    cases h
    · apply And.intro
      · apply Equiv.ext
        intro p
        unfold Spin.isSpinAbout createRectangleSpin at *
        simp_all only [Equiv.trans_apply, Equiv.coe_fn_mk, Nat.mul_eq]
        by_cases h1 : isInsideRectangle (to2d p) R1
        · by_cases h2 : isInsideRectangle (to2d p) R2
          · simp_all only [ite_true, to2d_to1d_inverse, rectangles_disjoint]
          · simp_all [rect_disjoint_comm, spin_stays_outside_disj]
        · by_cases h2 : isInsideRectangle (to2d p) R2
          · simp_all only [ite_false, ite_true, to2d_to1d_inverse, spin_stays_outside_disj]
          · simp_all only [ite_false]
      · funext p
        simp_all only [Spin.isSpinAbout, createRectangleSpin, Equiv.coe_fn_symm_mk]
        by_cases h2 : isInsideRectangle (to2d p) R1
        · split
          · simp_all only [to2d_to1d_inverse, spin_stays_outside_disj, rect_disjoint_comm]
          · simp_all only [to2d_to1d_inverse, rect_disjoint_comm, spin_stays_outside_disj]
            decide
        · split
          · simp_all only [to2d_to1d_inverse, spin_stays_outside_disj]
            decide
          · rfl
    · apply And.intro
      · apply Equiv.ext
        intro p
        unfold Spin.isSpinAbout createRectangleSpin at *
        simp_all only [Equiv.trans_apply, Equiv.coe_fn_mk, Nat.mul_eq]
        by_cases h1 : isInsideRectangle (to2d p) R1
        · by_cases h2 : isInsideRectangle (to2d p) R2
          · simp_all only [ite_true, to2d_to1d_inverse]
            split
            · simp_all only [common_center, and_imp, spin_stays_inside, ite_true]
            · simp_all only [rect_common_center_eq, spin_stays_inside_cent, not_true_eq_false]
          · simp_all [rect_common_center_eq, spin_stays_outside_cent]
        · by_cases h2 : isInsideRectangle (to2d p) R2
          · simp_all only [ite_false, ite_true, to2d_to1d_inverse, not_false_eq_true, spin_stays_outside_cent]
          · simp_all only [ite_false]
      · funext p
        simp_all only [Spin.isSpinAbout, createRectangleSpin, Equiv.coe_fn_symm_mk]
        by_cases h2 : isInsideRectangle (to2d p) R1
        · simp [h2]
          split
          · simp_all only [to2d_to1d_inverse, spin_stays_inside_cent, rect_common_center_eq]
          · simp_all only [not_false_eq_true, rect_common_center_eq, spin_stays_outside_cent]
            decide
        · simp [h2]
          split
          · simp_all only [to2d_to1d_inverse, not_false_eq_true, spin_stays_outside_cent]
          · exact h2

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
