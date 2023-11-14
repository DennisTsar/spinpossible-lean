import Spinpossible.Definitions
import Mathlib.Data.Zmod.Basic

def is_spin_about {m n : PNat} (s : Spin m n) (R : Rectangle m n) : Prop :=
  s = createRectangleSpin R

def is_lowercase_spin {m n : PNat} (s : Spin m n) : Prop :=
  ∃ (r : Rectangle m n), is_spin_about s r

variable {m n : PNat} (s1 s2 : Spin m n) (R1 R2 : Rectangle m n)
  (h_s1 : is_spin_about s1 R1) (h_s2 : is_spin_about s2 R2)

-- proposition 1
-- theorem spin_is_own_inverse : (s1 * s1).action_on_board b = b := by
--   funext i j
--   let initTile := b i j
--   let movedTile := s1.action_on_board (s1.action_on_board b) i j
--   sorry
  -- in case either of these are useful
  -- have a : ∀ (x : Fin (m.val * n.val)), s1.α.symm (s1.α.symm⁻¹ x) = x := Equiv.Perm.apply_inv_self s1.α.symm
  -- have b : ∀ (x : Fin (m.val * n.val)), s1.α.symm⁻¹ (s1.α.symm x) = x := Equiv.Perm.apply_inv_self s1.α.symm⁻¹

lemma orientation.other_self (o : orientation) : o.other.other = o :=
  match o with
  | orientation.positive => rfl
  | orientation.negative => rfl

lemma to_2d_to_1d_inverse (p : Point m n) : to_2d (to_1d p) = p := by
  let row := p.row
  let col := p.col
  unfold to_1d to_2d
  have row_eq : (to_1d ⟨row, col⟩).val / n = row.val := by
    calc
      (to_1d p).val / n = (row * n + col) / n := rfl
      _ = (col + n * row) / n := by rw [Nat.add_comm, Nat.mul_comm]
      _ = col / n + row := Nat.add_mul_div_left _ _ n.pos
      _ = row := by rw [Nat.div_eq_of_lt col.isLt, Nat.zero_add]
  have col_eq : (to_1d ⟨row, col⟩).val % n = col := by
    calc
      (to_1d ⟨row, col⟩).val % n = (row * n + col) % n := rfl
      _ = col % n := Nat.mul_add_mod ..
      _ = col := Nat.mod_eq_of_lt col.isLt

  congr

lemma spin_does_not_change_outside (r : Rectangle m n) (h : ¬isInsideRectangle ⟨i, j⟩ r) :
  ((performSpin r b) i j) = (b i j) := by
  unfold performSpin createRectangleSpin Spin.action_on_board
  simp [h, to_2d_to_1d_inverse]

-- don't think this is true as stated (needs more conditions)
lemma rotate_calc_twice_inverse (h1 : i ≥ c) (h2 : a ≥ i) : rotate_calc a (rotate_calc a i c) c = i := by
  unfold rotate_calc
  simp
  congr
  calc
    a.val - (a.val - (i.val - c.val) - c.val) = a.val - (a.val - (i.val - c.val) - c.val) := rfl
    _ = a.val - (a.val - ((i.val - c.val) + c.val)) := by rw [Nat.sub_add_eq]
    _ = a.val - (a.val - i.val) := by rw [Nat.sub_add_cancel h1]
    _ = i.val := by exact Nat.sub_sub_self h2

lemma rotate180_twice_inverse (r : Rectangle m n) (h : isInsideRectangle ⟨i,j⟩ r) : rotate180 (rotate180 ⟨i, j⟩ r) r = ⟨i, j⟩ := by
  unfold rotate180
  simp
  unfold isInsideRectangle at h
  simp [And.decidable] at h
  have h1 : j.val ≥ r.topLeft.col.val := h.left
  have h2 : j.val ≤ r.bottomRight.col.val := h.right.left
  have h3 : i.val ≥ r.topLeft.row.val := h.right.right.left
  have h4 : i.val ≤ r.bottomRight.row.val := h.right.right.right
  simp [rotate_calc_twice_inverse h1 h2, rotate_calc_twice_inverse h3 h4]

lemma spin_stays_inside (r : Rectangle m n) (h : isInsideRectangle ⟨i, j⟩ r) :
  isInsideRectangle (rotate180 ⟨i, j⟩ r) r := by
  unfold isInsideRectangle rotate180 rotate_calc
  unfold isInsideRectangle at h
  simp [And.decidable] at h
  simp

  have h1 : j.val ≥ r.topLeft.col.val := h.left
  have h2 : j.val ≤ r.bottomRight.col.val := h.right.left

  have hx : r.bottomRight.col.val - j.val + r.topLeft.col.val = r.bottomRight.col.val - (j.val - r.topLeft.col.val) := by
    exact (tsub_tsub_assoc h2 h1).symm

  have h3 : i.val ≥ r.topLeft.row.val := h.right.right.left
  have h4 : i.val ≤ r.bottomRight.row.val := h.right.right.right

  have hy : r.bottomRight.row.val - i.val + r.topLeft.row.val = r.bottomRight.row.val - (i.val - r.topLeft.row.val) := by
    exact (tsub_tsub_assoc h4 h3).symm

  have h5 : r.topLeft.col.val ≤ r.bottomRight.col.val - (j.val - r.topLeft.col.val) := by
    have h_add6: r.topLeft.col.val ≤ r.bottomRight.col.val - j.val + r.topLeft.col.val := by
      exact Nat.le_add_left (r.topLeft.col) (r.bottomRight.col - j)
    simp [hx] at h_add6
    exact h_add6
  have h7 : r.topLeft.row.val ≤ r.bottomRight.row - (i - r.topLeft.row) := by
    have h_add6: r.topLeft.row.val ≤ r.bottomRight.row.val - i.val + r.topLeft.row.val := by
      exact Nat.le_add_left (r.topLeft.row) (r.bottomRight.row - i)
    simp [hy] at h_add6
    exact h_add6

  exact ⟨h5, h7⟩

lemma spin_effect  (h : isInsideRectangle ⟨i, j⟩ r) :
  ((performSpin r b) i j).orient = (b (rotate180 ⟨i, j⟩ r).row (rotate180 ⟨i, j⟩ r).col).orient.other := by
  unfold performSpin createRectangleSpin Spin.action_on_board
  simp [h, to_2d_to_1d_inverse, spin_stays_inside]

lemma spin_double_does_not_change_orientation (r : Rectangle m n) :
  (performSpin r (performSpin r b) i j).orient = (b i j).orient := by
  by_cases h : isInsideRectangle ⟨i, j⟩ r
  case _ := by
    let originalTile := b i j
    let firstRotation := performSpin r b
    let newPos := rotate180 ⟨i, j⟩ r
    let newTile := firstRotation newPos.row newPos.col

    have h9 : (rotate180 newPos r).row = i := by
      calc
        (rotate180 newPos r).row = (rotate180 (rotate180 ⟨i, j⟩ r) r).row := by simp
        _ = (Point.mk i j).row := by rw [rotate180_twice_inverse r h]
        _ = i := by simp
    have h10 : (rotate180 newPos r).col = j := by
      calc
        (rotate180 newPos r).col = (rotate180 (rotate180 ⟨i, j⟩ r) r).col := by simp
        _ = (Point.mk i j).col := by rw [rotate180_twice_inverse r h]
        _ = j := by simp

    have h1 : newTile.orient = originalTile.orient.other := by
      calc
        newTile.orient = (performSpin r b newPos.row newPos.col).orient := by simp
        _ = (b (rotate180 newPos r).row (rotate180 newPos r).col).orient.other := spin_effect ((spin_stays_inside r) h)
        _ = (b i j).orient.other := by rw [h9, h10]
        _ = originalTile.orient.other := by simp

    let secondRotation := performSpin r firstRotation
    let newPos2 := rotate180 newPos r

    let newTile2 := secondRotation newPos2.row newPos2.col

    have h7 : newPos2 = ⟨i, j⟩ := by
      calc
        newPos2 = rotate180 (rotate180 ⟨i, j⟩ r) r := by simp
        _ = ⟨i, j⟩ := by rw [rotate180_twice_inverse r h]

    have h2 : newTile2.orient = newTile.orient.other := by
      calc
        newTile2.orient = (performSpin r firstRotation newPos2.row newPos2.col).orient := by simp
        _ = (firstRotation (rotate180 newPos2 r).row (rotate180 newPos2 r).col).orient.other := spin_effect ((spin_stays_inside r) ((spin_stays_inside r) h))
        _ = (firstRotation (rotate180 (rotate180 newPos r) r).row (rotate180 (rotate180 newPos r) r).col).orient.other := by simp
        _ = (firstRotation newPos.row newPos.col).orient.other := by rw [rotate180_twice_inverse r h]
        _ = (performSpin r b newPos.row newPos.col).orient.other := by simp
        _ = newTile.orient.other := by simp

    have h3 : newTile2.orient = originalTile.orient := by
      calc
        newTile2.orient = newTile.orient.other := h2
        _ = originalTile.orient.other.other := by rw [h1]
        _ = originalTile.orient := by apply orientation.other_self

    have h8 : originalTile.orient = (secondRotation newPos2.row newPos2.col).orient := by
      calc
        originalTile.orient = newTile2.orient := by rw [h3]
        _ = (secondRotation newPos2.row newPos2.col).orient := by simp

    have h4 : originalTile.orient = (performSpin r (performSpin r b) i j).orient := by
      calc
        originalTile.orient = (secondRotation newPos2.row newPos2.col).orient := by rw [h8]
        _ = (secondRotation i j).orient := by rw [h7]
        _ = (performSpin r firstRotation i j).orient := by simp
        _ = (performSpin r (performSpin r b) i j).orient := by simp


    have h5 : (performSpin r (performSpin r b) i j).orient = (b i j).orient := by rw [h4]

    exact h5
  case _ := by repeat rw [spin_does_not_change_outside _ h]

lemma spin_double_does_not_change_id  (r : Rectangle m n) :
  (performSpin r (performSpin r b) i j).id = (b i j).id := by
  by_cases h : isInsideRectangle ⟨i, j⟩ r
  case _ := by sorry
  case _ := by repeat rw [spin_does_not_change_outside _ h]

-- or (s1 * s1).action_on_board b = b
-- or s1.action_on_board (s1.action_on_board b) = b
theorem spin_is_own_inverse : performSpin R1 (performSpin R1 b) = b := by
  funext i j -- Consider each tile individually
  let initTile := b i j -- Initial state of the tile
  let movedTile := performSpin R1 (performSpin R1 b) i j

  have a : initTile = movedTile := calc
    initTile = ⟨initTile.id, initTile.orient⟩   := by rfl
    _        = ⟨movedTile.id, initTile.orient⟩  := by rw [spin_double_does_not_change_id]
    _        = ⟨movedTile.id, movedTile.orient⟩ := by rw [spin_double_does_not_change_orientation]

  exact id a.symm

-- proposition 2

def moves_tile {m n : PNat} (s : Spin m n) (p : Fin (m * n)) (R : Rectangle m n) : Prop :=
  let newPos := s.α.symm (to_1d (to_2d p))
  newPos ≠ p ∧ isInsideRectangle (to_2d newPos) R

def common_center {m n : Nat} (R1 R2 : Rectangle m n) : Prop :=
  -- technically center * 2 but we don't care
  let center1 := (R1.topLeft.row + R1.bottomRight.row, R1.topLeft.col + R1.bottomRight.col)
  let center2 := (R2.topLeft.row + R2.bottomRight.row, R2.topLeft.col + R2.bottomRight.col)
  center1 = center2

lemma s1_eq_s2_of_R1_eq_R2 (h_R1_eq_R2 : R1 = R2) : s1 = s2 := by
  -- Since s1 is a spin about R1 and s2 is a spin about R2, and R1 = R2
  -- it follows that s1 and s2 are both spins about the same rectangle (R1 or R2)
  calc
    s1 = createRectangleSpin R1 := by rw [h_s1]
    _  = createRectangleSpin R2 := by rw[h_R1_eq_R2]
    _  = s2                     := by rw [h_s2.symm]

-- Assuming that s1 and s2 are spins about R1 and R2, respectively
-- and that s1 ≠ s2
lemma R1_ne_R2_of_s1_ne_s2 (h_s1_ne_s2 : s1 ≠ s2) : R1 ≠ R2 := by
  by_contra h
  have h_s1_eq_s2 : s1 = s2 := s1_eq_s2_of_R1_eq_R2 _ _ _ _ h_s1 h_s2 h
  contradiction

theorem s1s2_not_spin : ¬is_lowercase_spin (s1 * s2) := by
  rintro ⟨R3, h_s1s2_R3⟩

  have h_R1_ne_R2 : R1 ≠ R2 := R1_ne_R2_of_s1_ne_s2 _ _ _ _ h_s1 h_s2 sorry

  -- Handling the existence of p1 and p2
  obtain ⟨p1, h_p1_in_R1, h_p1_not_in_R2⟩ :
    ∃ p1, isInsideRectangle p1 R1 ∧ ¬isInsideRectangle p1 R2 := by sorry
  obtain ⟨p2, h_p2_in_R2, h_p2_not_in_R1⟩ :
    ∃ p2, isInsideRectangle p2 R2 ∧ ¬isInsideRectangle p2 R1 := by sorry

  have h_s1s2_moves_p1 : moves_tile (s1 * s2) (to_1d p1) R3 := by sorry
  have h_s1s2_moves_p2 : moves_tile (s1 * s2) (to_1d p2) R3 := by sorry

  have h_common_center_R1_R3 : common_center R1 R3 := by sorry
  have h_common_center_R2_R3 : common_center R2 R3 := by sorry

  sorry

-- proposition 3
def rectangles_disjoint {m n : Nat} (R1 R2 : Rectangle m n) : Prop :=
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

def rectangle_contains {m n : Nat} (R1 R2 : Rectangle m n) : Prop :=
  isInsideRectangle R2.topLeft R1 ∧ isInsideRectangle R2.bottomRight R1

def same_shape {m n : Nat} (R1 R2 : Rectangle m n) : Prop :=
  (R1.bottomRight.row - R1.topLeft.row) = (R2.bottomRight.row - R2.topLeft.row) ∧
  (R1.bottomRight.col - R1.topLeft.col) = (R2.bottomRight.col - R2.topLeft.col)

theorem s1s2s1_is_spin_iff :
  (∃ R3 : Rectangle m n, is_spin_about (s1 * s2 * s1) R3 ∧ same_shape R3 R2) ↔
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
