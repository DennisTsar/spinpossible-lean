import Spinpossible.Definitions

def Spin.isSpinAbout {m n : PNat} (s : Spin m n) (R : Rectangle m n) : Prop :=
  s = createRectangleSpin R

def isLowercaseSpin {m n : PNat} (s : Spin m n) : Prop :=
  ∃ (r : Rectangle m n), s.isSpinAbout r

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

lemma spin_effect (h : isInsideRectangle ⟨i, j⟩ r) :
    let spinResTile := (b (rotate180 ⟨i, j⟩ r).row (rotate180 ⟨i, j⟩ r).col)
    ((performSpin r b) i j) =
    { id := spinResTile.id, orient := spinResTile.orient.other } := by
  simp [h, performSpin, createRectangleSpin, Spin.actionOnBoard, to2d_to1d_inverse, spin_stays_inside]

-- or (s1 * s1).action_on_board b = b
theorem spin_is_own_inverse : performSpin r (performSpin r b) = b := by
  funext i j -- Consider each tile individually
  by_cases h : isInsideRectangle ⟨i, j⟩ r
  case _ := by
    let p := rotate180 ⟨i, j⟩ r
    have h2 : isInsideRectangle ⟨p.row, p.col⟩ r := spin_stays_inside h -- explicitly recreate point to match rotate behavior
    rw [spin_effect h, spin_effect h2, rotate180_self_inverse h, orientation.other_self]
  case _ := by simp [performSpin, createRectangleSpin, Spin.actionOnBoard, h, to2d_to1d_inverse]

theorem spin_is_own_inverse' (s: Spin _ _) (h : s.isSpinAbout r) : s.actionOnBoard (s.actionOnBoard b) = b := by
  have : Spin.actionOnBoard (createRectangleSpin r) = performSpin r := rfl
  dsimp only [Spin.isSpinAbout] at h
  rw [h, this, spin_is_own_inverse]

-- proposition 2

lemma rectangle_flips_at_least_one_tile {m n : PNat} (R : Rectangle m n) :
    ∃ (p : Fin (m * n)), (createRectangleSpin R).u p = 1 := by
  let p := R.topLeft
  use to1d p
  have h : isInsideRectangle p R := by
    simp [isInsideRectangle]
    exact ⟨R.validRow, R.validCol⟩
  simp_rw [createRectangleSpin, to2d_to1d_inverse, h, ite_true]

@[simp]
lemma zmod2_eq_zero_or_one {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  match x with
  | 0  => exact (h rfl).elim
  | 1  => simp

set_option trace.aesop true

lemma spin_mul_no_flips {m n : PNat} {r : Rectangle m n} (s : Spin m n) (h : s.isSpinAbout r) :
    (s * s).u = fun _ => 0 := by
  funext p
  simp_rw [HMul.hMul, Mul.mul, Spin.mul]
  let b := Spin.u s (s.α.symm p)
  by_cases h1 : Spin.u s p = 0
  . by_cases h2 : b = 0
    . simp [h1, h2]
    . dsimp only [Spin.isSpinAbout, createRectangleSpin] at h
      simp_all
  . by_cases h2 : b = 0
    . dsimp only [Spin.isSpinAbout, createRectangleSpin] at h
      simp_all [to2d_to1d_inverse, spin_stays_inside]
    . simp [h1, h2]; decide

variable {m n : PNat} (s1 s2 : Spin m n) (R1 R2 : Rectangle m n)
  (h_s1 : s1.isSpinAbout R1) (h_s2 : s2.isSpinAbout R2)

theorem same_spin (h1 : s1.isSpinAbout R1) (h2 : s2.isSpinAbout R2) : (s1 * s2).isSpinAbout R3 → s1 ≠ s2 := by
  intro h x
  obtain (b) := h
  have h5 : Spin.isSpinAbout (s2 * s2) R3 := by
    rw [x] at h
    exact h
  simp_all only [h2]
  simp [Spin.isSpinAbout] at h5
  let a := s2 * s2
  have h8 : a.u = fun _ => 0 := by
    simp [a]
    apply spin_mul_no_flips s2 h2
  have h9 : ¬∃ (r : Rectangle m n), a = createRectangleSpin r := by
    intro h10
    obtain ⟨r, h11⟩ := h10
    have h12 : ∃ (p : Fin (m.val * n.val)), a.u p = 1 := by
      simp only
      have x : ∃ p, (createRectangleSpin r).u p = 1 := rectangle_flips_at_least_one_tile r
      have y : createRectangleSpin r = s2 * s2 := by
        rw [← h11]
      rw [← y]
      exact x
    have h13 : ¬∃ (p : Fin (m * n)), a.u p = 1 := by
      rw [h8]
      intro h14
      obtain ⟨p, h15⟩ := h14
      have h16 : 1 = 0 := Fin.mk_eq_mk.mp (id h15.symm)
      contradiction
    contradiction
  simp [a] at h9
  exact h9 R3 h5

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
