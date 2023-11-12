import Spinpossible.Definitions

-- proposition 1
theorem spin_is_own_inverse :
  ∀ (m n : PosNat) (s : Spin m n) (b : board m n), (s * s).action_on_board b = b :=
    sorry

-- proposition 2
def is_spin_about {m n : PosNat} (s : Spin m n) (R : Rectangle m n) : Prop :=
  s = createRectangleSpin R

def moves_tile {m n : PosNat} (s : Spin m n) (p : Fin (m * n)) (R : Rectangle m n) : Prop :=
  let newPos := s.α.symm (to_1d (to_2d p))
  newPos ≠ p ∧ isInsideRectangle (to_2d newPos) R


def common_center {m n : Nat} (R1 R2 : Rectangle m n) : Prop :=
  -- technically center * 2 but we don't care
  let center1 := (R1.topLeft.row + R1.bottomRight.row, R1.topLeft.col + R1.bottomRight.col)
  let center2 := (R2.topLeft.row + R2.bottomRight.row, R2.topLeft.col + R2.bottomRight.col)
  center1 = center2

lemma s1_eq_s2_of_R1_eq_R2 {m n : PosNat} {s1 s2 : Spin m n} {R1 R2 : Rectangle m n}
  (h_s1 : is_spin_about s1 R1) (h_s2 : is_spin_about s2 R2) (h_R1_eq_R2 : R1 = R2) : s1 = s2 := by
  -- Since s1 is a spin about R1 and s2 is a spin about R2, and R1 = R2
  -- it follows that s1 and s2 are both spins about the same rectangle (R1 or R2)
  calc
    s1 = createRectangleSpin R1 := by rw [h_s1]
    _  = createRectangleSpin R2 := by rw[h_R1_eq_R2]
    _  = s2                     := by rw [h_s2.symm]

-- Assuming that s1 and s2 are spins about R1 and R2, respectively
-- and that s1 ≠ s2
lemma R1_ne_R2_of_s1_ne_s2 {m n : PosNat} {s1 s2 : Spin m n} {R1 R2 : Rectangle m n}
  (h_s1 : is_spin_about s1 R1) (h_s2 : is_spin_about s2 R2) (h_s1_ne_s2 : s1 ≠ s2) : R1 ≠ R2 := by
  -- Assume for contradiction that R1 = R2
  by_contra h
  -- If R1 = R2, then s1 and s2 are both spins about the same rectangle, R1 (or R2)
  have h_s1_eq_s2 : s1 = s2 := by
    -- Use the fact that is_spin_about s1 R1 and is_spin_about s2 R2
    -- and that R1 = R2 to conclude that s1 = s2
    exact s1_eq_s2_of_R1_eq_R2 h_s1 h_s2 h
  -- But this contradicts the assumption that s1 ≠ s2
  contradiction

theorem s1s2_not_spin {m n : PosNat} {s1 s2 : Spin m n} {R1 R2 : Rectangle m n}
  (h_s1 : is_spin_about s1 R1) (h_s2 : is_spin_about s2 R2) : ¬(exists (R3 : Rectangle m n), is_spin_about (s1 * s2) R3) := by
  rintro ⟨R3, h_s1s2_R3⟩

  have h_R1_ne_R2 : R1 ≠ R2 := R1_ne_R2_of_s1_ne_s2 h_s1 h_s2 sorry

  -- Handling the existence of p1 and p2
  obtain ⟨p1, h_p1_in_R1, h_p1_not_in_R2⟩ :
    ∃ p1, isInsideRectangle p1 R1 ∧ ¬isInsideRectangle p1 R2 := by sorry
  obtain ⟨p2, h_p2_in_R2, h_p2_not_in_R1⟩ : ∃ p2, isInsideRectangle p2 R2 ∧ ¬isInsideRectangle p2 R1 := by sorry

  have h_s1s2_moves_p1 : moves_tile (s1 * s2) (to_1d p1) R3 := by sorry
  have h_s1s2_moves_p2 : moves_tile (s1 * s2) (to_1d p2) R3 := by sorry

  have h_common_center_R1_R3 : common_center R1 R3 := by sorry
  have h_common_center_R2_R3 : common_center R2 R3 := by sorry

  sorry
