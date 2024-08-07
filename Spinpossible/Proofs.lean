import Spinpossible.Definitions

def Spin.IsSpinAbout (s : Spin m n) (r : Rectangle m n) : Prop :=
  s = r.toSpin

def IsLowercaseSpin (s : Spin m n) : Prop :=
  ∃ (r : Rectangle m n), s.IsSpinAbout r

theorem rect_spin_mul_eq_chain : ((Rectangle.toSpin r1) * (Rectangle.toSpin r2)).actionOnBoard b =
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
  . funext p
    by_cases h1 : (to2d p).IsInside r
    · simp [h1, spin_stays_inside]
    · simp [h1]
  . funext p
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

-- more convenient to have this version than number-based version,
-- but maybe worth showing that they're equivalent
-- this might be missing a condition that there exists such a point? (aka not disjoint)
def CommonCenter (r1 r2 : Rectangle m n) : Prop :=
  ∀ p, (p.IsInside r1 ∧ p.IsInside r2) → (rotate180 p r2 = rotate180 p r1)

lemma rotate_calc_helper {a b c d e : Nat} (h : d - (e - c) = b - (e - a))
    (h4 : e ≤ b) (h5 : e ≤ d) (h6 : a ≤ e) (h7 : c ≤ e) :
    ∀ x, (x ≤ b ∧ x ≤ d ∧ a ≤ x ∧ c ≤ x) → d - (x - c) = b - (x - a) := by omega

lemma rect_cent_if_rotate_eq (h1 : Point.IsInside p r1) (h2 : Point.IsInside p r2)
    (h3 : rotate180 p r2 = rotate180 p r1) : CommonCenter r1 r2 := by
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

lemma rect_commonCenter_comm : CommonCenter r1 r2 ↔ CommonCenter r2 r1 := by
  simp only [CommonCenter]
  aesop

-- "r1 contains r2"
def Rectangle.Contains (r1 r2 : Rectangle m n) : Prop :=
  ∀ p, Point.IsInside p r2 → Point.IsInside p r1

lemma exists_point_in_rect (r: Rectangle m n) : ∃ p, Point.IsInside p r := by
  simp only [Point.IsInside]
  use r.topLeft
  exact ⟨by apply Preorder.le_refl, r.validRow, by apply Preorder.le_refl, r.validCol⟩

lemma s1_eq_s2_of_r1_eq_r2 (h_s1 : Spin.IsSpinAbout s1 r1) (h_s2 : s2.IsSpinAbout r2)
    (h : r1 = r2) : s1 = s2 := by
  calc
    s1 = r1.toSpin := h_s1
    _  = r2.toSpin := by rw [h]
    _  = s2        := h_s2.symm

lemma point_outside_unaffected (h1 : s1.IsSpinAbout r1) (h2 : s2.IsSpinAbout r2)
    (h3 : Spin.IsSpinAbout (s1 * s2) r3) (h4 : ¬Point.IsInside p r2) :
    (performSpin r1 b) p.row p.col = (performSpin r3 b) p.row p.col := by
  let a := performSpin r1 b
  have x : (performSpin r3 b) p.row p.col = (performSpin r2 a) p.row p.col := by
    dsimp only [performSpin]
    have x2 : r3.toSpin.actionOnBoard b = (s1 * s2).actionOnBoard b := by
      rw [h3]
    have x3 : (s1 * s2).actionOnBoard b =
        r2.toSpin.actionOnBoard (r1.toSpin.actionOnBoard b) := by
      rw [h1, h2, rect_spin_mul_eq_chain]
    rw [x2, x3]; rfl
  have y : (performSpin r2 a) p.row p.col = a p.row p.col := by
    dsimp only [performSpin, Rectangle.toSpin, Spin.actionOnBoard]
    simp [h4, to2d_to1d_inverse]
  rw [x, y]

lemma point_outside_rect_unchanged (h : ¬Point.IsInside p r) :
    (performSpin r b) p.row p.col = b p.row p.col := by
  simp [performSpin, Rectangle.toSpin, Spin.actionOnBoard, h]

-- TODO: what's the most convenient way to write this?
--  Specifically, I want to handle both when I have this as a hypothesis and as a goal
lemma to1d_inj (h : to1d p = to1d q) : p = q := by
  have x : to2d (to1d p) = to2d (to1d q) := by congr
  simpa only [to2d_to1d_inverse] using x

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
  . obtain ⟨p1, h_p1_r1, h_p1_not_r2⟩ := h_exists_p1_p2.left
    obtain ⟨p2, h_p2_r2, h_p2_not_r1⟩ := h_exists_p1_p2.right

    -- have a1 : (b : board m n) → (performSpin r1 b) p1.row p1.col = (performSpin r3 b) p1.row p1.col := by
    --   intro b
    --   exact point_outside_unaffected h_s1 h_s2 h_s1s2_r3 h_p1_not_r2
    -- have a2 : (b : board m n) → (performSpin r1 b) p2.row p2.col = b p2.row p2.col := by
    --   intro b
    --   exact point_outside_rect_unchanged h_p2_not_r1

    have a3 : r2.toSpin.α.toFun (to1d p2) = r3.toSpin.α.toFun (to1d p2) := by
      have a3_3 : r1.toSpin.α.toFun (to1d p2) = to1d p2 := by
        simp_all only [Rectangle.toSpin, to2d_to1d_inverse, ite_false]
      rw [← h_s1s2_r3, h_s1, h_s2]
      exact congrArg (Rectangle.toSpin r2).α.toFun (a3_3.symm)

    have a4 : CommonCenter r2 r3 := by
      by_cases hx6 : (rotate180 p2 r2).IsInside r1
      · have b1 : (rotate180 p2 r2).IsInside r2 := spin_stays_inside h_p2_r2
        have b2 : (rotate180 p2 r2).IsInside r3 := by
          have b4 : r3.toSpin.u (to1d (rotate180 p2 r2)) = 1 := by
            rw [← h_s1s2_r3, h_s1, h_s2]
            dsimp only [HMul.hMul, Mul.mul, Spin.mul, perm.actionRight, Rectangle.toSpin]
            simp only [spin_stays_inside h_p2_r2, reduceIte, rotate180_self_inverse h_p2_r2,
              to2d_to1d_inverse, add_left_eq_self, ite_eq_right_iff, one_ne_zero]
            exact h_p2_not_r1
          simpa [Rectangle.toSpin] using b4

        have x : rotate180 p2 r2 ≠ p2 := by
          by_contra l
          rw [l] at hx6
          exact h_p2_not_r1 hx6

        simp [Rectangle.toSpin, h_p2_r2] at a3
        have x2 : p2.IsInside r3 := by
          by_contra l
          simp only [l] at a3
          exact x (to1d_inj a3.symm).symm
        refine rect_cent_if_rotate_eq b1 b2 ?_
        simp only [x2] at a3
        nth_rw 1 [← to1d_inj a3.symm]
        simp only [rotate180_self_inverse h_p2_r2, rotate180_self_inverse x2]
      · have b2 : p2.IsInside r3 := by
          have b4 : r3.toSpin.u (to1d p2) = 1 := by
            rw [← h_s1s2_r3, h_s1, h_s2]
            dsimp only [HMul.hMul, Mul.mul, Spin.mul, perm.actionRight, Rectangle.toSpin]
            simp only [to2d_to1d_inverse, h_p2_r2, reduceIte, hx6, zero_add]
          simpa [Rectangle.toSpin] using b4
        refine rect_cent_if_rotate_eq h_p2_r2 b2 ?_
        simp [Rectangle.toSpin, spin_stays_inside h_p2_r2, h_p2_r2, b2] at a3
        exact to1d_inj a3.symm

    have a6_2 : CommonCenter r1 r3 := by
      by_cases hx6 : (rotate180 p1 r1).IsInside r2
      · have b1 : r1.toSpin.α.toFun (to1d (rotate180 p1 r1)) = r3.toSpin.α.toFun (to1d (rotate180 p1 r1)) := by
          have a3_7 : ¬(rotate180 (rotate180 p1 r1) r1).IsInside r2 := by
            simp only [rotate180_self_inverse h_p1_r1, h_p1_not_r2, not_false_eq_true]
          rw [← h_s1s2_r3, h_s1, h_s2]
          dsimp only [HMul.hMul, Mul.mul, Spin.mul]
          dsimp only [perm.actionRight, Rectangle.toSpin]
          simp [h_p1_not_r2, spin_stays_inside h_p1_r1, a3_7]

        have b2 : (rotate180 p1 r1).IsInside r3 := by
          have t1 : (rotate180 p1 r1) ≠ p1 := by
            by_contra l
            rw [l] at hx6
            exact h_p1_not_r2 hx6
          by_contra l
          simp only [Rectangle.toSpin, to2d_to1d_inverse, h_p1_r1, spin_stays_inside,
            rotate180_self_inverse, reduceIte, l] at b1
          exact t1 (to1d_inj b1).symm

        have a3_6 : (rotate180 p1 r1).IsInside r1 := spin_stays_inside h_p1_r1

        refine rect_cent_if_rotate_eq a3_6 b2 ?_
        simp [Rectangle.toSpin, Equiv.toFun_as_coe, ite_true, a3_6, b2] at b1
        exact to1d_inj b1.symm
      · have b1 : r1.toSpin.α.toFun (to1d p1) = r3.toSpin.α.toFun (to1d p1) := by
          rw [← h_s1s2_r3, h_s1, h_s2]
          simp only [HMul.hMul, Mul.mul, Spin.mul, perm.actionRight, Rectangle.toSpin]
          simp [h_p1_r1, hx6]

        have b4 : r3.toSpin.u (to1d p1) = 1 := by
          rw [← h_s1s2_r3, h_s1, h_s2]
          dsimp only [HMul.hMul, Mul.mul, Spin.mul, perm.actionRight, Rectangle.toSpin]
          simp only [to2d_to1d_inverse, h_p1_not_r2, reduceIte, h_p1_r1, add_zero]

        have b2 : p1.IsInside r3 := by simpa [Rectangle.toSpin] using b4

        refine rect_cent_if_rotate_eq h_p1_r1 b2 ?_
        simp [Rectangle.toSpin, Equiv.toFun_as_coe, ite_true, b2, h_p1_r1] at b1
        exact to1d_inj b1.symm

    sorry
  .
    have r1_contains_r2_or_r2_contains_r1 : r1.Contains r2 ∨ r2.Contains r1 := by
      by_contra! h
      simp [exists_p1_p2] at h_exists_p1_p2
      simp [Rectangle.Contains] at h
      obtain ⟨p1, h_p1⟩ := h.left
      obtain ⟨p2, h_p2⟩ := h.right
      absurd h_p1.right
      exact h_exists_p1_p2 p2 h_p2.left h_p2.right p1 h_p1.left
    rcases r1_contains_r2_or_r2_contains_r1 with h1 | h1
    ·
      simp [Rectangle.Contains] at h1

      have : ∃ p : Point .., p.IsInside r1 ∧ ¬p.IsInside r2 := by
        by_contra! h
        apply h_r1_ne_r2
        have a1 : r1.topLeft.IsInside r2 := by
          have : r1.topLeft.IsInside r1 := by
            simp only [Point.IsInside]
            exact ⟨by apply Preorder.le_refl, r1.validRow, by apply Preorder.le_refl, r1.validCol⟩
          exact h r1.topLeft (h1 r1.topLeft (h r1.topLeft this))
        have a2 : r2.topLeft.IsInside r1 := by
          have : r2.topLeft.IsInside r2 := by
            simp only [Point.IsInside]
            exact ⟨by apply Preorder.le_refl, r2.validRow, by apply Preorder.le_refl, r2.validCol⟩
          exact h1 r2.topLeft (h r2.topLeft (h1 r2.topLeft this))
        have b1 : r1.bottomRight.IsInside r2 := by
          have : r1.bottomRight.IsInside r1 := by
            simp only [Point.IsInside]
            exact ⟨r1.validRow, by apply Preorder.le_refl, r1.validCol, by apply Preorder.le_refl⟩
          exact h r1.bottomRight (h1 r1.bottomRight (h r1.bottomRight this))
        have b2 : r2.bottomRight.IsInside r1 := by
          have : r2.bottomRight.IsInside r2 := by
            simp only [Point.IsInside]
            exact ⟨r2.validRow, by apply Preorder.le_refl, r2.validCol, by apply Preorder.le_refl⟩
          exact h1 r2.bottomRight (h r2.bottomRight (h1 r2.bottomRight this))
        ext
        · simp only [Point.IsInside] at a1 a2
          omega
        · simp only [Point.IsInside] at a1 a2
          omega
        · simp only [Point.IsInside] at b1 b2
          omega
        · simp only [Point.IsInside] at b1 b2
          omega

      obtain ⟨a1, a2⟩ := this
      sorry
    · sorry

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
  unfold CommonCenter at h1
  contrapose! h1
  use (rotate180 p r2)
  simp_rw [spin_stays_inside h3, h1, true_and]
  by_contra a
  absurd h2
  rw [rotate180_self_inverse h3] at a
  rw [a]
  exact spin_stays_inside h1

lemma spin_stays_inside_cent (h1 : CommonCenter r1 r2) (h2 : Point.IsInside p r1)
    (h3 : Point.IsInside p r2) : (rotate180 p r2).IsInside r1 := by
  rw [h1 _ ⟨h2, h3⟩]
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
      intro p a
      have hp : s1.α.trans s2.α (to1d p) = s2.α.trans s1.α (to1d p) := by simp_rw [h]

      rw [h_s1, h_s2] at hp
      simp_rw [Equiv.trans_apply, Rectangle.toSpin, Equiv.coe_fn_mk, to2d_to1d_inverse,
        a, ite_true, to2d_to1d_inverse] at hp

      by_cases h1 : (rotate180 p r1).IsInside r2
      · by_cases h2 : (rotate180 p r2).IsInside r1
        . simp_rw [h1, h2, ite_true] at hp
          exact rotate_eq_if_comm (to1d_inj hp) a.left a.right
        . absurd h.right
          exact spin_not_comm_if_outside h_s1 h_s2 a.left a.right h2
      · by_cases h2 : (rotate180 p r2).IsInside r1
        . absurd h.right
          exact (spin_not_comm_if_outside h_s2 h_s1 a.right a.left h1).symm
        . simp_rw [h1, h2, ite_false] at hp
          exact to1d_inj hp.symm
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
            have h4 := spin_stays_inside_cent (rect_commonCenter_comm.mp a) h2 h1
            simp_rw [h1, h2, ite_true, to2d_to1d_inverse, h4, ite_true, h3]
            congr 1
            dsimp only [CommonCenter] at a
            simp only [spin_stays_inside h1, h4, and_self, a, h1, h2]
          · simp_rw [h2, ite_false, h1, ite_true, to2d_to1d_inverse, ite_eq_right_iff]
            intro h3
            absurd h2
            have h4 := spin_stays_inside_cent (rect_commonCenter_comm.mp a) h3 (spin_stays_inside h1)
            simpa only [rotate180_self_inverse h1] using h4
        · by_cases h2 : (to2d p).IsInside r2
          · have h3 := spin_stays_outside_cent a h1 h2
            simp_rw [h1, ite_false, h2, ite_true, to2d_to1d_inverse, h3, ite_false]
          · simp_rw [h2, h1, ite_false, h2, h1, ite_false]
      · funext p
        by_cases h1 : (to2d p).IsInside r1
        · by_cases h2 : (to2d p).IsInside r2
          · have h3 := spin_stays_inside_cent a h1 h2
            have h4 := spin_stays_inside_cent (rect_commonCenter_comm.mp a) h2 h1
            simp_rw [h1, h2, ite_true, to2d_to1d_inverse, h4, h3]
          · have h3 := spin_stays_outside_cent (rect_commonCenter_comm.mp a) h2 h1
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
