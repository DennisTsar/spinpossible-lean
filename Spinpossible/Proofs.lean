import Spinpossible.Definitions
import Mathlib.Tactic

open scoped CharTwo -- useful since orient is in `ZMod 2` (specifically `CharTwo.two_eq_zero`)
open Function.Involutive -- to make theorem names shorter

/-- We say that an element of `Spin m n` is a *spin* if it is a spin about some rectangle `r` -/
@[ext]
structure RectSpin (m n : PNat) extends Spin m n where
  r : Rectangle m n
  h : toSpin = r.toSpin
  deriving DecidableEq, Fintype

instance : Coe (RectSpin m n) (Spin m n) := ⟨RectSpin.toSpin⟩

/-- **Proposition 1.1**: A spin about a rectangle is its own inverse -/
theorem spin_is_own_inverse (s : RectSpin m n) : s.toSpin * s.toSpin = 1 := by
  rw [s.h, Spin.mul_def, Spin.one_def, Rectangle.toSpin]
  ext p : 1
  · apply Equiv.ext_iff.mp
    exact Equiv.eq_symm_iff_trans_eq_refl.mp rfl
  · by_cases h1 : (to2d p).IsInside s.r
    · simp [h1, spin_stays_inside]
    · simp [h1]

lemma Rectangle.corners_inside (r : Rectangle m n) :
    r.topLeft.IsInside r ∧ r.bottomRight.IsInside r := by
  simp [Point.IsInside, r.validRow, r.validCol]

lemma Rectangle.corners_rotate (r : Rectangle m n) :
    rotate180 r.topLeft r = r.bottomRight ∧ rotate180 r.bottomRight r = r.topLeft := by
  cases r
  simp [rotate180, Point.ext_iff, Fin.ext_iff]
  omega

lemma spin_inverse_is_not_spin (s : RectSpin m n) :
    ∀ s2 : RectSpin m n, s2.toSpin * s2.toSpin ≠ s := by
  intro s2 hs
  rw [spin_is_own_inverse, Spin.one_def, s.h, Rectangle.toSpin] at hs
  simpa [s.r.corners_inside] using congr(Spin.u $hs (to1d s.r.topLeft))

def CommonCenter (r1 r2 : Rectangle m n) : Prop :=
  r1.topLeft.row.val + r1.bottomRight.row.val = r2.topLeft.row.val + r2.bottomRight.row.val ∧
  r1.topLeft.col.val + r1.bottomRight.col.val = r2.topLeft.col.val + r2.bottomRight.col.val

lemma CommonCenter.rotate_eq (h : CommonCenter r1 r2) :
    ∀ p : Point .., p.IsInside r1 → p.IsInside r2 → (rotate180 p r2 = rotate180 p r1) := by
  simp [CommonCenter, Point.IsInside, rotate180] at *
  omega

lemma CommonCenter.trans (h1 : CommonCenter r1 r2) (h2 : CommonCenter r2 r3) :
    CommonCenter r1 r3 := by dsimp only [CommonCenter] at *; omega

lemma CommonCenter.symm (h : CommonCenter r1 r2) : CommonCenter r2 r1 := by
  dsimp only [CommonCenter] at *; omega

lemma commonCenter_if_rotate_eq (h1 : p.IsInside r1) (h2 : p.IsInside r2)
    (h3 : rotate180 p r2 = rotate180 p r1) : CommonCenter r1 r2 := by
  simp [CommonCenter, Point.IsInside, rotate180] at *
  omega

/-- `r1` contains `r2` -/
def Rectangle.Contains (r1 r2 : Rectangle m n) : Prop :=
  ∀ p : Point .., p.IsInside r2 → p.IsInside r1

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

private lemma s1s2_not_spin.aux1 {s1 s2 s3 : RectSpin m n} {p : Point m n}
    (p_in_r1 : p.IsInside s1.r) (p_not_in_r2 : ¬p.IsInside s2.r)
    (hs3 : s1.toSpin * s2.toSpin = s3.toSpin)
    (r2_in_r1 : ∀ p : Point m n, p.IsInside s2.r → p.IsInside s1.r)
    -- This arg is only needed for the final parts
    (p_is_corner : p = s1.r.topLeft ∨ p = s1.r.bottomRight)
    : False := by
  simp only [RectSpin.h, Rectangle.toSpin, Spin.mul_def, Spin.ext_iff] at hs3
  obtain ⟨hs3_perm, hs3_orient⟩ := hs3

  set r1 := s1.r
  set r2 := s2.r
  set r3 := s3.r

  have : p.IsInside r3 := by simpa [p_not_in_r2, p_in_r1, eq_ite_iff] using hs3_orient (to1d p)
  have r2_bot_in_r3 : (rotate180 p r1).IsInside r3 := by
    by_contra! h
    have r1_bot_in_r2 : (rotate180 p r1).IsInside r2 := by
      by_contra! h2
      absurd hs3_orient (to1d (rotate180 p r1))
      simp [h2, spin_stays_inside p_in_r1, h]
    have app := hs3_perm (to1d (rotate180 p r1))
    simp only [Equiv.trans_apply, coe_toPerm, to2d_to1d_inverse, r1_bot_in_r2, r2_in_r1,
      reduceIte, p_in_r1, rotate180_self_inverse, p_not_in_r2, h, to1d_inj] at app
    exact (app ▸ p_not_in_r2) r1_bot_in_r2

  have ⟨r1_top_in_r3, r1_bot_in_r3⟩ : r1.topLeft.IsInside r3 ∧ r1.bottomRight.IsInside r3 := by
    cases p_is_corner <;> simp_all [r1.corners_rotate]

  have r3_eq_r1 : r3 = r1 := by
    apply rect_eq_if_corners_inside ?_ r1_top_in_r3 ?_ r1_bot_in_r3
    · by_contra h
      absurd hs3_orient (to1d r3.topLeft)
      simp [h, (r2_in_r1 r3.topLeft).mt, r3.corners_inside]
    · by_contra h
      absurd hs3_orient (to1d r3.bottomRight)
      simp [h, (r2_in_r1 r3.bottomRight).mt h, r3.corners_inside]
  have app_orient := hs3_orient (to1d r2.topLeft)
  simp [r2.corners_inside, r2.corners_rotate, r2_in_r1, r3_eq_r1] at app_orient

private lemma s1s2_not_spin.aux2 {s1 s2 s3 : RectSpin m n}
    -- This is implied by the last arg, but most of the proof needs only this weaker
    -- assumption, so we leave it to show intention
    (p_in_r2 : p.IsInside s2.r)
    (hs3 : s1.toSpin * s2.toSpin = s3.toSpin)
    (r1_in_r2 : ∀ p : Point m n, p.IsInside s1.r → p.IsInside s2.r)
    (p_rot_not_in_r1 : ¬(rotate180 p s2.r).IsInside s1.r)
    (p_is_corner : p = s2.r.topLeft ∨ p = s2.r.bottomRight)
    : False := by
  simp only [RectSpin.h, Rectangle.toSpin, Spin.mul_def, Spin.ext_iff] at hs3
  obtain ⟨hs3_perm, hs3_orient⟩ := hs3

  set r1 := s1.r
  set r2 := s2.r
  set r3 := s3.r

  have r3_top_in_r2 : r3.topLeft.IsInside r2 := by
    by_contra! h
    have app := hs3_orient (to1d r3.topLeft)
    simp_all [r3.corners_inside]

  have r3_bot_in_r2 : r3.bottomRight.IsInside r2 := by
    by_contra! h
    have app := hs3_orient (to1d r3.bottomRight)
    simp_all [r3.corners_inside]

  have r2_bot_in_r3 : p.IsInside r3 := by
    simpa [p_rot_not_in_r1, p_in_r2, eq_ite_iff] using hs3_orient (to1d p)

  have r2_top_not_in_r3 : ¬(rotate180 p r2).IsInside r3 := by
    by_contra! h
    have r2_eq_r3 : r2 = r3 := by
      refine rect_eq_if_corners_inside ?top r3_top_in_r2 ?bot r3_bot_in_r2 <;>
      rcases p_is_corner with rfl | rfl
      case bot.inr | top.inl => exact r2_bot_in_r3
      case bot.inl | top.inr => simpa [r2.corners_rotate] using h
    have r1_bot_in_r3 : r1.bottomRight.IsInside r3 :=
      r2_eq_r3 ▸ r1_in_r2 r1.bottomRight r1.corners_inside.2
    absurd hs3_orient (to1d (rotate180 r1.bottomRight r2))
    simp [r1_bot_in_r3, spin_stays_inside, r2_eq_r3, r1.corners_inside]

  have app := hs3_perm (to1d (rotate180 p r2))
  simp [Equiv.trans_apply, coe_toPerm, to2d_to1d_inverse, p_rot_not_in_r1, reduceIte,
    p_in_r2, spin_stays_inside, rotate180_self_inverse, r2_top_not_in_r3, to1d_inj] at app
  rw [app, rotate180_self_inverse p_in_r2] at r2_top_not_in_r3
  contradiction

private lemma s1s2_not_spin.aux3 {r1 r2 : Rectangle m n}
    (h_contains : r1.Contains r2) (h_r1_ne_r2 : r1 ≠ r2) :
    ¬r1.topLeft.IsInside r2 ∨ ¬r1.bottomRight.IsInside r2 := by
  contrapose! h_r1_ne_r2 with h
  refine rect_eq_if_corners_inside h.1 ?_ h.2 ?_
  · exact h_contains r2.topLeft r2.corners_inside.1
  · exact h_contains r2.bottomRight r2.corners_inside.2

/-- **Proposition 1.2**: Let `s1` and `s2` be spins about rectangles `r1` and `r2` respectively.
    `s1 * s2` is not a spin. -/
theorem s1s2_not_spin (s1 s2 : RectSpin m n) :
    ∀ s : RectSpin m n, s1.toSpin * s2.toSpin ≠ s.toSpin := by
  intro s3 hs3

  -- These used to be plain `let`s, but starting in Lean 4.16.0,
  -- `simp` doesn't see that `r1` and `s1.r` are the same
  -- Note: `simp +zetaDelta` works, but I don't want to have to use that for everything time
  -- I want an "inline let", but `letI` doesn't work either
  set r1 := s1.r with ← hr1
  set r2 := s2.r with ← hr2
  set r3 := s3.r with ← hr3

  have h_r1_ne_r2 : s1.r ≠ r2 := by
    by_contra h1
    rw [RectSpin.h, h1, ← RectSpin.h] at hs3
    exact (spin_inverse_is_not_spin s3) s2 hs3

  let exists_p1_p2 :=
    (∃ p1 p2 : Point .., p1.IsInside r1 ∧ ¬p1.IsInside r2 ∧ p2.IsInside r2 ∧ ¬p2.IsInside r1)

  by_cases h_exists_p1_p2 : exists_p1_p2
  · simp only [RectSpin.h, Rectangle.toSpin, Spin.mul_def, Spin.ext_iff] at hs3
    obtain ⟨hs3_perm, hs3_orient⟩ := hs3
    -- See note above: I don't want to have to do this
    rw [hr1, hr2, hr3] at hs3_perm hs3_orient
    clear hr1 hr2 hr3
    obtain ⟨p1, p2, h_p1_r1, h_p1_not_r2, h_p2_r2, h_p2_not_r1⟩ := h_exists_p1_p2

    have r2_r3_commonCenter : CommonCenter r2 r3 := by
      have app := hs3_perm (to1d p2)
      simp [h_p2_r2, h_p2_not_r1] at app
      have : p2.IsInside r3 := by
        by_contra h
        absurd hs3_orient (to1d p2)
        simp [h_p2_r2, h_p2_not_r1, h, app]
      apply commonCenter_if_rotate_eq h_p2_r2 this
      simpa [this] using app.symm

    have r1_r3_commonCenter : CommonCenter r1 r3 := by
      have app := hs3_perm (to1d (rotate180 p1 r1))
      simp [spin_stays_inside, h_p1_r1, h_p1_not_r2] at app
      have : (rotate180 p1 r1).IsInside r3 := by
        by_contra h
        simp only [h, reduceIte, to1d_inj] at app
        rw [← app] at h
        absurd hs3_orient (to1d p1)
        simp [h_p1_not_r2, h_p1_r1, h]
      apply commonCenter_if_rotate_eq (spin_stays_inside h_p1_r1) this
      simp_rw [this, reduceIte, to1d_inj] at app
      rw [← app, rotate180_self_inverse h_p1_r1]

    clear hs3_perm
    dsimp [CommonCenter] at r1_r3_commonCenter r2_r3_commonCenter

    have r1_top_not_in_r2 : ¬r1.topLeft.IsInside r2 := by
      dsimp [Point.IsInside] at h_p1_r1 h_p1_not_r2 ⊢
      omega

    have r1_top_in_r3 : r1.topLeft.IsInside r3 := by
      have := hs3_orient (to1d r1.topLeft)
      simpa [r1.corners_inside, r1_top_not_in_r2, eq_ite_iff]
    have r3_top_in_r1 : r3.topLeft.IsInside r1 := by
      have : ¬r3.topLeft.IsInside r2 := by
        dsimp [Point.IsInside] at r1_top_not_in_r2 r1_top_in_r3 ⊢
        omega
      have app := hs3_orient (to1d r3.topLeft)
      simpa [r3.corners_inside, this] using app

    have r1_eq_r3 : r1 = r3 := by
      apply rect_eq_if_corners_inside r1_top_in_r3 r3_top_in_r1 <;>
      dsimp [Point.IsInside] at r1_top_in_r3 r3_top_in_r1 ⊢ <;> omega

    have r2_top_not_in_r3 : ¬r2.topLeft.IsInside r3 := by
      dsimp [Point.IsInside] at h_p2_r2 h_p2_not_r1 r3_top_in_r1 ⊢
      omega
    have r2_bot_in_r3 : r2.bottomRight.IsInside r3 := by
      by_contra! h
      absurd hs3_orient (to1d r2.topLeft)
      simp [h, r2_top_not_in_r3, r2.corners_rotate, r2.corners_inside, r1_eq_r3]

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
      · exact s1s2_not_spin.aux1 r1.corners_inside.1 h_corner hs3 h (Or.inl rfl)
      · exact s1s2_not_spin.aux1 r1.corners_inside.2 h_corner hs3 h (Or.inr rfl)
    · rcases s1s2_not_spin.aux3 h h_r1_ne_r2.symm with h_corner | h_corner
      · apply s1s2_not_spin.aux2 r2.corners_inside.2 hs3 h ?_ (Or.inr rfl)
        exact r2.corners_rotate.2 ▸ h_corner
      · apply s1s2_not_spin.aux2 r2.corners_inside.1 hs3 h ?_ (Or.inl rfl)
        exact r2.corners_rotate.1 ▸ h_corner

def DisjointRect (r1 r2 : Rectangle m n) : Prop :=
  ∀ p : Point .., p.IsInside r1 → ¬p.IsInside r2

lemma DisjointRect.symm (h : DisjointRect r1 r2) : DisjointRect r2 r1 :=
  fun p h2 h3 => h p h3 h2

lemma DisjointRect.not_iff :
    ¬DisjointRect r1 r2 ↔ ∃ p : Point .., p.IsInside r1 ∧ p.IsInside r2 := by
  simp [DisjointRect]

lemma spin_stays_outside_disj (h1 : DisjointRect r1 r2) (h2 : p.IsInside r2) :
    ¬(rotate180 p r2).IsInside r1 := h1.symm _ (spin_stays_inside h2)

lemma spin_stays_outside_cent (h1 : CommonCenter r1 r2) (h2 : ¬p.IsInside r1)
    (h3 : p.IsInside r2) : ¬(rotate180 p r2).IsInside r1 := by
  by_contra h5
  have h4 := h1.rotate_eq (rotate180 p r2)
  simp_rw [spin_stays_inside h3, h5, true_implies, rotate180_self_inverse h3] at h4
  exact h4 ▸ h2 <| spin_stays_inside h5

lemma spin_stays_inside_cent (h1 : CommonCenter r1 r2) (h2 : p.IsInside r1)
    (h3 : p.IsInside r2) : (rotate180 p r2).IsInside r1 :=
  h1.rotate_eq p h2 h3 ▸ spin_stays_inside h2

private lemma rotate_eq_if_comm.aux1 {a b c d e : Nat}
    (h : d - (b - (e - a) - c) = b - (d - (e - c) - a))
    (_ : a ≤ e) (_ : c ≤ e) (_ : e ≤ b) (_ : e ≤ d) :
    d - (e - c) = b - (e - a) := by omega

lemma rotate_eq_if_comm (h1 : rotate180 (rotate180 p r1) r2 = rotate180 (rotate180 p r2) r1)
    (h2 : p.IsInside r1) (h3 : p.IsInside r2) :
    rotate180 p r2 = rotate180 p r1 := by
  simp only [rotate180, Point.ext_iff, Fin.ext_iff] at h1 ⊢
  constructor
  · exact rotate_eq_if_comm.aux1 h1.1 h2.1 h3.1 h2.2.1 h3.2.1
  · exact rotate_eq_if_comm.aux1 h1.2 h2.2.2.1 h3.2.2.1 h2.2.2.2 h3.2.2.2

/-- **Proposition 1.3**: Let `s1` and `s2` be spins about rectangles `r1` and `r2` respectively.
    `s1 * s2 = s2 * s1` if and only if `r1` and `r2` are disjoint or have a common center. -/
theorem s1s2_eq_s2s1_iff {s1 s2 : RectSpin m n} :
    s1.toSpin * s2 = s2 * s1 ↔ (DisjointRect s1.r s2.r ∨ CommonCenter s1.r s2.r) := by
  -- These used to be plain `let`s, see note in `s1s2_not_spin` above
  set r1 := s1.r with ← hr1
  set r2 := s2.r with ← hr2

  apply Iff.intro
  · rw [or_iff_not_imp_left, DisjointRect.not_iff]
    intro h ⟨p, hp_r1, hp_r2⟩
    apply commonCenter_if_rotate_eq hp_r1 hp_r2
    refine rotate_eq_if_comm ?_ hp_r1 hp_r2
    simp only [RectSpin.h, Rectangle.toSpin, Spin.mul_def, Spin.ext_iff] at h
    obtain ⟨h_perm, h_orient⟩ := h
    specialize h_perm (to1d p)
    specialize h_orient (to1d p)
    simp [hp_r1, hp_r2] at h_perm h_orient
    split_ifs at h_orient <;> simp_all [spin_stays_inside]
  · intro h
    simp only [RectSpin.h, Rectangle.toSpin, Spin.mul_def, hr1, hr2]
    rcases h with a | a
    · ext p : 1
      · by_cases h1 : (to2d p).IsInside r1
        · have : ¬(to2d p).IsInside r2 := a (to2d p) h1
          simp [this, h1, spin_stays_outside_disj a.symm h1]
        · by_cases h2 : (to2d p).IsInside r2
          · simp [spin_stays_outside_disj a h2, h2, h1]
          · simp [h1, h2]
      · by_cases h1 : (to2d p).IsInside r1
        · have : ¬(to2d p).IsInside r2 := a (to2d p) h1
          simp [this, h1, spin_stays_outside_disj a.symm h1]
        · by_cases h2 : (to2d p).IsInside r2
          · simp [spin_stays_outside_disj a h2, h2, h1]
          · simp [h1, h2]
    · ext p : 1
      · by_cases h1 : (to2d p).IsInside r1
        · by_cases h2 : (to2d p).IsInside r2
          · simp [h1, h2, spin_stays_inside_cent a.symm, spin_stays_inside, a.rotate_eq]
          · simp [spin_stays_outside_cent a.symm h2 h1, h1, h2]
        · by_cases h2 : (to2d p).IsInside r2
          · simp [spin_stays_outside_cent a h1 h2, h1, h2]
          · simp [h1, h2]
      · by_cases h1 : (to2d p).IsInside r1
        · by_cases h2 : (to2d p).IsInside r2
          · simp [h1, h2, spin_stays_inside_cent a.symm, spin_stays_inside, a.rotate_eq]
          · simp [spin_stays_outside_cent a.symm h2 h1, h1, h2]
        · by_cases h2 : (to2d p).IsInside r2
          · simp [spin_stays_outside_cent a h1 h2, h1, h2]
          · simp [h1, h2]

def SameShape (r1 r2 : Rectangle m n) : Prop :=
  (r1.bottomRight.row.val - r1.topLeft.row.val) = (r2.bottomRight.row.val - r2.topLeft.row.val) ∧
  (r1.bottomRight.col.val - r1.topLeft.col.val) = (r2.bottomRight.col.val - r2.topLeft.col.val)

private lemma s1s2s1_is_spin_iff.aux1 {r1t r1b r2t r2b p : Fin x}
  (_ : r2t ≤ r2b) (_ : r1t ≤ r2t) (_ : r1b ≥ r2b)
  (_ : r1b - (r2b - r1t) ≤ p.val)
  (_ : p.val ≤ r1b - (r2t - r1t))
  : r1b.val - (r2b.val - (r1b.val - (p.val - r1t.val) - r2t.val) - r1t.val) =
    r1b.val - (r2t.val - r1t.val) - (p.val - (r1b.val - (r2b.val - r1t.val))) := by
  omega

private lemma s1s2s1_is_spin_iff.aux2 {r1 r2 r3 : Rectangle m n} (h : r1.Contains r2)
    (h_r3 : r3.topLeft = rotate180 r2.bottomRight r1 ∧ r3.bottomRight = rotate180 r2.topLeft r1) :
    ∀ p : Point m n, p.IsInside r1 → (p.IsInside r3 ↔ (rotate180 p r1).IsInside r2) := by
  have : _ ∧ _ := ⟨r2.validRow, r2.validCol⟩
  have : r2.topLeft.IsInside r1 := h r2.topLeft r2.corners_inside.1
  dsimp [Point.IsInside, rotate180] at *
  simp only [h_r3]
  omega

-- Together these save about 2s
attribute [-simp] PNat.val_ofNat in
instance : NeZero (1 : ZMod 2) := NeZero.one in
seal Mul.mul in
/-- **Proposition 1.4**: Let `s1` and `s2` be spins about rectangles `r1` and `r2` respectively.
    `s1 * s2 * s1` is a spin `s3` if and only if either `s1` and `s2` commute or `r1` contains `r2`.
    The rectangle of `s3` has the same shape as `r2`. -/
theorem s1s2s1_is_spin_iff {s1 s2 : RectSpin m n} :
    (∃ s3 : RectSpin m n, s1.toSpin * s2 * s1 = s3 ∧ SameShape s3.r s2.r) ↔
    (s1.toSpin * s2 = s2 * s1 ∨ s1.r.Contains s2.r) := by
  set r1 := s1.r
  set r2 := s2.r
  apply Iff.intro
  · rw [s1s2_eq_s2s1_iff, or_iff_not_imp_right, or_iff_not_imp_left]
    rintro ⟨s3, h3, -⟩ h1 h2
    have r2_corner_not_in_r1 : ¬r2.topLeft.IsInside r1 ∨ ¬r2.bottomRight.IsInside r1 := by
      contrapose! h1
      dsimp [Point.IsInside, Rectangle.Contains] at h1 ⊢
      omega

    simp only [RectSpin.h, Rectangle.toSpin, Spin.mul_def, Spin.ext_iff] at h3
    obtain ⟨h_perm, h_orient⟩ := h3
    refold_let r1 r2 at h_perm h_orient h2

    obtain ⟨p, h_p⟩ := DisjointRect.not_iff.mp h2

    have ⟨r2_r3_commonCenter, p_in_r3⟩ : CommonCenter s3.r r2 ∧ p.IsInside s3.r := by
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
        have : CommonCenter s3.r r2 :=
          commonCenter_if_rotate_eq h_orient r2.corners_inside.1 h_perm
        refine ⟨this, ?_⟩
        dsimp [Point.IsInside, CommonCenter, r1, r2] at *
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
        have : CommonCenter s3.r r2 :=
          commonCenter_if_rotate_eq h_orient r2.corners_inside.2 h_perm
        refine ⟨this, ?_⟩
        dsimp [Point.IsInside, CommonCenter, r1, r2] at *
        omega

    specialize h_perm (to1d p)
    specialize h_orient (to1d p)

    have : (rotate180 p r1).IsInside r2 := by
      by_contra! h
      simp [h, h_p, spin_stays_inside, p_in_r3] at h_orient
    simp [this, h_p] at h_perm h_orient

    have hx : (rotate180 (rotate180 p r1) r2).IsInside r1 := by
      contrapose p_in_r3
      simpa [p_in_r3, apply_ite] using h_orient
    simp [hx, apply_ite] at h_perm h_orient
    rw [if_pos h_orient] at h_perm
    apply commonCenter_if_rotate_eq h_p.1 h_p.2
    apply rotate_eq_if_comm ?_ h_p.1 h_p.2
    rw [r2_r3_commonCenter.rotate_eq p h_orient h_p.2]
    exact rotate180_self_inverse hx ▸ congr(rotate180 $h_perm r1)
  · intro h
    -- Below the `+zetaDelta` and `r1, r2` had to be added Lean 4.16.0, see note in `s1s2_not_spin`
    rcases h with h | h
    · use s2, h ▸ ?_, rfl
      ext : 1 <;>
      · by_contra! hp
        simp only [RectSpin.h, Rectangle.toSpin, Spin.mul_def, Equiv.trans_apply, coe_toPerm] at hp
        split_ifs at hp <;> simp_all [spin_stays_inside]
    · let r3 : Rectangle m n := ⟨
        rotate180 r2.bottomRight r1,
        rotate180 r2.topLeft r1,
        by dsimp [rotate180]; have := r2.validCol; fin_omega,
        by dsimp [rotate180]; have := r2.validRow; fin_omega,
      ⟩
      have r2_top_in_r1 := h r2.topLeft r2.corners_inside.1
      have r2_bot_in_r1 := h r2.bottomRight r2.corners_inside.2
      -- the `p.IsInside r1` is kinda superfluous, but easier to accept it than fight it
      have : ∀ p, p.IsInside r1 → (p.IsInside r3 ↔ (rotate180 p r1).IsInside r2) :=
        s1s2s1_is_spin_iff.aux2 h ⟨rfl, rfl⟩
      have r3_in_r1 : r1.Contains r3 := by
        intro p h_p
        dsimp [Point.IsInside, rotate180, r3] at r2_bot_in_r1 h_p ⊢
        omega
      use ⟨r3.toSpin, r3, rfl⟩
      constructor
      · simp only [RectSpin.h, Rectangle.toSpin, Spin.mul_def]
        ext p : 1
        · simp only [Equiv.trans_apply, coe_toPerm]
          specialize r3_in_r1 (to2d p)
          specialize this (to2d p)
          split_ifs <;> simp_all [spin_stays_inside, Rectangle.Contains, r1, r2]
          · dsimp [Point.IsInside, rotate180] at *
            ext <;> apply s1s2s1_is_spin_iff.aux1 <;> omega
        · simp only [Equiv.invFun_as_coe, toPerm_symm, coe_toPerm]
          specialize r3_in_r1 (to2d p)
          specialize this (to2d p)
          clear r2_bot_in_r1 r2_top_in_r1
          split_ifs <;> simp_all [spin_stays_inside, Rectangle.Contains, r1, r2]
      · dsimp +zetaDelta only [SameShape, Point.IsInside, rotate180] at r2_bot_in_r1 r2_top_in_r1 ⊢
        omega
