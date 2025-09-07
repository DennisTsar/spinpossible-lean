import Spinpossible.Corollary1

lemma SameShape_rectSpin_mem {s1 s2 : RectSpin m n} (h : SameShape s1.r s2.r) :
    s1 ∈ RectSpinSet i j m n ↔ s2 ∈ RectSpinSet i j m n := by
  grind [RectSpinSet, SameShape]

def blah (l : List (RectSpin m n)) (i : Nat) (hi : i < l.length) (hl : l[i] ∈ SpinSet 1 1 m n) : List (RectSpin m n) :=
  if hi' : i + 1 = l.length then l else
  let t := l[i+1].toSpin * l[i].toSpin * l[i+1].toSpin
  have hlbah : ∃ t' : RectSpin m n, t = t'.toSpin ∧ SameShape t'.r l[i].r := by
    unfold t
    by_cases h : l[i + 1].r.Contains l[i].r
    · apply s1s2s1_is_spin_iff.mpr
      exact Or.inr h
    · apply s1s2s1_is_spin_iff.mpr
      left
      rw [s1s2_eq_s2s1_iff]
      left
      intro p hp
      have cx : l[i].r.topLeft = l[i].r.bottomRight := by
        simp [SpinSet, RectSpinSet] at hl
        ext
        · have := l[i].r.validRow
          omega
        · have := l[i].r.validCol
          omega
      obtain ⟨z, hz⟩ := not_forall.mp h
      by_cases hv : p = z
      · grind
      · by_contra hm
        have := (Classical.not_imp.mp hz).1
        simp [Point.IsInside, cx] at this hm
        have : p.row ≠ z.row ∨ p.col ≠ z.col := by
          simp [Point.ext_iff] at hv
          omega
        omega

  have hlbah2 : ∃! t' : RectSpin m n, t = t'.toSpin ∧ SameShape t'.r l[i].r := by
    refine existsUnique_of_exists_of_unique hlbah ?_
    intro a b ha hb
    rw [RectSpin.h] at ha hb
    exact RectSpin.r_bijective.injective <| Rectangle.toSpin_injective (ha.1 ▸ hb.1)

  let x := Fintype.chooseX _ hlbah2

  let l' := l.take i ++ [l[i+1]] ++ [x.1] ++ l.drop (i + 2)

  have : l'.length = l.length := by
    simp [l']
    omega

  blah l' (i + 1) (by omega) (by
    have : l'[i + 1] = x.1 := by
      simp [l', show min i l.length = i by omega]
    rw [this]
    simp [SpinSet] at hl ⊢
    exact SameShape_rectSpin_mem x.2.2 |>.mpr hl)

theorem blah_spec (l' : List (RectSpin m n)) (i' : Nat)
    (hi : i' < l'.length) (hl : l'[i'] ∈ SpinSet 1 1 m n) :
  (l'.map (RectSpin.toSpin)).prod = ((blah l' i' hi hl).map (RectSpin.toSpin)).prod := by
  fun_induction blah with
  | case1 => rfl
  | case2 l i hi hl hi' t ht1 ht2 x l'' h1 h2 =>
    rw [← h2]
    unfold l''
    let lother := l.take i ++ [l[i]] ++ [l[i+1]] ++ l.drop (i + 2)
    have : l = lother := by
      simp [lother, List.take_append_drop]
    rw [show (List.map RectSpin.toSpin l).prod = (List.map RectSpin.toSpin lother).prod from this ▸ rfl]
    unfold lother
    simp only [List.append_assoc, List.cons_append,
      List.nil_append, List.map_append, List.map_take, List.map_cons, List.map_drop,
      List.prod_append, List.prod_cons]
    congr! 1
    rw [← mul_assoc, ← mul_assoc]
    congr! 1
    rw [← x.2.1]
    unfold t
    rw [← mul_assoc, ← mul_assoc]
    simp [spin_is_own_inverse]

theorem blah_spec4 (l' : List (RectSpin m n)) (i' : Nat)
    (hi : i' < l'.length) (hl : l'[i'] ∈ SpinSet 1 1 m n) :
  (blah l' i' hi hl).length = l'.length := by
  fun_induction blah with
  | case1 => rfl
  | case2 l i hi hl hi' t ht1 ht2 x l'' h1 h2 =>
    rw [h2]
    unfold l''
    simp
    omega

theorem blah_spec3 (l' : List (RectSpin m n)) (i' : Nat)
    (hi : i' < l'.length) (hl : l'[i'] ∈ SpinSet 1 1 m n) :
  blah l' i' hi hl = l'.eraseIdx i' ++ [(blah l' i' hi hl)[l'.length - 1]'(by rw [blah_spec4]; omega)] := by
  fun_induction blah with
  | case1 l i hi hl hi' =>
    have a2 : l.eraseIdx i = l.take i ++ l.drop (i + 1) := List.eraseIdx_eq_take_drop_succ l i
    have a1 : l.drop (i + 1) = [] := by
      simp [hi']
    rw [a1] at a2
    rw [a2]
    simp
    have : l.length - 1 = i := by omega
    unfold blah
    simp_all
  | case2 l i hi hl hi' t ht1 ht2 x l'' h1 h2 =>
    unfold blah
    simp -zeta [hi']
    lift_lets
    intro a ha hb b c d
    have : c = l'' := rfl
    simp [this, ← h1]
    generalize_proofs at h2 ⊢
    convert h2 using 2
    simp [l'']
    rw [List.eraseIdx_append_of_length_le (by simp)]
    simp [show min i l.length = i by omega, List.eraseIdx_eq_take_drop_succ]


theorem blah_spec6 {m n} (l' : List (RectSpin m n)) (i' : Nat)
    (hi : i' < l'.length) (hl : l'[i'] ∈ SpinSet 1 1 m n) :
  (blah l' i' hi hl)[l'.length - 1]'(by rw [blah_spec4]; omega) ∈ SpinSet 1 1 m n := by
  fun_induction blah with
  | case1 l i hi hl hi' =>
    have : l.length - 1 = i := by omega
    unfold blah
    simp_all
  | case2 l i hi hl hi' t ht1 ht2 x l'' h1 h2 =>
    unfold blah
    simp -zeta [hi']
    lift_lets
    intro a ha hb b c d
    have : c = l'' := rfl
    simp [this, ← h1]
    generalize_proofs at h2 ⊢
    convert h2 using 2


theorem lemma6_1 (l : List (RectSpin m n)) :
    ∀ i, (_ : i < l.length - 1) → l[i] ∈ SpinSet 1 1 m n →
    (∃ t : RectSpin m n, t ∈ SpinSet 1 1 m n ∧
      ((l.eraseIdx i).map (RectSpin.toSpin)).prod * t.toSpin = (l.map (RectSpin.toSpin)).prod) := by
  intro i hi hl
  let t := l[i+1].toSpin * l[i].toSpin * l[i+1].toSpin
  have ⟨t', ht⟩ : ∃ t' : RectSpin m n, t = t'.toSpin ∧ SameShape t'.r l[i].r := by
    unfold t
    by_cases h : l[i + 1].r.Contains l[i].r
    · apply s1s2s1_is_spin_iff.mpr
      exact Or.inr h
    · apply s1s2s1_is_spin_iff.mpr
      left
      rw [s1s2_eq_s2s1_iff]
      left
      intro p hp
      have cx : l[i].r.topLeft = l[i].r.bottomRight := by
        simp [SpinSet, RectSpinSet] at hl
        ext
        · have := l[i].r.validRow
          omega
        · have := l[i].r.validCol
          omega
      obtain ⟨z, hz⟩ := not_forall.mp h
      by_cases hv : p = z
      · grind
      · by_contra hm
        have := (Classical.not_imp.mp hz).1
        simp [Point.IsInside, cx] at this hm
        have : p.row ≠ z.row ∨ p.col ≠ z.col := by
          simp [Point.ext_iff] at hv
          omega
        omega
  let l' := blah l i (by omega) hl
  let llast := l'[l.length - 1]'(by rw [blah_spec4]; omega)
  use llast
  constructor
  · apply blah_spec6
  suffices ((l.eraseIdx i).map (RectSpin.toSpin)).prod * llast.toSpin = (l'.map (RectSpin.toSpin)).prod by
    convert this using 1
    apply blah_spec
  suffices (l.eraseIdx i) ++ [llast] = l' by
    simp [← this]
  unfold llast l'
  exact blah_spec3 l i _ hl |>.symm

