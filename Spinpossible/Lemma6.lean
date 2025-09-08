import Spinpossible.Corollary1

set_option pp.showLetValues true

lemma SameShape_rectSpinSet_mem {s1 s2 : RectSpin m n} (h : SameShape s1.r s2.r) :
    s1 ∈ RectSpinSet i j m n ↔ s2 ∈ RectSpinSet i j m n := by
  grind [RectSpinSet, SameShape]

lemma SameShape_spinSet_mem {s1 s2 : RectSpin m n} (h : SameShape s1.r s2.r) :
    s1 ∈ SpinSet i j m n ↔ s2 ∈ SpinSet i j m n := by
  grind [SpinSet, SameShape_rectSpinSet_mem]

theorem uniq_s1s2s1_of_single (s1 s2 : RectSpin m n) (hl : s2 ∈ SpinSet 1 1 m n) :
    ∃! t : RectSpin m n, (s1.toSpin * s2 * s1) = t ∧ SameShape t.r s2.r := by
  refine existsUnique_of_exists_of_unique ?_ ?_
  · rw [s1s2s1_is_spin_iff, or_iff_not_imp_right, s1s2_eq_s2s1_iff]
    refine fun h => Or.inl fun p hp => ?_
    have : s2.r.topLeft = s2.r.bottomRight := by
      simp [SpinSet, RectSpinSet] at hl
      have : _ ∧ _ := ⟨s2.r.validRow, s2.r.validCol⟩
      ext <;> omega
    grind [Point.IsInside, Rectangle.Contains]
  · exact fun a b ha hb => RectSpin.toSpin_injective (ha.1 ▸ hb.1)

-- Consider making a more general version that shifts to a given index instead of the end
def shiftSingleToEnd (l : List (RectSpin m n)) (i : Nat) (hi : i < l.length)
    (hl : l[i] ∈ SpinSet 1 1 m n) : List (RectSpin m n) :=
  if hi' : i = l.length - 1 then l else
  haveI : i + 1 < l.length := by omega -- `get_elem_tactic` is a bit too slow without this
  let x := Fintype.chooseX _ (uniq_s1s2s1_of_single l[i+1] l[i] hl)
  let l' := l.take i ++ l[i+1] :: x.1 :: l.drop (i + 2)
  shiftSingleToEnd l' (i + 1) (by grind) (by grind [SameShape_spinSet_mem])
  termination_by l.length - i
  decreasing_by grind -- about 20x faster than default

theorem sste_prod_eq (l' : List (RectSpin m n)) (i' : Nat) (hi' : i' < l'.length)
    (hl' : l'[i'] ∈ SpinSet 1 1 m n) :
    ((shiftSingleToEnd l' i' hi' hl').map RectSpin.toSpin).prod =
    (l'.map RectSpin.toSpin).prod := by
  fun_induction shiftSingleToEnd with
  | case1 => rfl
  | case2 l i _ _ _ x l2 h2 =>
    have : i + 1 < l.length := by omega -- `get_elem_tactic` is a bit too slow without this
    suffices l[i].toSpin * l[i + 1] = l[i + 1] * x.1 by
      rw [h2, show l = l.take i ++ [l[i], l[i+1]] ++ l.drop (i + 2) by simp]
      simp [- List.append_assoc, this, l2, mul_assoc]
    simp_rw [← x.2.1, ← mul_assoc, spin_is_own_inverse, one_mul]

theorem sste_length (l : List (RectSpin m n)) (i : Nat)
    (hi : i < l.length) (hl : l[i] ∈ SpinSet 1 1 m n) :
    (shiftSingleToEnd l i hi hl).length = l.length := by
  fun_induction shiftSingleToEnd <;> grind -ring -linarith

theorem sste_eq (l' : List (RectSpin m n)) (i' : Nat)
    (hi' : i' < l'.length) (hl' : l'[i'] ∈ SpinSet 1 1 m n) :
    shiftSingleToEnd l' i' hi' hl' = l'.eraseIdx i' ++
      [(shiftSingleToEnd l' i' hi' hl').getLast (by grind [sste_length])] := by
  fun_induction shiftSingleToEnd with
  | case1 => simp (disch := omega) [shiftSingleToEnd, List.eraseIdx_eq_take_drop_succ]
  | case2 l i _ hl hi x l2 h2 =>
    -- a bit too slow
    -- grind [shiftSingleToEnd, add_tsub_cancel_left, List.drop_drop, List.getElem_cons_drop]
    unfold shiftSingleToEnd
    simp only [hi, ↓reduceDIte]
    convert h2 using 2
    rw [List.eraseIdx_append_of_length_le (by simp) _]
    simp [show min i l.length = i by omega, List.eraseIdx_eq_take_drop_succ]

theorem sste_last_mem_single (l : List (RectSpin m n)) (i : Nat) (hi : i < l.length)
    (hl : l[i] ∈ SpinSet 1 1 m n) :
    (shiftSingleToEnd l i hi hl).getLast (by grind [sste_length]) ∈ SpinSet 1 1 m n := by
  fun_induction shiftSingleToEnd <;> grind [shiftSingleToEnd]

-- the `i = l.length - 1` case is trivial but still true
theorem lemma6_1 (l : List (RectSpin m n)) (i : Nat) (hi : i < l.length)
    (hl : l[i] ∈ SpinSet 1 1 m n) :
    ∃ t : RectSpin m n, t ∈ SpinSet 1 1 m n ∧
      ((l.eraseIdx i).map RectSpin.toSpin).prod * t.toSpin = (l.map RectSpin.toSpin).prod := by
  let l' := shiftSingleToEnd l i (by omega) hl
  use l'.getLast (by grind [sste_length])
  refine ⟨sste_last_mem_single .., ?_⟩
  rw [← sste_prod_eq l i _ hl, sste_eq]
  simp [l']

