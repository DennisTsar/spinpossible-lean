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
      grind [Rectangle.validRow, Rectangle.validCol]
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
  | case1 => grind [shiftSingleToEnd, List.take_append_getLast]
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

theorem uniq_s1s2s1_of_whole {m n} (s1 s2 : RectSpin m n) (hl : s1 ∈ SpinSet m n m n) :
    ∃! t : RectSpin m n, (s1.toSpin * s2 * s1) = t ∧ SameShape t.r s2.r := by
  refine existsUnique_of_exists_of_unique ?_ ?_
  · rw [s1s2s1_is_spin_iff, or_iff_not_imp_right, s1s2_eq_s2s1_iff]
    grind [Point.IsInside, Rectangle.Contains, SpinSet, RectSpinSet]
  · exact fun a b ha hb => RectSpin.toSpin_injective (ha.1 ▸ hb.1)

def shiftWholeToEnd (l : List (RectSpin m n)) (i : Nat) (hi : i < l.length)
    (hl : l[i] ∈ SpinSet m n m n) : List (RectSpin m n) :=
  if hi' : i = l.length - 1 then l else
  haveI : i + 1 < l.length := by omega -- `get_elem_tactic` is a bit too slow without this
  let x := Fintype.chooseX _ (uniq_s1s2s1_of_whole l[i] l[i+1] hl)
  let l' := l.take i ++ x.1 :: l[i] :: l.drop (i + 2)
  shiftWholeToEnd l' (i + 1) (by grind) (by grind)
  termination_by l.length - i
  decreasing_by grind -- about 20x faster than default

theorem swte_prod_eq (l' : List (RectSpin m n)) (i' : Nat) (hi' : i' < l'.length)
    (hl' : l'[i'] ∈ SpinSet m n m n) :
    ((shiftWholeToEnd l' i' hi' hl').map RectSpin.toSpin).prod =
    (l'.map RectSpin.toSpin).prod := by
  fun_induction shiftWholeToEnd with
  | case1 => rfl
  | case2 l i _ _ _ x l2 h2 =>
    have : i + 1 < l.length := by omega -- `get_elem_tactic` is a bit too slow without this
    suffices l[i].toSpin * l[i + 1] = x.1 * l[i]  by
      rw [h2, show l = l.take i ++ [l[i], l[i+1]] ++ l.drop (i + 2) by simp]
      simp [- List.append_assoc, this, l2, mul_assoc]
    simp_rw [← x.2.1, mul_assoc, spin_is_own_inverse, mul_one]

theorem swte_length (l : List (RectSpin m n)) (i : Nat)
    (hi : i < l.length) (hl : l[i] ∈ SpinSet m n m n) :
    (shiftWholeToEnd l i hi hl).length = l.length := by
  fun_induction shiftWholeToEnd <;> grind -ring -linarith

lemma List.take_something {l1 l2 : List α} (h : l1.take n = l2.take n) (m : Nat) (hmn : m ≤ n) :
    l1.take m = l2.take m := by
  induction n with
  | zero => grind
  | succ n ih =>
    rw [show take m l1 = take m (take (n + 1) l1) by grind]
    grind

theorem swte_eq_beg (l : List (RectSpin m n)) (i : Nat)
    (hi : i < l.length) (hl : l[i] ∈ SpinSet m n m n) :
    (shiftWholeToEnd l i hi hl).take i = l.take i := by
  fun_induction shiftWholeToEnd with
  | case1 => rfl
  | case2 => grind [List.take_left', List.take_something]

theorem swte_last (l : List (RectSpin m n)) (i : Nat)
    (hi : i < l.length) (hl : l[i] ∈ SpinSet m n m n) :
    (shiftWholeToEnd l i hi hl).getLast (by grind [swte_length]) = l[i] := by
  fun_induction shiftWholeToEnd <;> unfold shiftWholeToEnd <;> grind

theorem swte_sameShape (l : List (RectSpin m n)) (i j : Nat)
    (hi : i < l.length) (hj : i ≤ j ∧ j < l.length - 1) (hl : l[i] ∈ SpinSet m n m n) :
    SameShape ((shiftWholeToEnd l i hi hl)[j]'(by grind [swte_length])).r l[j+1].r := by
  generalize_proofs ha
  fun_induction shiftWholeToEnd with
  | case1 => omega
  | case2 l i _ _ _ x l2 h2 =>
    by_cases hj' : j = i
    · have := swte_eq_beg l2 (i + 1) (by grind) (by grind only)
      have := List.getElem_take ▸ congr($this[j]'(by grind))
      grind -ring -linarith
    · convert h2 (by grind) ha (by grind) using 2
      simp [l2, List.getElem_cons, List.getElem_append]
      grind -ring -linarith only [= Nat.min_def, getElem_congr_idx]

-- Original: "If `sᵢ ∈ Sₘₓₙ`, then `b` can be written as `b = sᵢ⋯sᵢ₋₁tᵢ₊₁⋯tₖsᵢ`, with each `tⱼ` a spin of the same type as `sⱼ`, for `i ≤ j ≤ k`."
-- Corrected (I think?): If `sᵢ ∈ Sₘₓₙ`, then `b` can be written as `b = s₁⋯sᵢ₋₁tᵢ₊₁⋯tₖsᵢ`, with each `tⱼ` a spin of the same type as `sⱼ`, for `i < j ≤ k`.
-- Corrected (reindexed version): If `sᵢ ∈ Sₘₓₙ`, then `b` can be written as `b = s₀⋯sᵢ₋₁tᵢ⋯tₖsᵢ`, with each `tⱼ` a spin of the same type as `sⱼ₊₁`, for `i ≤ j < k`.
theorem lemma6_2 (l : List (RectSpin m n)) :
    ∀ i, (_ : i < l.length - 1) → l[i] ∈ SpinSet m n m n →
    (∃ l' : List (RectSpin m n), (l'.map RectSpin.toSpin).prod = (l.map RectSpin.toSpin).prod
      ∧ l'.length = l.length ∧ l'.take i = l.take i ∧ l'.getLast? = l[i] ∧
      (∀ j, (_ : i ≤ j) → (_ : j < l.length - 1 ∧ j < l'.length) → SameShape l'[j].r l[j+1].r)) := by
  intro i hi hl
  use shiftWholeToEnd l i (by omega) hl
  refine ⟨swte_prod_eq .., swte_length .., swte_eq_beg .., ?_, ?_⟩
  · grind [swte_last, List.getLast?_eq_getLast]
  · grind [swte_sameShape]
