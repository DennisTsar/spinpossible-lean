import Spinpossible.Proofs
import Mathlib.Data.Finset.Basic

lemma to2d_injective {m n : PNat} : Function.Injective (to2d : Fin (m * n) -> _)
  | p1, p2, h => by simpa only [to1d_to2d_inverse] using congr(to1d $h)

lemma to2d_surjective {m n : PNat} : Function.Surjective (to2d : Fin (m * n) -> _) :=
  fun x => ⟨to1d x, by simp [to1d_to2d_inverse]⟩

instance {m n : PNat} : Fintype (Point m n) :=
  Fintype.ofBijective to2d ⟨to2d_injective, to2d_surjective⟩

abbrev Rectangle.fromPoints {m n : PNat} (p1 p2 : Point m n) : Option (Rectangle m n) :=
  if h : p1.row ≤ p2.row ∧ p1.col ≤ p2.col then
    some ⟨p1, p2, h.2, h.1⟩
  else
    none

-- Define the set of valid spins S(m, n) as a Finset of rectangles
def validSpins (m n : PNat) : Finset (Rectangle m n) :=
  Finset.univ ×ˢ (Finset.univ)
    |>.filterMap (fun (p1, p2) => Rectangle.fromPoints p1 p2) (by aesop)

-- Define the set of spins R(i x j), which are the spins about i x j rectangles
-- Not sure this is a helpful definition since the return type is too broad
def RectangleSet (i j : PNat) (m n : PNat) : Finset (Rectangle m n) :=
  (validSpins m n).filter (fun r => r.bottomRight.row.val - r.topLeft.row.val + 1 = i ∧
                                    r.bottomRight.col.val - r.topLeft.col.val + 1 = j)

lemma rectangleSet_cond_iff {r : Rectangle m n} :
  r ∈ RectangleSet i j m n ↔
    r.bottomRight.row.val - r.topLeft.row.val + 1 = i ∧
    r.bottomRight.col.val - r.topLeft.col.val + 1 = j := by
  apply Iff.intro
  · intro h
    exact Finset.mem_filter.mp h |>.2
  · intro h
    refine Finset.mem_filter.mpr ⟨?_, h⟩
    unfold validSpins
    simp only [Finset.mem_filterMap, dite_some_none_eq_some, Prod.exists]
    use r.topLeft, r.bottomRight
    constructor
    · apply Finset.mk_mem_product <;> simp only [Finset.mem_univ]
    · simp only [and_self, exists_const, r.validRow, r.validCol]

/-- The set `R_i×j` is necessarily empty if `i > m` or `j > n` -/
example {i j m n : PNat} : (i > m ∨ j > n) → (RectangleSet i j m n) = ∅ := by
  intro h
  apply Finset.filter_eq_empty_iff.mpr
  intro r
  simp_rw [←PNat.coe_lt_coe] at h
  omega

/-- we may have `R_i×j = ∅` even when `R_j×i ≠ ∅` (although this can occur only when `m ≠ n`) -/
example {i j m n} : (RectangleSet i j m n = ∅ ∧ RectangleSet j i m n ≠ ∅) → m ≠ n := by
  intro ⟨h1, h2⟩
  have := Finset.filter_eq_empty_iff.mp h1
  have ⟨r, hr, hp⟩ := Finset.filter_nonempty_iff.mp (Finset.nonempty_iff_ne_empty.mpr h2)
  specialize this hr
  have ⟨a, b⟩ := (Finset.mem_filterMap _).mp hr
  simp [Rectangle.fromPoints] at b
  obtain ⟨h9, h7, h6⟩ := b
  simp at *
  sorry

/-- **Proposition 2.1**
    NOTE: The original conditions `i ≤ m`, `j ≤ n`, an `m ≤ n` are not necessary.
-/
theorem rectangleSet_card_val {m n i j : PNat} :
    (RectangleSet i j m n).card = (m.val + 1 - i) * (n.val + 1 - j) := by
  rw [←Finset.card_range (m + 1 - i), ←Finset.card_range (n + 1 - j), ←Finset.card_product]
  apply Finset.card_bij (fun r _ => ⟨r.topLeft.row, r.topLeft.col⟩)
  · intro r hr
    apply Finset.mem_product.mpr
    have := rectangleSet_cond_iff.mp hr
    have : r.topLeft.row.val < m + 1 - i := by omega
    have : r.topLeft.col.val < n + 1 - j := by omega
    simp only [*, and_self, Finset.mem_range]
  · intro r1 hr1 r2 hr2 h3
    simp only [Prod.mk.injEq] at h3
    have := rectangleSet_cond_iff.mp hr1
    have := rectangleSet_cond_iff.mp hr2
    have : _ ∧ _ := ⟨r1.validRow, r1.validCol⟩
    have : _ ∧ _ := ⟨r2.validRow, r2.validCol⟩
    ext <;> omega
  · intro ⟨p1, p2⟩ hp
    have ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    simp only [Finset.mem_range] at hp1 hp2
    have : i.val - 1 + 1 = i := Nat.sub_add_cancel i.2
    have : j.val - 1 + 1 = j := Nat.sub_add_cancel j.2
    use ⟨
      ⟨⟨p1, by omega⟩, ⟨p2, by omega⟩⟩,
      ⟨⟨i - 1 + p1, by omega⟩, ⟨j - 1 + p2, by omega⟩⟩,
      by simp, by simp⟩
    simp only [exists_prop, and_true]
    apply rectangleSet_cond_iff.mpr
    simp only
    omega

def SpinSet (i j : PNat) (m n : PNat) : Finset (Rectangle m n) :=
  RectangleSet i j m n ∪ RectangleSet j i m n

/-- **Proposition 2.2** -/
theorem prop2 {m n i j : PNat} :
  (SpinSet i j m n ).card = if i = j then (RectangleSet i j m n).card
    else (RectangleSet i j m n).card + (RectangleSet j i m n).card := by
  rw [SpinSet]
  split
  · simp_all only [Finset.union_idempotent]
  rw [RectangleSet]
  apply Finset.card_union_of_disjoint
  apply Finset.disjoint_filter.mpr
  intros
  simp_all only [PNat.coe_inj, false_and, not_false_eq_true]

-- really this should probably be the original def?
lemma validSpins_def2 : validSpins m n =
  ((Finset.range m) ×ˢ (Finset.range n)).biUnion
    (fun p => RectangleSet ⟨p.1 + 1, by omega⟩ ⟨p.2 + 1, by omega⟩ m n) := by
  refine Finset.ext_iff.mpr ?_
  intro r
  constructor
  · intro
    simp
    use r.bottomRight.row.val - r.topLeft.row.val, (by omega)
    use r.bottomRight.col.val - r.topLeft.col.val, (by omega)
    apply rectangleSet_cond_iff.mpr
    simp
  · intro
    simp [validSpins]
    use r.topLeft, r.bottomRight
    have : _ ∧ _ := ⟨r.validRow, r.validCol⟩
    simp_all only [and_self, exists_const]

lemma sum_m_minus_x1.aux1 {a b c : Nat} (h: (a : ℤ) = b - c) : a = b - c := by omega

open Finset in
lemma sum_m_minus_x1 (m : PNat) :
    (∑ x in range m, (m.val - x)) * 2 = m.val * (m.val + 1) := by
  set n := m.val
  have : ∑ x in range n, (n - x) = (∑ _i in range n, n) - (∑ i in range n, i) := by
    apply sum_m_minus_x1.aux1
    zify
    convert Finset.sum_sub_distrib
    · rename_i a b
      have : a < n := List.mem_range.mp b
      omega
  rw [this, Nat.sub_mul, Finset.sum_range_id_mul_two, Nat.mul_sub_one, Nat.sub_eq_of_eq_add]
  simp only [sum_const, card_range, smul_eq_mul]
  linarith [Nat.add_sub_of_le <| Nat.le_mul_self n]

lemma sum_m_minus_x (m : PNat) :
    ∑ i in Finset.range m, (m.val - i) = m.val * (m.val + 1) / 2 := by
  have := sum_m_minus_x1 m
  omega

/-- **Proposition 2.3** -/
theorem total_valid_spins_card {m n : PNat} :
  (validSpins m n).card = (m * (m + 1) / 2) * (n * (n + 1) / 2) := by
  rw [validSpins_def2]
  rw [Finset.card_biUnion]
  · simp only [rectangleSet_card_val, PNat.mk_coe, Nat.reduceSubDiff]
    rw [Finset.sum_product, ←Finset.sum_mul_sum, sum_m_minus_x m, sum_m_minus_x n]
  · simp only [Finset.mem_product, Finset.mem_range, ne_eq, and_imp, Prod.forall,
      Prod.mk.injEq, not_and]
    intros
    apply Finset.disjoint_left.mpr
    intro r hr
    by_contra hr2
    have := rectangleSet_cond_iff.mp hr
    have := rectangleSet_cond_iff.mp hr2
    simp_all
