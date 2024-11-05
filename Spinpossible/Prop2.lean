import Spinpossible.Proofs
import Mathlib.Algebra.BigOperators.Intervals

lemma to2d_injective {m n : PNat} : Function.Injective (to2d : Fin (m * n) -> _)
  | p1, p2, h => by simpa only [to1d_to2d_inverse] using congr(to1d $h)

lemma to2d_surjective {m n : PNat} : Function.Surjective (to2d : Fin (m * n) -> _) :=
  fun x => ⟨to1d x, to2d_to1d_inverse⟩

instance {m n : PNat} : Fintype (Point m n) :=
  Fintype.ofBijective to2d ⟨to2d_injective, to2d_surjective⟩

abbrev Rectangle.fromPoints {m n : PNat} (p1 p2 : Point m n) : Option (Rectangle m n) :=
  if h : p1.row ≤ p2.row ∧ p1.col ≤ p2.col then
    some ⟨p1, p2, h.2, h.1⟩
  else
    none

-- Define the set of valid spins S(m, n) as a Finset of rectangles
def validSpins (m n : PNat) : Finset (Rectangle m n) :=
  Finset.univ.filterMap (fun (p1, p2) => Rectangle.fromPoints p1 p2) (by aesop)

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
    simp only [validSpins, Finset.mem_filterMap, Finset.mem_univ, true_and, Prod.exists]
    use r.topLeft, r.bottomRight
    simp [r.validRow, r.validCol]

/-- "The set `R_i×j` is necessarily empty if `i > m` or `j > n`" -/
lemma rectangleSet_empty_if {i j m n : PNat} : (i > m.val ∨ j > n.val) → (RectangleSet i j m n) = ∅ := by
  intro h
  apply Finset.filter_eq_empty_iff.mpr
  intro r
  omega

/-- "we may have `R_i×j = ∅` even when `R_j×i ≠ ∅` (although this can occur only when `m ≠ n`)" -/
lemma rectangleSet_empty_nonempty {m n : PNat} :
  (m.val ≠ n → ∃ i j, RectangleSet i j m n = ∅ ∧ RectangleSet j i m n ≠ ∅) ∧
    (RectangleSet i j m n = ∅ ∧ RectangleSet j i m n ≠ ∅ → m ≠ n) := by
  constructor
  · intro h
    use n, m
    constructor
    · exact rectangleSet_empty_if (lt_or_gt_of_ne h)
    · apply Finset.nonempty_iff_ne_empty.mp
      have : m.val > 0 ∧ n.val > 0 := ⟨m.2, n.2⟩
      use ⟨⟨⟨0, m.2⟩, ⟨0, n.2⟩⟩, ⟨⟨m - 1, by omega⟩, ⟨n - 1, by omega⟩⟩, by simp, by simp⟩
      simp [rectangleSet_cond_iff]
      omega
  · intro ⟨h1, h2⟩
    let ⟨_, _, hr⟩ := Finset.filter_nonempty_iff.mp (Finset.nonempty_iff_ne_empty.mpr h2)
    have : i.val > m.val ∨ j.val > n.val := by
      by_contra!
      absurd h1
      apply Finset.nonempty_iff_ne_empty.mp
      use ⟨⟨⟨0, m.2⟩, ⟨0, n.2⟩⟩, ⟨⟨i.val - 1, by omega⟩, ⟨j.val - 1, by omega⟩⟩, by simp, by simp⟩
      simp [rectangleSet_cond_iff]
      omega
    rw [ne_eq, ←PNat.coe_inj]
    omega

/-- **Proposition 2.1**
    NOTE: The original conditions `i ≤ m`, `j ≤ n`, an `m ≤ n` are not necessary.
-/
theorem rectangleSet_card_val {m n i j : PNat} :
    (RectangleSet i j m n).card = (m.val + 1 - i) * (n.val + 1 - j) := by
  rw [←Finset.card_range (m + 1 - i), ←Finset.card_range (n + 1 - j), ←Finset.card_product]
  apply Finset.card_bij (fun r _ => ⟨r.topLeft.row, r.topLeft.col⟩)
  · intro r hr
    have := rectangleSet_cond_iff.mp hr
    have : r.topLeft.row.val < m + 1 - i := by omega
    have : r.topLeft.col.val < n + 1 - j := by omega
    simp only [Finset.mem_range, and_self, Finset.mem_product.mpr, *]
  · intro r1 hr1 r2 hr2 h3
    rw [Prod.mk.injEq] at h3
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
    simp [rectangleSet_cond_iff.mpr, *]

def SpinSet (i j : PNat) (m n : PNat) : Finset (Rectangle m n) :=
  RectangleSet i j m n ∪ RectangleSet j i m n

/-- **Proposition 2.2** -/
theorem prop2 {m n i j : PNat} :
  (SpinSet i j m n).card = if i = j then (RectangleSet i j m n).card
    else (RectangleSet i j m n).card + (RectangleSet j i m n).card := by
  split
  · simp_all only [SpinSet, Finset.union_idempotent]
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
    simp only [Finset.product_biUnion, Finset.mem_biUnion, Finset.mem_range]
    use r.bottomRight.row.val - r.topLeft.row.val, (by omega)
    use r.bottomRight.col.val - r.topLeft.col.val, (by omega)
    simp [rectangleSet_cond_iff.mpr]
  · intro
    simp [validSpins]
    use r.topLeft, r.bottomRight
    simp_all only [r.validRow, r.validCol, and_self, exists_const]

private lemma sum_nat_sub_distrib.aux1 {a b c : Nat} (h: (a : ℤ) = b - c) : a = b - c := by omega

lemma Finset.sum_nat_sub_distrib {m n : Nat} (h : n ≥ m) :
    ∑ x in range m, (n - x) = (∑ _i in range m, n) - (∑ i in range m, i) := by
  apply sum_nat_sub_distrib.aux1
  zify
  convert Finset.sum_sub_distrib with a ha
  have : a < m := List.mem_range.mp ha
  omega

lemma sum_m_minus_x_mul_two (m : Nat) : (∑ x in Finset.range m, (m - x)) * 2 = (m + 1) * m := by
  rw [Finset.sum_nat_sub_distrib (by omega), Nat.sub_mul, Finset.sum_range_id_mul_two,
    Nat.mul_sub_one, Nat.sub_eq_of_eq_add]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  linarith [Nat.add_sub_of_le <| Nat.le_mul_self m]

lemma sum_m_minus_x (m : PNat) :
    ∑ i in Finset.range m, (m - i) = (m + 1) * m / 2 := by
  have := sum_m_minus_x_mul_two m
  omega

/-- **Proposition 2.3** -/
theorem total_valid_spins_card {m n : PNat} :
  (validSpins m n).card = (m.val + 1).choose 2 * (n.val + 1).choose 2 := by
  rw [validSpins_def2, Finset.card_biUnion]
  · simp only [rectangleSet_card_val, PNat.mk_coe, Nat.reduceSubDiff, Nat.choose_two_right]
    rw [Finset.sum_product, ←Finset.sum_mul_sum, sum_m_minus_x m, sum_m_minus_x n]
  · simp only [Finset.mem_product, Finset.mem_range, ne_eq, and_imp, Prod.forall,
      Prod.mk.injEq, not_and]
    intros
    apply Finset.disjoint_left.mpr
    intro r hr
    by_contra
    simp_all only [rectangleSet_cond_iff, PNat.mk_coe, add_left_inj, not_true_eq_false, imp_false]

-- More convenient version of `ne_of_mem_of_not_mem'`
lemma ne_of_mem_of_not_mem'' {a b : Finset α} (x : α) : x ∈ a ∧ x ∉ b → a ≠ b := by
  intro h
  exact ne_of_mem_of_not_mem' h.1 h.2

abbrev numsToSpinSet (i j : Nat) (m n : PNat) :=
  SpinSet ⟨i + 1, Nat.zero_lt_succ _⟩ ⟨j + 1, Nat.zero_lt_succ _⟩ m n

lemma spinSet_comm : SpinSet i j m n = SpinSet j i m n := by
  simp [SpinSet, Finset.union_comm]

lemma numsToSpinSet_comm : numsToSpinSet i j m n = numsToSpinSet j i m n := spinSet_comm

lemma sizes_eq_of_spinSet_eq (h : numsToSpinSet a b m n = numsToSpinSet c d m n)
  (h2 : a < m ∧ b < n) (h3 : ¬(a = d ∧ b = c)) : a = c ∧ b = d := by
  by_contra hc
  absurd h
  apply ne_of_mem_of_not_mem'' ⟨⟨0,0⟩, ⟨⟨a, h2.1⟩, ⟨b, h2.2⟩⟩, Fin.zero_le' _, Fin.zero_le' _⟩
  simp [SpinSet, RectangleSet, validSpins, hc, h3]

abbrev spinSetNums (m n : PNat) :=
  ((Finset.range m) ×ˢ (Finset.range n)).image (fun (a,b) => if a ≤ b then (a,b) else (b, a))

lemma spinSetNums_card (m n : PNat) (h : m.val ≤ n) :
    (spinSetNums m n).card = m * (2 * n - m + 1) / 2 := by
  let s := (Finset.range m).biUnion (fun i => (Finset.Ico i n)
    |>.map ⟨fun j => (i, j), by intros a1 a2 ha; aesop⟩)
  have : spinSetNums m n = s := by
    refine Finset.ext_iff.mpr ?_
    intro x
    constructor
    · intro hx
      simp [s] at hx ⊢
      obtain ⟨_, _, _, hx⟩ := hx
      use x.1
      split_ifs at hx
      · have := Prod.ext_iff.mp hx
        refine ⟨by omega, ?_⟩
        use x.2
        simp_all
      · have := Prod.ext_iff.mp hx
        refine ⟨by omega, ?_⟩
        use x.2
        simp_all [-h]
        omega
    · intro hx
      simp [s] at hx ⊢
      use x.1, x.2
      aesop
  rw [this, Finset.card_biUnion]
  · simp_all only [Finset.card_map, Finset.card_attach, Prod.mk.eta, PNat.coe_le_coe,
      Nat.card_Ico, -h]
    refine Nat.eq_div_of_mul_eq_right (by omega) ?_
    rw [Finset.sum_nat_sub_distrib h, Finset.sum_const, Finset.card_range, smul_eq_mul,
      Finset.sum_range_id]
    set x1 := m.val
    set x2 := n.val
    have : x1 ≥ 1 := NeZero.one_le
    rw [Nat.mul_sub_left_distrib, Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self x1),
      show 2 * x2 - x1 + 1 = 2 * x2 - (x1 - 1) by omega,
      Nat.mul_sub_left_distrib x1 (2 * x2) _, Nat.mul_left_comm]
  · intro x _ y _ hxy
    refine Finset.disjoint_left.mpr ?_
    intro k _ _
    have : k.1 = x ∧ k.1 = y := by aesop
    exact hxy (this.1 ▸ this.2)

def spinSetsFromNums (m n : PNat) : Finset (Finset (Rectangle m n)) :=
  (spinSetNums m n)|>.attach.map ⟨fun ⟨(a,b), _⟩ => numsToSpinSet a b m n, by
    intro ⟨⟨a1, a2⟩, ha⟩ ⟨⟨b1, b2⟩, hb⟩ h_eq
    simp only at h_eq
    rw [@Subtype.mk_eq_mk, Prod.mk.injEq]
    by_cases op_eq : (a1 = b2 ∧ a2 = b1)
    · let ⟨_, _, hc2⟩:= Finset.mem_image.mp ha
      let ⟨_, _, hc4⟩:= Finset.mem_image.mp hb
      simp only [Prod.mk.eta] at hc2 hc4
      split_ifs at hc2 hc4 <;> (simp_all; omega)
    · have : (a1 < m ∧ a2 < n) ∨ (a1 < n ∧ a2 < m) := by aesop
      rcases this with h | h
      · exact sizes_eq_of_spinSet_eq h_eq h op_eq
      · rw [numsToSpinSet_comm, numsToSpinSet_comm (i := b1)] at h_eq
        exact sizes_eq_of_spinSet_eq h_eq ⟨h.2, h.1⟩ (by omega) |>.symm
  ⟩

def spinSetTypes (m n : PNat) :=
  { (a, b) : Nat × Nat | (numsToSpinSet a b m n).Nonempty }
  |>.image (fun (a,b) => numsToSpinSet a b m n)

lemma spinSetTypes_eq {m n : PNat} (h : m.val ≤ n) :
    spinSetTypes m n = spinSetsFromNums m n := by
  refine Set.ext_iff.mpr ?_
  intro s
  constructor
  · intro hs
    refine Finset.mem_map.mpr ?_
    let ⟨x, y, _, _⟩ : ∃ x y : Nat,
        s = numsToSpinSet x y m n ∧ (numsToSpinSet x y m n).Nonempty := by
      simp [spinSetTypes] at *
      aesop

    let ⟨c, d, hcd⟩ : ∃ c d : Nat,
        (c < m ∧ d < n) ∧ numsToSpinSet c d m n = numsToSpinSet x y m n := by
      let a : PNat := ⟨x + 1, Nat.zero_lt_succ _⟩
      let b : PNat := ⟨y + 1, Nat.zero_lt_succ _⟩
      have : (RectangleSet a b m n).Nonempty ∨ (RectangleSet b a m n).Nonempty := by
        by_contra
        simp_all [SpinSet]
      rcases this with h5 | h5
      · use x, y
        refine ⟨?_, rfl⟩
        by_contra
        have : a > m.val ∨ b > n.val := by simp [a,b]; omega
        exact Finset.nonempty_iff_ne_empty.mp h5 (rectangleSet_empty_if this)
      · use y, x
        refine ⟨?_, spinSet_comm⟩
        by_contra
        have : b > m.val ∨ a > n.val := by simp [a,b]; omega
        exact Finset.nonempty_iff_ne_empty.mp h5 (rectangleSet_empty_if this)

    simp only [Finset.mem_attach, Function.Embedding.coeFn_mk, true_and,
      Subtype.exists, Finset.mem_image, Finset.mem_product, Finset.mem_range, Prod.exists]
    dsimp only [numsToSpinSet] at hcd
    by_cases h8 : c ≤ d
    · use c, d
      refine ⟨?_, by simp_all only⟩
      use c, d
      simp only [hcd, and_self, h8, reduceIte]
    · use d, c
      refine ⟨?_, by simp_all only [spinSet_comm ▸ hcd.2]⟩
      use c, d
      simp only [hcd, and_self, h8, reduceIte]
  · intro hs
    let ⟨⟨⟨x, y⟩, hxy⟩, _⟩ := Finset.mem_map.mp hs
    simp only [Set.mem_image, Prod.exists, spinSetTypes]
    use x, y
    simp_all only [Finset.mem_coe, Finset.mem_attach, SpinSet, Function.Embedding.coeFn_mk,
      true_and, and_true]

    have : (x < m ∧ y < n) ∨ (y < m ∧ x < n) := by
      by_contra
      absurd hxy
      simp only [Prod.mk.eta, Finset.mem_image, Finset.mem_product, Finset.mem_range,
        Prod.exists, not_exists, not_and, and_imp]
      intros
      split_ifs
      · by_contra h
        have := Prod.ext_iff.mp h
        omega
      · by_contra h
        have := Prod.ext_iff.mp h
        omega

    rcases this with hmn | hmn
    · refine Finset.Nonempty.inl ?_
      use ⟨⟨0,0⟩, ⟨⟨x, hmn.1⟩, ⟨y, hmn.2⟩⟩, Fin.zero_le' _, Fin.zero_le' _⟩
      simp [RectangleSet, validSpins]
    · refine Finset.Nonempty.inr ?_
      use ⟨⟨0,0⟩, ⟨⟨y, hmn.1⟩, ⟨x, hmn.2⟩⟩, Fin.zero_le' _, Fin.zero_le' _⟩
      simp [RectangleSet, validSpins]

lemma spinSetTypes_finite {m n : PNat} (h : m.val ≤ n) : (spinSetTypes m n).Finite :=
  spinSetTypes_eq h ▸ Finset.finite_toSet _

/-- **Proposition 2.4** -/
theorem spinSetsTypes_card (m n : PNat) (h : m.val ≤ n) :
    let _ := (spinSetTypes_finite h).fintype
    (spinSetTypes m n).toFinset.card = m * (2 * n - m + 1) / 2 := by
  simp [spinSetTypes_eq h]
  simp [spinSetsFromNums, spinSetNums_card m n h]

