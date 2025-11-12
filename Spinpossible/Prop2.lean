import Spinpossible.Proofs
import Mathlib.Algebra.BigOperators.Intervals

lemma Rectangle.toSpin_injective : Function.Injective (Rectangle.toSpin : Rectangle m n -> _)
  | r1, r2, h => by
    have app := congr(Spin.u $h)
    simp only [toSpin, funext_iff, eq_ite_iff] at app
    apply rect_eq_if_corners_inside
    · simpa [corners_inside] using app r1.topLeft
    · simpa [corners_inside] using app r2.topLeft
    · simpa [corners_inside] using app r1.bottomRight
    · simpa [corners_inside] using app r2.bottomRight

abbrev RectSpin.fromRect (r : Rectangle m n) : RectSpin m n := ⟨r.toSpin, r, rfl⟩

lemma RectSpin.r_bijective : Function.Bijective (RectSpin.r : RectSpin m n -> _) where
  left s1 s2 h := by
    ext : 1
    · rw [s1.h, s2.h, h]
    · rw [s1.h, s2.h, h]
    · exact h
  right r := ⟨fromRect r, rfl⟩

lemma RectSpin.toSpin_injective : Function.Injective (RectSpin.toSpin : RectSpin m n -> _)
  | s1, s2, h => r_bijective.1 (Rectangle.toSpin_injective (s1.h ▸ s2.h ▸ h))

abbrev validSpins (m n : PNat) : Finset (RectSpin m n) := Finset.univ

-- @[simp]
-- lemma validSpins_eq_univ {m n : PNat} : validSpins m n = Finset.univ := rfl

-- Define the set of spins R(i x j), which are the spins about i x j rectangles
-- Technically the return type is over-broad, but it works for now
def RectSpinSet (i j : PNat) (m n : PNat) : Finset (RectSpin m n) :=
  (validSpins m n).filter (fun s => s.r.bottomRight.row.val - s.r.topLeft.row.val + 1 = i ∧
                                    s.r.bottomRight.col.val - s.r.topLeft.col.val + 1 = j)

lemma rectSpinSet_cond_iff {s : RectSpin m n} :
  s ∈ RectSpinSet i j m n ↔
    s.r.bottomRight.row.val - s.r.topLeft.row.val + 1 = i ∧
    s.r.bottomRight.col.val - s.r.topLeft.col.val + 1 = j :=
  ⟨(Finset.mem_filter.mp · |>.2), (Finset.mem_filter.mpr ⟨by simp, ·⟩)⟩

/-- "The set `Rᵢₓⱼ` is necessarily empty if `i > m` or `j > n`" -/
lemma rectSpinSet_empty_if {i j m n : PNat} :
  (i > m.val ∨ j > n.val) → RectSpinSet i j m n = ∅ := by grind [RectSpinSet]

/-- "we may have `Rᵢₓⱼ = ∅` even when `Rⱼₓᵢ ≠ ∅` (although this can occur only when `m ≠ n`)" -/
lemma rectSpinSet_empty_nonempty {m n : PNat} :
  (m.val ≠ n → ∃ i j, RectSpinSet i j m n = ∅ ∧ RectSpinSet j i m n ≠ ∅) ∧
    (RectSpinSet i j m n = ∅ ∧ RectSpinSet j i m n ≠ ∅ → m ≠ n) := by
  refine ⟨fun h => ⟨n, m, ?_, ?_⟩, fun ⟨h1, h2⟩ => ?_⟩
  · exact rectSpinSet_empty_if (lt_or_gt_of_ne h)
  · apply Finset.nonempty_iff_ne_empty.mp
    have : m.val > 0 ∧ n.val > 0 := ⟨m.2, n.2⟩
    use RectSpin.fromRect ⟨⟨0, 0⟩, ⟨⟨m.val - 1, by omega⟩, ⟨n.val - 1, by omega⟩⟩, by simp, by simp⟩
    simp [rectSpinSet_cond_iff]
    omega
  · have := Finset.filter_nonempty_iff.mp (Finset.nonempty_iff_ne_empty.mpr h2)
    have : i.val > m.val ∨ j.val > n.val := by
      contrapose! h1
      rw [← Finset.nonempty_iff_ne_empty]
      use RectSpin.fromRect ⟨
        ⟨⟨0, m.2⟩, ⟨0, n.2⟩⟩,
        ⟨⟨i.val - 1, by omega⟩, ⟨j.val - 1, by omega⟩⟩,
        by simp, by simp⟩
      simp [rectSpinSet_cond_iff]
      omega
    grind

/-- **Proposition 2.1**
    NOTE: The original conditions `i ≤ m`, `j ≤ n`, an `m ≤ n` are not necessary.
-/
theorem rectSpinSet_card_val {i j m n : PNat} :
    (RectSpinSet i j m n).card = (m.val + 1 - i) * (n.val + 1 - j) := by
  rw [← Finset.card_range (m + 1 - i), ← Finset.card_range (n + 1 - j), ← Finset.card_product]
  apply Finset.card_bij (fun s _ => ⟨s.r.topLeft.row, s.r.topLeft.col⟩)
  · grind [rectSpinSet_cond_iff]
  · intro s1 hs1 s2 hs2 h3
    apply RectSpin.r_bijective.1
    ext <;> grind [rectSpinSet_cond_iff, Rectangle.validRow, Rectangle.validCol]
  · intro ⟨p1, p2⟩ hp
    have ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    simp only [Finset.mem_range] at hp1 hp2
    have : i.val - 1 + 1 = i := Nat.sub_add_cancel i.2
    have : j.val - 1 + 1 = j := Nat.sub_add_cancel j.2
    use RectSpin.fromRect ⟨
      ⟨⟨p1, by omega⟩, ⟨p2, by omega⟩⟩,
      ⟨⟨i - 1 + p1, by omega⟩, ⟨j - 1 + p2, by omega⟩⟩,
      by simp, by simp⟩
    simp [rectSpinSet_cond_iff, *]

/-- `Sᵢₓⱼ = Rᵢₓⱼ ∪ Rⱼₓᵢ` -/
def SpinSet (i j : PNat) (m n : PNat) : Finset (RectSpin m n) :=
  RectSpinSet i j m n ∪ RectSpinSet j i m n

/-- **Proposition 2.2** -/
theorem prop2 {i j m n : PNat} :
  (SpinSet i j m n).card = if i = j then (RectSpinSet i j m n).card
    else (RectSpinSet i j m n).card + (RectSpinSet j i m n).card := by
  split
  · simp_all only [SpinSet, Finset.union_idempotent]
  apply Finset.card_union_of_disjoint
  apply Finset.disjoint_filter.mpr
  intros
  simp_all only [PNat.coe_inj, false_and, not_false_eq_true]

lemma validSpins_union_rectSpinSet : validSpins m n =
  ((Finset.range m) ×ˢ (Finset.range n)).biUnion
    (fun p => RectSpinSet ⟨p.1 + 1, Nat.zero_lt_succ _⟩ ⟨p.2 + 1, Nat.zero_lt_succ _⟩ m n) := by
  simp [Finset.ext_iff, rectSpinSet_cond_iff]
  omega

private lemma sum_nat_sub_distrib.aux1 {a b c : Nat} (h : (a : ℤ) = b - c) : a = b - c := by omega

lemma Finset.sum_nat_sub_distrib {m n : Nat} (h : n ≥ m) :
    ∑ x ∈ range m, (n - x) = (∑ _i ∈ range m, n) - (∑ i ∈ range m, i) := by
  apply sum_nat_sub_distrib.aux1
  zify
  convert Finset.sum_sub_distrib _ _ with a ha
  have : a < m := Finset.mem_range.mp ha
  omega

lemma sum_m_minus_x_mul_two (m : Nat) : (∑ x ∈ Finset.range m, (m - x)) * 2 = (m + 1) * m := by
  rw [Finset.sum_nat_sub_distrib (Nat.le_refl m), Nat.sub_mul, Finset.sum_range_id_mul_two,
    Nat.mul_sub_one, Nat.sub_eq_of_eq_add]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  -- grind [Nat.le_mul_self] -- used to work in 4.24.0
  rw [← Nat.add_sub_assoc (Nat.le_mul_self _) _]
  grind [Nat.add_sub_assoc]

lemma sum_m_minus_x (m : PNat) :
    ∑ i ∈ Finset.range m, (m - i) = (m + 1) * m / 2 := by grind [sum_m_minus_x_mul_two]

/-- **Proposition 2.3** -/
theorem total_valid_spins_card {m n : PNat} :
  (validSpins m n).card = (m.val + 1).choose 2 * (n.val + 1).choose 2 := by
  rw [validSpins_union_rectSpinSet, Finset.card_biUnion]
  · simp only [rectSpinSet_card_val, PNat.mk_coe, Nat.reduceSubDiff, Nat.choose_two_right]
    rw [Finset.sum_product, ← Finset.sum_mul_sum, sum_m_minus_x m, sum_m_minus_x n]
  · intro h
    grind [rectSpinSet_cond_iff, Finset.disjoint_left, PNat.mk_coe]

-- More convenient version of `ne_of_mem_of_not_mem'`
lemma ne_of_mem_of_not_mem'' {a b : Finset α} (x : α) : x ∈ a ∧ x ∉ b → a ≠ b :=
  fun h => ne_of_mem_of_not_mem' h.1 h.2

abbrev numsToSpinSet (i j : Nat) (m n : PNat) :=
  SpinSet ⟨i + 1, Nat.zero_lt_succ _⟩ ⟨j + 1, Nat.zero_lt_succ _⟩ m n

lemma spinSet_comm : SpinSet i j m n = SpinSet j i m n := by
  simp [SpinSet, Finset.union_comm]

lemma numsToSpinSet_comm : numsToSpinSet i j m n = numsToSpinSet j i m n := spinSet_comm

lemma sizes_eq_of_spinSet_eq (h : numsToSpinSet a b m n = numsToSpinSet c d m n)
    (h2 : a < m ∧ b < n) (h3 : ¬(a = d ∧ b = c)) : a = c ∧ b = d := by
  contrapose h
  apply ne_of_mem_of_not_mem''
   <| RectSpin.fromRect ⟨⟨0, 0⟩, ⟨⟨a, h2.1⟩, ⟨b, h2.2⟩⟩, Fin.zero_le _, Fin.zero_le _⟩
  simp [SpinSet, rectSpinSet_cond_iff, h, h3]

abbrev spinSetNums (m n : PNat) :=
  ((Finset.range m) ×ˢ (Finset.range n)).image (fun (a,b) => if a ≤ b then (a,b) else (b, a))

lemma spinSetNums_card {m n : PNat} (h : m.val ≤ n) :
    (spinSetNums m n).card = m * (2 * n - m + 1) / 2 := by
  let s := (Finset.range m).biUnion (fun i => Finset.Ico i n
    |>.map ⟨fun j => (i, j), Prod.mk_right_injective i⟩)
  have : spinSetNums m n = s := by
    ext x
    constructor
    · simp [s] -- this could be a single `grind` but it doesn't understand `Function.Embedding.coeFn_mk`
      grind
    · intro hx
      simp
      use x.1, x.2
      grind [Finset.mem_Ico, Function.Embedding.coeFn_mk]
  rw [this, Finset.card_biUnion]
  · simp only [Finset.card_map, Nat.card_Ico]
    apply Nat.eq_div_of_mul_eq_right (by omega)
    rw [Finset.sum_nat_sub_distrib h, Finset.sum_const, Finset.card_range, smul_eq_mul,
      Finset.sum_range_id]
    set x1 := m.val
    set x2 := n.val
    have : x1 ≥ 1 := NeZero.one_le
    rw [Nat.mul_sub_left_distrib, Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self x1),
      show 2 * x2 - x1 + 1 = 2 * x2 - (x1 - 1) by omega,
      Nat.mul_sub_left_distrib x1 (2 * x2) _, Nat.mul_left_comm]
  · intro x _ y _ hxy
    grind [Finset.disjoint_left, Function.Embedding.coeFn_mk]

def spinSetsFromNums (m n : PNat) : Finset (Finset (RectSpin m n)) :=
  (spinSetNums m n).attach.map ⟨fun ⟨(a,b), _⟩ => numsToSpinSet a b m n, by
    intro ⟨⟨a1, a2⟩, ha⟩ ⟨⟨b1, b2⟩, hb⟩ h_eq
    simp only at h_eq
    rw [Subtype.mk_eq_mk, Prod.mk_inj]
    by_cases op_eq : a1 = b2 ∧ a2 = b1
    · grind
    · obtain h | h : (a1 < m ∧ a2 < n) ∨ (a1 < n ∧ a2 < m) := by grind
      · exact sizes_eq_of_spinSet_eq h_eq h op_eq
      · rw [numsToSpinSet_comm, numsToSpinSet_comm (i := b1)] at h_eq
        exact sizes_eq_of_spinSet_eq h_eq h.symm (by omega) |>.symm
  ⟩

def spinSetTypes (m n : PNat) :=
  { (a, b) : Nat × Nat | (numsToSpinSet a b m n).Nonempty }
  |>.image (fun (a,b) => numsToSpinSet a b m n)

lemma spinSetTypes_eq {m n : PNat} (h : m.val ≤ n) :
    spinSetTypes m n = spinSetsFromNums m n := by
  ext s
  constructor
  · intro hs
    apply Finset.mem_map.mpr
    let ⟨x, y, _, h_nonempty⟩ : ∃ x y : Nat,
      s = numsToSpinSet x y m n ∧ (numsToSpinSet x y m n).Nonempty := by grind [spinSetTypes]

    let ⟨c, d, hcd⟩ : ∃ c d : Nat,
        (c < m ∧ d < n) ∧ numsToSpinSet c d m n = numsToSpinSet x y m n := by
      rcases Finset.union_nonempty.mp h_nonempty with h5 | h5
      · use x, y, ?_
        by_contra
        exact Finset.nonempty_iff_ne_empty.mp h5 <| rectSpinSet_empty_if (by grind [PNat.mk_coe])
      · use y, x, ?_, spinSet_comm
        by_contra
        exact Finset.nonempty_iff_ne_empty.mp h5 <| rectSpinSet_empty_if (by grind [PNat.mk_coe])

    simp only [Finset.mem_attach, Function.Embedding.coeFn_mk, true_and,
      Subtype.exists, Finset.mem_image, Finset.mem_product, Finset.mem_range, Prod.exists]
    dsimp only [numsToSpinSet] at hcd
    by_cases h8 : c ≤ d
    · use c, d
      grind
    · use d, c
      grind [spinSet_comm]
  · intro hs
    let ⟨⟨⟨x, y⟩, hxy⟩, _⟩ := Finset.mem_map.mp hs
    simp only [Set.mem_image, Prod.exists, spinSetTypes]
    use x, y
    simp_all only [Finset.mem_coe, Finset.mem_attach, SpinSet, Function.Embedding.coeFn_mk,
      true_and, and_true]

    obtain hmn | hmn : (x < m ∧ y < n) ∨ (y < m ∧ x < n) := by grind
    · apply Finset.Nonempty.inl
      use RectSpin.fromRect ⟨⟨0,0⟩, ⟨⟨x, hmn.1⟩, ⟨y, hmn.2⟩⟩, Fin.zero_le _, Fin.zero_le _⟩
      simp [RectSpinSet]
    · apply Finset.Nonempty.inr
      use RectSpin.fromRect ⟨⟨0,0⟩, ⟨⟨y, hmn.1⟩, ⟨x, hmn.2⟩⟩, Fin.zero_le _, Fin.zero_le _⟩
      simp [RectSpinSet]

lemma spinSetTypes_finite {m n : PNat} (h : m.val ≤ n) : (spinSetTypes m n).Finite :=
  spinSetTypes_eq h ▸ Finset.finite_toSet _

/-- **Proposition 2.4** -/
theorem spinSetsTypes_card (m n : PNat) (h : m.val ≤ n) :
    let _ := (spinSetTypes_finite h).fintype
    (spinSetTypes m n).toFinset.card = m * (2 * n - m + 1) / 2 := by
  simp [spinSetTypes_eq h]
  simp [spinSetsFromNums, spinSetNums_card h]
