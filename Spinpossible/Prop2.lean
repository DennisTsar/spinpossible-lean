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
  Finset.univ.product (Finset.univ)
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
    exact Finset.mem_filter.mp h|>.2
  · intro h
    refine Finset.mem_filter.mpr ⟨?_, h⟩
    unfold validSpins
    simp only [Finset.mem_filterMap, dite_some_none_eq_some, Prod.exists]
    use r.topLeft, r.bottomRight
    constructor
    · apply Finset.mk_mem_product <;> simp only [Finset.mem_univ]
    · simp only [and_self, exists_const, r.validRow, r.validCol]

/-- **Proposition 2.1**
    NOTE: The original conditions `i ≤ m`, `j ≤ n`, an `m ≤ n` are not necessary.
-/
theorem rectangleSet_card_val {m n i j : PNat}
    : (RectangleSet i j m n).card = (m.val + 1 - i) * (n.val + 1 - j) := by
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
