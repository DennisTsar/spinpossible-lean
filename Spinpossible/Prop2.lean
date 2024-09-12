import Spinpossible.Proofs
import Mathlib.Data.Finset.Basic

lemma to2d_injective { m n : PNat} : Function.Injective (to2d : Fin (m * n) -> _)
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
  · intro
    simp only [RectangleSet] at *
    simp_all only [Finset.mem_filter, and_self]
  · simp only [RectangleSet, Finset.mem_filter, and_true];
    have : _ ∧ _ := ⟨r.validRow, r.validCol⟩
    unfold validSpins Rectangle.fromPoints
    aesop
    use r.topLeft, r.bottomRight
    aesop
    apply Finset.mk_mem_product <;> simp


-- Define the spin types S(i x j), which is the union of R(i x j) and R(j x i)
def SpinSet (i j : PNat) (m n : PNat) : Finset (Rectangle m n) :=
  (RectangleSet i j m n) ∪ (RectangleSet j i m n)

lemma helper (a : Nat) (b : PNat) : a ≤ a + b - 1 :=
  Nat.le_sub_one_of_lt (Nat.lt_add_of_pos_right b.2)

lemma helper2 {a : Nat} {b c : PNat} (h : a ≤ b.val - c.val) : a < b := by
  have : b.val - c.val ≤ b.val - 1 := Nat.sub_le_sub_left c.2 ↑b
  have : a ≤ b.val - 1 := by linarith
  exact Nat.lt_of_le_pred b.2 this

theorem Finset.card_product' (s : Finset α) (t : Finset β) : card (s.product t) = card s * card t :=
  Finset.card_product _ _

/- Proposition 2.1 -/
lemma rectangleSet_card_val {m n i j : PNat} (h1 : i ≤ m) (h2 : j ≤ n) (h3 : m ≤ n)
    : (RectangleSet i j m n).card = (m+1-i)*(n+1-j) := by
  have ewq : ∀ r, r ∈ RectangleSet i j m n →
      (r.topLeft.row.val + i -1 < m ∧ r.topLeft.col.val + j - 1 < n) := by
    intro r hr_in_set
    have : r.bottomRight.row.val - r.topLeft.row.val + 1 = ↑↑i ∧ r.bottomRight.col.val - r.topLeft.col.val + 1 = ↑↑j := by
      unfold RectangleSet at hr_in_set
      aesop
    omega

    -- We need to prove that each rectangle in RectangleSet corresponds uniquely to a pair of row and column values
  have h_bij : ∀ r ∈ RectangleSet i j m n, (r.topLeft.row.val ∈ Finset.Icc 0 (m - i : ℕ) ∧ r.topLeft.col.val ∈ Finset.Icc 0 (n - j : ℕ)) := by
    intros r hr
    have := ewq r hr
    have : r.topLeft.row.val ≤ ↑m - ↑i := by omega
    have : r.topLeft.col.val ≤ ↑n - ↑j := by omega
    aesop

  have h_bij2 : ∀ r ∈ RectangleSet i j m n, ⟨r.topLeft.row, r.topLeft.col⟩ ∈ ((Finset.Icc 0 (m - i : ℕ)).product (Finset.Icc 0 (n - j : ℕ))) := by
    intros r hr
    -- Apply h_bij to get row and column membership in the respective intervals
    have h_row_col := h_bij r hr
    obtain ⟨h_row, h_col⟩ := h_row_col
    -- Decompose the membership in the row and column intervals
    -- Now use Finset.mem_product to conclude that ⟨r.topLeft.row, r.topLeft.col⟩ is in the product of the intervals
    apply Finset.mem_product.mpr
    exact ⟨h_row, h_col⟩

  -- have := Finset.card_bij ?_ h_bij2

  have : (RectangleSet i j m n).card = ((Finset.Icc 0 (m - i : ℕ)).product (Finset.Icc 0 (n - j : ℕ))).card := by
    apply Finset.card_bij (fun r _ => (⟨r.topLeft.row, r.topLeft.col⟩ : Prod _ _)) h_bij2
    ·
      intro r1 hr1 r2 hr2 h3
      have : r1.bottomRight.row.val - r1.topLeft.row.val + 1 = ↑↑i ∧ r1.bottomRight.col.val - r1.topLeft.col.val + 1 = ↑↑j := by
        unfold RectangleSet at hr1
        aesop
      have : r2.bottomRight.row.val - r2.topLeft.row.val + 1 = ↑↑i ∧ r2.bottomRight.col.val - r2.topLeft.col.val + 1 = ↑↑j := by
        unfold RectangleSet at hr2
        aesop
      have : _ ∧ _ := ⟨r1.validRow, r1.validCol⟩
      have : _ ∧ _ := ⟨r2.validRow, r2.validCol⟩
      have : r1.topLeft.row.val = r2.topLeft.row.val := by simp_all
      have : r1.topLeft.col.val = r2.topLeft.col.val := by simp_all
      ext
      · assumption
      · assumption
      · omega
      · omega
    · intro ⟨num1, num2⟩ h12
      have ⟨hp1, hp2⟩ := (Finset.mem_product.mp h12)
      simp at hp1 hp2
      have w1 : num1 ≤ ↑m - ↑i := by omega
      have w2 : num2 ≤ ↑n - ↑j := by omega
      have : ↑m.val - ↑i.val + 1 = ↑m.val + 1 - ↑i.val := Eq.symm (Nat.sub_add_comm h1)
      have w3: num1 + i - 1 < ↑m := Nat.sub_lt_right_of_lt_add (le_add_of_le_right i.2) (by omega)
      have : ↑n.val - ↑j.val + 1 = ↑n.val + 1 - ↑j.val := Eq.symm (Nat.sub_add_comm h2)
      have w4 : num2 + j - 1 < ↑n := Nat.sub_lt_right_of_lt_add (le_add_of_le_right j.2) (by omega)
      use ⟨
        ⟨⟨num1, helper2 w1⟩, ⟨num2, helper2 w2⟩⟩,
        ⟨⟨num1 + i - 1, w3⟩, ⟨num2 + j - 1, w4⟩⟩,
        by simp; apply helper,
        by simp; apply helper⟩
      simp
      apply rectangleSet_cond_iff.mpr
      simp
      constructor
      · have : i.val - 1 + 1 = i.val := Nat.sub_add_cancel i.2
        omega
      · have : j.val - 1 + 1 = j.val := Nat.sub_add_cancel j.2
        omega

  rw [Finset.card_product'] at this
  simp at this
  have x1: ↑m.val - ↑i.val + 1 = m.val + 1 - i.val := Eq.symm (Nat.sub_add_comm h1)
  have x2 : ↑n.val - ↑j.val + 1 = n.val + 1 - j.val := Eq.symm (Nat.sub_add_comm h2)
  rwa [x1, x2] at this
