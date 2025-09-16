import Spinpossible.Prop2
import Spinpossible.Lemma1
import Spinpossible.Corollary1
import Mathlib.Data.Set.Finite.List

lemma RectSpin.perm_symm (s : RectSpin m n) : s.α.symm = s.α := by simp [s.h, Rectangle.toSpin]

lemma RectSpin.orient_def (s : RectSpin m n) : ∀ x, s.u (s.α x) = s.u x := by
  simp [s.h, Rectangle.toSpin]
  grind

lemma RectSpin.inv_self (s : RectSpin m n) : s.toSpin⁻¹ = s.toSpin := by
  simp [s.h, Rectangle.toSpin, Spin.inv_def]
  grind

abbrev validSpins_spin (m n : PNat) : Finset (Spin m n) := validSpins m n
  |>.map ⟨fun r => r.toSpin, RectSpin.toSpin_injective⟩

lemma exists_rectSpin {s : Spin m n} (hs : s ∈ l) (hl : l ⊆ (validSpins_spin m n).toList) :
    ∃! a : RectSpin m n, a = s := by
  let ⟨a, ha⟩ : ∃ a ∈ validSpins m n, a = s := by
    suffices ∃ a ∈ validSpins_spin m n, a = s by simpa
    exact exists_eq_right.mpr (Finset.mem_toList.mp (hl hs))
  use a, ha.2
  intro b rfl
  exact RectSpin.toSpin_injective ha.2.symm

lemma rectSpin_prod_inv_eq_reverse_prod (l : List (RectSpin m n)) :
    (l.map RectSpin.toSpin).prod⁻¹ = (l.map RectSpin.toSpin).reverse.prod := by
  rw [Spin.inv_def]
  induction' l with hd tl ih
  · simp [Spin.one_def]
  · simp [Spin.mul_def, RectSpin.orient_def, ZMod.neg_eq_self_mod_two, ← ih,
      RectSpin.perm_symm, Equiv.ext_iff]

/-- "In mathematical terms, the game works as follows: given an element `b ∈ Spinₘₓₙ`
    (the starting board), write `b⁻¹` as a product `s₁s₂s₃⋯sₖ` of elements in `S`, with `k`
    as small as possible (a solution)."
-/
def Spin.IsSolution (l : List (RectSpin m n)) (b : Spin m n) : Prop :=
  (l.map RectSpin.toSpin).prod = b⁻¹ ∧
  ∀ l' : List (RectSpin m n), (l'.map RectSpin.toSpin).prod = b⁻¹ → l'.length ≥ l.length

/-- "Applying the spins `s₁s₂s₃⋯sₖ` to `b` then yields the identity (the standard board)." -/
lemma Spin.IsSolution.apply_self {b : Spin m n} (h : Spin.IsSolution l b) :
  b * (l.map RectSpin.toSpin).prod = 1 := h.1 ▸ (mul_inv_cancel _)

def spinSet_to_rectSpin (l : List (Spin m n))
    (h : l ⊆ (validSpins_spin m n).toList) : List (RectSpin m n) :=
  l.attach.map fun ⟨s, hs⟩ =>
    Finset.choose (· = s) (validSpins m n) (by simp [exists_rectSpin hs h])

@[simp]
lemma spinSet_to_rectSpin_inv : (spinSet_to_rectSpin l h).map RectSpin.toSpin = l := by
  induction' l with hd tl ih
  · rfl
  · simp [spinSet_to_rectSpin] at ih h ⊢
    exact ⟨Finset.choose_property (fun x : RectSpin _ _ => x.toSpin = hd) _ _, @ih h.2⟩

lemma spin_prod_inv_eq_reverse_prod {l : List (Spin m n)}
    (h : l ⊆ (validSpins_spin m n).toList) : l.prod⁻¹ = l.reverse.prod := by
  simpa using rectSpin_prod_inv_eq_reverse_prod (spinSet_to_rectSpin l h)

/-- "every starting board in the Spinpossible game has a solution." -/
lemma every_board_has_solution (b : Spin m n) : ∃ l, Spin.IsSolution l b := by
  suffices ∃ l : List (RectSpin m n), (l.map RectSpin.toSpin).prod = b⁻¹ by
    obtain ⟨l, hl1⟩ := this
    let s := {l' : List (RectSpin m n) | (l'.map RectSpin.toSpin).prod = b⁻¹ ∧ l'.length ≤ l.length}
    have : s.Finite := Set.Finite.subset (List.finite_length_le _ l.length) (fun a b => b.2)
    let ⟨y, hy1, hy2⟩ := s.exists_min_image (·.length) this ⟨l, hl1, le_refl _⟩
    use y, hy1.1
    intro z hz1
    by_contra! hz2
    have : z ∈ s := Set.mem_setOf.mpr ⟨hz1, by rw [Set.mem_setOf_eq] at hy1; omega⟩
    exact Nat.not_le_of_lt hz2 (hy2 _ this)
  have : b ∈ Subgroup.closure (mySet m n) := by rw [spin_s11_s12_closure]; trivial
  obtain ⟨l, hl1, rfl⟩ := Subgroup.exists_list_of_mem_closure.mp this
  have hl3 : l ⊆ (validSpins_spin m n).toList := by
    grind [mySet, Function.Embedding.coeFn_mk, Finset.mem_toList, RectSpin.inv_self, inv_inv]
  use (spinSet_to_rectSpin l hl3).reverse
  rw [List.map_reverse, spinSet_to_rectSpin_inv, spin_prod_inv_eq_reverse_prod hl3]
