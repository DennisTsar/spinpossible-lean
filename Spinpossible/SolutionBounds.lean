import Spinpossible.Solution

lemma rect_spin_one (p : Point m n) : Rectangle.toSpin ⟨p, p, by simp, by simp⟩ =
    ⟨Equiv.refl _, fun x => if to2d x = p then 1 else 0⟩ := by
  simp_all [Rectangle.toSpin, Equiv.ext_iff, rotate_around_one_eq_self]
  funext
  exact if_ctx_congr Point.isInside_one_iff (congrFun rfl) (congrFun rfl)

theorem theorem1 (b : Spin m n) : ∀ l, Spin.IsSolution l b → l.length ≤ 3 * m * n - (m + n) := by
  let ⟨v, hv⟩ : ∃ v, b = ⟨b.α, v⟩ * ⟨1, b.u + v⟩ := by
    use 0
    simp [Spin.mul_def]
  have hv2 : b⁻¹ = ⟨1, b.u + v⟩⁻¹ * ⟨b.α, v⟩⁻¹ := by
    nth_rw 1 [hv]
    simp [Spin.mul_def, Spin.inv_def, funext_iff, add_comm]
  have h3 : ∃ l : List (RectSpin m n), (l.map RectSpin.toSpin).prod =
      ⟨1, b.u + v⟩⁻¹ ∧ l.length ≤ m * n := by
    let z1 : List (RectSpin m n) := []
    let z1' : List (Spin m n) := z1.map RectSpin.toSpin
    let z2 : List (RectSpin m n) := (List.finRange (m * n)).filterMap fun x : Fin (m * n) =>
      if (z1'.prod.u x ≠ (b.u + v) x)
      then some (RectSpin.fromRect ⟨to2d x, to2d x, by simp, by simp⟩)
      else none

    use z2
    constructor
    · simp only [z2, Spin.inv_def, Equiv.Perm.one_symm, Equiv.toFun_as_coe, Equiv.Perm.coe_one, id_eq,
        CharTwo.neg_eq, RectSpin.fromRect, List.map_filterMap, Option.map_if, rect_spin_one]
      set l : List (Spin m n) := List.finRange (↑m * ↑n) |>.filterMap fun x ↦
        if z1'.prod.u x ≠ (b.u + v) x then
          some ⟨Equiv.refl (Fin (↑m * ↑n)), fun y => if to2d y = to2d x then 1 else 0⟩
        else none with hl
      apply Corollary1.aux1 (l := z1') (k := l) (by rfl)
      convert hl
      simp [to2d_injective.eq_iff, eq_comm]
    · have : (List.finRange (m * n)).length = m.val * n.val := by simp
      rw [← this]
      apply List.length_filterMap_le
  suffices h2 : ∃ l, Spin.IsSolution l ⟨b.α, v⟩ ∧ l.length ≤ 2 * m * n - (m + n) by
    obtain ⟨l1, hl1⟩ := h3
    obtain ⟨l2, hl2⟩ := h2
    have zz : (List.map RectSpin.toSpin (l1 ++ l2)).prod = b⁻¹ := by
      simp [hv2, hl1, hl2.1.1]
    intro l5 hl5
    simp [Spin.IsSolution] at hl5
    have l5size : (l1 ++ l2).length ≤ m * n + (2 * m * n - (m + n)) := by
      rw [List.length_append]
      omega
    have : 2 * m.val * n.val ≥ m.val + n.val := by
      have : 2 * m.val * n.val = m.val * n.val + m.val * n.val := by ring
      have : m.val * n.val ≥ m.val := Nat.le_mul_of_pos_right _ n.2
      have : m.val * n.val ≥ n.val := Nat.le_mul_of_pos_left _ m.2
      omega
    have : m.val * n.val + 2 * m.val * n.val - (m.val + n.val) =
      3 * m.val * n.val - (m.val + n.val) := by ring_nf
    have := hl5.2 (l1 ++ l2) zz
    omega
  sorry
