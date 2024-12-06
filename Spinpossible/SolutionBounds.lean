import Spinpossible.Solution

lemma rect_spin_one (p : Point m n) : Rectangle.toSpin ⟨p, p, by simp, by simp⟩ =
    ⟨Equiv.refl _, fun x => if to2d x = p then 1 else 0⟩ := by
  simp_all [Rectangle.toSpin, Equiv.ext_iff, rotate_around_one_eq_self]
  funext
  exact if_congr Point.isInside_one_iff rfl rfl

set_option linter.haveLet 0

open scoped CharTwo

lemma Spin.perm_distrib (s1 s2 : Spin m n) : (s1 * s2).α = (s2.α * s1.α) := by
  simp [Spin.mul_def]; rfl

@[simp]
lemma Spin.inv_perm (s : Spin m n) : s⁻¹.α = s.α⁻¹ := rfl

private lemma aux1 {s1 : Spin m n} {s2 : RectSpin m n}
    (a : { l // (l.map RectSpin.toSpin).prod.α = (s1⁻¹ * s2).α }) :
    (a.1 ++ [s2] |>.map RectSpin.toSpin).prod.α⁻¹ = s1.α := by
  simp only [List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons,
    List.prod_nil, mul_one, Spin.perm_distrib, a.2, Spin.inv_perm, mul_inv_rev, inv_inv]
  nth_rw 1 [← Spin.inv_perm, RectSpin.inv_self, mul_inv_cancel_right]

private lemma aux2 {s1 : Spin m n} {s2 s3 : RectSpin m n}
    (a : { l // (l.map RectSpin.toSpin).prod.α = (s1⁻¹ * s2 * s3).α }) :
    (a.1 ++ [s3, s2] |>.map RectSpin.toSpin).prod.α⁻¹ = s1.α := by
  simp only [List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons,
    List.prod_nil, mul_one, ← mul_assoc, Spin.perm_distrib, a.2, Spin.inv_perm, mul_inv_rev,
    inv_inv]
  nth_rw 1 [← Spin.inv_perm, ← Spin.inv_perm]
  simp [RectSpin.inv_self]

lemma Rectangle.spin_perm_const {p : Point m n} {r : Rectangle m n}
    (h : p.row.val < r.topLeft.row.val ∨ p.col.val < r.topLeft.col.val) :
    r.toSpin.α (to1d p) = to1d p := by
  simp [Rectangle.toSpin, Point.IsInside]
  omega

lemma Rectangle.corners_rotate_perm {r : Rectangle m n} :
    r.toSpin.α (to1d r.topLeft) = to1d r.bottomRight ∧
    r.toSpin.α (to1d r.bottomRight) = to1d r.topLeft := by
  simp [Rectangle.toSpin, Rectangle.corners_inside, Rectangle.corners_rotate]

-- `toPerm_symm` exists, should I be using `symm` instead of `⁻¹`?
@[simp]
theorem Function.Involutive.toPerm_inv {f : α → α} (h : Function.Involutive f) :
  (h.toPerm f)⁻¹ = h.toPerm f := rfl

lemma Rectangle.spin_eq_iff {s : Rectangle m n} : s.toSpin.α p1 = p2 ↔ p1 = s.toSpin.α p2 := by
  rw [← Equiv.Perm.eq_inv_iff_eq]
  simp [Rectangle.toSpin]

lemma funtimes3 (row col : Nat) (hrow : row < m.val) (hcol : col < n.val) (s : Spin m n)
    (hj2 : ¬ row + 1 < m) (hj3 : ¬ col + 1 < n)
    (this : (to2d (s.α⁻¹ (to1d ⟨⟨row, by omega⟩, ⟨col, by omega⟩⟩))).col.val ≥ col)
    (hs_row2 : ∀ x, (_ : x < row) → s.α⁻¹ (to1d ⟨⟨x, by omega⟩, ⟨col, by omega⟩⟩)
      = to1d ⟨⟨x, by omega⟩, ⟨col, by omega⟩⟩)
    (hs_col2 : ∀ x y, (_ : x < col ∧ y < m.val) → s.α⁻¹ (to1d ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩)
      = to1d ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩) :
    let tile_pos := to2d (s.α⁻¹ (to1d ⟨⟨row, by omega⟩, ⟨col, by omega⟩⟩))
    let row_spin : RectSpin m n := if hr2 : tile_pos.row.val < row then
      RectSpin.fromRect ⟨tile_pos, ⟨⟨row, by omega⟩, tile_pos.col⟩, by simp, Fin.le_of_lt hr2⟩
    else
      RectSpin.fromRect ⟨⟨⟨row, by omega⟩, tile_pos.col⟩, tile_pos, by simp, by simp; fin_omega⟩
    let col_spin : RectSpin m n := RectSpin.fromRect
      ⟨⟨⟨row, by omega⟩, ⟨col, by omega⟩⟩, ⟨⟨row, by omega⟩, tile_pos.col⟩, this, by simp⟩

    ([].map RectSpin.toSpin).prod.α = (s⁻¹ * row_spin * col_spin).α := by
  intro tile_pos row_spin col_spin
  simp [Spin.mul_def]
  rw [Equiv.ext_iff]
  intro i
  simp [Spin.one_def, Spin.mul_def, ← Rectangle.spin_eq_iff]

  have hb : tile_pos.col.val = col := by simp [tile_pos] at this ⊢; omega
  have hc : tile_pos.row.val = row := by
    by_contra! hx
    have := hs_row2 tile_pos.row.val (by omega)
    simp [← hb] at this
    simp_all [tile_pos]
  simp [← hb, ← hc, rect_spin_one, row_spin]

  by_cases hx : (to2d i).col.val < tile_pos.col.val
  · have := hs_col2 (to2d i).col (to2d i).row (by omega) |>.symm
    simpa
  · have asd : tile_pos.col = (to2d i).col := by omega
    by_cases hxy : (to2d i).row.val < tile_pos.row.val
    · have := hs_row2 (to2d i).row (by omega) |>.symm
      simpa [← hb, asd]
    · have : i = to1d tile_pos := by
        simp [← to2d_injective.eq_iff, Point.ext_iff]
        omega
      rw [this]
      conv_lhs => simp [tile_pos]
      simp [Point.ext_iff]
      simp only [Fin.ext_iff]
      omega

lemma funtimes (row col : Nat) (hrow : row < m.val) (hcol : col < n.val) (s : Spin m n)
    (hj2 : ¬ row + 1 < m) (hj3 : col + 1 < n)
    (this : (to2d (s.α⁻¹ (to1d ⟨⟨row, by omega⟩, ⟨col, by omega⟩⟩))).col.val ≥ col)
    (hs_row2 : ∀ x, (_ : x < row) → s.α⁻¹ (to1d ⟨⟨x, by omega⟩, ⟨col, by omega⟩⟩)
      = to1d ⟨⟨x, by omega⟩, ⟨col, by omega⟩⟩)
    (hs_col2 : ∀ x y, (_ : x < col ∧ y < m.val) → s.α⁻¹ (to1d ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩)
      = to1d ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩) :
    let tile_pos := to2d (s.α⁻¹ (to1d ⟨⟨row, _⟩, ⟨col, _⟩⟩))
    let row_spin : RectSpin m n := if hr2 : tile_pos.row.val < row then
      RectSpin.fromRect ⟨tile_pos, ⟨⟨row, by omega⟩, tile_pos.col⟩, by simp, Fin.le_of_lt hr2⟩
    else
      RectSpin.fromRect ⟨⟨⟨row, by omega⟩, tile_pos.col⟩, tile_pos, by simp, by simp; fin_omega⟩
    let col_spin : RectSpin m n := RectSpin.fromRect
      ⟨⟨⟨row, by omega⟩, ⟨col, by omega⟩⟩, ⟨⟨row, by omega⟩, tile_pos.col⟩, this, by simp⟩

    ∀ x y, (_ : x < col + 1 ∧ y < m.val) →
      (s⁻¹ * row_spin.toSpin * col_spin.toSpin).α (to1d ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩)
        = to1d ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩ := by

  intro tile_pos row_spin col_spin x y hxy
  simp only [Spin.mul_def, Spin.inv_perm, Equiv.invFun_as_coe, Equiv.trans_apply]
  rw [Rectangle.spin_eq_iff]
  by_cases hg : x < col
  · have : tile_pos.col.val ≥ col := by simp [tile_pos]; omega
    rw [hs_col2 x y (by omega), Rectangle.spin_perm_const (by simp only; omega)]
    simp [row_spin]
    split_ifs <;> rw [Rectangle.spin_perm_const (by simp only; omega)]
  · have : x = col := by omega
    subst x
    by_cases hg2 : y = row
    · subst y
      simp only [Rectangle.corners_rotate_perm.1, row_spin]
      split_ifs
      · simp [Rectangle.spin_eq_iff, Rectangle.corners_rotate_perm.2, tile_pos]
      · simp [Rectangle.spin_eq_iff, Rectangle.corners_rotate_perm.1, tile_pos]
    · rw [hs_row2 y (by omega), Rectangle.spin_perm_const (by simp only; omega)]
      simp only [row_spin]
      split_ifs
      · have hg4 : col ≠ tile_pos.col.val := by
          by_contra! hg4
          absurd hs_row2 tile_pos.row.val (by omega)
          simp [hg4]
          conv_rhs => rhs; simp [tile_pos]
          simp [Point.ext_iff]
          simp only [Fin.ext_iff]
          omega
        have : col < tile_pos.col.val := by simp [tile_pos] at *; omega
        rw [Rectangle.spin_eq_iff, Rectangle.spin_perm_const (by simp only; omega)]
      · rw [Rectangle.spin_perm_const (by simp only; omega)]

-- set_option debug.skipKernelTC true in -- Speeds up proof during dev, but DO NOT COMMIT
def attempt4 (row col : Nat) (hrow : row < m.val) (hcol : col < n.val) (s : Spin m n)
    (hs_row : ∀ x, (_ : x < row) → s.α (to1d ⟨⟨x, by omega⟩, ⟨col, by omega⟩⟩)
      = to1d ⟨⟨x, by omega⟩, ⟨col, by omega⟩⟩)
    (hs_col: ∀ x y, (_ : x < col ∧ y < m.val) → s.α (to1d ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩)
      = to1d ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩) :
    {l : List (RectSpin m n) // (l.map RectSpin.toSpin).prod.α = s.α } :=
  let tile_pos := to2d (s.α⁻¹ (to1d ⟨⟨row, by omega⟩, ⟨col, by omega⟩⟩))

  have hs_row2 : ∀ x, (_ : x < row) → s.α⁻¹ (to1d ⟨⟨x, _⟩, ⟨col, _⟩⟩) = to1d ⟨⟨x, _⟩, ⟨col, _⟩⟩ := by
    intro x hx
    exact Equiv.Perm.eq_inv_iff_eq.mp (hs_row x hx |>.symm)
  have hs_col2 : ∀ x y, (_ : x < col ∧ y < m.val) →
      s.α⁻¹ (to1d ⟨⟨y, _⟩, ⟨x, _⟩⟩) = to1d ⟨⟨y, _⟩, ⟨x, _⟩⟩ := by
    intro x y hxy
    exact Equiv.Perm.eq_inv_iff_eq.mp (hs_col x y hxy |>.symm)

  have : tile_pos.col.val ≥ col := by
    by_contra hx
    absurd hs_col2 tile_pos.col.val tile_pos.row.val (by omega)
    conv_rhs => rhs; simp [tile_pos]
    simp [Point.ext_iff]
    simp only [Fin.ext_iff]
    omega

  if hj : row = 0 then
    let next_spin := RectSpin.fromRect
      ⟨⟨⟨row, by omega⟩, ⟨col, by omega⟩⟩, tile_pos, by assumption, by fin_omega⟩
    let a := if hj2 : row + 1 < m then
        attempt4 (row + 1) col hj2 hcol (s⁻¹ * next_spin) (by
          intro x hx
          have : x = row := by omega
          simp only [Spin.mul_def, Spin.inv_perm, Equiv.invFun_as_coe, Equiv.trans_apply]
          rw [Rectangle.spin_eq_iff]
          simp [this, Rectangle.corners_rotate_perm.1, tile_pos]
        ) (by
          intro x y hxy
          simp only [Spin.mul_def, Spin.inv_perm, Equiv.invFun_as_coe, Equiv.trans_apply]
          rw [Rectangle.spin_eq_iff, Rectangle.spin_perm_const (Or.inr hxy.1)]
          exact hs_col2 x y hxy
        )
      else if hj3 : col + 1 < n then
        attempt4 0 (col + 1) (by omega) hj3 (s⁻¹ * next_spin.toSpin) (by omega) (by
          intro x y hxy
          simp only [Spin.mul_def, Spin.inv_perm, Equiv.invFun_as_coe, Equiv.trans_apply]
          by_cases hg : x = col
          · by_cases hg2 : y = row
            · simp [hg, hg2]
              rw [Rectangle.spin_eq_iff]
              simp [Rectangle.corners_rotate_perm.1, tile_pos]
            · rw [Rectangle.spin_eq_iff, Rectangle.spin_perm_const (by simp only; omega)]
              exact hg ▸ (hs_row2 y (by omega))
          · rw [hs_col2 x y (by omega), Rectangle.spin_perm_const (by simp only; omega)]
        )
      else ⟨[], by
        simp [Spin.mul_def]
        rw [Equiv.ext_iff]
        intro i
        simp [Rectangle.toSpin, Spin.one_def]
        split_ifs with hk
        · have : (to2d (s.α⁻¹ i)) = ⟨⟨row, by omega⟩, ⟨col, by omega⟩⟩ := by
            simp [Point.IsInside] at hk
            ext <;> (simp only; omega)
          rw [this]
          simp [rotate180, rotateCalc, tile_pos, ← this]
          have : s.α⁻¹ i = i := by
            by_cases hy : col = (to2d i).col
            · by_cases hx : row = (to2d i).row.val
              · simpa [hx, hy, to2d_injective.eq_iff]
              · have := hs_row2 (to2d i).row (by omega)
                simpa [hy]
            · have := hs_col2 (to2d i).col (to2d i).row (by omega)
              simpa
          simp [this]
        · have : (to2d (s.α⁻¹ i)).col.val < col := by
            simp only [Point.IsInside] at hk
            omega
          have := hs_col2 (to2d (s.α⁻¹ i)).col (to2d (s.α⁻¹ i)).row ⟨this, by omega⟩ |>.symm
          simpa
        ⟩
    let ha := a.1 ++ [next_spin]
    have : (ha.reverse.map RectSpin.toSpin).prod.α = s.α := by
      rw [List.map_reverse, ← rectSpin_prod_inv_eq_reverse_prod, Spin.inv_perm, aux1 a]
    ⟨ha.reverse, this⟩
  else
    -- moves the tile into the correct row (by spinning along a column)
    let row_spin : RectSpin m n := if hr2 : tile_pos.row.val < row then
      RectSpin.fromRect ⟨tile_pos, ⟨⟨row, by omega⟩, tile_pos.col⟩, by simp, Fin.le_of_lt hr2⟩
    else
      RectSpin.fromRect ⟨⟨⟨row, by omega⟩, tile_pos.col⟩, tile_pos, by simp, by simp; fin_omega⟩

    -- moves the tile into the correct column (by spinning along a row)
    let col_spin : RectSpin m n := RectSpin.fromRect
      ⟨⟨⟨row, by omega⟩, ⟨col, by omega⟩⟩, ⟨⟨row, by omega⟩, tile_pos.col⟩, this, by simp⟩

    let a := if hj2 : row + 1 < m then
      attempt4 (row + 1) col hj2 hcol (s⁻¹ * row_spin * col_spin) (by
        intro x hx
        simp [Spin.mul_def]
        by_cases hg : x = row
        · simp only [hg, row_spin]
          split_ifs
          · simp [Rectangle.spin_eq_iff, Rectangle.corners_rotate_perm.1,
              Rectangle.corners_rotate_perm.2, tile_pos]
          · simp [Rectangle.spin_eq_iff, Rectangle.corners_rotate_perm.1, tile_pos]
        · rw [Rectangle.spin_eq_iff, Rectangle.spin_perm_const (by simp only; omega)]
          simp only [hs_row2 x (by omega), row_spin]
          split_ifs
          · have hg4 : col ≠ tile_pos.col.val := by
              by_contra! hg4
              absurd hs_row2 tile_pos.row.val (by omega)
              simp [hg4]
              conv_rhs => rhs; simp [tile_pos]
              simp [Point.ext_iff]
              simp only [Fin.ext_iff]
              omega
            rw [Rectangle.spin_perm_const (by simp only; omega)]
          · rw [Rectangle.spin_perm_const (by simp only; omega)]
      ) (by
        intro x y hxy
        simp [Spin.mul_def, hs_col2 _ _ hxy]
        rw [Rectangle.spin_eq_iff, Rectangle.spin_perm_const (by simp only; omega)]
        simp only [row_spin]
        split_ifs <;> (exact Rectangle.spin_perm_const (by simp only; omega))
      )
    else if hj3 : col + 1 < n then
      attempt4 0 (col + 1) (by omega) hj3 (s⁻¹ * row_spin.toSpin * col_spin.toSpin) (by omega)
        (funtimes row col hrow hcol s hj2 hj3 this hs_row2 hs_col2)
    else ⟨[], funtimes3 row col hrow hcol s hj2 hj3 this hs_row2 hs_col2⟩

    let ha := a.1 ++ [col_spin, row_spin]
    have : (ha.reverse.map RectSpin.toSpin).prod.α = s.α := by
      rw [List.map_reverse, ← rectSpin_prod_inv_eq_reverse_prod, Spin.inv_perm, aux2 a]
    ⟨ha.reverse, this⟩
termination_by (n.val - col, m.val - row)
decreasing_by all_goals omega -- slightly quicker than default implementation

-- TODO: figure out how to avoid this popping up
lemma Spin.symm_inv (s : Spin m n) : Equiv.symm s.α = s.α⁻¹ := rfl

theorem theorem1 (b : Spin m n) : ∀ l, Spin.IsSolution l b → l.length ≤ 3 * m * n - (m + n) := by
  have exists_v : ∀ v, b = ⟨b.α, v⟩ * ⟨1, b.u + v⟩ := by
    intro v
    simp [Spin.mul_def, Spin.ext_iff]
    funext
    rw [add_comm, CharTwo.eq_add_iff_add_eq]

  have hv2 v : b⁻¹ = ⟨1, b.u + v⟩⁻¹ * ⟨b.α, v⟩⁻¹ := by
    nth_rw 1 [exists_v v]
    simp [Spin.mul_def, Spin.inv_def, funext_iff, add_comm]
  have h3 v : ∃ l : List (RectSpin m n), (l.map RectSpin.toSpin).prod =
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
  suffices h2 : ∃ l : List (RectSpin m n), (l.map RectSpin.toSpin).prod.α = b.α⁻¹ ∧
      l.length ≤ 2 * m * n - (m + n) by
    obtain ⟨l2, hl2⟩ := h2
    obtain ⟨l1, hl1⟩ := h3 ((l2.map RectSpin.toSpin).prod.u ∘ (b.α.symm))
    have zz : (List.map RectSpin.toSpin (l1 ++ l2)).prod = b⁻¹ := by
      simp [hl1, hl2.1, Spin.inv_def, Spin.mul_def, hl2, add_assoc, ← Spin.symm_inv]
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

  let res : { l : List (RectSpin m n) // (List.map RectSpin.toSpin l).prod.α = b⁻¹.α } :=
    attempt4 0 0 m.2 n.2 b⁻¹ (by omega) (by omega)

  use res, res.2
  sorry
