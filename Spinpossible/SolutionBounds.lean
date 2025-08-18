import Spinpossible.Solution

lemma rect_spin_one (p : Point m n) : Rectangle.toSpin ⟨p, p, Fin.le_refl _, Fin.le_refl _⟩ =
    ⟨Equiv.refl _, fun x => if to2d x = p then 1 else 0⟩ := by
  simp_all [Rectangle.toSpin, Equiv.ext_iff, rotate_around_one_eq_self]
  funext
  exact if_congr Point.isInside_one_iff rfl rfl

set_option linter.haveLet 0

open scoped CharTwo

lemma Spin.perm_distrib (s1 s2 : Spin m n) : (s1 * s2).α = s2.α * s1.α := rfl

@[simp]
lemma Spin.inv_perm (s : Spin m n) : s⁻¹.α = s.α⁻¹ := rfl

private lemma aux1 {s1 : Spin m n} {s2 : RectSpin m n}
    (a : { l // (l.map RectSpin.toSpin).prod.α = (s1⁻¹ * s2).α }) :
    (a.1 ++ [s2] |>.map RectSpin.toSpin).prod.α⁻¹ = s1.α := by
  simp [Spin.perm_distrib, a.2]
  grind [RectSpin.inv_self, Spin.inv_perm, mul_inv_cancel_right]

private lemma aux2 {s1 : Spin m n} {s2 s3 : RectSpin m n}
    (a : { l // (l.map RectSpin.toSpin).prod.α = (s1⁻¹ * s2 * s3).α }) :
    (a.1 ++ [s3, s2] |>.map RectSpin.toSpin).prod.α⁻¹ = s1.α := by
  simp [← mul_assoc, Spin.perm_distrib, a.2]
  grind [RectSpin.inv_self, Spin.inv_perm, mul_inv_cancel_right]

lemma Rectangle.spin_perm_const {p : Point m n} {r : Rectangle m n}
    (h : p.row.val < r.topLeft.row.val ∨ p.col.val < r.topLeft.col.val) :
    r.toSpin.α (to1d p) = to1d p := by
  grind [Rectangle.toSpin, Point.IsInside]

lemma Rectangle.corners_rotate_perm {r : Rectangle m n} :
    r.toSpin.α (to1d r.topLeft) = to1d r.bottomRight ∧
    r.toSpin.α (to1d r.bottomRight) = to1d r.topLeft := by
  simp [Rectangle.toSpin, Rectangle.corners_inside, Rectangle.corners_rotate]

-- `toPerm_symm` exists, should I be using `symm` instead of `⁻¹`?
@[simp]
theorem Function.Involutive.toPerm_inv {f : α → α} (h : Function.Involutive f) :
  (h.toPerm f)⁻¹ = h.toPerm f := rfl

lemma Rectangle.spin_eq_iff {s : Rectangle m n} :
    s.toSpin.α p1 = p2 ↔ p1 = s.toSpin.α p2 := by grind [Rectangle.toSpin]

lemma funtimes3 (row col : Nat) (hrow : row < m.val) (hcol : col < n.val) (s : Spin m n)
    (hj2 : ¬ row + 1 < m) (hj3 : ¬ col + 1 < n)
    (this : (to2d (s.α⁻¹ (to1d ⟨⟨row, hrow⟩, ⟨col, hcol⟩⟩))).col.val ≥ col)
    (hs_row2 : ∀ x, (_ : x < row) → s.α⁻¹ (to1d ⟨⟨x, by omega⟩, ⟨col, hcol⟩⟩)
      = to1d ⟨⟨x, by omega⟩, ⟨col, hcol⟩⟩)
    (hs_col2 : ∀ x y, (_ : x < col ∧ y < m.val) → s.α⁻¹ (to1d ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩)
      = to1d ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩) :
    let tile_pos := to2d (s.α⁻¹ (to1d ⟨⟨row, hrow⟩, ⟨col, hcol⟩⟩))
    let row_spin : RectSpin m n := if hr2 : tile_pos.row.val < row then
      RectSpin.fromRect ⟨tile_pos, ⟨⟨row, hrow⟩, tile_pos.col⟩, Fin.le_refl _, Fin.le_of_lt hr2⟩
    else
      RectSpin.fromRect ⟨⟨⟨row, hrow⟩, tile_pos.col⟩, tile_pos, Fin.le_refl _, by omega⟩
    let col_spin : RectSpin m n := RectSpin.fromRect
      ⟨⟨⟨row, hrow⟩, ⟨col, hcol⟩⟩, ⟨⟨row, hrow⟩, tile_pos.col⟩, this, by simp⟩

    ([].map RectSpin.toSpin).prod.α = (s⁻¹ * row_spin * col_spin).α := by
  intro tile_pos row_spin col_spin
  ext i : 1

  have hb : col = tile_pos.col.val := by grind
  have hc : row = tile_pos.row.val := by
    by_contra! hx
    have := hs_row2 tile_pos.row.val (by omega)
    grind [EmbeddingLike.apply_eq_iff_eq, Fin.eta]
  simp [hb, hc, rect_spin_one, row_spin, col_spin,  List.map_nil, List.prod_nil,
    Equiv.invFun_as_coe, Spin.mul_def, Spin.one_def, Spin.inv_perm]

  by_cases hx : (to2d i).col.val < tile_pos.col.val
  · simpa using hs_col2 (to2d i).col (to2d i).row (by omega) |>.symm
  · by_cases (to2d i).row.val < tile_pos.row.val <;> grind [Fin.eta]

lemma funtimes (row col : Nat) (hrow : row < m.val) (hcol : col < n.val) (s : Spin m n)
    (hj2 : ¬ row + 1 < m) (hj3 : col + 1 < n)
    (this : (to2d (s.α⁻¹ (to1d ⟨⟨row, hrow⟩, ⟨col, hcol⟩⟩))).col.val ≥ col)
    (hs_row2 : ∀ x, (_ : x < row) → s.α⁻¹ (to1d ⟨⟨x, by omega⟩, ⟨col, hcol⟩⟩)
      = to1d ⟨⟨x, by omega⟩, ⟨col, hcol⟩⟩)
    (hs_col2 : ∀ x y, (_ : x < col ∧ y < m.val) → s.α⁻¹ (to1d ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩)
      = to1d ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩) :
    let tile_pos := to2d (s.α⁻¹ (to1d ⟨⟨row, _⟩, ⟨col, _⟩⟩))
    let row_spin : RectSpin m n := if hr2 : tile_pos.row.val < row then
      RectSpin.fromRect ⟨tile_pos, ⟨⟨row, hrow⟩, tile_pos.col⟩, Fin.le_refl _, Fin.le_of_lt hr2⟩
    else
      RectSpin.fromRect ⟨⟨⟨row, hrow⟩, tile_pos.col⟩, tile_pos, Fin.le_refl _, by omega⟩
    let col_spin : RectSpin m n := RectSpin.fromRect
      ⟨⟨⟨row, hrow⟩, ⟨col, hcol⟩⟩, ⟨⟨row, hrow⟩, tile_pos.col⟩, this, by simp⟩

    ∀ x y, (_ : x < col + 1 ∧ y < m.val) →
      (s⁻¹ * row_spin.toSpin * col_spin.toSpin).α (to1d ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩)
        = to1d ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩ := by
  intro tile_pos row_spin col_spin x y hxy
  simp only [Spin.mul_def, Spin.inv_perm, Equiv.invFun_as_coe, Equiv.trans_apply]
  by_cases hg : x < col
  · grind [Rectangle.spin_perm_const]
  · grind [Rectangle.corners_rotate_perm, Rectangle.spin_eq_iff, Rectangle.spin_perm_const,
      EmbeddingLike.apply_eq_iff_eq, Fin.eta]

-- `grind -ring -linarith` saves ~1s over `grind` alone
-- set_option debug.skipKernelTC true in -- Speeds up proof during dev, but DO NOT COMMIT
def attempt4 (row col : Nat) (hrow : row < m.val) (hcol : col < n.val) (s : Spin m n)
    (hs_row : ∀ x, (_ : x < row) → s.α (to1d ⟨⟨x, by omega⟩, ⟨col, hcol⟩⟩)
      = to1d ⟨⟨x, by omega⟩, ⟨col, hcol⟩⟩)
    (hs_col : ∀ x y, (_ : x < col ∧ y < m.val) → s.α (to1d ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩)
      = to1d ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩) :
    {l : List (RectSpin m n) // (l.map RectSpin.toSpin).prod.α = s.α } :=
  let tile_pos := to2d (s.α⁻¹ (to1d ⟨⟨row, hrow⟩, ⟨col, hcol⟩⟩))

  have hs_row2 (x) (hx : x < row) : s.α⁻¹ (to1d ⟨⟨x, _⟩, ⟨col, _⟩⟩) = to1d ⟨⟨x, _⟩, ⟨col, _⟩⟩ :=
    Equiv.Perm.eq_inv_iff_eq.mp (hs_row x hx |>.symm)
  have hs_col2 (x y) (hxy : x < col ∧ y < m.val) :
      s.α⁻¹ (to1d ⟨⟨y, _⟩, ⟨x, _⟩⟩) = to1d ⟨⟨y, _⟩, ⟨x, _⟩⟩ :=
    Equiv.Perm.eq_inv_iff_eq.mp (hs_col x y hxy |>.symm)

  have : tile_pos.col.val ≥ col := by
    by_contra hx
    absurd hs_col2 tile_pos.col.val tile_pos.row.val (by omega)
    grind -ring -linarith [Fin.eta, EmbeddingLike.apply_eq_iff_eq]

  if hj : row = 0 then
    let next_spin := RectSpin.fromRect
      ⟨⟨⟨row, hrow⟩, ⟨col, hcol⟩⟩, tile_pos, this, by fin_omega⟩
    let a := if hj2 : row + 1 < m then
        attempt4 (row + 1) col hj2 hcol (s⁻¹ * next_spin)
          (by grind -ring -linarith [= Spin.mul_def, Spin.inv_perm,
            Rectangle.corners_rotate_perm, Equiv.invFun_as_coe, Equiv.trans_apply])
          (by grind -ring -linarith [= Spin.mul_def, Spin.inv_perm,
            Rectangle.spin_perm_const, Equiv.invFun_as_coe, Equiv.trans_apply])
      else if hj3 : col + 1 < n then
        attempt4 0 (col + 1) (by omega) hj3 (s⁻¹ * next_spin.toSpin) (by omega) (by
          intro x y hxy
          simp only [Spin.mul_def, Spin.inv_perm, Equiv.invFun_as_coe, Equiv.trans_apply]
          by_cases hg : x = col
          · grind -ring -linarith [Rectangle.corners_rotate_perm]
          · rw [hs_col2 x y (by omega), Rectangle.spin_perm_const (by fin_omega)]
        )
      else ⟨[], by
        simp [Spin.mul_def]
        rw [Equiv.ext_iff]
        intro i
        simp [Rectangle.toSpin, Spin.one_def, next_spin]
        split_ifs with hk
        · have : (to2d (s.α⁻¹ i)) = ⟨⟨row, hrow⟩, ⟨col, hcol⟩⟩ := by
            simp [Point.IsInside] at hk
            ext <;> fin_omega
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
          have := hs_col2 (to2d (s.α⁻¹ i)).col (to2d (s.α⁻¹ i)).row ⟨this, Fin.isLt _⟩ |>.symm
          simpa
        ⟩
    let ha := a.1 ++ [next_spin]
    have : (ha.reverse.map RectSpin.toSpin).prod.α = s.α := by
      rw [List.map_reverse, ← rectSpin_prod_inv_eq_reverse_prod, Spin.inv_perm, aux1 a]
    ⟨ha.reverse, this⟩
  else
    -- moves the tile into the correct row (by spinning along a column)
    let row_spin : RectSpin m n := if hr2 : tile_pos.row.val < row then
      RectSpin.fromRect ⟨tile_pos, ⟨⟨row, hrow⟩, tile_pos.col⟩, Fin.le_refl _, Fin.le_of_lt hr2⟩
    else
      RectSpin.fromRect ⟨⟨⟨row, hrow⟩, tile_pos.col⟩, tile_pos, Fin.le_refl _, by fin_omega⟩

    -- moves the tile into the correct column (by spinning along a row)
    let col_spin : RectSpin m n := RectSpin.fromRect
      ⟨⟨⟨row, hrow⟩, ⟨col, hcol⟩⟩, ⟨⟨row, hrow⟩, tile_pos.col⟩, this, Fin.le_refl _⟩

    let a := if hj2 : row + 1 < m then
      attempt4 (row + 1) col hj2 hcol (s⁻¹ * row_spin * col_spin) (by
        intro x hx
        simp [Spin.mul_def]
        by_cases hg : x = row
        · simp only [hg, row_spin, col_spin, tile_pos]
          split_ifs
          · simp [Rectangle.spin_eq_iff, Rectangle.corners_rotate_perm.1,
              Rectangle.corners_rotate_perm.2]
          · simp [Rectangle.spin_eq_iff, Rectangle.corners_rotate_perm.1]
        · rw [Rectangle.spin_eq_iff, Rectangle.spin_perm_const (by fin_omega)]
          simp only [hs_row2 x (by omega), row_spin]
          split_ifs
          · have hg4 : col ≠ tile_pos.col.val := by
              by_contra! hg4
              absurd hs_row2 tile_pos.row.val (by omega)
              simp [hg4]
              grind -ring -linarith [EmbeddingLike.apply_eq_iff_eq]
            rw [Rectangle.spin_perm_const (by fin_omega)]
          · rw [Rectangle.spin_perm_const (by fin_omega)]
      ) (by grind -ring -linarith [= Spin.mul_def, Rectangle.spin_perm_const, Spin.inv_perm,
          Equiv.invFun_as_coe, Equiv.trans_apply])
    else if hj3 : col + 1 < n then
      attempt4 0 (col + 1) m.2 hj3 (s⁻¹ * row_spin.toSpin * col_spin.toSpin) (by omega)
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
    intro
    rw [add_comm, CharTwo.eq_add_iff_add_eq]

  have hv2 v : b⁻¹ = ⟨1, b.u + v⟩⁻¹ * ⟨b.α, v⟩⁻¹ := by
    nth_rw 1 [exists_v v, mul_inv_rev]
  have h3 v : ∃ l : List (RectSpin m n), (l.map RectSpin.toSpin).prod =
      ⟨1, b.u + v⟩⁻¹ ∧ l.length ≤ m * n := by
    let z1 : List (RectSpin m n) := []
    let z1' : List (Spin m n) := z1.map RectSpin.toSpin
    let z2 : List (RectSpin m n) := (List.finRange (m * n)).filterMap fun x : Fin (m * n) =>
      if (z1'.prod.u x ≠ (b.u + v) x)
      then RectSpin.fromRect ⟨to2d x, to2d x, Fin.le_refl _, Fin.le_refl _⟩
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
      rw [to2d_injective.eq_iff, eq_comm]
    · exact List.length_finRange (n := m * n) ▸ List.length_filterMap_le ..
  suffices h2 : ∃ l : List (RectSpin m n), (l.map RectSpin.toSpin).prod.α = b.α⁻¹ ∧
      l.length ≤ 2 * m * n - (m + n) by
    obtain ⟨l2, hl2⟩ := h2
    obtain ⟨l1, hl1⟩ := h3 ((l2.map RectSpin.toSpin).prod.u ∘ (b.α.symm))
    have zz : (List.map RectSpin.toSpin (l1 ++ l2)).prod = b⁻¹ := by
      simp [hl1, hl2.1, Spin.inv_def, Spin.mul_def, add_assoc, ← Spin.symm_inv]
    intro l5 hl5
    simp [Spin.IsSolution] at hl5
    grw [hl5.2 (l1 ++ l2) zz, List.length_append, hl2.2, hl1.2]
    have : m.val + n.val ≤ 2 * m.val * n.val := by
      have : 2 * m.val * n.val = m.val * n.val + m.val * n.val := by ring
      have : m.val * n.val ≥ m.val := Nat.le_mul_of_pos_right _ n.2
      have : m.val * n.val ≥ n.val := Nat.le_mul_of_pos_left _ m.2
      omega
    have : m.val * n.val + 2 * m.val * n.val - (m.val + n.val) =
      3 * m.val * n.val - (m.val + n.val) := by ring_nf
    omega

  let res : { l : List (RectSpin m n) // (List.map RectSpin.toSpin l).prod.α = b⁻¹.α } :=
    attempt4 0 0 m.2 n.2 b⁻¹ (by omega) (by omega)

  use res, res.2
  sorry
