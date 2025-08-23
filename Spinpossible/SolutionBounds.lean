import Spinpossible.Solution

-- Thanks, https://demo.projectnumina.ai/
theorem attempt5.extracted_6 {m n : ℕ+} (row col : ℕ) (hcol : col + 2 < ↑n) (hrow : 0 < row) :
    (↑n - (col + 1) - 1) * (2 * (row + 1) - 1) + row + 1 + 1 ≤
      (↑n - col - 1) * (2 * (row + 1) - 1) + (row + 1) - 2 * row := by
  set M := row
  set N := n.val - (col + 1)
  have hN0 : 2 ≤ N := by omega
  have hM0 : 0 < M := by omega
  have : n.val - col = N + 1 := by omega
  rw [this]
  have : N + 1 - 1 = N := by omega
  rw [this]
  have h1 : N ≥ 2 := by omega
  have h2 : M > 0 := by omega
  have eq1 : 2 * (M + 1) - 1 = 2 * M + 1 := by
    omega
  rw [eq1]
  cases h : N with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega -- contradicts hN
    | succ n =>
      simp [Nat.mul_add, Nat.add_mul] at *
      omega

-- Thanks, https://demo.projectnumina.ai/
theorem attempt5.extracted_7 {m n : ℕ+} (row col : ℕ) (hcol : col + 1 < ↑n) (hrow : 0 < row)
    (hrow2 : row + 1 < m.val) :
    (↑n - col - 1) * (2 * ↑m - 1) + ↑m - 2 * (row + 1) + 1 + 1 ≤
      (↑n - col - 1) * (2 * ↑m - 1) + ↑m - 2 * row := by
  set M := row
  set N := n.val - col - 1
  have hN0 : 1 ≤ N := by omega
  have hM0 : 0 < M := by omega
  set t := m.val
  have h3 : N * (2 * t - 1) + t ≥ 2 * (M + 1) := by
    have h4 : N ≥ 1 := by omega
    have h5 : 2 * t - 1 ≥ 1 := by
      omega
    have h6 : N * (2 * t - 1) ≥ 2 * t - 1 := by
      nlinarith [show 2 * t - 1 ≥ 1 by omega]
    have h7 : N * (2 * t - 1) + t ≥ 3 * t - 1 := by
      omega
    have h8 : 3 * t - 1 ≥ 2 * (M + 1) := by
      have h9 : t > M + 1 := by omega
      have h10 : t ≥ M + 2 := by omega
      have h11 : 3 * t ≥ 3 * (M + 2) := by
        nlinarith
      omega
    omega
  omega



lemma rect_spin_one (p : Point m n) : Rectangle.toSpin ⟨p, p, Fin.le_refl _, Fin.le_refl _⟩ =
    ⟨Equiv.refl _, fun x => if x = p then 1 else 0⟩ := by
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

private lemma aux3 {s1 : Spin m n} {s2 s3 : RectSpin m n} (hs3 : s3.toSpin.α = Equiv.refl _)
    (a : { l // (l.map RectSpin.toSpin).prod.α = (s1⁻¹ * s2 * s3).α }) :
    (a.1 ++ [s2] |>.map RectSpin.toSpin).prod.α⁻¹ = s1.α := by
  simp [← mul_assoc, Spin.perm_distrib, a.2, hs3]
  grind [RectSpin.inv_self, Spin.inv_perm, mul_inv_cancel_right]

lemma Rectangle.spin_perm_const {p : Point m n} {r : Rectangle m n}
    (h : p.row.val < r.topLeft.row.val ∨ p.col.val < r.topLeft.col.val) :
    r.toSpin.α p = p := by
  grind [Rectangle.toSpin, Point.IsInside]

lemma Rectangle.corners_rotate_perm {r : Rectangle m n} :
    r.toSpin.α r.topLeft = r.bottomRight ∧
    r.toSpin.α r.bottomRight = r.topLeft := by
  simp [Rectangle.toSpin, Rectangle.corners_inside, Rectangle.corners_rotate]

-- `toPerm_symm` exists, should I be using `symm` instead of `⁻¹`?
@[simp]
theorem Function.Involutive.toPerm_inv {f : α → α} (h : Function.Involutive f) :
  (h.toPerm f)⁻¹ = h.toPerm f := rfl

lemma Rectangle.spin_eq_iff {s : Rectangle m n} :
    s.toSpin.α p1 = p2 ↔ p1 = s.toSpin.α p2 := by grind [Rectangle.toSpin]

lemma funtimes3 (row col : Nat) (hrow : row < m.val) (hcol : col < n.val) (s : Spin m n)
    (hj2 : ¬ row + 1 < m) (hj3 : ¬ col + 1 < n)
    (this : (s.α⁻¹ ⟨⟨row, hrow⟩, ⟨col, hcol⟩⟩).col.val ≥ col)
    (hs_row2 : ∀ x, (_ : x < row) → s.α⁻¹ ⟨⟨x, by omega⟩, ⟨col, hcol⟩⟩
      = ⟨⟨x, by omega⟩, ⟨col, hcol⟩⟩)
    (hs_col2 : ∀ x y, (_ : x < col ∧ y < m.val) → s.α⁻¹ ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩
      = ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩) :
    let tile_pos := s.α⁻¹ ⟨⟨row, hrow⟩, ⟨col, hcol⟩⟩
    let row_spin : RectSpin m n := if hr2 : tile_pos.row.val < row then
      RectSpin.fromRect ⟨tile_pos, ⟨⟨row, hrow⟩, tile_pos.col⟩, Fin.le_refl _, Fin.le_of_lt hr2⟩
    else
      RectSpin.fromRect ⟨⟨⟨row, hrow⟩, tile_pos.col⟩, tile_pos, Fin.le_refl _, Fin.not_lt.mp hr2⟩
    let col_spin : RectSpin m n := RectSpin.fromRect
      ⟨⟨⟨row, hrow⟩, ⟨col, hcol⟩⟩, ⟨⟨row, hrow⟩, tile_pos.col⟩, this, Fin.ge_of_eq rfl⟩

    ([].map RectSpin.toSpin).prod.α = (s⁻¹ * row_spin * col_spin).α := by
  intro tile_pos row_spin col_spin
  ext i : 1

  have hb : col = tile_pos.col.val := by grind
  have hc : row = tile_pos.row.val := by
    by_contra! hx
    have := hs_row2 tile_pos.row.val (by omega)
    grind [EmbeddingLike.apply_eq_iff_eq, Fin.eta]
  simp [hb, hc, rect_spin_one, row_spin, col_spin,  List.map_nil, List.prod_nil,
    Spin.mul_def, Spin.one_def, Spin.inv_perm]

  by_cases hx : i.col.val <tile_pos.col.val
  · simpa using hs_col2 i.col i.row (by omega) |>.symm
  · by_cases i.row.val < tile_pos.row.val <;> grind [Fin.eta]

lemma funtimes (row col : Nat) (hrow : row < m.val) (hcol : col < n.val) (s : Spin m n)
    (hj2 : ¬ row + 1 < m) (hj3 : col + 1 < n)
    (this : (s.α⁻¹ ⟨⟨row, hrow⟩, ⟨col, hcol⟩⟩).col.val ≥ col)
    (hs_row2 : ∀ x, (_ : x < row) → s.α⁻¹ ⟨⟨x, by omega⟩, ⟨col, hcol⟩⟩
      = ⟨⟨x, by omega⟩, ⟨col, hcol⟩⟩)
    (hs_col2 : ∀ x y, (_ : x < col ∧ y < m.val) → s.α⁻¹ ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩
      = ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩) :
    let tile_pos := s.α⁻¹ ⟨⟨row, _⟩, ⟨col, _⟩⟩
    let row_spin : RectSpin m n := if hr2 : tile_pos.row.val < row then
      RectSpin.fromRect ⟨tile_pos, ⟨⟨row, hrow⟩, tile_pos.col⟩, Fin.le_refl _, Fin.le_of_lt hr2⟩
    else
      RectSpin.fromRect ⟨⟨⟨row, hrow⟩, tile_pos.col⟩, tile_pos, Fin.le_refl _, by omega⟩
    let col_spin : RectSpin m n := RectSpin.fromRect
      ⟨⟨⟨row, hrow⟩, ⟨col, hcol⟩⟩, ⟨⟨row, hrow⟩, tile_pos.col⟩, this, by simp⟩

    ∀ x y, (_ : x < col + 1 ∧ y < m.val) →
      (s⁻¹ * row_spin.toSpin * col_spin.toSpin).α ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩
        = ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩ := by
  intro tile_pos row_spin col_spin x y hxy
  simp only [Spin.mul_def, Spin.inv_perm, Equiv.trans_apply]
  by_cases hg : x < col
  · grind [Rectangle.spin_perm_const]
  · grind [Rectangle.corners_rotate_perm, Rectangle.spin_eq_iff, Rectangle.spin_perm_const,
      EmbeddingLike.apply_eq_iff_eq, Fin.eta]

-- `grind -ring -linarith` saves ~1s over `grind` alone
-- set_option debug.skipKernelTC true in -- Speeds up proof during dev, but DO NOT COMMIT
def attempt4 (row col : Nat) (hrow : row < m.val) (hcol : col < n.val) (s : Spin m n)
    (hs_row : ∀ x, (_ : x < row) → s.α ⟨⟨x, by omega⟩, ⟨col, hcol⟩⟩
      = ⟨⟨x, by omega⟩, ⟨col, hcol⟩⟩)
    (hs_col : ∀ x y, (_ : x < col ∧ y < m.val) → s.α ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩
      = ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩) :
    {l : List (RectSpin m n) // (l.map RectSpin.toSpin).prod.α = s.α } :=
  let tile_pos := s.α⁻¹ ⟨⟨row, hrow⟩, ⟨col, hcol⟩⟩

  have hs_row2 (x) (hx : x < row) : s.α⁻¹ ⟨⟨x, _⟩, ⟨col, _⟩⟩ = ⟨⟨x, _⟩, ⟨col, _⟩⟩ :=
    Equiv.Perm.eq_inv_iff_eq.mp (hs_row x hx |>.symm)
  have hs_col2 (x y) (hxy : x < col ∧ y < m.val) :
      s.α⁻¹ ⟨⟨y, _⟩, ⟨x, _⟩⟩ = ⟨⟨y, _⟩, ⟨x, _⟩⟩ :=
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
            Rectangle.corners_rotate_perm, Equiv.trans_apply])
          (by grind -ring -linarith [= Spin.mul_def, Spin.inv_perm,
            Rectangle.spin_perm_const, Equiv.trans_apply])
      else if hj3 : col + 1 < n then
        attempt4 0 (col + 1) (by omega) hj3 (s⁻¹ * next_spin.toSpin) (by omega) (by
          intro x y hxy
          simp only [Spin.mul_def, Spin.inv_perm, Equiv.trans_apply]
          by_cases hg : x = col
          · grind -ring -linarith [Rectangle.corners_rotate_perm]
          · rw [hs_col2 x y (by omega), Rectangle.spin_perm_const (by fin_omega)]
        )
      else ⟨[], by
        ext i : 1
        simp only [List.map_nil, List.prod_nil, Spin.one_def, Equiv.refl_apply, Rectangle.toSpin,
          Spin.mul_def, Spin.inv_perm, Function.Involutive.toPerm_symm,
          Function.Involutive.coe_toPerm, Equiv.trans_apply, next_spin]
        split_ifs with hk
        · have : (s.α⁻¹ i) = ⟨⟨row, hrow⟩, ⟨col, hcol⟩⟩ := by
            simp [Point.IsInside] at hk
            ext <;> fin_omega
          rw [this]
          simp [rotate180, rotateCalc, tile_pos, ← this]
          suffices s.α⁻¹ i = i by simp [this]
          by_cases hy : col = i.col
          · by_cases hx : row = i.row.val
            · simpa [hx, hy]
            · simpa [hy] using hs_row2 i.row (by omega)
          · simpa using hs_col2 i.col i.row (by omega)
        · have : (s.α⁻¹ i).col.val < col := by
            simp only [Point.IsInside] at hk
            omega
          have := hs_col2 (s.α⁻¹ i).col (s.α⁻¹ i).row ⟨this, Fin.isLt _⟩ |>.symm
          simpa
        ⟩
    let (eq := haha) ha := if m.val = 1 ∧ ¬ col + 1 < n then a.1 else a.1 ++ [next_spin]
    have : (ha.reverse.map RectSpin.toSpin).prod.α = s.α := by
      rw [haha, List.map_reverse, ← rectSpin_prod_inv_eq_reverse_prod, Spin.inv_perm]
      split_ifs with hahaha
      · have : n.val = col + 1 := by omega
        rw [a.2]
        have : tile_pos = ⟨⟨row, hrow⟩, ⟨col, hcol⟩⟩ := by
          ext
          · simp; omega
          · simp; omega
        simp [next_spin, this, rect_spin_one, Spin.mul_def, Spin.inv_perm]
      · exact aux1 a
    ⟨ha.reverse, this⟩
  else
    -- moves the tile into the correct row (by spinning along a column)
    let row_spin : RectSpin m n := if hr2 : tile_pos.row.val < row then
      RectSpin.fromRect ⟨tile_pos, ⟨⟨row, hrow⟩, tile_pos.col⟩, Fin.le_refl _, Fin.le_of_lt hr2⟩
    else
      RectSpin.fromRect ⟨⟨⟨row, hrow⟩, tile_pos.col⟩, tile_pos, Fin.le_refl _, Fin.not_lt.mp hr2⟩

    -- moves the tile into the correct column (by spinning along a row)
    let col_spin : RectSpin m n := RectSpin.fromRect
      ⟨⟨⟨row, hrow⟩, ⟨col, hcol⟩⟩, ⟨⟨row, hrow⟩, tile_pos.col⟩, this, Fin.le_refl _⟩

    let a := if hj2 : row + 1 < m then
      attempt4 (row + 1) col hj2 hcol (s⁻¹ * row_spin * col_spin) (by
        intro x hx
        simp only [Spin.mul_def, Spin.inv_perm, Equiv.trans_apply]
        by_cases hg : x = row
        · simp only [hg, row_spin, col_spin, tile_pos]
          split_ifs
          · simp [Rectangle.corners_rotate_perm.1, Rectangle.corners_rotate_perm.2]
          · simp [Rectangle.spin_eq_iff, Rectangle.corners_rotate_perm.1]
        · rw [Rectangle.spin_eq_iff, Rectangle.spin_perm_const (by fin_omega)]
          simp only [hs_row2 x (by omega), row_spin]
          split_ifs
          · have hg4 : col ≠ tile_pos.col.val := by
              by_contra! hg4
              absurd hs_row2 tile_pos.row.val (by omega)
              grind -ring -linarith [EmbeddingLike.apply_eq_iff_eq, Fin.eta]
            rw [Rectangle.spin_perm_const (by fin_omega)]
          · rw [Rectangle.spin_perm_const (by fin_omega)]
      ) (by grind -ring -linarith [= Spin.mul_def, Rectangle.spin_perm_const, Spin.inv_perm,
          Equiv.trans_apply])
    else if hj3 : col + 1 < n then
      attempt4 0 (col + 1) m.2 hj3 (s⁻¹ * row_spin.toSpin * col_spin.toSpin) (by omega)
        (funtimes row col hrow hcol s hj2 hj3 this hs_row2 hs_col2)
    else ⟨[], funtimes3 row col hrow hcol s hj2 hj3 this hs_row2 hs_col2⟩

    have (h : ¬ col + 1 < n) : col_spin.α = Equiv.refl _ := by
      ext i : 1
      simp [col_spin, Rectangle.toSpin, Point.IsInside, rotate180, rotateCalc]
      intros
      ext <;> (simp; omega)

    let (eq := haha) ha := if hlast : col + 1 < n then
      a.1 ++ [col_spin, row_spin]
    else if hrow1 : row + 1 < m then
      a.1 ++ [row_spin]
    else
      a.1
    have : (ha.reverse.map RectSpin.toSpin).prod.α = s.α := by
      rw [haha, List.map_reverse, ← rectSpin_prod_inv_eq_reverse_prod, Spin.inv_perm]
      split_ifs with hahaha
      · exact aux2 a
      · exact aux3 (this hahaha) a
      · simp [Spin.perm_distrib, a.2, this hahaha]
        have xx2 : tile_pos.col.val = col := by omega
        have xx1: tile_pos.row.val = row := by
          by_contra! hx
          have := hs_row2 tile_pos.row.val (by omega)
          have cc : ⟨⟨tile_pos.row.val, by omega⟩, ⟨col, hcol⟩⟩ = tile_pos := by ext <;> simp [xx2]
          rw [cc] at this
          conv_rhs at this => unfold tile_pos
          simp at this
          have := congr(Point.row $this)
          simp [Fin.ext_iff] at this
          omega
        ext i : 1
        simp [row_spin, xx1, xx2, Rectangle.toSpin, Point.IsInside, rotate180, rotateCalc]
        intros
        ext <;> (simp; omega)
    ⟨ha.reverse, this⟩
termination_by (n.val - col, m.val - row)
decreasing_by all_goals omega -- slightly quicker than default implementation

def listSize (m n : PNat) (row col : Nat) :=
  if col + 1 = n.val then
    (if m.val = 1 then 0 else m.val - 1 - row)
  else if row  = 0 then
    (n.val - col - 1) * (2 * m.val - 1) + (m.val - 1)
  else
    (n.val - col - 1) * (2 * m.val - 1) + m.val - 2 * row

lemma attempt4_proof {m n} (row col : Nat) (hrow : row < m.val) (hcol : col < n.val) (s : Spin m n)
    (hextra : 1 < m.val ∨ 1 < n.val) -- to simplify things, handle the 1x1 case separately
    (hs_row : ∀ x, (_ : x < row) → s.α ⟨⟨x, by omega⟩, ⟨col, hcol⟩⟩
      = ⟨⟨x, by omega⟩, ⟨col, hcol⟩⟩)
    (hs_col : ∀ x y, (_ : x < col ∧ y < m.val) → s.α ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩
      = ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩) :
   (attempt4 row col hrow hcol s hs_row hs_col).1.length ≤ listSize m n row col := by
  unfold attempt4
  dsimp only
  have hs_row2 (x) (hx : x < row) : s.α⁻¹ ⟨⟨x, _⟩, ⟨col, _⟩⟩ = ⟨⟨x, _⟩, ⟨col, _⟩⟩ :=
  Equiv.Perm.eq_inv_iff_eq.mp (hs_row x hx |>.symm)
  have hs_col2 (x y) (hxy : x < col ∧ y < m.val) :
      s.α⁻¹ ⟨⟨y, _⟩, ⟨x, _⟩⟩ = ⟨⟨y, _⟩, ⟨x, _⟩⟩ :=
    Equiv.Perm.eq_inv_iff_eq.mp (hs_col x y hxy |>.symm)

  set tile_pos := s.α⁻¹ ⟨⟨row, hrow⟩, ⟨col, hcol⟩⟩
  have : tile_pos.col.val ≥ col := by
    by_contra hx
    absurd hs_col2 tile_pos.col.val tile_pos.row.val (by omega)
    grind -ring -linarith [Fin.eta, EmbeddingLike.apply_eq_iff_eq]

  split
  next ha =>
    simp [- PNat.coe_eq_one_iff]
    split
    next hb =>
      have : ¬ col + 1 < n.val := by omega
      simp [hb, ha, this]
    next hb =>
      simp [listSize];
      split
      next hc =>
        let next_spin := RectSpin.fromRect
          ⟨⟨⟨row, hrow⟩, ⟨col, hcol⟩⟩, tile_pos, this, by fin_omega⟩
        have := attempt4_proof (row + 1) col (by omega) hcol (s⁻¹ * next_spin.toSpin) hextra
            (by grind -ring -linarith [= Spin.mul_def, Spin.inv_perm,
              Rectangle.corners_rotate_perm, Equiv.trans_apply])
            (by grind -ring -linarith [= Spin.mul_def, Spin.inv_perm,
              Rectangle.spin_perm_const, Equiv.trans_apply])
        grw [this]
        simp [listSize]
        split_ifs
        · absurd hb; simp [← PNat.coe_eq_one_iff] at *; omega
        · omega
        · omega
      next hc =>
        let next_spin := RectSpin.fromRect
          ⟨⟨⟨row, hrow⟩, ⟨col, hcol⟩⟩, tile_pos, this, by fin_omega⟩
        by_cases hn1 : col + 1 < ↑n
        · have : col + 1 ≠ n.val := by omega
          simp [hn1, this]
          have := attempt4_proof 0 (col + 1) (by omega) (by omega) (s⁻¹ * next_spin.toSpin) hextra (by omega) (by
            intro x y hxy
            simp only [Spin.mul_def, Spin.inv_perm, Equiv.trans_apply]
            by_cases hg : x = col
            · grind -ring -linarith [Rectangle.corners_rotate_perm]
            · rw [hs_col2 x y (by omega), Rectangle.spin_perm_const (by fin_omega)]
          )
          grw [this]
          have : m.val = row + 1 := by omega
          simp [this, listSize, ha]
          split_ifs <;> omega
        · omega
  next ha =>
    simp only
    split
    next hb =>
      split
      next hc =>
        simp
        set row_spin : RectSpin m n := if hr2 : tile_pos.row.val < row then
          RectSpin.fromRect ⟨tile_pos, ⟨⟨row, hrow⟩, tile_pos.col⟩, Fin.le_refl _, Fin.le_of_lt hr2⟩
        else
          RectSpin.fromRect ⟨⟨⟨row, hrow⟩, tile_pos.col⟩, tile_pos, Fin.le_refl _, Fin.not_lt.mp hr2⟩ with hs2
        have hs_col2 (x y) (hxy : x < col ∧ y < m.val) :
            s.α⁻¹ ⟨⟨y, _⟩, ⟨x, _⟩⟩ = ⟨⟨y, _⟩, ⟨x, _⟩⟩ :=
          Equiv.Perm.eq_inv_iff_eq.mp (hs_col x y hxy |>.symm)
        set col_spin : RectSpin m n := RectSpin.fromRect
          ⟨⟨⟨row, hrow⟩, ⟨col, hcol⟩⟩, ⟨⟨row, hrow⟩, tile_pos.col⟩, by omega, Fin.le_refl _⟩
        have := attempt4_proof (row + 1) col (by omega) hcol (s⁻¹ * row_spin.toSpin * col_spin.toSpin) hextra (by
          intro x hx
          simp only [Spin.mul_def, Spin.inv_perm, Equiv.trans_apply]
          by_cases hg : x = row
          -- · grind -ring -linarith [Rectangle.corners_rotate_perm] -- too slow
          · simp only [hg, row_spin, col_spin, tile_pos]
            split_ifs
            · simp [Rectangle.corners_rotate_perm.1, Rectangle.corners_rotate_perm.2]
            · simp [Rectangle.spin_eq_iff, Rectangle.corners_rotate_perm.1]
          · rw [Rectangle.spin_eq_iff, Rectangle.spin_perm_const (by fin_omega)]
            simp only [hs_row2 x (by omega), row_spin]
            split_ifs
            · have hg4 : col ≠ tile_pos.col.val := by
                by_contra! hg4
                absurd hs_row2 tile_pos.row.val (by omega)
                grind -ring -linarith [EmbeddingLike.apply_eq_iff_eq, Fin.eta]
              rw [Rectangle.spin_perm_const (by fin_omega)]
            · rw [Rectangle.spin_perm_const (by fin_omega)]
        ) (by grind -ring -linarith [= Spin.mul_def, Rectangle.spin_perm_const, Spin.inv_perm,
            Equiv.trans_apply])
        grw [this]
        simp [listSize, ha]
        split_ifs
        · omega
        · omega
        · apply attempt5.extracted_7 row col <;> omega
      next hc =>
        simp
        set row_spin : RectSpin m n := if hr2 : tile_pos.row.val < row then
          RectSpin.fromRect ⟨tile_pos, ⟨⟨row, hrow⟩, tile_pos.col⟩, Fin.le_refl _, Fin.le_of_lt hr2⟩
        else
          RectSpin.fromRect ⟨⟨⟨row, hrow⟩, tile_pos.col⟩, tile_pos, Fin.le_refl _, Fin.not_lt.mp hr2⟩ with hs2
        have hs_col2 (x y) (hxy : x < col ∧ y < m.val) :
            s.α⁻¹ ⟨⟨y, _⟩, ⟨x, _⟩⟩ = ⟨⟨y, _⟩, ⟨x, _⟩⟩ :=
          Equiv.Perm.eq_inv_iff_eq.mp (hs_col x y hxy |>.symm)
        set col_spin : RectSpin m n := RectSpin.fromRect
          ⟨⟨⟨row, hrow⟩, ⟨col, hcol⟩⟩, ⟨⟨row, hrow⟩, tile_pos.col⟩, by omega, Fin.le_refl _⟩
        have := attempt4_proof 0 (col + 1) m.2 (by omega) (s⁻¹ * row_spin.toSpin * col_spin.toSpin) hextra (by omega)
          (funtimes row col hrow hcol s (by omega) (by omega) this hs_row2 hs_col2)
        grw [this]
        have : m.val = row + 1 := by omega
        simp [this, listSize, ha]
        split_ifs with hn1 hn2
        · omega
        · simp [← hn1]
          grind
        · omega
        · apply attempt5.extracted_6 row col <;> omega
    next hb =>
      split
      next hc =>
        have vv : n.val = col + 1 := by omega
        have : tile_pos.col.val = col := by omega
        simp

        set row_spin : RectSpin m n := if hr2 : tile_pos.row.val < row then
          RectSpin.fromRect ⟨tile_pos, ⟨⟨row, hrow⟩, tile_pos.col⟩, Fin.le_refl _, Fin.le_of_lt hr2⟩
        else
          RectSpin.fromRect ⟨⟨⟨row, hrow⟩, tile_pos.col⟩, tile_pos, Fin.le_refl _, Fin.not_lt.mp hr2⟩ with hs2
        have hs_col2 (x y) (hxy : x < col ∧ y < m.val) :
            s.α⁻¹ ⟨⟨y, _⟩, ⟨x, _⟩⟩ = ⟨⟨y, _⟩, ⟨x, _⟩⟩ :=
          Equiv.Perm.eq_inv_iff_eq.mp (hs_col x y hxy |>.symm)
        set col_spin : RectSpin m n := RectSpin.fromRect
          ⟨⟨⟨row, hrow⟩, ⟨col, hcol⟩⟩, ⟨⟨row, hrow⟩, tile_pos.col⟩, by omega, Fin.le_refl _⟩
        -- refold_let row_spin
        have := attempt4_proof (row + 1) col (by omega) hcol (s⁻¹ * row_spin.toSpin * col_spin.toSpin) hextra (by
          intro x hx
          simp only [Spin.mul_def, Spin.inv_perm, Equiv.trans_apply]
          by_cases hg : x = row
          -- · grind -ring -linarith [Rectangle.corners_rotate_perm] -- too slow
          · simp only [hg, row_spin, col_spin, tile_pos]
            split_ifs
            · simp [Rectangle.corners_rotate_perm.1, Rectangle.corners_rotate_perm.2]
            · simp [Rectangle.spin_eq_iff, Rectangle.corners_rotate_perm.1]
          · rw [Rectangle.spin_eq_iff, Rectangle.spin_perm_const (by fin_omega)]
            simp only [hs_row2 x (by omega), row_spin]
            split_ifs
            · have hg4 : col ≠ tile_pos.col.val := by
                by_contra! hg4
                absurd hs_row2 tile_pos.row.val (by omega)
                grind -ring -linarith [EmbeddingLike.apply_eq_iff_eq, Fin.eta]
              rw [Rectangle.spin_perm_const (by fin_omega)]
            · rw [Rectangle.spin_perm_const (by fin_omega)]
        ) (by grind -ring -linarith [= Spin.mul_def, Rectangle.spin_perm_const, Spin.inv_perm,
            Equiv.trans_apply])
        grw [this]
        have : m.val ≠ 1 := by omega
        simp [vv, listSize, this]
        omega
      next hc => simp

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
    let z2 : List (RectSpin m n) := (.univ : Finset (Point m n)).toList.filterMap fun x =>
      if z1'.prod.u x ≠ (b.u + v) x
      then RectSpin.fromRect ⟨x, x, Fin.le_refl _, Fin.le_refl _⟩
      else none

    use z2
    constructor
    · simp only [z2, Spin.inv_def, Equiv.Perm.one_symm, Equiv.Perm.coe_one, id_eq,
        CharTwo.neg_eq, RectSpin.fromRect, List.map_filterMap, Option.map_if, rect_spin_one]
      set l : List (Spin m n) := (.univ : Finset (Point m n)).toList.filterMap fun x =>
        if z1'.prod.u x ≠ (b.u + v) x
        then some ⟨Equiv.refl _, fun y => if y = x then 1 else 0⟩
        else none with hl
      exact Corollary1.aux1 (l := z1') (k := l) (by rfl) hl
    · have : (.univ : Finset (Point m n)).card = (.univ : Finset (Fin m × Fin n)).card := by
        apply Finset.card_bij (fun r _ => (r.row, r.col)) (by simp) (by simp [Point.ext_iff])
        exact fun b hb => ⟨⟨b.1, b.2⟩, by simp⟩
      grind [Finset.length_toList, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
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

  by_cases hextra : ¬ (1 < m.val ∨ 1 < n.val)
  · use [], ?_, by simp
    ext i : 1
    simp [Spin.one_def, Point.ext_iff]
    omega

  use res, res.2
  grw [attempt4_proof 0 0]
  · simp [listSize]
    split_ifs with ho
    · simp [← ho]
    · cases hg : m.val with
      | zero => omega
      | succ m =>
        cases hg2 : n.val with
        | zero => absurd hg2; simp
        | succ n =>
          simp [Nat.mul_add, Nat.add_mul, mul_comm]
          omega
    · cases hg : m.val with
      | zero => omega
      | succ m =>
        cases hg2 : n.val with
        | zero => absurd hg2; simp
        | succ n =>
          simp [Nat.mul_add, Nat.add_mul, mul_comm]
          omega
  · omega
