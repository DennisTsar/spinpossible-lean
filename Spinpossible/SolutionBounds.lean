import Spinpossible.Solution

instance : Inhabited (Rectangle m n) := ⟨⟨0, 0⟩, ⟨0, 0⟩, by simp, by simp⟩

/-- Create a `RectSpin` from the given points if they form a valid rectangle,
  or panic / return a default value if they do not -/
abbrev RectSpin.fromPoints (topLeft bottomRight : Point m n) : RectSpin m n :=
  if h : topLeft.row ≤ bottomRight.row ∧ topLeft.col ≤ bottomRight.col then
    fromRect ⟨topLeft, bottomRight, h.1, h.2⟩
  else
    fromRect (panic! "Invalid rectangle")

def buildBasicPermSolution (row col : Nat) (hrow : row < m.val) (hcol : col < n.val)
    (s : Spin m n) : List (RectSpin m n) :=
  let cur_pos : Point m n := ⟨⟨row, hrow⟩, ⟨col, hcol⟩⟩
  let tile_pos := s.α.symm cur_pos

  if row = 0 then
    let next_spin := RectSpin.fromPoints
      cur_pos tile_pos
    let rest := if hrow : row + 1 < m then
        buildBasicPermSolution (row + 1) col hrow hcol (s⁻¹ * next_spin)
      else if hcol : col + 1 < n then
        buildBasicPermSolution 0 (col + 1) m.2 hcol (s⁻¹ * next_spin)
      else []
    if m.val = 1 ∧ ¬ col + 1 < n then rest.reverse
    else next_spin :: rest.reverse
  else
    -- moves the tile into the correct row (by spinning along a column)
    let row_spin : RectSpin m n := if tile_pos.row.val < row then
      RectSpin.fromPoints tile_pos ⟨⟨row, hrow⟩, tile_pos.col⟩
    else
      RectSpin.fromPoints ⟨⟨row, hrow⟩, tile_pos.col⟩ tile_pos

    -- moves the tile into the correct column (by spinning along a row)
    let col_spin : RectSpin m n := RectSpin.fromPoints cur_pos ⟨⟨row, hrow⟩, tile_pos.col⟩

    let rest := if hrow : row + 1 < m then
        buildBasicPermSolution (row + 1) col hrow hcol (s⁻¹ * row_spin * col_spin)
      else if hcol : col + 1 < n then
        buildBasicPermSolution 0 (col + 1) m.2 hcol (s⁻¹ * row_spin * col_spin)
      else []

    if col + 1 < n then row_spin :: col_spin :: rest.reverse
    else if row + 1 < m then row_spin :: rest.reverse
    else rest.reverse
termination_by (n.val - col, m.val - row)
decreasing_by all_goals omega -- slightly quicker than default implementation

@[simp]
lemma Spin.inv_perm (s : Spin m n) : s⁻¹.α = s.α⁻¹ := rfl

lemma Rectangle.spin_perm_const {p : Point m n} {r : Rectangle m n}
    (h : p.row.val < r.topLeft.row.val ∨ p.col.val < r.topLeft.col.val) :
    r.toSpin.α p = p := by
  grind [Rectangle.toSpin, Point.IsInside]

lemma Rectangle.corners_rotate_perm {r : Rectangle m n} :
    r.toSpin.α r.topLeft = r.bottomRight ∧
    r.toSpin.α r.bottomRight = r.topLeft := by
  simp [Rectangle.toSpin, Rectangle.corners_inside, Rectangle.corners_rotate]

lemma Rectangle.spin_eq_iff {s : Rectangle m n} :
    s.toSpin.α p1 = p2 ↔ p1 = s.toSpin.α p2 := by grind [Rectangle.toSpin]

lemma Spin.perm_distrib (s1 s2 : Spin m n) : (s1 * s2).α = s2.α * s1.α := rfl

private lemma aux1 (n row col : Nat) (hcol : col + 2 < n) :
    (n - (col + 1) - 1) * (2 * (row + 1) - 1) + row + 1 + 1 ≤
      (n - col - 1) * (2 * (row + 1) - 1) + (row + 1) - 2 * row := by
  set N := n - (col + 1)
  rw [show n - col = N + 1 by omega]
  cases h : N <;> grind

private lemma aux2 (m n row col : Nat) (hcol : col + 1 < n) (hrow : row + 1 < m) :
    (n - col - 1) * (2 * m - 1) + m - 2 * (row + 1) + 1 + 1 ≤
      (n - col - 1) * (2 * m - 1) + m - 2 * row := by
  have : (n - col - 1) * (2 * m - 1) ≥ 2 * m - 1 := by
    nlinarith [show 1 ≤ 2 * m - 1 by omega, show 1 ≤ n - col - 1 by omega]
  omega

private lemma aux3 {row col : Nat} (hrow : row < m.val) (hcol : col < n.val) (s : Spin m n)
    (hj2 : ¬ row + 1 < m) (hj3 : col + 1 < n)
    (this : (s.α.symm ⟨⟨row, hrow⟩, ⟨col, hcol⟩⟩).col.val ≥ col)
    (hs_row2 : ∀ x, (_ : x < row) → s.α.symm ⟨⟨x, by omega⟩, ⟨col, hcol⟩⟩
      = ⟨⟨x, by omega⟩, ⟨col, hcol⟩⟩)
    (hs_col2 : ∀ x y, (_ : x < col ∧ y < m.val) → s.α.symm ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩
      = ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩) :
    let tile_pos := s.α.symm ⟨⟨row, _⟩, ⟨col, _⟩⟩
    let row_spin : RectSpin m n := if hr2 : tile_pos.row.val < row then
      RectSpin.fromRect ⟨tile_pos, ⟨⟨row, hrow⟩, tile_pos.col⟩, Fin.le_of_lt hr2, Fin.le_refl _⟩
    else
      RectSpin.fromRect ⟨⟨⟨row, hrow⟩, tile_pos.col⟩, tile_pos, by omega, Fin.le_refl _⟩
    let col_spin : RectSpin m n := RectSpin.fromRect
      ⟨⟨⟨row, hrow⟩, ⟨col, hcol⟩⟩, ⟨⟨row, hrow⟩, tile_pos.col⟩, by simp, this⟩

    ∀ x y, (_ : x < col + 1 ∧ y < m.val) →
      (s⁻¹ * row_spin.toSpin * col_spin.toSpin).α ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩
        = ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩ := by
  intro tile_pos row_spin col_spin x y hxy
  simp [Spin.mul_def]
  by_cases hg : x < col
  · grind [Rectangle.spin_perm_const]
  · grind [Rectangle.corners_rotate_perm, Rectangle.spin_eq_iff, Rectangle.spin_perm_const,
      Equiv.apply_eq_iff_eq, Point.mk.injEq]

private def listSize (m n : PNat) (row col : Nat) :=
  if n.val = col + 1 then
    (if m.val = 1 then 0 else m.val - 1 - row)
  else if row = 0 then
    (n.val - col - 1) * (2 * m.val - 1) + (m.val - 1)
  else
    (n.val - col - 1) * (2 * m.val - 1) + m.val - 2 * row

set_option pp.showLetValues true in
lemma buildBasicPermSolution_correct {m n} (a b : Nat) (hrow : a < m.val) (hcol : b < n.val)
    (s : Spin m n)
    (hs_row : ∀ x, (_ : x < a) → s.α ⟨⟨x, by omega⟩, ⟨b, hcol⟩⟩ = ⟨⟨x, by omega⟩, ⟨b, hcol⟩⟩)
    (hs_col : ∀ x y, (_ : x < b ∧ y < m.val) → s.α ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩
      = ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩) :
    let l := buildBasicPermSolution a b hrow hcol s
    (l.map RectSpin.toSpin).prod.α = s.α ∧ l.length ≤ listSize m n a b := by
  intro l
  fun_induction buildBasicPermSolution with
  | case1 col hcol s d _ _ tile_pos next_spin k ih1 ih2 =>
    unfold l k

    -- is there a way to avoid repeating this in every case?
    have hs_col2 (x y) (hxy : x < col ∧ y < m.val) : s.α.symm ⟨⟨y, _⟩, ⟨x, _⟩⟩ = ⟨⟨y, _⟩, ⟨x, _⟩⟩ :=
      Equiv.Perm.eq_inv_iff_eq.mp (hs_col x y hxy |>.symm)

    have : tile_pos.col.val ≥ col := by
      by_contra hx
      absurd hs_col tile_pos.col.val tile_pos.row.val (by omega)
      grind -ring -linarith

    split_ifs with h1 h2
    · grind
    · grind
    · simp only [List.reverse_nil, List.map_nil, List.prod_nil, Spin.one_def, Equiv.ext_iff,
        Equiv.refl_apply, List.length_nil, zero_le, and_true]
      intro i
      by_cases hy : col = i.col
      · contrapose! hs_col2 with heq
        let r := s.α i
        have : r.row = i.row := by omega
        have : r.col ≠ i.col := by grind
        use r.col, r.row, by omega
        rwa [Equiv.symm_apply_apply]
      · simpa using hs_col i.col i.row (by omega) |>.symm
  | case2 col hcol s _ hm cur_pos tile_pos next_spin k ih1 ih2 =>
    unfold l k

    have hs_col2 (x y) (hxy : x < col ∧ y < m.val) : s.α⁻¹ ⟨⟨y, _⟩, ⟨x, _⟩⟩ = ⟨⟨y, _⟩, ⟨x, _⟩⟩ :=
      Equiv.Perm.eq_inv_iff_eq.mp (hs_col x y hxy |>.symm)

    have : tile_pos.col.val ≥ col := by
      by_contra hx
      absurd hs_col2 tile_pos.col.val tile_pos.row.val (by omega)
      grind -ring -linarith [Equiv.apply_eq_iff_eq_symm_apply]

    have next_spin_eq : next_spin = RectSpin.fromRect
      ⟨⟨⟨0, hm⟩, ⟨col, hcol⟩⟩, tile_pos, by fin_omega, by omega⟩ := by
        simp (disch := omega) [next_spin, RectSpin.fromPoints, dif_pos, cur_pos]

    simp only [zero_add, List.map_cons, List.map_reverse, List.prod_cons, List.length_cons,
      List.length_reverse]
    split_ifs with h1 h2
    · specialize ih1 h1
        (fun x hx => by simp [next_spin_eq, Fin.mk_zero', Spin.mul_def, Spin.inv_perm,
          show x = 0 by omega, Equiv.trans_apply, Rectangle.spin_eq_iff,
          Rectangle.corners_rotate_perm.1, tile_pos, cur_pos])
        (fun x y hxy => by rw [Spin.mul_def, Spin.inv_perm, Equiv.trans_apply, next_spin_eq,
          Rectangle.spin_eq_iff, Rectangle.spin_perm_const (Or.inr hxy.1), hs_col2 x y hxy])
      constructor
      · simp [← rectSpin_prod_inv_eq_reverse_prod, Spin.perm_distrib, ih1.1]
      · grind [listSize]
    · specialize ih2 (by omega) (by omega) (by
        intro x y hxy
        simp only [Spin.mul_def, Spin.inv_perm, Equiv.trans_apply]
        by_cases hg : x = col
        · simp_rw [show y = 0 by omega, hg, next_spin_eq]
          apply Rectangle.corners_rotate_perm.2
        · rw [hs_col2 x y (by omega), next_spin_eq, Rectangle.spin_perm_const (by lia)]
      )
      constructor
      · simp [← rectSpin_prod_inv_eq_reverse_prod, Spin.perm_distrib, ih2.1]
      · grw [ih2.2]
        simp only [listSize]
        lia
    · lia
  | case3 row col hrow hcol s cur_pos tile_pos hrow2 row_spin col_spin k a1 ih1 ih2 =>
    unfold l k

    have hs_row2 (x) (hx : x < row) : s.α⁻¹ ⟨⟨x, _⟩, ⟨col, _⟩⟩ = ⟨⟨x, _⟩, ⟨col, _⟩⟩ :=
      Equiv.Perm.eq_inv_iff_eq.mp (hs_row x hx |>.symm)

    have hs_col2 (x y) (hxy : x < col ∧ y < m.val) : s.α⁻¹ ⟨⟨y, _⟩, ⟨x, _⟩⟩ = ⟨⟨y, _⟩, ⟨x, _⟩⟩ :=
      Equiv.Perm.eq_inv_iff_eq.mp (hs_col x y hxy |>.symm)

    have : tile_pos.col.val ≥ col := by
      by_contra hx
      absurd hs_col2 tile_pos.col.val tile_pos.row.val (by omega)
      grind -ring -linarith [Equiv.apply_eq_iff_eq_symm_apply]

    have col_spin_eq : col_spin =
        RectSpin.fromRect ⟨cur_pos, ⟨⟨row, hrow⟩, tile_pos.col⟩, Fin.le_refl _, by omega⟩ := by
      simp (disch := omega) [col_spin, RectSpin.fromPoints, dif_pos, cur_pos]
    have row_spin_eq : row_spin =
        if ht : tile_pos.row.val < row then
          RectSpin.fromRect ⟨tile_pos, ⟨⟨row, hrow⟩, tile_pos.col⟩, Fin.le_of_lt ht, by simp⟩
        else
          RectSpin.fromRect ⟨⟨⟨row, hrow⟩, tile_pos.col⟩, tile_pos, Fin.not_lt.mp ht, by simp⟩ := by
      split_ifs with hr <;>
      simp (disch := omega) [hr, row_spin, RectSpin.fromPoints, dif_pos, ← Fin.val_fin_le]

    split_ifs with h1
    · specialize ih1 h1 (fun x hx => by
        simp only [Spin.mul_def, Spin.inv_perm, Equiv.trans_apply]
        by_cases hg : x = row
        · simp only [hg, cur_pos, col_spin_eq, row_spin_eq, tile_pos]
          split_ifs
          · simp [Rectangle.corners_rotate_perm.1, Rectangle.corners_rotate_perm.2]
          · simp [Rectangle.spin_eq_iff, Rectangle.corners_rotate_perm.1]
        · rw [col_spin_eq, row_spin_eq, Rectangle.spin_eq_iff,
            Rectangle.spin_perm_const (by simp [cur_pos]; omega), hs_row2 x (by omega)]
          split_ifs
          · have hg4 : col ≠ tile_pos.col.val := by
              by_contra! hg4
              absurd hs_row2 tile_pos.row.val (by omega)
              grind -ring -linarith [Equiv.apply_eq_iff_eq, Point.ext]
            rw [Rectangle.spin_perm_const (by lia)]
          · rw [Rectangle.spin_perm_const (by lia)]
      ) (fun x y hxy => by
        simp only [row_spin_eq, Spin.mul_def, Spin.inv_perm, col_spin_eq, Equiv.trans_apply,
          hs_col2 _ _ hxy, Rectangle.spin_eq_iff]
        split_ifs with hz <;>
        rw [Rectangle.spin_perm_const (by simp only; omega),
          Rectangle.spin_perm_const (by simp [cur_pos]; omega)])
      constructor
      · simp [← rectSpin_prod_inv_eq_reverse_prod, Spin.perm_distrib, ih1.1]
      · simp only [List.length_cons, List.length_reverse]
        grw [ih1.2]
        simp [listSize, show n.val ≠ col + 1 by omega, hrow2, aux2, a1, h1]
    · rw [col_spin_eq, row_spin_eq] at ih2
      specialize ih2 a1 (by omega) (aux3 hrow hcol s h1 a1 this hs_row2 hs_col2)
      rw [← col_spin_eq, ← row_spin_eq] at ih2
      constructor
      · simp [← rectSpin_prod_inv_eq_reverse_prod, Spin.perm_distrib, ih2.1]
      · simp only [List.length_cons, List.length_reverse]
        grw [ih2.2]
        simp only [listSize, show m.val = row + 1 by omega, Nat.add_eq_right, hrow2, ↓reduceIte,
          show n.val ≠ col + 1 by omega]
        split_ifs with hn1
        · lia
        · exact aux1 n row col (by lia)
  | case4 row col hrow hcol s cur_pos tile_pos hrow2 row_spin col_spin k a1 a2 ih1 ih2 =>
    unfold l k

    have hs_row2 (x) (hx : x < row) : s.α⁻¹ ⟨⟨x, _⟩, ⟨col, _⟩⟩ = ⟨⟨x, _⟩, ⟨col, _⟩⟩ :=
      Equiv.Perm.eq_inv_iff_eq.mp (hs_row x hx |>.symm)

    have hs_col2 (x y) (hxy : x < col ∧ y < m.val) : s.α⁻¹ ⟨⟨y, _⟩, ⟨x, _⟩⟩ = ⟨⟨y, _⟩, ⟨x, _⟩⟩ :=
      Equiv.Perm.eq_inv_iff_eq.mp (hs_col x y hxy |>.symm)

    have : tile_pos.col.val ≥ col := by
      by_contra hx
      absurd hs_col2 tile_pos.col.val tile_pos.row.val (by omega)
      grind -ring -linarith [Equiv.apply_eq_iff_eq_symm_apply]

    have col_spin_eq : col_spin =
        RectSpin.fromRect ⟨cur_pos, ⟨⟨row, hrow⟩, tile_pos.col⟩, by simp [cur_pos], by omega⟩ := by
      simp (disch := omega) [col_spin, RectSpin.fromPoints, dif_pos, cur_pos]
    have row_spin_eq : row_spin =
        if ht : tile_pos.row.val < row then
          RectSpin.fromRect ⟨tile_pos, ⟨⟨row, hrow⟩, tile_pos.col⟩, Fin.le_of_lt ht, by simp⟩
        else
          RectSpin.fromRect ⟨⟨⟨row, hrow⟩, tile_pos.col⟩, tile_pos, Fin.not_lt.mp ht, by simp⟩ := by
      split_ifs with hr <;>
      simp (disch := omega) [hr, row_spin, RectSpin.fromPoints, dif_pos, ← Fin.val_fin_le]

    simp only [a2, ↓reduceDIte, List.map_cons, List.map_reverse, List.prod_cons, List.length_cons,
      List.length_reverse]
    -- TODO: this is shared with case3
    specialize ih1 a2 (by
      intro x hx
      simp only [Spin.mul_def, Spin.inv_perm, Equiv.trans_apply]
      by_cases hg : x = row
      · simp only [hg, cur_pos, col_spin_eq, row_spin_eq, tile_pos]
        split_ifs
        · simp [Rectangle.corners_rotate_perm.1, Rectangle.corners_rotate_perm.2]
        · simp [Rectangle.spin_eq_iff, Rectangle.corners_rotate_perm.1]
      · rw [col_spin_eq, row_spin_eq, Rectangle.spin_eq_iff,
          Rectangle.spin_perm_const (by simp [cur_pos]; omega), hs_row2 x (by omega)]
        split_ifs
        · have hg4 : col ≠ tile_pos.col.val := by
            by_contra! hg4
            absurd hs_row2 tile_pos.row.val (by omega)
            grind -ring -linarith [Equiv.apply_eq_iff_eq, Point.ext]
          rw [Rectangle.spin_perm_const (by lia)]
        · rw [Rectangle.spin_perm_const (by lia)]
    ) (fun x y hxy => by
        simp only [row_spin_eq, Spin.mul_def, Spin.inv_perm, col_spin_eq, Equiv.trans_apply,
          hs_col2 _ _ hxy, Rectangle.spin_eq_iff]
        split_ifs with hz <;>
        rw [Rectangle.spin_perm_const (by simp only; omega),
          Rectangle.spin_perm_const (by simp [cur_pos]; omega)])
    constructor
    · have col_spin_eq' : col_spin.α = Equiv.refl _ := by
        ext i : 1
        simp [col_spin_eq, cur_pos, Rectangle.toSpin, Point.IsInside, rotate180, rotateCalc]
        grind -ring -linarith
      simp [← rectSpin_prod_inv_eq_reverse_prod, Spin.perm_distrib, ih1.1, col_spin_eq']
    · grw [ih1.2]
      simp only [listSize]
      lia
  | case5 row col hrow hcol s _ tile_pos hrow2 row_spin col_spin k a1 a2 ih1 ih2 =>
    unfold l k
    simp only [a2, ↓reduceDIte, a1, List.reverse_nil, List.length_nil, zero_le, and_true]

    have hb : col = tile_pos.col.val := by
      by_contra! hx
      absurd hs_col tile_pos.col.val tile_pos.row.val (by omega)
      grind -ring -linarith
    have hc : row = tile_pos.row.val := by
      by_contra! hx
      absurd hs_row tile_pos.row.val (by omega)
      grind -ring -linarith
    ext i : 1
    by_cases hx : i.col.val < col
    · simpa using hs_col i.col i.row (by omega) |>.symm
    · have : i.col.val = col := by omega
      by_cases i.row.val < row
      · simpa [← this] using hs_row i.row.val (by omega) |>.symm
      · grind -ring -linarith [Spin.one_def]

open scoped CharTwo in
/-- Every element of `Spinₘₓₙ` can be expressed as a product of at most `3mn - (m + n)` spins. -/
theorem theorem1 (b : Spin m n) :
    ∀ l, Spin.IsSolution l b → l.length ≤ 3 * m * n - (m + n) := by
  have h3 v : ∃ l : List (RectSpin m n), (l.map RectSpin.toSpin).prod =
      ⟨1, b.u + v⟩⁻¹ ∧ l.length ≤ m * n := by
    let z1 : List (RectSpin m n) := []
    let z2 : List (RectSpin m n) := (.univ : Finset (Point m n)).toList.filterMap fun x =>
      if (z1.map RectSpin.toSpin).prod.u x ≠ (b.u + v) x
      then RectSpin.fromRect ⟨x, x, Fin.le_refl _, Fin.le_refl _⟩
      else none

    use z1 ++ z2
    constructor
    · unfold z1 z2
      rw [List.map_append]
      apply Corollary1.aux1 (by simp [Spin.one_def, Equiv.Perm.one_def])
      -- `ite_not` doesn't work well with `Option.map_if`
      simp [-ite_not, -Classical.ite_not, List.map_filterMap, Spin.inv_def, z1]
    · have : (.univ : Finset (Point m n)).card = (.univ : Finset (Fin m × Fin n)).card := by
        apply Finset.card_bij (fun r _ => (r.row, r.col)) (by simp) (by simp [Point.ext_iff])
        exact fun b _ => ⟨⟨b.1, b.2⟩, by simp⟩
      grind [Fintype.card_prod, Fintype.card_fin]
  suffices h2 : ∃ l : List (RectSpin m n), (l.map RectSpin.toSpin).prod.α = b.α.symm ∧
      l.length ≤ 2 * m * n - (m + n) by
    obtain ⟨l2, hl2⟩ := h2
    obtain ⟨l1, hl1⟩ := h3 ((l2.map RectSpin.toSpin).prod.u ∘ (b.α.symm))
    have zz : (List.map RectSpin.toSpin (l1 ++ l2)).prod = b⁻¹ := by
      simp [hl1, hl2.1, Spin.inv_def, Spin.mul_def]
    intro l5 hl5
    simp only [Spin.IsSolution] at hl5
    grw [← hl5.2 (l1 ++ l2) zz, List.length_append, hl2.2, hl1.2]
    have : m.val + n.val ≤ 2 * (m.val * n.val) := by
      rw [two_mul]
      gcongr
      · exact Nat.le_mul_of_pos_right m.val n.2
      · exact Nat.le_mul_of_pos_left n.val m.2
    lia

  use buildBasicPermSolution 0 0 m.2 n.2 b⁻¹
  convert buildBasicPermSolution_correct 0 0 m.2 n.2 b⁻¹ (by omega) (by omega) using 2
  simp only [listSize]
  split_ifs with h7 h8
  · rw [h7, h8]
  · lia
  · cases m.val <;> cases _ : n.val <;> grind -ring -linarith only [PNat.ne_zero]
