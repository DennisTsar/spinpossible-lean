import Spinpossible.Solution




attribute [-grind] List.eq_nil_of_map_eq_nil
attribute [-instance] NeZero.charZero_one

attribute [-simp] PNat.coe_eq_one_iff
attribute [-simp]
  OfNat.ofNat_ne_zero OfNat.zero_ne_ofNat OfNat.ofNat_ne_one OfNat.one_ne_ofNat OfNat.ofNat_eq_ofNat

attribute [-simp] Nat.sub_eq_zero_of_le

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

instance : Inhabited (Rectangle m n) := ⟨⟨0, 0⟩, ⟨0, 0⟩, by simp, by simp⟩

/-- Create a `RectSpin` from the given points if they form a valid rectangle,
  or panic / return a default value if they do not -/
abbrev RectSpin.fromPoints (topLeft bottomRight : Point m n) : RectSpin m n :=
  if h : topLeft.row ≤ bottomRight.row ∧ topLeft.col ≤ bottomRight.col then
    fromRect ⟨topLeft, bottomRight, h.2, h.1⟩
  else
    fromRect (panic! "Invalid rectangle")

def buildBasicPermSolution (row col : Nat) (hrow : row < m.val) (hcol : col < n.val)
    (s : Spin m n) : List (RectSpin m n) :=
  let cur_pos : Point m n := ⟨⟨row, hrow⟩, ⟨col, hcol⟩⟩
  let tile_pos := s.α⁻¹ cur_pos

  if row = 0 then
    let next_spin := RectSpin.fromPoints
      cur_pos tile_pos
    let rest := if hrow : row + 1 < m then
        buildBasicPermSolution (row + 1) col hrow hcol (s⁻¹ * next_spin)
      else if hcol : col + 1 < n then
        buildBasicPermSolution 0 (col + 1) m.2 hcol (s⁻¹ * next_spin)
      else []
    if m.val = 1 ∧ ¬ col + 1 < n then rest.reverse
    else [next_spin] ++ rest.reverse
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

    if col + 1 < n then [row_spin, col_spin] ++ rest.reverse
    else if row + 1 < m then [row_spin] ++ rest.reverse
    else rest.reverse
termination_by (n.val - col, m.val - row)
decreasing_by all_goals omega -- slightly quicker than default implementation

private def listSize (m n : PNat) (row col : Nat) :=
  if n.val = col + 1 then
    (if m.val = 1 then 0 else m.val - 1 - row)
  else if row = 0 then
    (n.val - col - 1) * (2 * m.val - 1) + (m.val - 1)
  else
    (n.val - col - 1) * (2 * m.val - 1) + m.val - 2 * row

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

    have hs_col2 (x y) (hxy : x < col ∧ y < m.val) :
        s.α⁻¹ ⟨⟨y, _⟩, ⟨x, _⟩⟩ = ⟨⟨y, _⟩, ⟨x, _⟩⟩ :=
      Equiv.Perm.eq_inv_iff_eq.mp (hs_col x y hxy |>.symm)

    have : tile_pos.col.val ≥ col := by
      by_contra hx
      absurd hs_col2 tile_pos.col.val tile_pos.row.val (by omega)
      grind -ring -linarith [Fin.eta, EmbeddingLike.apply_eq_iff_eq]

    split_ifs with h1 h2
    · grind
    · grind
    · simp [Spin.one_def, Equiv.ext_iff]
      intro i
      by_cases hy : col = i.col
      · contrapose! hs_col2 with heq
        let r := s.α i
        have : r.row = i.row := by omega
        have : r.col ≠ i.col := by grind
        use r.col, r.row, by omega
        rwa [Equiv.Perm.inv_apply_self]
      · simpa using hs_col i.col i.row (by omega) |>.symm
  | case2 col hcol s _ hm cur_pos tile_pos next_spin k ih1 ih2 =>
    unfold l k

    have hs_col2 (x y) (hxy : x < col ∧ y < m.val) :
        s.α⁻¹ ⟨⟨y, _⟩, ⟨x, _⟩⟩ = ⟨⟨y, _⟩, ⟨x, _⟩⟩ :=
      Equiv.Perm.eq_inv_iff_eq.mp (hs_col x y hxy |>.symm)

    have : tile_pos.col.val ≥ col := by
      by_contra hx
      absurd hs_col2 tile_pos.col.val tile_pos.row.val (by omega)
      grind -ring -linarith [Fin.eta, EmbeddingLike.apply_eq_iff_eq]

    have next_spin_eq : next_spin = RectSpin.fromRect
      ⟨⟨⟨0, hm⟩, ⟨col, hcol⟩⟩, tile_pos, by omega, by fin_omega⟩ := by
        simp (disch := omega) [next_spin, RectSpin.fromPoints, dif_pos, cur_pos]

    simp only [zero_add, List.cons_append, List.nil_append, List.map_cons, List.map_reverse,
      List.prod_cons, List.length_cons, List.length_reverse]
    split_ifs with h1 h2
    · specialize ih1 h1
        (fun x hx => by simp only [next_spin_eq, Fin.mk_zero', Spin.mul_def, Spin.inv_perm,
          show x = 0 by omega, Equiv.trans_apply, Rectangle.spin_eq_iff,
          Rectangle.corners_rotate_perm.1, tile_pos, cur_pos])
        (fun x y hxy => by rw [Spin.mul_def, Spin.inv_perm, Equiv.trans_apply, next_spin_eq,
          Rectangle.spin_eq_iff, Rectangle.spin_perm_const (Or.inr hxy.1), hs_col2 x y hxy]
        )
      constructor
      · rw [← rectSpin_prod_inv_eq_reverse_prod, Spin.perm_distrib, Spin.inv_perm, ih1.1, Spin.perm_distrib]
        simp
      · grw [ih1.2]
        simp [listSize, show m.val ≠ 1 by omega]
        split_ifs <;> omega
    · specialize ih2 (by omega) (by omega) (by
        intro x y hxy
        simp only [Spin.mul_def, Spin.inv_perm, Equiv.trans_apply]
        by_cases hg : x = col
        · grind -ring -linarith [Rectangle.corners_rotate_perm]
        · rw [hs_col2 x y (by omega), next_spin_eq, Rectangle.spin_perm_const (by fin_omega)]
      )
      constructor
      · rw [← rectSpin_prod_inv_eq_reverse_prod, Spin.perm_distrib, Spin.inv_perm, ih2.1, Spin.perm_distrib]
        simp
      · grw [ih2.2]
        simp [listSize, show m.val = 1 by omega]
        split_ifs <;> omega
    · grind
  | case3 row col hrow hcol s cur_pos tile_pos hrow2 row_spin col_spin k a1 ih1 ih2 =>
    unfold l k

    have hs_row2 (x) (hx : x < row) : s.α⁻¹ ⟨⟨x, _⟩, ⟨col, _⟩⟩ = ⟨⟨x, _⟩, ⟨col, _⟩⟩ :=
      Equiv.Perm.eq_inv_iff_eq.mp (hs_row x hx |>.symm)

    have hs_col2 (x y) (hxy : x < col ∧ y < m.val) :
        s.α⁻¹ ⟨⟨y, _⟩, ⟨x, _⟩⟩ = ⟨⟨y, _⟩, ⟨x, _⟩⟩ :=
      Equiv.Perm.eq_inv_iff_eq.mp (hs_col x y hxy |>.symm)

    have : tile_pos.col.val ≥ col := by
      by_contra hx
      absurd hs_col2 tile_pos.col.val tile_pos.row.val (by omega)
      grind -ring -linarith [Fin.eta, EmbeddingLike.apply_eq_iff_eq]

    have col_spin_eq : col_spin =
        RectSpin.fromRect ⟨cur_pos, ⟨⟨row, hrow⟩, tile_pos.col⟩, by omega, Fin.ge_of_eq rfl⟩ := by
      simp (disch := omega) [col_spin, RectSpin.fromPoints, dif_pos, cur_pos]
    have row_spin_eq : row_spin =
        if ht : tile_pos.row.val < row then
          RectSpin.fromRect ⟨tile_pos, ⟨⟨row, hrow⟩, tile_pos.col⟩, by simp, Fin.le_of_lt ht⟩
        else
          RectSpin.fromRect ⟨⟨⟨row, hrow⟩, tile_pos.col⟩, tile_pos, by simp, Fin.not_lt.mp ht⟩ := by
      split_ifs with hr <;>
      simp (disch := omega) [hr, row_spin, RectSpin.fromPoints, dif_pos, ← Fin.val_fin_le]

    split_ifs with h1
    · specialize ih1 h1 (fun x hx => by
        simp only [Spin.mul_def, Spin.inv_perm, Equiv.trans_apply]
        by_cases hg : x = row
        -- · grind -ring -linarith [Rectangle.corners_rotate_perm] -- too slow
        · simp only [hg, cur_pos, col_spin_eq, row_spin_eq, tile_pos]
          split_ifs
          · simp [Rectangle.corners_rotate_perm.1, Rectangle.corners_rotate_perm.2]
          · simp [Rectangle.spin_eq_iff, Rectangle.corners_rotate_perm.1]
        · rw [col_spin_eq, Rectangle.spin_eq_iff, Rectangle.spin_perm_const (by simp [cur_pos]; omega)]
          simp only [hs_row2 x (by omega), row_spin_eq]
          split_ifs
          · have hg4 : col ≠ tile_pos.col.val := by
              by_contra! hg4
              absurd hs_row2 tile_pos.row.val (by omega)
              grind -ring -linarith [EmbeddingLike.apply_eq_iff_eq, Fin.eta]
            rw [Rectangle.spin_perm_const (by fin_omega)]
          · rw [Rectangle.spin_perm_const (by fin_omega)]
      ) (fun x y hxy => by
        simp only [row_spin_eq, Spin.mul_def, Spin.inv_perm, col_spin_eq, Equiv.trans_apply,
          hs_col2 _ _ hxy, Rectangle.spin_eq_iff]
        split_ifs with hz <;>
        rw [Rectangle.spin_perm_const (by simp only; omega),
          Rectangle.spin_perm_const (by simp [cur_pos]; omega)]
      )
      constructor
      · simp only [List.cons_append, List.nil_append, List.map_cons, List.map_reverse,
          List.prod_cons]
        rw [← rectSpin_prod_inv_eq_reverse_prod, Spin.perm_distrib, Spin.perm_distrib,
          Spin.inv_perm, ih1.1, Spin.perm_distrib, Spin.perm_distrib]
        simp
      · simp only [List.cons_append, List.nil_append, List.length_cons, List.length_reverse]
        grw [ih1.2]
        simp [listSize, show n.val ≠ col + 1 by omega, hrow2, aux2, a1, h1]
    · rw [col_spin_eq, row_spin_eq] at ih2
      specialize ih2 a1 (by omega) (funtimes row col hrow hcol s h1 a1 this hs_row2 hs_col2)
      rw [← col_spin_eq, ← row_spin_eq] at ih2
      constructor
      · simp only [List.cons_append, List.nil_append, List.map_cons, List.map_reverse,
          List.prod_cons]
        rw [← rectSpin_prod_inv_eq_reverse_prod, Spin.perm_distrib, Spin.perm_distrib,
          Spin.inv_perm, ih2.1, Spin.perm_distrib, Spin.perm_distrib]
        simp
      · simp only [List.cons_append, List.nil_append, List.length_cons, List.length_reverse]
        grw [ih2.2]
        simp [listSize, show m.val = row + 1 by omega, show n.val ≠ col + 1 by omega, hrow2]
        split_ifs with hn1
        · rw [hn1]; grind
        · exact aux1 n row col (by omega)
  | case4 row col hrow hcol s cur_pos tile_pos hrow2 row_spin col_spin k a1 a2 ih1 ih2 =>
    unfold l k

    have hs_row2 (x) (hx : x < row) : s.α⁻¹ ⟨⟨x, _⟩, ⟨col, _⟩⟩ = ⟨⟨x, _⟩, ⟨col, _⟩⟩ :=
      Equiv.Perm.eq_inv_iff_eq.mp (hs_row x hx |>.symm)

    have hs_col2 (x y) (hxy : x < col ∧ y < m.val) :
        s.α⁻¹ ⟨⟨y, _⟩, ⟨x, _⟩⟩ = ⟨⟨y, _⟩, ⟨x, _⟩⟩ :=
      Equiv.Perm.eq_inv_iff_eq.mp (hs_col x y hxy |>.symm)

    have : tile_pos.col.val ≥ col := by
      by_contra hx
      absurd hs_col2 tile_pos.col.val tile_pos.row.val (by omega)
      grind -ring -linarith [Fin.eta, EmbeddingLike.apply_eq_iff_eq]

    have col_spin_eq : col_spin =
        RectSpin.fromRect ⟨cur_pos, ⟨⟨row, hrow⟩, tile_pos.col⟩, by omega, by simp [cur_pos]⟩ := by
      simp (disch := omega) [col_spin, RectSpin.fromPoints, dif_pos, cur_pos]
    have row_spin_eq : row_spin =
        if ht : tile_pos.row.val < row then
          RectSpin.fromRect ⟨tile_pos, ⟨⟨row, hrow⟩, tile_pos.col⟩, by simp, Fin.le_of_lt ht⟩
        else
          RectSpin.fromRect ⟨⟨⟨row, hrow⟩, tile_pos.col⟩, tile_pos, by simp, Fin.not_lt.mp ht⟩ := by
      split_ifs with hr <;>
      simp (disch := omega) [hr, row_spin, RectSpin.fromPoints, dif_pos, ← Fin.val_fin_le]

    simp [a2]
    -- TODO: this is shared with case3
    specialize ih1 a2 (by
      intro x hx
      simp only [Spin.mul_def, Spin.inv_perm, Equiv.trans_apply]
      by_cases hg : x = row
      · simp only [hg, cur_pos, col_spin_eq, row_spin_eq, tile_pos]
        split_ifs
        · simp [Rectangle.corners_rotate_perm.1, Rectangle.corners_rotate_perm.2]
        · simp [Rectangle.spin_eq_iff, Rectangle.corners_rotate_perm.1]
      · rw [col_spin_eq, Rectangle.spin_eq_iff, Rectangle.spin_perm_const (by simp [cur_pos]; omega)]
        simp only [hs_row2 x (by omega), row_spin_eq]
        split_ifs
        · have hg4 : col ≠ tile_pos.col.val := by
            by_contra! hg4
            absurd hs_row2 tile_pos.row.val (by omega)
            grind -ring -linarith [EmbeddingLike.apply_eq_iff_eq, Fin.eta]
          rw [Rectangle.spin_perm_const (by fin_omega)]
        · rw [Rectangle.spin_perm_const (by fin_omega)]
    ) (fun x y hxy => by
        simp only [row_spin_eq, Spin.mul_def, Spin.inv_perm, col_spin_eq, Equiv.trans_apply,
          hs_col2 _ _ hxy, Rectangle.spin_eq_iff]
        split_ifs with hz <;>
        rw [Rectangle.spin_perm_const (by simp only; omega),
          Rectangle.spin_perm_const (by simp [cur_pos]; omega)]
      )
    constructor
    · have col_spin_eq' : col_spin.α = Equiv.refl _ := by
        ext i : 1
        simp [col_spin_eq, cur_pos, Rectangle.toSpin, Point.IsInside, rotate180, rotateCalc]
        intros
        ext <;> fin_omega
      rw [← rectSpin_prod_inv_eq_reverse_prod, Spin.perm_distrib, Spin.inv_perm,
        ih1.1, Spin.perm_distrib, Spin.perm_distrib, Spin.inv_perm, col_spin_eq']
      simp
    · grw [ih1.2]
      simp (disch := omega) [listSize, show n.val = col + 1 by omega, show m.val ≠ 1 by omega]
      omega
  | case5 row col hrow hcol s cur_pos tile_pos hrow2 row_spin col_spin k a1 a2 ih1 ih2 =>
    unfold l k

    have hs_row2 (x) (hx : x < row) : s.α⁻¹ ⟨⟨x, _⟩, ⟨col, _⟩⟩ = ⟨⟨x, _⟩, ⟨col, _⟩⟩ :=
      Equiv.Perm.eq_inv_iff_eq.mp (hs_row x hx |>.symm)

    have hs_col2 (x y) (hxy : x < col ∧ y < m.val) :
        s.α⁻¹ ⟨⟨y, _⟩, ⟨x, _⟩⟩ = ⟨⟨y, _⟩, ⟨x, _⟩⟩ :=
      Equiv.Perm.eq_inv_iff_eq.mp (hs_col x y hxy |>.symm)

    have : tile_pos.col.val ≥ col := by
      by_contra hx
      absurd hs_col2 tile_pos.col.val tile_pos.row.val (by omega)
      grind -ring -linarith [Fin.eta, EmbeddingLike.apply_eq_iff_eq]

    have col_spin_eq : col_spin =
        RectSpin.fromRect ⟨cur_pos, ⟨⟨row, hrow⟩, tile_pos.col⟩, by omega, by simp [cur_pos]⟩ := by
      simp (disch := omega) [col_spin, RectSpin.fromPoints, dif_pos, cur_pos]
    have row_spin_eq : row_spin =
        if ht : tile_pos.row.val < row then
          RectSpin.fromRect ⟨tile_pos, ⟨⟨row, hrow⟩, tile_pos.col⟩, by simp, Fin.le_of_lt ht⟩
        else
          RectSpin.fromRect ⟨⟨⟨row, hrow⟩, tile_pos.col⟩, tile_pos, by simp, Fin.not_lt.mp ht⟩ := by
      split_ifs with hr <;>
      simp (disch := omega) [hr, row_spin, RectSpin.fromPoints, dif_pos, ← Fin.val_fin_le]

    simp [a2, a1]
    simp [Spin.one_def]

    have hb : col = tile_pos.col.val := by grind
    have hc : row = tile_pos.row.val := by
      by_contra! hx
      have := hs_row2 tile_pos.row.val (by omega)
      grind [EmbeddingLike.apply_eq_iff_eq, Fin.eta]
    ext i : 1
    by_cases hx : i.col.val < col
    · simpa using hs_col i.col i.row (by omega) |>.symm
    · have : i.col.val = col := by omega
      by_cases i.row.val < row
      · simpa [← this] using hs_row i.row.val (by omega) |>.symm
      · have : i = tile_pos := by ext <;> omega
        conv_rhs => rw [this]
        simp [tile_pos, cur_pos]
        ext <;> grind

-- TODO: figure out how to avoid this popping up
lemma Spin.symm_inv (s : Spin m n) : Equiv.symm s.α = s.α⁻¹ := rfl

lemma rect_spin_one (p : Point m n) : Rectangle.toSpin ⟨p, p, Fin.le_refl _, Fin.le_refl _⟩ =
    ⟨Equiv.refl _, fun x => if x = p then 1 else 0⟩ := by
  simp_all [Rectangle.toSpin, Equiv.ext_iff, rotate_around_one_eq_self]
  funext
  exact if_congr Point.isInside_one_iff rfl rfl

open scoped CharTwo in
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
    have : m.val + n.val ≤ 2 * (m.val * n.val) := by
      rw [two_mul]
      gcongr
      · exact Nat.le_mul_of_pos_right m.val n.2
      · exact Nat.le_mul_of_pos_left n.val m.2
    grind

  use buildBasicPermSolution 0 0 m.2 n.2 b⁻¹
  have := buildBasicPermSolution_correct 0 0 m.2 n.2 b⁻¹ (by omega) (by omega)
  convert this using 2
  simp only [listSize, zero_add, tsub_zero, ↓reduceIte]
  split_ifs with h7 h8
  · rw [h7, h8]
  · rw [h7]; omega
  · cases m.val <;> cases _ : n.val <;> grind [PNat.ne_zero]
