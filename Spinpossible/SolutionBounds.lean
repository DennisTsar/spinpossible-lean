import Spinpossible.Solution

lemma rect_spin_one (p : Point m n) : Rectangle.toSpin ⟨p, p, by simp, by simp⟩ =
    ⟨Equiv.refl _, fun x => if to2d x = p then 1 else 0⟩ := by
  simp_all [Rectangle.toSpin, Equiv.ext_iff, rotate_around_one_eq_self]
  funext
  exact if_ctx_congr Point.isInside_one_iff (congrFun rfl) (congrFun rfl)

set_option linter.haveLet 0

open scoped CharTwo

attribute [-simp] IsEmpty.forall_iff
attribute [-simp] PNat.val_ofNat
attribute [-simp] ge_iff_le
attribute [-simp] le_of_subsingleton

lemma asdf (s1 s2 : Spin m n) : Equiv.trans (s1.α) s2.α = (s1 * s2).α := by
  simp [Spin.mul_def]

lemma smth {s1 : Spin m n} {s2 : RectSpin m n} (a : { l // (List.map RectSpin.toSpin l).prod.α = (s1 * s2).α }) :
    ((a.1 ++ [s2]).map RectSpin.toSpin).prod.α = s1.α := by
  -- simp only [spin_prod_perm_eq_perm_prod]
  have := a.2
  simp [List.prod_append]
  simp [Spin.mul_def]
  simp [a.2]
  simp [asdf]
  rw [mul_assoc]
  simp [spin_is_own_inverse s2]

lemma smth' {s1 : Spin m n} {s2 : RectSpin m n} (a : { l // (List.map RectSpin.toSpin l).prod.α = (s1 * s2).α }) :
    ((a.1 ++ [s2]).map RectSpin.toSpin).reverse.prod.α = s1⁻¹.α := by
  have := smth a
  simp only [← rectSpin_prod_inv_eq_reverse_prod]
  exact congr($this ⁻¹)

lemma smth2 {s1 : Spin m n} {s2 s3 : RectSpin m n} (a : { l // (List.map RectSpin.toSpin l).prod.α = (s1 * s2 * s3).α }) :
    ((a.1 ++ [s3, s2]).map RectSpin.toSpin).prod.α = s1.α := by
  -- simp only [spin_prod_perm_eq_perm_prod]
  have := a.2
  simp [List.prod_append]
  simp [Spin.mul_def]
  simp [a.2]
  simp [asdf]
  rw [mul_assoc]
  have : s3.toSpin * (s3.toSpin * s2.toSpin) = s3.toSpin * s3.toSpin * s2.toSpin := by rw [mul_assoc]
  rw [this]
  simp [spin_is_own_inverse s3]
  rw [mul_assoc]
  simp [spin_is_own_inverse s2]

lemma smth2' {s1 : Spin m n} {s2 s3 : RectSpin m n} (a : { l // (List.map RectSpin.toSpin l).prod.α = (s1 * s2 * s3).α }) :
    ((a.1 ++ [s3, s2]).map RectSpin.toSpin).reverse.prod.α = s1⁻¹.α := by
  have := smth2 a
  simp only [← rectSpin_prod_inv_eq_reverse_prod]
  exact congr($this ⁻¹)

lemma asdfg {r : Rectangle m n} (h : ¬p.IsInside r) : r.toSpin.α (to1d p) = to1d p := by
  simp [Rectangle.toSpin]
  simp [Point.IsInside] at *
  omega

lemma asdfgg {p : Point m n} {r : Rectangle m n} (h : p.row.val < r.topLeft.row.val ∨ p.col.val < r.topLeft.col.val) :
    ¬p.IsInside r := by
  simp [Point.IsInside]
  omega

-- TODO: make them unnecessary
lemma Rectangle.perm_inv (s : Rectangle m n) : s.toSpin.α⁻¹ = s.toSpin.α := by simp [Rectangle.toSpin]; rfl

set_option maxHeartbeats 400000 in
lemma funtimes3 (row col : Nat) (hrow : row < m.val) (hcol : col < n.val) (s : Spin m n)
    (hj2 : ¬ row + 1 < m) (hj3 : ¬ col + 1 < n)
    (this : (to2d (s.α⁻¹ (to1d ⟨⟨row, by omega⟩, ⟨col, by omega⟩⟩))).col.val ≥ col)
    (hs_row2 : ∀ x, (_ : x < row) → s.α⁻¹ (to1d ⟨⟨x, by omega⟩, ⟨col, by omega⟩⟩) = to1d ⟨⟨x, by omega⟩, ⟨col, by omega⟩⟩)
    (hs_col2 : ∀ x y, (_ : x < col ∧ y < m.val) → s.α⁻¹ (to1d ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩) = to1d ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩) :
    let tile_pos := to2d (s.α⁻¹ (to1d ⟨⟨row, by omega⟩, ⟨col, by omega⟩⟩))
    let row_spin : RectSpin m n := if hr2 : row > tile_pos.row.val then
      RectSpin.fromRect ⟨tile_pos, ⟨⟨row, by omega⟩, tile_pos.col⟩, by simp, Fin.le_of_lt hr2⟩
    else
      RectSpin.fromRect ⟨⟨⟨row, by omega⟩, tile_pos.col⟩, tile_pos, by simp, by simp; fin_omega⟩

    -- moves the tile into the correct column (by spinning along a row)
    let col_spin : RectSpin m n := RectSpin.fromRect ⟨⟨⟨row, by omega⟩, ⟨col, by omega⟩⟩, ⟨⟨row, by omega⟩, tile_pos.col⟩, this, by simp⟩
    (List.map RectSpin.toSpin []).prod.α = (s⁻¹ * row_spin.toSpin * col_spin.toSpin).α := by
  intro tile_pos row_spin col_spin
  simp [Spin.mul_def]
  rw [Equiv.ext_iff]
  intro i
  have : row = m - 1 := by omega
  have : col = n - 1 := by omega
  have hb : tile_pos.col.val = col := by simp [tile_pos] at *; omega
  simp
  symm
  rw [← Equiv.Perm.eq_inv_iff_eq, Rectangle.perm_inv]
  simp [Spin.one_def]
  simp [show tile_pos.col = ⟨col, by omega⟩ from Fin.eq_mk_iff_val_eq.mpr hb]

  suffices row_spin.α (s⁻¹.α i) = i by
    rw [this]
    simp [Rectangle.toSpin]
    split_ifs with hv
    ·
      have : (to2d i) = ⟨⟨row, by omega⟩, ⟨col, by omega⟩⟩ := Point.isInside_one_iff.mp hv
      simp [← to2d_injective.eq_iff]
      simp [rotate180, rotateCalc]
      simp_all
    · simp_all

  simp [row_spin]
  have : tile_pos.row.val = row := by
    by_contra! hx
    have : tile_pos.row.val < row := by omega
    have := hs_row2 tile_pos.row.val this
    simp at this
    simp [← hb] at this
    simp_all [tile_pos]
  simp [this]
  by_cases hx : (to2d i).col.val < tile_pos.col.val
  ·
    have := hs_col2 (to2d i).col (to2d i).row ⟨by omega, by omega⟩
    simp at this
    simp [show s⁻¹.α i = i from this]
    simp [Rectangle.toSpin]
    simp [Point.IsInside]
    omega
  ·
    have asd : tile_pos.col = (to2d i).col := by omega
    by_cases hxy : (to2d i).row.val < tile_pos.row.val
    ·
      have := hs_row2 (to2d i).row (by omega)
      simp [← hb, asd] at this
      simp [show s⁻¹.α i = i from this]
      simp [Rectangle.toSpin]
      simp [Point.IsInside]
      omega
    ·
      have : (to2d i) = tile_pos := by ext <;> omega
      have : i = to1d tile_pos := by simpa [← to2d_injective.eq_iff]
      rw [← Equiv.Perm.eq_inv_iff_eq, Rectangle.perm_inv]
      rw [this]
      simp [Rectangle.toSpin]
      simp [Point.IsInside]
      have : row = tile_pos.row.val := by omega
      simp [this]
      simp [rotate180, rotateCalc]
      suffices s.α⁻¹ (to1d ⟨⟨row, by omega⟩, ⟨col, by omega⟩⟩) = to1d ⟨⟨row, by omega⟩, ⟨col, by omega⟩⟩ by
        have qwe : s⁻¹.α = s.α⁻¹ := by rfl
        simp [qwe]
        simp [tile_pos]
        simp [this]
      simp [← to2d_injective.eq_iff]
      refold_let tile_pos
      ext <;> (simp; omega)

lemma funtimes (row col : Nat) (hrow : row < m.val) (hcol : col < n.val) (s : Spin m n)
    (hj2 : ¬ row + 1 < m) (hj3 : col + 1 < n)
    (this : (to2d (s.α⁻¹ (to1d ⟨⟨row, by omega⟩, ⟨col, by omega⟩⟩))).col.val ≥ col)
    (hs_row2 : ∀ x, (_ : x < row) → s.α⁻¹ (to1d ⟨⟨x, by omega⟩, ⟨col, by omega⟩⟩) = to1d ⟨⟨x, by omega⟩, ⟨col, by omega⟩⟩)
    (hs_col2 : ∀ x y, (_ : x < col ∧ y < m.val) → s.α⁻¹ (to1d ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩) = to1d ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩) :
    let tile_pos := to2d (s.α⁻¹ (to1d ⟨⟨row, _⟩, ⟨col, _⟩⟩))
    let row_spin : RectSpin m n := if hr2 : row > tile_pos.row.val then
      RectSpin.fromRect ⟨tile_pos, ⟨⟨row, by omega⟩, tile_pos.col⟩, by simp, Fin.le_of_lt hr2⟩
    else
      RectSpin.fromRect ⟨⟨⟨row, by omega⟩, tile_pos.col⟩, tile_pos, by simp, by simp; fin_omega⟩

    -- moves the tile into the correct column (by spinning along a row)
    let col_spin : RectSpin m n := RectSpin.fromRect ⟨⟨⟨row, by omega⟩, ⟨col, by omega⟩⟩, ⟨⟨row, by omega⟩, tile_pos.col⟩, this, by simp⟩
    ∀ x y, (_ : x < col + 1 ∧ y < m.val) →
      (s⁻¹ * row_spin.toSpin * col_spin.toSpin).α (to1d ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩)
        = to1d ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩ := by
  have hs_row3 : ∀ x, (_ : x < row) → s⁻¹.α (to1d ⟨⟨x, _⟩, ⟨col, _⟩⟩) = to1d ⟨⟨x, _⟩, ⟨col, _⟩⟩ := hs_row2
  have hs_col3 : ∀ x y, (_ : x < col ∧ y < m.val) → s⁻¹.α (to1d ⟨⟨y, _⟩, ⟨x, _⟩⟩) = to1d ⟨⟨y, _⟩, ⟨x, _⟩⟩ := hs_col2

  intro tile_pos row_spin col_spin x y hxy
  simp only [Spin.mul_def, Equiv.invFun_as_coe, Equiv.trans_apply]
  by_cases hg : x = col
  · by_cases hg2 : y = row
    ·
      rw [← Equiv.Perm.eq_inv_iff_eq, Rectangle.perm_inv]
      rw [← Equiv.Perm.eq_inv_iff_eq]
      simp [hg, hg2]
      simp [← to2d_injective.eq_iff]
      refold_let tile_pos
      simp [Rectangle.toSpin]
      simp [Point.IsInside]
      simp [rotate180, rotateCalc]
      simp [this]
      simp [row_spin]
      split_ifs
      ·
        have hg4 : tile_pos.col.val ≠ col := by
          by_contra! hg4
          have fge : to2d (s.α⁻¹ (to1d tile_pos)) = tile_pos := by
            have := hs_row2 tile_pos.row.val (by omega)
            simpa [← hg4, ← to2d_injective.eq_iff]
          rw [to2d_injective.eq_iff, EmbeddingLike.apply_eq_iff_eq, to1d_inj] at fge
          simp only [Point.ext_iff, Fin.ext_iff] at fge
          omega
        have : tile_pos.col.val > col := by simp [tile_pos] at *; omega
        -- sorry
        simp [Rectangle.perm_inv]
        simp [Rectangle.toSpin]
        simp [Point.IsInside]
        have : tile_pos.row.val ≤ row := by omega
        simp [this]
        simp [rotate180, rotateCalc]
        ext <;> (simp; try omega)
      ·
        simp [Rectangle.perm_inv]
        simp [Rectangle.toSpin]
        simp [Point.IsInside]
        have : row ≤ tile_pos.row.val := by omega
        simp [this]
        simp [rotate180, rotateCalc]
    ·
      -- sorry -- THIS PROOF WORKS, BUT SLOW
      rw [← Equiv.Perm.eq_inv_iff_eq, Rectangle.perm_inv]
      have : y < row := by omega
      simp [hg]
      simp [hs_row3 y (by omega)]
      simp [Rectangle.toSpin]
      simp [Point.IsInside]
      simp [rotate180, rotateCalc]
      have : ¬ row ≤ y := by omega
      simp [this]
      simp [row_spin]
      split_ifs
      ·
        have hg4 : tile_pos.col.val ≠ col := by
          by_contra! hg4
          have fge : to2d (s.α⁻¹ (to1d tile_pos)) = tile_pos := by
            have := hs_row2 tile_pos.row.val (by omega)
            simpa [← hg4, ← to2d_injective.eq_iff]
          rw [to2d_injective.eq_iff, EmbeddingLike.apply_eq_iff_eq, to1d_inj] at fge
          simp only [Point.ext_iff, Fin.ext_iff] at fge
          omega
        have : tile_pos.col.val > col := by simp [tile_pos] at *; omega
        simp [Rectangle.toSpin]
        simp [Point.IsInside]
        omega
      ·
        simp [Rectangle.toSpin]
        simp [Point.IsInside]
        omega
  ·
    -- sorry -- THIS PROOF WORKS, BUT SLOW
    have : tile_pos.col.val ≥ col := by simp [tile_pos]; omega
    rw [← Equiv.Perm.eq_inv_iff_eq]
    simp [Rectangle.perm_inv]
    have : x < col ∧ y < m.val := by omega
    have := hs_col3 _ _ this
    simp [this]
    simp [Rectangle.toSpin]
    simp [Point.IsInside]
    simp [rotate180, rotateCalc]
    have : ¬ col ≤ x := by omega
    simp [this]
    simp [row_spin]
    split_ifs
    ·
      simp [Rectangle.toSpin]
      simp [Point.IsInside]
      omega
    ·
      simp [Rectangle.toSpin]
      simp [Point.IsInside]
      omega


lemma funtimes2 (row col : Nat) (hrow : row < m.val) (hcol : col < n.val) (s : Spin m n)
    (hj2 : ¬ row + 1 < m) (hj3 : ¬ col + 1 < n) (i : Fin (m * n)) (hi : (to2d (s.α⁻¹ i)) = ⟨⟨m - 1, by omega⟩, ⟨n - 1, by omega⟩⟩)
    (hs_row2 : ∀ x, (_ : x < row) → s.α⁻¹ (to1d ⟨⟨x, by omega⟩, ⟨col, by omega⟩⟩) = to1d ⟨⟨x, by omega⟩, ⟨col, by omega⟩⟩)
    (hs_col2 : ∀ x y, (_ : x < col ∧ y < m.val) → s.α⁻¹ (to1d ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩) = to1d ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩) :
    s.α⁻¹ i = i  := by
  by_cases hx : (to2d i).row.val = m - 1
  · by_cases hy : (to2d i).col.val = n - 1
    · simp [← to2d_injective.eq_iff]
      ext <;> simp_all
    · have : (to2d i).col.val < n - 1 := by omega
      have : (to2d i).col.val < col := by omega
      have := hs_col2 (to2d i).col.val (to2d i).row.val ⟨this, by omega⟩
      simpa
  ·
    have : (to2d i).row.val < row := by omega
    have := hs_row2 (to2d i).row.val this
    by_cases hy : (to2d i).col.val = n - 1
    · simp at this
      have qq : col = n - 1 := by omega
      simpa [qq, ← hy]
    · have := hs_col2 (to2d i).col.val (to2d i).row.val ⟨by omega, by omega⟩
      simpa

set_option maxHeartbeats 400000 in
def attempt4 (row col : Nat) (hrow : row < m.val) (hcol : col < n.val) (s : Spin m n)
      (hs_row : ∀ x, (_ : x < row) → s.α (to1d ⟨⟨x, by omega⟩, ⟨col, by omega⟩⟩)
        = to1d ⟨⟨x, by omega⟩, ⟨col, by omega⟩⟩)
      (hs_col: ∀ x y, (_ : x < col ∧ y < m.val) → s.α (to1d ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩)
        = to1d ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩) : {l : List (RectSpin m n) // (l.map RectSpin.toSpin).prod.α = s.α } :=
  let tile_pos := to2d (s.α⁻¹ (to1d ⟨⟨row, by omega⟩, ⟨col, by omega⟩⟩))

  have hs_row2 : ∀ x, (_ : x < row) → s.α⁻¹ (to1d ⟨⟨x, _⟩, ⟨col, _⟩⟩) = to1d ⟨⟨x, _⟩, ⟨col, _⟩⟩ := by
    intro x hx
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact hs_row x hx |>.symm
  have hs_row3 : ∀ x, (_ : x < row) → s⁻¹.α (to1d ⟨⟨x, _⟩, ⟨col, _⟩⟩) = to1d ⟨⟨x, _⟩, ⟨col, _⟩⟩ := hs_row2
    -- exact hs_row x hx |>.symm
  have hs_col2 : ∀ x y, (_ : x < col ∧ y < m.val) → s.α⁻¹ (to1d ⟨⟨y, _⟩, ⟨x, _⟩⟩) = to1d ⟨⟨y, _⟩, ⟨x, _⟩⟩ := by
    intro x y hxy
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact hs_col x y hxy |>.symm
  have hs_col3 : ∀ x y, (_ : x < col ∧ y < m.val) → s⁻¹.α (to1d ⟨⟨y, _⟩, ⟨x, _⟩⟩) = to1d ⟨⟨y, _⟩, ⟨x, _⟩⟩ := hs_col2

  have : tile_pos.col.val ≥ col := by
    -- sorry -- THIS PROOF WORKS, BUT SLOW
    by_contra! hx
    have fde : ∀ y, (_ : y < m.val) → s.α⁻¹ (to1d ⟨⟨y, by omega⟩, ⟨tile_pos.col.val, by omega⟩⟩) =
        to1d ⟨⟨y, by omega⟩, ⟨tile_pos.col.val, by omega⟩⟩ := by
      intro y hy
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact hs_col _ y ⟨hx, by omega⟩ |>.symm
    have fge : s.α⁻¹ (to1d tile_pos) = to1d tile_pos := fde tile_pos.row (by omega)
    simp_all only [Fin.eta, to1d_to2d_inverse, EmbeddingLike.apply_eq_iff_eq, to2d_to1d_inverse,
      lt_self_iff_false, tile_pos]

  if hj : row = 0 then
    let next_spin := RectSpin.fromRect ⟨⟨⟨row, by omega⟩, ⟨col, by omega⟩⟩, tile_pos, by assumption, by fin_omega⟩
    have zxc : next_spin.toSpin.α (to1d (⟨⟨row, by omega⟩, ⟨col, by omega⟩⟩)) = to1d tile_pos := by
      simp [next_spin, Rectangle.toSpin]
      -- This simp could be covered by Rectangle.corners_inside probably
      simp_all [Point.IsInside, Rectangle.validRow, Rectangle.validCol]
      apply (Rectangle.corners_rotate _).1
    let a := if hj2 : row + 1 < m then
        attempt4 (row + 1) col hj2 hcol (s⁻¹ * next_spin) (by
          -- sorry -- THIS PROOF WORKS, BUT SLOW
          intro x hx
          have : x = row := by omega
          simp only [Spin.mul_def, Equiv.invFun_as_coe, Equiv.trans_apply]
          rw [← Equiv.Perm.eq_inv_iff_eq, Rectangle.perm_inv]
          simp [this]
          simp [zxc]
          simp_all [tile_pos]
          rfl
        ) (by
          -- sorry -- THIS PROOF WORKS, BUT SLOW
          intro x y hxy
          simp only [Spin.mul_def, Equiv.invFun_as_coe, Equiv.trans_apply]
          rw [← Equiv.Perm.eq_inv_iff_eq, Rectangle.perm_inv]
          convert hs_col2 x y hxy
          -- apply asdfg
          -- apply asdfgg
          -- simp only
          -- omega
          simp [Rectangle.toSpin]
          -- This can be some lemma
          simp [Point.IsInside, Rectangle.validRow, Rectangle.validCol]
          omega
        )
      else if hj3 : col + 1 < n then
        attempt4 0 (col + 1) (by omega) hj3 (s⁻¹ * next_spin.toSpin) (by omega) (by
          -- sorry -- THIS PROOF WORKS, BUT SLOW
          intro x y hxy
          simp only [Spin.mul_def, Equiv.invFun_as_coe, Equiv.trans_apply]
          by_cases hg : x = col
          · by_cases hg2 : y = row
            · simp [hg, hg2, zxc]
              rw [← Equiv.Perm.eq_inv_iff_eq, Rectangle.perm_inv]
              simp [Rectangle.toSpin]
              simp [Point.IsInside, Rectangle.validRow, Rectangle.validCol]
              simp [hj, this]
              simp [rotate180, rotateCalc, tile_pos, hj]
              rfl
            · rw [← Equiv.Perm.eq_inv_iff_eq, Rectangle.perm_inv]
              have : y < row := by omega
              convert hs_row2 y this
              simp [Rectangle.toSpin]
              -- This can be some lemma
              simp [Point.IsInside, Rectangle.validRow, Rectangle.validCol]
              omega
          · rw [← Equiv.Perm.eq_inv_iff_eq, Rectangle.perm_inv]
            convert hs_col2 x y (by omega)
            simp [Rectangle.toSpin]
            -- This can be some lemma
            simp [Point.IsInside, Rectangle.validRow, Rectangle.validCol]
            omega
        )
      else ⟨[], by
        simp [Spin.mul_def]
        rw [Equiv.ext_iff]
        intro i
        have : row = m - 1 := by omega
        have : col = n - 1 := by omega
        -- have : tile_pos.col.val < n := tile_pos.col.2
        have : tile_pos.col.val = col := by omega
        simp [Rectangle.toSpin, Spin.one_def]
        split_ifs with hk
        · simp_all
          have : m = 1 := PNat.le_one_iff.mp hj2
          have : tile_pos.row.val = 0 := by omega
          have : (to2d (s⁻¹.α i)) = ⟨⟨0, by omega⟩, ⟨n.val - 1, by omega⟩⟩ := by
            simp [Point.IsInside] at hk
            ext <;> (simp; fin_omega)
          simp [this]
          simp [rotate180, rotateCalc]
          simp_all [tile_pos]
          simp [← this]
          have := funtimes2 row col hrow hcol s (by omega) (by omega) i
            (by simp [show m.val - 1 = 0 by omega]; exact this) (by simp_all) (by simp [*]; exact hs_col2)
          have this2 : s⁻¹.α i = i := this
          simp [this, this2]
        · simp_all
          have : m = 1 := PNat.le_one_iff.mp hj2
          have : (to2d (s⁻¹.α i)).col.val < n.val - 1 := by
            simp [Point.IsInside] at hk
            omega
          -- have : (to2d (s⁻¹.α i)).col.val < col := by omega
          have := hs_col3 (to2d (s⁻¹.α i)).col.val (to2d (s⁻¹.α i)).row.val ⟨this, by omega⟩
          simp at this
          simp_all
        ⟩
    let ha := a.1 ++ [next_spin]
    have : (ha.map RectSpin.toSpin).prod.α = s⁻¹.α := smth _
    have : (ha.map RectSpin.toSpin).reverse.prod.α = s.α := smth' _
    have : (ha.reverse.map RectSpin.toSpin).prod.α = s.α := by simp [this]
    ⟨ha.reverse, this⟩
    -- next_spin :: a
  else

    let row_spin : RectSpin m n := if hr2 : row > tile_pos.row.val then
      RectSpin.fromRect ⟨tile_pos, ⟨⟨row, by omega⟩, tile_pos.col⟩, by simp, Fin.le_of_lt hr2⟩
    else
      RectSpin.fromRect ⟨⟨⟨row, by omega⟩, tile_pos.col⟩, tile_pos, by simp, by simp; fin_omega⟩

    -- moves the tile into the correct column (by spinning along a row)
    let col_spin : RectSpin m n := RectSpin.fromRect ⟨⟨⟨row, by omega⟩, ⟨col, by omega⟩⟩, ⟨⟨row, by omega⟩, tile_pos.col⟩, this, by simp⟩

    let a := if hj2 : row + 1 < m then
      attempt4 (row + 1) col hj2 hcol (s⁻¹ * row_spin * col_spin) (by
        -- sorry -- THIS PROOF WORKS, BUT SLOW
        intro x hx
        simp [Spin.mul_def]
        by_cases hg : x = row
        ·
          simp [hg, col_spin, row_spin]
          split_ifs
          · -- sorry -- THIS PROOF WORKS, BUT SLOW
            rw [← Equiv.Perm.eq_inv_iff_eq, Rectangle.perm_inv]
            have : (⟨⟨⟨row, by omega⟩, ⟨col, by omega⟩⟩, ⟨⟨row, by omega⟩, tile_pos.col⟩, this, by simp⟩ : Rectangle m n).toSpin.α
                (to1d ⟨⟨row, by omega⟩, ⟨col, by omega⟩⟩) = to1d ⟨⟨row, by omega⟩, ⟨tile_pos.col, by omega⟩⟩ := by
              simp [Rectangle.toSpin]
              -- This can be some lemma
              simp [Point.IsInside, Rectangle.validRow, Rectangle.validCol]
              have : col ≤ tile_pos.col.val := by omega
              simp [this]
              simp [rotate180, rotateCalc]
            rw [this, ← Equiv.Perm.eq_inv_iff_eq, Rectangle.perm_inv, ← to2d_injective.eq_iff]
            refold_let tile_pos
            simp [Rectangle.toSpin]
            -- This can be some lemma
            simp [Point.IsInside, rotate180, rotateCalc]
            have : tile_pos.row.val ≤ row := by omega
            simp [this]
            ext
            · simp; omega
            · simp
          ·
            -- sorry -- THIS PROOF WORKS, BUT SLOW
            rw [← Equiv.Perm.eq_inv_iff_eq, Rectangle.perm_inv]
            have : (⟨⟨⟨row, by omega⟩, ⟨col, by omega⟩⟩, ⟨⟨row, by omega⟩, tile_pos.col⟩, this, by simp⟩ : Rectangle m n).toSpin.α
                (to1d ⟨⟨row, by omega⟩, ⟨col, by omega⟩⟩) = to1d ⟨⟨row, by omega⟩, ⟨tile_pos.col, by omega⟩⟩ := by
              simp [Rectangle.toSpin]
              -- This can be some lemma
              simp [Point.IsInside, Rectangle.validRow, Rectangle.validCol]
              have : col ≤ tile_pos.col.val := by omega
              simp [this]
              simp [rotate180, rotateCalc]
            simp [this]
            rw [← Equiv.Perm.eq_inv_iff_eq, Rectangle.perm_inv]
            apply to2d_injective
            change tile_pos = _
            simp [Rectangle.toSpin]
            -- This can be some lemma
            simp [Point.IsInside, Rectangle.validRow, Rectangle.validCol]
            have : row ≤ tile_pos.row.val := by omega
            simp [this, rotate180, rotateCalc]
        ·
          rw [← Equiv.Perm.eq_inv_iff_eq, Rectangle.perm_inv]

          have : (⟨⟨⟨row, by omega⟩, ⟨col, by omega⟩⟩, ⟨⟨row, by omega⟩, tile_pos.col⟩, this, by simp⟩ : Rectangle m n).toSpin.α
              (to1d ⟨⟨x, by omega⟩, ⟨col, by omega⟩⟩) = to1d ⟨⟨x, by omega⟩, ⟨col, by omega⟩⟩ := by
            simp [Rectangle.toSpin, Point.IsInside]
            omega
          simp [this, Spin.inv_def, col_spin, row_spin]
          split_ifs with kl
          · have hg4 : tile_pos.col.val ≠ col := by
              by_contra! hg4
              have fge : to2d (s.α⁻¹ (to1d tile_pos)) = tile_pos := by
                have := hs_row2 tile_pos.row.val (by omega)
                simpa [← hg4, ← to2d_injective.eq_iff]
              rw [to2d_injective.eq_iff, EmbeddingLike.apply_eq_iff_eq, to1d_inj] at fge
              simp only [Point.ext_iff, Fin.ext_iff] at fge
              omega
            -- rw [← Equiv.Perm.inv_eq_iff_eq]
            rw [← Equiv.Perm.eq_inv_iff_eq, Rectangle.perm_inv]
            convert hs_row2 x (by omega)
            simp [Rectangle.toSpin, Point.IsInside]
            fin_omega
          · rw [← Equiv.Perm.eq_inv_iff_eq, Rectangle.perm_inv]
            convert hs_row2 x (by omega)
            simp [Rectangle.toSpin, Point.IsInside]
            omega
      ) (by
        -- sorry -- THIS PROOF WORKS, BUT SLOW
        intro x y hxy
        simp [Spin.mul_def]
        simp [hs_col3 _ _ hxy]
        rw [← Equiv.Perm.eq_inv_iff_eq, Rectangle.perm_inv]
        have : col_spin.α (to1d ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩) = to1d ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩ := by
          simp [Rectangle.toSpin, Point.IsInside]
          omega
        simp [this, row_spin]
        split_ifs <;> (simp [Rectangle.toSpin, Point.IsInside]; fin_omega)
      )
    else if hj3 : col + 1 < n then
      attempt4 0 (col + 1) (by omega) hj3 (s⁻¹ * row_spin.toSpin * col_spin.toSpin) (by omega) (by
        convert funtimes row col hrow hcol s hj2 hj3 this hs_row2 hs_col2
      )

    else ⟨[], by
      -- simp [Spin.mul_def]
      -- rw [Equiv.ext_iff]
      -- intro i
      convert funtimes3 row col hrow hcol s hj2 hj3 this hs_row2 hs_col2
    ⟩


    let ha := a.1 ++ [col_spin, row_spin]
    have : (ha.map RectSpin.toSpin).prod.α = s⁻¹.α := smth2 _
    have : (ha.map RectSpin.toSpin).reverse.prod.α = s.α := smth2' _
    have : (ha.reverse.map RectSpin.toSpin).prod.α = s.α := by simp [this]
    ⟨ha.reverse, this⟩
    -- have : (ha.map RectSpin.toSpin).reverse.prod.α = s.α := by
    --   sorry
  -- ⟨[], by sorry⟩
termination_by (n.val - col, m.val - row)

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
