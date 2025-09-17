import Spinpossible.Solution

import Lean

def forall_eq_of_let {c : α → Sort _} (h : let a := b; c a) : ∀ a, b = a → c a := by
  intro val
  exact Eq.ndrec h

abbrev Eq.recr.{u, u_1} {α : Sort u_1} {a : α} {motive : (b : α) → b = a → Sort u}
    (refl : motive a (Eq.refl a)) {b : α} (t : b = a) : motive b t :=
  t ▸ refl

open Lean Parser Elab Tactic
elab "add_value " hyp:term : tactic => do
  withMainContext do
    let u ← Meta.mkFreshLevelMVar
    let α ← Meta.mkFreshExprMVar (some (.sort u))
    let lhs ← Meta.mkFreshExprMVar α
    let rhs ← Meta.mkFreshExprMVar α
    let mut eq ← elabTermEnsuringType hyp (some (mkApp3 (mkConst ``Eq [u]) α lhs rhs))
    let mut goal ← getMainGoal
    unless eq.isFVar do
      goal ← goal.assert `h (mkApp3 (mkConst ``Eq [u]) α lhs rhs) eq
      let (eqVar, goal') ← goal.intro1
      eq := .fvar eqVar
      goal := goal'
    let eqVar := eq.fvarId!
    let mut symm := false
    let mut var := default
    if let .fvar v ← Meta.whnf lhs then
      var := v
      symm := true
    else if let .fvar v ← Meta.whnf rhs then
      var := v
      symm := false
    else
      Meta.throwTacticEx `add_value goal "expected variable on lhs"
    if ← var.isLetVar then
      Meta.throwTacticEx `add_value goal "variable already has a value"
    let reverted := #[var, eqVar]
    let (_, goal') ← (← getMainGoal).withReverted reverted fun goal fvars => goal.withContext do
      if fvars[0]! != var then
        Meta.throwTacticEx `add_value goal "unexpected error"
      if fvars[1]! != eqVar then
        Meta.throwTacticEx `add_value goal "invalid dependencies"
      let .forallE varNm t (.forallE _ (mkApp3 (.const ``Eq [univ]) _ lhs rhs) b _) _ ← goal.getType |
        Meta.throwTacticEx `add_value goal "unexpected goal state"
      let value := if symm then rhs else lhs
      if value.hasLooseBVars then
        Meta.throwTacticEx `add_value goal "recursive substitution"
      let newType : Expr := .letE varNm t value (b.instantiate1 (mkApp2 (.const ``rfl [univ]) t (.bvar 0))) false
      let newGoal ← Meta.mkFreshExprMVar newType
      let lvl' ← Meta.getLevel b
      let recNm := if symm then ``Eq.recr else ``Eq.rec
      let motive : Expr := .lam varNm t (.lam `h (mkApp3 (.const ``Eq [univ]) t lhs rhs) b .default) .default
      let newValue := mkApp4 (.const recNm [lvl', univ]) t value motive newGoal
      goal.assign newValue
      return ((), (fvars.map some).eraseIdx! 1, newGoal.mvarId!)
    replaceMainGoal [goal']

#print Lean.Parser.Tactic.simp

syntax "simp_value" optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? " at " ident : tactic

macro_rules
  | `(tactic| simp_value $cfg:optConfig $(disch)? $[only%$o]? $[[$args,*]]? at $i:ident) =>
    `(tactic| (
      clear_value (h : $i = _)
      simp $cfg:optConfig $[$disch]? $[only%$o]? $[[$args,*]]? at h
      add_value h
    ))

macro "conv_value" &" at " a:ident arrow:" => " c:Conv.convSeq : tactic =>
  `(tactic| (
    clear_value (h : $a = _)
    conv at h => rhs; conv =>%$arrow $c
    add_value h
  ))

example : ∀ a b, (h : 25 * 3 + b = a) → a < 4 → True := by
  intro a b h
  add_value h
  intro h
  conv_value at a => simp; rw [Nat.add_comm]
  sorry

-- set_option linter.unusedVariables.analyzeTactics true

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
    (this : (s.α⁻¹ ⟨⟨row, hrow⟩, ⟨col, hcol⟩⟩).col.val ≥ col)
    (hs_row2 : ∀ x, (_ : x < row) → s.α⁻¹ ⟨⟨x, by omega⟩, ⟨col, hcol⟩⟩
      = ⟨⟨x, by omega⟩, ⟨col, hcol⟩⟩)
    (hs_col2 : ∀ x y, (_ : x < col ∧ y < m.val) → s.α⁻¹ ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩
      = ⟨⟨y, by omega⟩, ⟨x, by omega⟩⟩) :
    let tile_pos := s.α⁻¹ ⟨⟨row, _⟩, ⟨col, _⟩⟩
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
  simp only [Spin.mul_def, Spin.inv_perm, Equiv.trans_apply]
  by_cases hg : x < col
  · grind [Rectangle.spin_perm_const]
  · grind [Rectangle.corners_rotate_perm, Rectangle.spin_eq_iff, Rectangle.spin_perm_const,
      EmbeddingLike.apply_eq_iff_eq, Fin.eta]

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
    have hs_col2 (x y) (hxy : x < col ∧ y < m.val) : s.α⁻¹ ⟨⟨y, _⟩, ⟨x, _⟩⟩ = ⟨⟨y, _⟩, ⟨x, _⟩⟩ :=
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

    have hs_col2 (x y) (hxy : x < col ∧ y < m.val) : s.α⁻¹ ⟨⟨y, _⟩, ⟨x, _⟩⟩ = ⟨⟨y, _⟩, ⟨x, _⟩⟩ :=
      Equiv.Perm.eq_inv_iff_eq.mp (hs_col x y hxy |>.symm)

    have : tile_pos.col.val ≥ col := by
      by_contra hx
      absurd hs_col2 tile_pos.col.val tile_pos.row.val (by omega)
      grind -ring -linarith [Fin.eta, EmbeddingLike.apply_eq_iff_eq]

    conv_value at next_spin => simp (disch := omega) [RectSpin.fromPoints, dif_pos, cur_pos]

    simp only [zero_add, List.cons_append, List.nil_append, List.map_cons, List.map_reverse,
      List.prod_cons, List.length_cons, List.length_reverse]
    split_ifs with h1 h2
    · specialize ih1 h1
        (fun x hx => by simp only [next_spin, Fin.mk_zero', Spin.mul_def, Spin.inv_perm,
          show x = 0 by omega, Equiv.trans_apply, Rectangle.spin_eq_iff,
          Rectangle.corners_rotate_perm.1, tile_pos, cur_pos])
        (fun x y hxy => by rw [Spin.mul_def, Spin.inv_perm, Equiv.trans_apply,
          Rectangle.spin_eq_iff, Rectangle.spin_perm_const (Or.inr hxy.1), hs_col2 x y hxy])
      constructor
      · simp [← rectSpin_prod_inv_eq_reverse_prod, Spin.perm_distrib, ih1.1]
      · grw [ih1.2]
        simp [listSize, show m.val ≠ 1 by omega]
        split_ifs <;> omega
    · specialize ih2 (by omega) (by omega) (by
        intro x y hxy
        simp only [Spin.mul_def, Spin.inv_perm, Equiv.trans_apply]
        by_cases hg : x = col
        · simp_rw [show y = 0 by omega, hg]
          apply Rectangle.corners_rotate_perm.2
        · rw [hs_col2 x y (by omega), Rectangle.spin_perm_const (by fin_omega)]
      )
      constructor
      · simp [← rectSpin_prod_inv_eq_reverse_prod, Spin.perm_distrib, ih2.1]
      · grw [ih2.2]
        simp [listSize, show m.val = 1 by omega]
        split_ifs <;> omega
    · grind
  | case3 row col hrow hcol s cur_pos tile_pos hrow2 row_spin col_spin k a1 ih1 ih2 =>
    unfold l k

    have hs_row2 (x) (hx : x < row) : s.α⁻¹ ⟨⟨x, _⟩, ⟨col, _⟩⟩ = ⟨⟨x, _⟩, ⟨col, _⟩⟩ :=
      Equiv.Perm.eq_inv_iff_eq.mp (hs_row x hx |>.symm)

    have hs_col2 (x y) (hxy : x < col ∧ y < m.val) : s.α⁻¹ ⟨⟨y, _⟩, ⟨x, _⟩⟩ = ⟨⟨y, _⟩, ⟨x, _⟩⟩ :=
      Equiv.Perm.eq_inv_iff_eq.mp (hs_col x y hxy |>.symm)

    have : tile_pos.col.val ≥ col := by
      by_contra hx
      absurd hs_col2 tile_pos.col.val tile_pos.row.val (by omega)
      grind -ring -linarith [Fin.eta, EmbeddingLike.apply_eq_iff_eq]

    conv_value at col_spin => simp (disch := omega) [RectSpin.fromPoints, dif_pos, cur_pos]
    have row_spin_eq : value_of% row_spin =
        if ht : tile_pos.row.val < row then
          RectSpin.fromRect ⟨tile_pos, ⟨⟨row, hrow⟩, tile_pos.col⟩, Fin.le_of_lt ht, by simp⟩
        else
          RectSpin.fromRect ⟨⟨⟨row, hrow⟩, tile_pos.col⟩, tile_pos, Fin.not_lt.mp ht, by simp⟩ := by
      split_ifs with hr <;>
      simp (disch := omega) [RectSpin.fromPoints, dif_pos, ← Fin.val_fin_le]
    conv_value at row_spin => rw [row_spin_eq]
    clear row_spin_eq

    split_ifs with h1
    · specialize ih1 h1 (fun x hx => by
        simp only [Spin.mul_def, Spin.inv_perm, Equiv.trans_apply]
        by_cases hg : x = row
        · simp only [hg, cur_pos, col_spin, row_spin, tile_pos]
          split_ifs
          · simp [Rectangle.corners_rotate_perm.1, Rectangle.corners_rotate_perm.2]
          · simp [Rectangle.spin_eq_iff, Rectangle.corners_rotate_perm.1]
        · rw [Rectangle.spin_eq_iff,
            Rectangle.spin_perm_const (by simp only; omega), hs_row2 x (by omega)]
          unfold row_spin
          split_ifs
          · have hg4 : col ≠ tile_pos.col.val := by
              by_contra! hg4
              absurd hs_row2 tile_pos.row.val (by omega)
              grind -ring -linarith [EmbeddingLike.apply_eq_iff_eq, Fin.eta]
            rw [Rectangle.spin_perm_const (by fin_omega)]
          · rw [Rectangle.spin_perm_const (by fin_omega)]
      ) (fun x y hxy => by
        simp only [row_spin, Spin.mul_def, Spin.inv_perm, col_spin, Equiv.trans_apply,
          hs_col2 _ _ hxy, Rectangle.spin_eq_iff]
        split_ifs with hz <;>
        rw [Rectangle.spin_perm_const (by simp only; omega),
          Rectangle.spin_perm_const (by simp only; omega)])
      constructor
      · simp [← rectSpin_prod_inv_eq_reverse_prod, Spin.perm_distrib, ih1.1]
      · simp only [List.cons_append, List.nil_append, List.length_cons, List.length_reverse]
        grw [ih1.2]
        simp [listSize, show n.val ≠ col + 1 by omega, hrow2, aux2, a1, h1]
    · specialize ih2 a1 (by omega) (aux3 hrow hcol s h1 a1 this hs_row2 hs_col2)
      constructor
      · simp [← rectSpin_prod_inv_eq_reverse_prod, Spin.perm_distrib, ih2.1]
      · simp only [List.cons_append, List.nil_append, List.length_cons, List.length_reverse]
        grw [ih2.2]
        simp [listSize, show m.val = row + 1 by omega, show n.val ≠ col + 1 by omega, hrow2]
        split_ifs with hn1
        · rw [show n.val - col - 1 = 1 by omega]; omega
        · exact aux1 n row col (by omega)
  | case4 row col hrow hcol s cur_pos tile_pos hrow2 row_spin col_spin k a1 a2 ih1 ih2 =>
    unfold l k

    have hs_row2 (x) (hx : x < row) : s.α⁻¹ ⟨⟨x, _⟩, ⟨col, _⟩⟩ = ⟨⟨x, _⟩, ⟨col, _⟩⟩ :=
      Equiv.Perm.eq_inv_iff_eq.mp (hs_row x hx |>.symm)

    have hs_col2 (x y) (hxy : x < col ∧ y < m.val) : s.α⁻¹ ⟨⟨y, _⟩, ⟨x, _⟩⟩ = ⟨⟨y, _⟩, ⟨x, _⟩⟩ :=
      Equiv.Perm.eq_inv_iff_eq.mp (hs_col x y hxy |>.symm)

    have : tile_pos.col.val ≥ col := by
      by_contra hx
      absurd hs_col2 tile_pos.col.val tile_pos.row.val (by omega)
      grind -ring -linarith [Fin.eta, EmbeddingLike.apply_eq_iff_eq]

    conv_value at col_spin => simp (disch := omega) [RectSpin.fromPoints, dif_pos, cur_pos]
    have row_spin_eq : value_of% row_spin =
        if ht : tile_pos.row.val < row then
          RectSpin.fromRect ⟨tile_pos, ⟨⟨row, hrow⟩, tile_pos.col⟩, Fin.le_of_lt ht, by simp⟩
        else
          RectSpin.fromRect ⟨⟨⟨row, hrow⟩, tile_pos.col⟩, tile_pos, Fin.not_lt.mp ht, by simp⟩ := by
      split_ifs with hr <;>
      simp (disch := omega) [RectSpin.fromPoints, dif_pos, ← Fin.val_fin_le]
    conv_value at row_spin => rw [row_spin_eq]
    clear row_spin_eq

    simp [a2]
    -- TODO: this is shared with case3
    specialize ih1 a2 (by
      intro x hx
      simp only [Spin.mul_def, Spin.inv_perm, Equiv.trans_apply]
      by_cases hg : x = row
      · simp only [hg, cur_pos, col_spin, row_spin, tile_pos]
        split_ifs
        · simp [Rectangle.corners_rotate_perm.1, Rectangle.corners_rotate_perm.2]
        · simp [Rectangle.spin_eq_iff, Rectangle.corners_rotate_perm.1]
      · rw [Rectangle.spin_eq_iff,
          Rectangle.spin_perm_const (by simp only; omega), hs_row2 x (by omega)]
        unfold row_spin
        split_ifs
        · have hg4 : col ≠ tile_pos.col.val := by
            by_contra! hg4
            absurd hs_row2 tile_pos.row.val (by omega)
            grind -ring -linarith [EmbeddingLike.apply_eq_iff_eq, Fin.eta]
          rw [Rectangle.spin_perm_const (by fin_omega)]
        · rw [Rectangle.spin_perm_const (by fin_omega)]
    ) (fun x y hxy => by
        simp only [row_spin, Spin.mul_def, Spin.inv_perm, col_spin, Equiv.trans_apply,
          hs_col2 _ _ hxy, Rectangle.spin_eq_iff]
        split_ifs with hz <;>
        rw [Rectangle.spin_perm_const (by simp only; omega),
          Rectangle.spin_perm_const (by simp only; omega)])
    constructor
    · have col_spin_eq : col_spin.α = Equiv.refl _ := by
        ext i : 1
        simp [col_spin, Rectangle.toSpin, Point.IsInside, rotate180, rotateCalc]
        intros
        ext <;> fin_omega
      simp [← rectSpin_prod_inv_eq_reverse_prod, Spin.perm_distrib, ih1.1, col_spin_eq]
    · grw [ih1.2]
      simp [listSize, show n.val = col + 1 by omega, show m.val ≠ 1 by omega]
      omega
  | case5 row col hrow hcol s _ tile_pos hrow2 row_spin col_spin k a1 a2 ih1 ih2 =>
    unfold l k

    have hs_row2 (x) (hx : x < row) : s.α⁻¹ ⟨⟨x, _⟩, ⟨col, _⟩⟩ = ⟨⟨x, _⟩, ⟨col, _⟩⟩ :=
      Equiv.Perm.eq_inv_iff_eq.mp (hs_row x hx |>.symm)

    have hs_col2 (x y) (hxy : x < col ∧ y < m.val) : s.α⁻¹ ⟨⟨y, _⟩, ⟨x, _⟩⟩ = ⟨⟨y, _⟩, ⟨x, _⟩⟩ :=
      Equiv.Perm.eq_inv_iff_eq.mp (hs_col x y hxy |>.symm)

    simp [a2, a1, Spin.one_def]

    have hb : col = tile_pos.col.val := by
      by_contra! hx
      absurd hs_col2 tile_pos.col.val tile_pos.row.val (by omega)
      grind [EmbeddingLike.apply_eq_iff_eq, Fin.eta]
    have hc : row = tile_pos.row.val := by
      by_contra! hx
      absurd hs_row2 tile_pos.row.val (by omega)
      grind [EmbeddingLike.apply_eq_iff_eq, Fin.eta]
    ext i : 1
    by_cases hx : i.col.val < col
    · simpa using hs_col i.col i.row (by omega) |>.symm
    · have : i.col.val = col := by omega
      by_cases i.row.val < row
      · simpa [← this] using hs_row i.row.val (by omega) |>.symm
      · grind [Fin.eta, Equiv.Perm.apply_inv_self]

-- TODO: figure out how to avoid this popping up
lemma Spin.symm_inv (s : Spin m n) : Equiv.symm s.α = s.α⁻¹ := rfl

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
      grind [Finset.length_toList, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  suffices h2 : ∃ l : List (RectSpin m n), (l.map RectSpin.toSpin).prod.α = b.α⁻¹ ∧
      l.length ≤ 2 * m * n - (m + n) by
    obtain ⟨l2, hl2⟩ := h2
    obtain ⟨l1, hl1⟩ := h3 ((l2.map RectSpin.toSpin).prod.u ∘ (b.α.symm))
    have zz : (List.map RectSpin.toSpin (l1 ++ l2)).prod = b⁻¹ := by
      simp [hl1, hl2.1, Spin.inv_def, Spin.mul_def, ← Spin.symm_inv]
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
  convert buildBasicPermSolution_correct 0 0 m.2 n.2 b⁻¹ (by omega) (by omega) using 2
  simp only [listSize, zero_add, tsub_zero, ↓reduceIte]
  split_ifs with h7 h8
  · rw [h7, h8]
  · rw [h7]; omega
  · cases m.val <;> cases _ : n.val <;> grind [PNat.ne_zero]
