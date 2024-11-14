import Spinpossible.Prop2
import Spinpossible.Lemma1

def Spin.inv (x : Spin m n) : Spin m n := ⟨x.α.symm, fun i => -x.u (x.α.toFun i)⟩

instance : Inv (Spin m n) := ⟨Spin.inv⟩

theorem Spin.mul_assoc (x y z : Spin m n) : x * y * z = x * (y * z) := by
  ext
  · rw [Equiv.ext_iff]; exact fun _ ↦ rfl
  · funext; exact add_assoc ..

theorem Spin.one_mul (x : Spin m n) : 1 * x = x := by
  ext
  · rfl
  · funext; simp [mul_def]; rfl

theorem Spin.mul_one (x : Spin m n) : x * 1 = x := by
  ext
  · rfl
  · funext; exact ((self_eq_add_right.mpr) rfl).symm

theorem Spin.inv_mul_cancel (x : Spin m n) : x⁻¹ * x = 1 := by
  ext
  · rw [Equiv.ext_iff]; exact Equiv.apply_symm_apply _
  · simp [Inv.inv, Spin.inv, mul_def]; rfl

instance : Group (Spin m n) where
  mul_assoc := Spin.mul_assoc
  one_mul := Spin.one_mul
  mul_one := Spin.mul_one
  inv_mul_cancel := Spin.inv_mul_cancel



open scoped CharTwo

lemma prod_eq_refl_of_refl2 {l : List (Spin m n)} :
    l.prod.α = (l.map (fun s => (s.α : Equiv.Perm _))).reverse.prod  := by
  induction' l with head tail ih
  · rfl
  · simp_all [Spin.mul_def, perm.mul_def, Equiv.Perm.mul_def]

lemma prod_eq_refl_of_refl {l : List (Spin m n)} (h : ∀ w ∈ l, w.α = Equiv.refl _) :
    l.prod.α = Equiv.refl _  := by
  induction' l with head tail ih
  · rfl
  · simp_all [Spin.mul_def, perm.mul_def]

lemma ZMod.cases_two (a : ZMod 2) : a = 0 ∨ a = 1 :=
  match a with
  | 0 => Or.inl rfl
  | 1 => Or.inr rfl

attribute [-instance] NeZero.charZero_one -- saves about 0.75s

lemma Corollary1.aux1 {s : Spin m n} {l k : List (Spin m n)} (hl : l.prod.α = s.α)
    (hk : k = (List.finRange (↑m * ↑n)).filterMap (
      fun isp ↦
      if l.prod.u isp ≠ s.u isp
      then some ⟨Equiv.refl _, fun j ↦ if isp = j then 1 else 0⟩
      else none)
    ) : (l ++ k).prod = s := by
  simp only [List.prod_append, Spin.mul_def, Equiv.invFun_as_coe]
  have k_refl : ∀ w ∈ k, w.α = Equiv.refl _ := by aesop
  have k_prod_refl : k.prod.α = Equiv.refl _ := prod_eq_refl_of_refl k_refl
  ext
  · exact k_prod_refl ▸ hl
  · funext i
    simp only [hl, Equiv.refl_symm, Equiv.refl_apply]
    have bam : k.prod.u i = (k.map (fun x => x.u i)).sum := by
      clear hk k_prod_refl
      induction' k with head tail ih
      · rw [List.prod_nil, Spin.one_def, List.map_nil, List.sum_nil]
      · have : ∀ w ∈ tail, w.α = Equiv.refl _ := by
          intro w hw
          exact k_refl _ (List.mem_cons_of_mem head hw)
        simp [Spin.mul_def, prod_eq_refl_of_refl this, ih this]
    have : l.prod.u i = s.u i ∨ l.prod.u i = s.u i + 1 := by
      cases (l.prod.u i).cases_two <;> cases (s.u i).cases_two <;> simp [*]
    rcases this with h2 | h2
    · have : ∀ e ∈ k, e.u i = 0 := by aesop
      simp [k_prod_refl, h2, bam, List.map_eq_map_iff.mpr this]
    · simp only [k_prod_refl, Equiv.refl_symm, Equiv.refl_apply, h2, bam]
      apply add_eq_of_eq_add_neg
      simp only [CharTwo.neg_eq, add_right_inj]

      have k_nodup : k.Nodup := by
        refine hk ▸ List.Nodup.filterMap ?_ (List.nodup_finRange _)
        intro a1 a2 s hs1 hs2
        simp only [ite_not, Option.mem_def,
          Option.ite_none_left_eq_some, Option.some.injEq] at hs1 hs2
        have := hs1.2 ▸ hs2.2
        simp only [Spin.mk.injEq, true_and] at this
        symm;
        simpa using congr($this a1)

      let x_i_def : Spin m n := ⟨Equiv.refl _, fun j ↦ if i = j then 1 else 0⟩
      have x_i_in_k : x_i_def ∈ k := by
        apply (hk ▸ List.mem_filterMap).mpr
        use i
        simp [h2]
      obtain ⟨a, ha1, ha2⟩ := List.getElem_of_mem x_i_in_k

      set k' := List.map (fun x ↦ x.u i) k
      have k_length : k'.length = k.length := List.length_map k _
      have k'_cond : ∀ (y : Fin k'.length), k'[y.val] = 1 → y = a := by
        intro y hy
        have : k[y] = x_i_def := by
          unfold x_i_def
          have : k[y] ∈ k := List.getElem_mem _
          nth_rw 1 [hk] at this
          simp only [ite_not, List.mem_filterMap, List.mem_finRange,
            Option.ite_none_left_eq_some, Option.some.injEq, true_and] at this
          obtain ⟨x, -, hx⟩ := this
          ext
          · simp [← hx]
          · have : x = i := by
              simp_rw [k', List.getElem_map] at hy
              simpa [hy] using congr(Spin.u $hx i)
            exact this ▸ congr(Spin.u $hx).symm
        by_contra! h
        absurd k_nodup
        apply List.not_nodup_of_get_eq_of_ne k ⟨a, ha1⟩ ⟨y, k_length ▸ y.2⟩
        · simp [ha2, ← Fin.getElem_fin, this]
        · exact Fin.ne_of_val_ne h.symm
      simp only [Finset.sum_list_count, nsmul_eq_mul]
      have k'_one : 1 ∈ k' := by
        have : k'[a] = 1 := by simp [k', ha2]
        exact this ▸ List.getElem_mem _
      have : List.count 1 k' = 1 := by
        have : ¬List.Duplicate 1 k' := by
          by_contra! h
          obtain ⟨b1, b2, _, hb⟩ := List.duplicate_iff_exists_distinct_get.mp h
          simp only [List.get_eq_getElem] at hb
          have hb1 := k'_cond b1 hb.1.symm
          have hb2 := k'_cond b2 hb.2.symm
          simp only at hb1 hb2
          omega
        have := List.duplicate_iff_two_le_count.mpr.mt this
        have := List.count_pos_iff.mpr k'_one
        omega
      rw [Finset.sum_eq_single 1 ?_ ?_ ]
      · rw [this, mul_one, Nat.cast_one]
      · intro b _ hb
        rw [b.cases_two.resolve_right hb, mul_zero]
      · intro h
        absurd h
        exact List.mem_toFinset.mpr k'_one

lemma rectangle_toSpin_injective {m n : PNat}
    : Function.Injective (Rectangle.toSpin : Rectangle m n -> _)
  | r1, r2, h => by
    have app := congr(Spin.u $h)
    simp only [Rectangle.toSpin, Spin.mul_def] at app
    apply rect_eq_if_corners_inside
    · by_contra! h
      have := congr($app (to1d r1.topLeft))
      simp [r1.corners_inside, r1.corners_rotate, h] at this
    · by_contra! h
      have := congr($app (to1d r2.topLeft))
      simp [r2.corners_inside, r2.corners_rotate, h] at this
    · by_contra! h
      have := congr($app (to1d r1.bottomRight))
      simp [r1.corners_inside, r1.corners_rotate, h] at this
    · by_contra! h
      have := congr($app (to1d r2.bottomRight))
      simp [r2.corners_inside, r2.corners_rotate, h] at this


def mySet (m n : PNat) := (SpinSet 1 1 m n ∪ SpinSet 1 2 m n)
  |>.map ⟨fun x => x.toSpin, rectangle_toSpin_injective⟩

open scoped CharTwo -- useul since orient is in `ZMod 2` (specifically `CharTwo.two_eq_zero`)

lemma blah5 (h : p.IsInside ⟨a, a, Fin.le_refl _, Fin.le_refl _⟩) :
    rotate180 p ⟨a, a, Fin.le_refl _, Fin.le_refl _⟩ = p := by
  simp [rotate180, rotateCalc, to2d, to1d]
  dsimp [Point.IsInside] at h
  congr
  · rw [show (p.1 : Nat) = p.row from rfl]
    omega
  · rw [show (p.2 : Nat) = p.col from rfl]
    omega

def Point.IsAdjacent (p1 p2 : Point m n) : Prop :=
  (p1.row = p2.row ∧ (p1.col.val + 1 = p2.col.val ∨ p2.col.val + 1 = p1.col.val)) ∨
  (p1.col = p2.col ∧ (p1.row.val + 1 = p2.row.val ∨ p2.row.val + 1 = p1.row.val))

lemma Point.IsAdjacent.symm {p1 p2 : Point m n} (_ : p1.IsAdjacent p2) : p2.IsAdjacent p1 := by
  dsimp only [Point.IsAdjacent] at *
  omega

def Equiv.Perm.IsAdjacentSwap (perm: Equiv.Perm (Point m n)) : Prop :=
  let x := perm.support
  if h : x.card = 2 then
    have : x.toList.length = 2 := h ▸ Finset.length_toList _
    have : perm.IsSwap := Equiv.Perm.card_support_eq_two.mp h
    let a := x.toList[0]
    let b := x.toList[1]
    Point.IsAdjacent a b
  else
    False

def Equiv.Perm.IsAdjacentSwap2 {m n : PNat} (perm: Equiv.Perm (Fin (m * n))) : Prop :=
  let x := perm.support
  if h : x.card = 2 then
    have : x.toList.length = 2 := h ▸ Finset.length_toList _
    have : perm.IsSwap := Equiv.Perm.card_support_eq_two.mp h
    let a := to2d x.toList[0]
    let b := to2d x.toList[1]
    Point.IsAdjacent a b
  else
    False

lemma somethingj {a b : Point m n} (h : (to1d a) ≤ (to1d b)) (h2 : a.IsAdjacent b) :
    a.row ≤ b.row ∧ a.col ≤ b.col := by
  dsimp [to1d] at h;
  cases c : h2 <;> cases c <;> simp_all


lemma somethingk4{p1 p2 : Point m n} {r : Rectangle m n} (h : p1.IsAdjacent p2)
  (h4 : r.topLeft = p1 ∧ r.bottomRight = p2) :
    ∀ p3 : Point m n, p3.IsInside r ↔ (p3 = p1 ∨ p3 = p2)
    := by
  intro p3
  constructor
  ·
    by_contra! k
    have := Point.ext_iff.mpr.mt k.2.1
    have := Point.ext_iff.mpr.mt k.2.2
    simp [Point.IsInside, Point.IsAdjacent, h4] at *
    omega
  · intro hx
    have := h4.1 ▸ h4.2 ▸ r.validCol
    have := h4.1 ▸ h4.2 ▸ r.validRow
    simp [Point.IsInside, Point.IsAdjacent, h4] at *
    rcases hx with rfl | rfl <;> omega

lemma somethingk5 {p1 p2 : Point m n} {r : Rectangle m n} (h : p1.IsAdjacent p2)
  (h4 : r.topLeft = p1 ∧ r.bottomRight = p2) (h2 : to1d p1 ≤ to1d p2) :
    r.toSpin.α = Equiv.swap (to1d p1) (to1d p2)
    := by
  apply Equiv.coe_inj.mp
  funext j
  simp [Rectangle.toSpin]
  split_ifs with h7
  · simp [Equiv.swap, Equiv.swapCore]
    have := somethingj h2 h
    split_ifs with h8 h9
    · simp_all [rotate180, rotateCalc]
    · congr 1
      simp_all [rotate180, rotateCalc]
      ext <;> (simp; omega)
    · have := somethingk4 h h4 (to2d j)  |>.mp h7
      rcases this with h9 | h9
      · have := congr(to1d $h9)
        simp at this
        omega
      · have := congr(to1d $h9)
        simp at this
        omega
  · have := somethingj h2 h
    have := somethingk4 h h4 (to2d j) |>.mpr.mt h7
    rw [Equiv.swap_apply_of_ne_of_ne]
    · by_contra; simp_all
    · by_contra; simp_all

lemma blahj {l : List α} {x : α}(h : l.length = 2) (h : x ∈ l) : x = l[0] ∨ x = l[1] := by
  let gg := [l[0], l[1]]
  have qw : ∀ e ∈ gg, e = l[0] ∨ e = l[1] := fun e a ↦ List.mem_pair.mp a
  have : gg = l := by
    refine List.ext_get? ?_
    intro y
    match y with
    | 0 => aesop
    | 1 => aesop
    | _ + 2 => aesop
  exact qw _ (this ▸ h)

lemma somethingk6 [DecidableEq α] [Fintype α] (p : Equiv.Perm α) (h : p.support.toList.length = 2) :
    Equiv.swap (p.support.toList[0]) (p.support.toList[1]) = p := by
  have : p.support.card = 2 := h ▸ (Finset.length_toList _).symm
  let ⟨l1, l2, hl⟩ : p.IsSwap := Equiv.Perm.card_support_eq_two.mp this
  have : l1 = p.support.toList[0] ∨ l1 = p.support.toList[1] := blahj h (by simp_all)
  have : l2 = p.support.toList[0] ∨ l2 = p.support.toList[1] := blahj h (by simp_all)

  rcases this with u | u
  · rw [Equiv.swap_comm, ← u]
    convert hl.2.symm
    exact (u ▸ this).resolve_left hl.1 |>.symm
  · convert hl.2.symm
    · exact (u ▸ this).resolve_right hl.1 |>.symm
    · exact u.symm

-- I think this can be an iff and then reused more
-- UPDATE: somethink99
lemma somethink7 (h : r ∈ SpinSet 1 2 m n) : r.topLeft.IsAdjacent r.bottomRight := by
  simp [SpinSet, rectangleSet_cond_iff] at h
  simp [Point.IsAdjacent]
  have : _ ∧ _ := ⟨r.validRow, r.validCol⟩
  omega

lemma somethink8 (h : r ∈ SpinSet 1 2 m n) (h2 : Point.IsInside p r): r.topLeft = p ∨ r.bottomRight = p := by
  simp [SpinSet, rectangleSet_cond_iff] at h
  simp [Point.IsInside] at h2
  have : _ ∧ _ := ⟨r.validRow, r.validCol⟩
  simp [Point.ext_iff]
  omega

lemma somethink9 [DecidableEq α] [Fintype α]  {i j : Nat} (p : Equiv.Perm α) (h : i < p.support.card ∧ j < p.support.card) (h2 : i ≠ j) :
    have : i < p.support.toList.length := (Finset.length_toList _).symm ▸ h.1
    have : j < p.support.toList.length := (Finset.length_toList _).symm ▸ h.2
    p.support.toList[i] ≠ p.support.toList[j] := by
  have : i < p.support.toList.length := (Finset.length_toList _).symm ▸ h.1
  have : j < p.support.toList.length := (Finset.length_toList _).symm ▸ h.2
  have : p.support.toList.Nodup := Finset.nodup_toList _
  exact List.Nodup.getElem_inj_iff this |>.mp.mt h2

lemma somethink6 [DecidableEq α] [Fintype α] {x : α} {p : Equiv.Perm α}:
    x ∈ p.support ↔ x ∈ p.support.toList := by
  simp_all only [Equiv.Perm.mem_support, ne_eq, Finset.mem_toList]


lemma somethink99 (h : r.topLeft.IsAdjacent r.bottomRight) : r ∈ SpinSet 1 2 m n := by
  simp [SpinSet, rectangleSet_cond_iff]
  simp [Point.IsAdjacent] at h
  have : _ ∧ _ := ⟨r.validRow, r.validCol⟩
  omega


lemma mod_add_one_ne_zero_implies_lt {a b : ℕ} (h : (a + 1) % b ≠ 0) (hb : b ≠ 0) : b > a % b + 1 := by
  let c := a % b
  have h1 : (a + 1) % b = (c + 1) % b := by
    simp [c]
  have h2 : (c + 1) % b ≠ 0 := h1.symm ▸ h
  have h3 : c < b := Nat.mod_lt a (by omega)
  have h4 : c + 1 ≤ b := Nat.succ_le_of_lt h3
  cases Nat.lt_or_eq_of_le h4 with
  | inl h5 =>
    exact h5
  | inr h6 =>
    rw [h6] at h2
    have h7 : b % b = 0 := Nat.mod_self b
    rw [h7] at h2
    contradiction


set_option linter.haveLet 0 in
set_option maxHeartbeats 400000 in
example (m n : PNat) : Subgroup.closure ((mySet m n).toSet) = ⊤ := by
  let set1 : Set (Equiv.Perm (Fin (m * n))) := (SpinSet 1 2 m n).image (fun x => x.toSpin.α) |>.toSet

  have set1_swap : ∀ e ∈ set1, e.IsSwap := by
    intro e he
    simp [set1, SpinSet] at he
    obtain ⟨a, ha1, ha2⟩ := he
    use (to1d a.topLeft), (to1d a.bottomRight)
    simp [rectangleSet_cond_iff] at ha1
    have : _ ∧ _ := ⟨a.validRow, a.validCol⟩
    constructor
    · simp [to1d_inj, Point.ext_iff]
      omega
    · simp [Rectangle.toSpin] at ha2
      apply Equiv.coe_inj.mpr at ha2
      simp only [Equiv.coe_fn_mk, funext_iff] at ha2
      apply Equiv.coe_inj.mp
      simp [funext_iff]
      intro x
      have := ha2 x
      split_ifs at this with hv
      · rw [← this]
        rw [Equiv.swap_apply_def]
        have : to2d x = a.topLeft ∨ to2d x = a.bottomRight := by
          simp [Point.IsInside] at hv
          simp [Point.ext_iff]
          omega
        rcases this with hr | hr
        · have : x = to1d a.topLeft := by simpa using congr(to1d $hr)
          simp [this, rotate180, rotateCalc]
        · have z1 : x = to1d a.bottomRight := by simpa using congr(to1d $hr)
          have z2: a.topLeft ≠ a.bottomRight := by
            simp [Point.ext_iff]
            omega
          simp [z1, z2.symm, rotate180, rotateCalc]
          ext <;> (simp; omega)
      · have wq : x ≠ (to1d a.topLeft) := by
          by_contra g
          replace := congr(to2d $g)
          simp_all [a.corners_inside]
        have wq2 : x ≠ (to1d a.bottomRight) := by
          by_contra g
          replace := congr(to2d $g)
          simp_all [a.corners_inside]
        rw [Equiv.swap_apply_of_ne_of_ne wq wq2]
        exact this.symm

  let x1 : SimpleGraph (Fin (m * n)) := SimpleGraph.fromRel (fun x y => Equiv.swap x y ∈ set1)
  have ff : x1.Connected := by
    apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
    use 0
    intro v
    refine SimpleGraph.Walk.reachable ?h.p
    by_cases h : v = 0
    · rw [h]
    ·
      replace h : v.val ≠ 0 := Fin.val_eq_val v 0 |>.mp.mt (by omega)
      replace h : v.val > 0 := by omega
      have : _ ∧ _ := ⟨m.2, n.2⟩
      have q1 : m.val ≥ 1 := NeZero.one_le
      have q2 : n.val ≥ 1 := NeZero.one_le
      have : m.val * n.val ≥ m.val := Nat.le_mul_of_pos_right _ q2
      let rec build_walk_horiz (row col : Nat) (hrow : row < m.val) (hcol : col < n.val) :
          x1.Walk (to1d (Point.mk ⟨row, hrow⟩ ⟨col, hcol⟩)) (to1d (Point.mk ⟨row, hrow⟩ ⟨n.val - 1, by omega⟩)) :=
        if ht : col = n.val - 1 then
          SimpleGraph.Walk.nil.copy rfl (by simp [ht])
        else
          let tail := build_walk_horiz row (col + 1) hrow (by omega)
          have edge : x1.Adj (to1d (Point.mk ⟨row, hrow⟩ ⟨col, hcol⟩)) (to1d (Point.mk ⟨row, hrow⟩ ⟨col + 1, by omega⟩)) := by
            simp [x1]
            left
            simp [set1]
            let a : Point m n := (Point.mk ⟨row, hrow⟩ ⟨col, hcol⟩)
            let b : Point m n := (Point.mk ⟨row, hrow⟩ ⟨col + 1, by omega⟩)
            have ew : to1d a ≤ to1d b := by simp [to1d, a, b]
            have ew2 : a.IsAdjacent b := by simp [a, b, Point.IsAdjacent]
            have := somethingj ew ew2
            let r : Rectangle m n := ⟨a, b, by omega, by omega⟩
            have := somethingk5 (r := r) ew2 (by simp) ew
            use r
            simp [this, a, b]
            exact somethink99 (by simp [r]; exact ew2)
          SimpleGraph.Walk.cons edge tail
      let rec build_walk_full (z : Nat) (hz : z ≤ v.val) : x1.Walk ⟨z, by omega⟩ v :=
        if ht : z = v.val then
          SimpleGraph.Walk.nil.copy rfl (by simp [ht])
        else if hcol : (z + 1) % n.val ≠ 0 then
          have hcol' : z / n.val = (z + 1) / n.val := by
            simp [Nat.succ_div]
            omega
          have : z % n.val < n.val := Nat.mod_lt z (by omega)
          have : (z + 1) % n.val < n.val := Nat.mod_lt _ (by omega)
          have : (z + 1) % n.val > 0 := by omega
          have hcol'' : n.val > z % n.val + 1 := mod_add_one_ne_zero_implies_lt hcol (by omega)
          have hcol''' : ¬(n.val ≤ z % n.val + 1) := by omega
          let a : Fin (m * n) := ⟨z, by omega⟩
          let b : Fin (m * n) := ⟨z + 1, by omega⟩
          have ew : to1d (to2d a) ≤ to1d (to2d b) := by simp [a, b]
          have ew2 : (to2d a).IsAdjacent (to2d b) := by
            simp [Point.IsAdjacent]
            left
            set a_row := (to2d a).row
            set a_col := (to2d a).col
            set b_row := (to2d b).row
            set b_col := (to2d b).col
            have a1 : a_row.val = z / n.val := by simp [a_row, to2d]
            have a2 : b_row.val = (z + 1) / n.val := by simp [b_row, to2d]
            have : a_row.val = b_row.val := a1 ▸ hcol' ▸ a2
            simp [Fin.ext_iff, this]
            left
            have b1 : a_col.val = z % n.val := by simp [a_col, to2d]
            have b2 : b_col.val = (z + 1) % n.val := by simp [b_col, to2d]
            rw [b1, b2]
            rw [@Nat.add_mod_eq_ite]
            have : 1 % n.val = 1 := Nat.one_mod_eq_one.mpr (by omega)
            simp [this]
            simp [hcol''']
          have edge : x1.Adj ⟨z, by omega⟩ ⟨z + 1, by omega⟩ := by
            simp [x1]
            left
            simp [set1]
            have := somethingj ew ew2
            use ⟨to2d a, to2d b, by omega, by omega⟩
            constructor
            · exact somethink99 ew2
            · convert somethingk5  ew2 ?_ ew
              · simp [a]
              · simp [b]
              · simp

          let tail := build_walk_full (z + 1) (by omega)
          SimpleGraph.Walk.cons edge tail
        else
          have : z % n.val < n.val := Nat.mod_lt z (by omega)
          have : (z + 1) % n.val = 0 := by omega

          have : z + 1 ≤ n.val * (m.val - 1) := by
            rw [← @Nat.dvd_iff_mod_eq_zero] at this
            obtain ⟨w1, w2⟩ := this
            have w3 : z + 1 < m.val * n.val := by omega
            have : w1 < m.val := by
              by_contra! p
              have : m.val * n.val ≤ w1 * n.val := Nat.mul_le_mul_right _ p
              have : z + 1 <  n.val * w1 := by linarith
              omega
            have : w1 ≤ (m.val - 1) := by omega
            have : n.val * w1 ≤ n.val * (↑m - 1) := Nat.mul_le_mul_left _ this
            omega
          have : n.val * (m.val - 1) + n.val = m.val * n.val := by
            rw [Nat.mul_sub_one, mul_comm]
            refine Nat.sub_add_cancel ?_
            exact Nat.le_mul_of_pos_left _ q1
          let a : Fin (m * n) := ⟨z, by omega⟩
          let b : Fin (m * n) := ⟨z + n.val, by omega⟩
          have ew : to1d (to2d a) ≤ to1d (to2d b) := by simp [a, b]
          have ew2 : (to2d a).IsAdjacent (to2d b) := by
            simp [Point.IsAdjacent]
            right
            have : (to2d a).row.val = z / n.val := by simp [to2d, a]
            have a2 : (to2d b).row.val = (z + n.val) / n.val := by simp [b, to2d]
            have a3 : (z + n.val) / n.val = z / n.val + 1 := Nat.add_div_right z q2
            constructor
            ·
              have qw1 : (to2d a).col.val = z % n.val := by simp [to2d, a]
              have qw2 : (to2d b).col.val = z % n.val := by simp [to2d, a]
              simp [Fin.ext_iff, qw1, qw2]
            · left
              simp [this, a2, a3]
          have edge : x1.Adj ⟨z, by omega⟩ ⟨z + n.val, by omega⟩ := by
            simp [x1]
            left
            simp [set1]
            have := somethingj ew ew2
            use ⟨to2d a, to2d b, by omega, by omega⟩
            constructor
            · exact somethink99 ew2
            · convert somethingk5  ew2 ?_ ew
              · simp [a]
              · simp [b]
              · simp

          let tail := build_walk_full (z + 1) (by omega)
          have : (z + 1) < m.val * n.val := by omega
          have := (Nat.div_lt_iff_lt_mul q2).mpr this
          let temp := build_walk_horiz ((z + 1) / n.val) 0 this (by omega)
          have re1 : (to1d (⟨⟨(z + 1) / n.val, by omega⟩, ⟨0, by omega⟩⟩ : Point m n)) = ⟨z + 1, by omega⟩ := by
            ext
            simp [to1d, a]
            refine Nat.div_mul_cancel ?_
            exact Nat.dvd_of_mod_eq_zero ‹_›
          have re2 : (to1d (⟨⟨(z + 1) / n.val, by omega⟩, ⟨n.val - 1, by omega⟩⟩ : Point m n)) = ⟨z + n.val, by omega⟩ := by
            ext
            simp [to1d, a]
            rw [Nat.div_mul_cancel ?_]
            · omega
            · exact Nat.dvd_of_mod_eq_zero ‹_›
          let tail2 : x1.Walk ⟨z + 1, by omega⟩ ⟨z + n.val, by omega⟩ := temp.copy re1 re2
          let walk1 := tail2.reverse.append tail

          SimpleGraph.Walk.cons edge walk1

      let w := build_walk_full 0 (by omega)
      exact w
  have top := transpositions_generate_symm_group_iff_connected_graph (E := set1) set1_swap |>.mpr ff

  have : ∀ s : Spin m n, ∃ l : List (Equiv.Perm (Fin (m * n))),
    (∀ x ∈ l, x.IsAdjacentSwap2) ∧ l.prod = s.α
    := by
    intro s
    have : (s.α : Equiv.Perm _) ∈ Subgroup.closure set1 := by rw[top]; trivial
    let ⟨l, hl1, hl2⟩ := Subgroup.exists_list_of_mem_closure (s := set1) this
    use l
    refine ⟨?_, hl2⟩
    intro x hx
    have yo := hl1 x hx
    have : x⁻¹ ∈ set1 → x ∈ set1 := by
      intro he
      exact isSwap_inv_eq_self' (set1_swap _ he) ▸ he
    have := yo.imp_right this
    have : x ∈ set1 := or_self_iff.mp this
    simp [Equiv.Perm.IsAdjacentSwap2]
    have sw := set1_swap _ this
    use sw
    simp [set1] at this
    obtain ⟨a, ha1, ha2⟩ := this
    have : x.support.card = 2 := Equiv.Perm.card_support_eq_two.mpr sw
    have : x.support.toList.length = 2 := this ▸ Finset.length_toList _
    set b := to2d x.support.toList[0]
    set c := to2d x.support.toList[1]
    simp [Rectangle.toSpin] at ha2
    apply Equiv.coe_inj.mpr at ha2
    simp only [Equiv.coe_fn_mk, funext_iff] at ha2
    have e1 := ha2 (to1d b)
    simp at e1
    split_ifs at e1 with hj
    ·
      have e2 := ha2 (to1d c)
      simp at e2
      split_ifs at e2 with hk
      ·
        have := somethink8 ha1 hj
        have := somethink8 ha1 hk
        have : (to1d b) ≠ (to1d c) := by
          simp [b, c]
          apply somethink9 x (by omega) (by omega)
        have : b ≠ c := by simpa using this
        have : (a.topLeft = b ∧ a.bottomRight = c) ∨ (a.topLeft = c ∧ a.bottomRight = b) := by
          aesop
        rcases this with hr | hr
        · exact hr.1 ▸ hr.2 ▸ somethink7 ha1
        · exact hr.1 ▸ hr.2 ▸ somethink7 ha1 |>.symm
      · absurd e2
        clear e2
        have : x (to1d c) ≠ to1d c := by
          apply Equiv.Perm.mem_support.mp
          simp only [to1d_to2d_inverse, c]
          exact somethink6.mpr (List.getElem_mem _)
        exact this.symm
    · absurd e1
      clear e1
      have : x (to1d b) ≠ to1d b := by
        apply Equiv.Perm.mem_support.mp
        simp only [to1d_to2d_inverse, b]
        exact somethink6.mpr (List.getElem_mem _)
      exact this.symm
  have : ∀ s : Spin m n, ∃ l : List (Spin m n), l.prod.α = s.α ∧ (∀ x ∈ l, x ∈ mySet m n) := by
    intro s
    let ⟨l, hl, hl2⟩ := this s
    have zz : ∀ x ∈ l, x.support.card = 2 := by
      intro x hi
      have qq := hl _ hi
      unfold Equiv.Perm.IsAdjacentSwap2 at qq
      aesop
    let l3 : List ({x : Point m n × Point m n // x.1.IsAdjacent x.2}) := l.attach.map (fun ⟨i, hi⟩ =>
      have : i.support.toList.length = 2 := (zz _ hi) ▸ Finset.length_toList _
      let a := to2d i.support.toList[0]
      let b := to2d i.support.toList[1]
      have adj : a.IsAdjacent b := by simp_all [Equiv.Perm.IsAdjacentSwap2]
      ⟨(a,b), adj⟩
    )
    let y' : List (Rectangle m n) := l3.map (fun ⟨(a,b), adj⟩ =>
      if h : (to1d a) ≤ (to1d b) then
        have := somethingj h adj
        ⟨a, b, by omega, by omega⟩
      else
        have : (to1d b) ≤ (to1d a) := by omega
        have := somethingj this adj.symm
        ⟨b, a, by omega, by omega⟩
    )
    -- `reverse` since Equiv.perm and Spin do multiplication in opposite directions
    let y : List (Spin m n) := y'.map (fun x => x.toSpin) |>.reverse
    use y
    constructor
    ·
      have : y.prod.α = l.prod := by
        simp [y, y', prod_eq_refl_of_refl2, Function.comp_def, apply_dite]
        have : (fun x : { x : Point m n × Point m n // x.1.IsAdjacent x.2 } ↦
          if h : to1d x.1.1 ≤ to1d x.1.2
          then
            have := somethingj h x.2
            (⟨x.1.1, x.1.2, by omega, by omega⟩ : Rectangle m n).toSpin.α
          else
            have : (to1d x.1.2) ≤ (to1d x.1.1) := by omega
            have := somethingj this x.2.symm
            (⟨x.1.2, x.1.1, by omega, by omega⟩ : Rectangle m n).toSpin.α)
          = (fun x : { x : Point m n × Point m n // x.1.IsAdjacent x.2 }  ↦
            Equiv.swap (to1d x.1.1) (to1d x.1.2)) := by
          funext i
          split_ifs with h6
          · exact somethingk5 i.2 (by simp) h6
          · rw [Equiv.swap_comm]
            exact somethingk5 i.2.symm (by simp) (by omega)
        simp at this
        simp [this, y', l3, Function.comp_def]
        have : (fun x : { x // x ∈ l } ↦
            have : x.1.support.toList.length = 2 := (zz _ x.2) ▸ Finset.length_toList _
            Equiv.swap x.1.support.toList[0] x.1.support.toList[1]) = (fun x => x.1) := by
          funext x
          apply somethingk6
          exact (zz _ x.2) ▸ Finset.length_toList _
        simp [this]
      exact this ▸ hl2
    · intro x hx
      suffices x ∈ (SpinSet 1 2 m n).map ⟨fun x => x.toSpin, rectangle_toSpin_injective⟩ from by
        unfold mySet
        simp_all
        obtain ⟨a, ha⟩ := this
        use a
        refine ⟨?_, ha.2⟩
        exact Or.inr ha.1
      simp
      simp [y] at hx
      obtain ⟨a, ha1, ha2⟩ := hx
      use a
      refine ⟨?_, ha2⟩
      simp [y'] at ha1
      obtain ⟨b1, b2, hb1, hb2, hb3⟩ := ha1
      split_ifs at hb3 <;>
      · rw [← hb3]
        simp [SpinSet, rectangleSet_cond_iff]
        simp [Point.IsAdjacent] at hb1
        have c2 := a.validRow
        have c1 := a.validCol
        simp [← hb3] at c1 c2
        omega
  rw [Subgroup.eq_top_iff']
  intro s
  apply Subgroup.exists_list_of_mem_closure2
  let ⟨l, hl1, hl2⟩ := this s
  let k : List (Spin m n) := List.finRange (m * n)
    |>.filterMap (fun isp =>
    if l.prod.u isp ≠ s.u isp then
      letI x : VN (m * n) := fun j => if isp = j then 1 else 0
      some ⟨Equiv.refl _, x⟩
    else
      none
    )

  use l ++ k
  constructor
  · intro x hx
    left
    rcases List.mem_append.mp hx with hx | hx
    · exact hl2 x hx
    · unfold mySet
      rw [@Finset.map_union]
      suffices x ∈ (SpinSet 1 1 m n).map ⟨fun x => x.toSpin, rectangle_toSpin_injective⟩ from
        Finset.mem_union_left _ this
      refine Finset.mem_map.mpr ?_
      simp
      let ⟨c1, c2, c3⟩ := List.mem_filterMap.mp hx
      simp at c3
      use ⟨to2d c1, to2d c1, Fin.le_refl _, Fin.le_refl _⟩
      constructor
      · simp [SpinSet, RectangleSet, validSpins]
      · simp [Rectangle.toSpin, ←c3.2]
        constructor
        · congr
          all_goals
            funext i
            split_ifs with j1
            · simp [blah5 j1]
            · simp
        · funext i
          have : (to2d i).IsInside ⟨to2d c1, to2d c1, Fin.le_refl _, Fin.le_refl _⟩ ↔ i = c1 := by
            dsimp [Point.IsInside]
            constructor
            · intro h11
              have : (to2d i) = (to2d c1) := by ext <;> omega
              simpa using congr(to1d $this)
            · intro h11
              rw [h11]
              omega
          split_ifs <;> simp_all
  · exact Corollary1.aux1 hl1 rfl
