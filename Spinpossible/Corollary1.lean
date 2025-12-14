import Spinpossible.Prop2
import Spinpossible.Lemma1

open scoped CharTwo

def Spin.inv (x : Spin m n) : Spin m n := ⟨x.α.symm, fun i => -x.u (x.α i)⟩

instance : Inv (Spin m n) := ⟨Spin.inv⟩

lemma Spin.inv_def (x : Spin m n) : x⁻¹ = ⟨x.α.symm, fun i => -x.u (x.α i)⟩ := rfl

theorem Spin.mul_assoc (x y z : Spin m n) : x * y * z = x * (y * z) := by
  ext : 1
  · rfl
  · simp [Spin.mul_def, add_assoc]

theorem Spin.one_mul (x : Spin m n) : 1 * x = x := by
  ext : 1
  · rfl
  · simp [mul_def]; rfl

theorem Spin.mul_one (x : Spin m n) : x * 1 = x := by
  ext : 1
  · rfl
  · exact (left_eq_add.mpr rfl).symm

theorem Spin.inv_mul_cancel (x : Spin m n) : x⁻¹ * x = 1 := by
  ext : 1
  · exact Equiv.apply_symm_apply _ _
  · simp [Inv.inv, Spin.inv, mul_def]; rfl

instance : Group (Spin m n) where
  mul_assoc := Spin.mul_assoc
  one_mul := Spin.one_mul
  mul_one := Spin.mul_one
  inv_mul_cancel := Spin.inv_mul_cancel


lemma spin_prod_perm_eq_perm_prod {l : List (Spin m n)} :
    l.prod.α = (l.map (·.α)).reverse.prod := by
  induction' l with head tail ih
  · rfl
  · simp_all [Spin.mul_def, Equiv.Perm.mul_def]

lemma prod_eq_refl_of_refl {l : List (Spin m n)} (h : ∀ w ∈ l, w.α = Equiv.refl _) :
    l.prod.α = Equiv.refl _ := by
  induction' l with head tail ih
  · rfl
  · simp_all [Spin.mul_def]

lemma Point.isInside_one_iff {p a : Point m n} :
  p.IsInside ⟨a, a, Fin.le_refl _, Fin.le_refl _⟩ ↔ p = a := by grind [Point.IsInside]

lemma ZMod.cases_two : (a : ZMod 2) → a = 0 ∨ a = 1
  | 0 => Or.inl rfl
  | 1 => Or.inr rfl

lemma rotate_around_one_eq_self (h : p.IsInside ⟨a, a, Fin.le_refl _, Fin.le_refl _⟩) :
    rotate180 p ⟨a, a, Fin.le_refl _, Fin.le_refl _⟩ = p := by
  grind [Point.IsInside, rotate180]

-- @[grind? =]
@[simp]
lemma rect_spin_one (p : Point m n) : Rectangle.toSpin ⟨p, p, Fin.le_refl _, Fin.le_refl _⟩ =
    ⟨Equiv.refl _, fun x => if x = p then 1 else 0⟩ := by
  simp_all [Rectangle.toSpin, Equiv.ext_iff, rotate_around_one_eq_self, Point.isInside_one_iff]

grind_pattern rect_spin_one => Rectangle.toSpin (Rectangle.mk p p _ _)

attribute [-instance] NeZero.charZero_one -- saves about 0.75s

lemma Corollary1.aux1 {s : Spin m n} {l k : List (Spin m n)} (hl : l.prod.α = s.α)
    (hk : k = (.univ : Finset (Point m n)).toList.filterMap fun x =>
      if l.prod.u x ≠ s.u x
      then RectSpin.fromRect ⟨x, x, Fin.le_refl _, Fin.le_refl _⟩ |>.toSpin
      else none) : (l ++ k).prod = s := by
  simp only [List.prod_append, Spin.mul_def]
  have k_refl : ∀ w ∈ k, w.α = Equiv.refl _ := by grind
  have k_prod_refl : k.prod.α = Equiv.refl _ := prod_eq_refl_of_refl k_refl
  ext i : 1
  · exact k_prod_refl ▸ hl ▸ rfl
  · simp only
    have bam : k.prod.u i = (k.map (fun x => x.u i)).sum := by
      clear hk k_prod_refl
      induction' k with head tail ih
      · rfl
      · have : ∀ w ∈ tail, w.α = Equiv.refl _ := fun _ hw => k_refl _ (List.mem_cons_of_mem _ hw)
        simp [Spin.mul_def, prod_eq_refl_of_refl this, ih this]
    obtain h2 | h2 : l.prod.u i = s.u i ∨ l.prod.u i = s.u i + 1 := by
      cases (l.prod.u i).cases_two <;> cases (s.u i).cases_two <;> simp [*]
    · have (e) (_ : e ∈ k) : e.u i = 0 := by
        subst hk
        simp only [List.mem_filterMap] at *
        grind
      simp [k_prod_refl, h2, bam, List.map_eq_map_iff.mpr this]
    · have k_nodup : k.Nodup := by
        refine hk ▸ List.Nodup.filterMap ?_ (Finset.nodup_toList _)
        simp only [Option.mem_def, Option.ite_none_right_eq_some, Option.some_inj]
        intro a1 a2 s hs1 hs2
        have := congr(Spin.u $(hs2.2 ▸ hs1.2) a1)
        simpa

      let x_i_def : Spin m n := Rectangle.toSpin ⟨i, i, Fin.le_refl _, Fin.le_refl _⟩
      have x_i_in_k : x_i_def ∈ k := (hk ▸ List.mem_filterMap).mpr ⟨i, by simp [h2, x_i_def]⟩
      obtain ⟨a, ha1, ha2⟩ := List.getElem_of_mem x_i_in_k

      let k' := k.map fun x => x.u i
      have k_length : k'.length = k.length := List.length_map _
      have k'_cond (y : Fin k'.length) (hy : k'[y.val] = 1) : y = a := by
        rw [← k_nodup.getElem_inj_iff] <;> try omega
        have : k[y.val] ∈ k := List.getElem_mem _
        conv_lhs at this => rw [hk]
        simp only [ne_eq, ite_not, List.mem_filterMap, Finset.mem_toList, Finset.mem_univ,
          Option.ite_none_left_eq_some, Option.some_inj, true_and] at this
        obtain ⟨x, -, hx⟩ := this
        ext : 1
        · simp [ha2, ← hx, x_i_def]
        · have (rfl) : i = x := by
            rw [List.getElem_map] at hy
            simpa [hy] using congr(($hx).u i)
          rw [ha2, ← hx]
      simp only [k_prod_refl, Equiv.refl_symm, Equiv.refl_apply, h2, bam, Finset.sum_list_count,
        nsmul_eq_mul]
      have k'_one : 1 ∈ k' := by
        have : k'[a] = 1 := by simp [k', ha2, x_i_def]
        exact List.mem_of_getElem this
      have : List.count 1 k' = 1 := by
        have : ¬List.Duplicate 1 k' := by
          by_contra! h
          obtain ⟨b1, b2, _, hb1, hb2⟩ := List.duplicate_iff_exists_distinct_get.mp h
          have := k'_cond b1 hb1.symm
          have := k'_cond b2 hb2.symm
          omega
        rw [List.duplicate_iff_two_le_count] at this
        rw [← List.count_pos_iff] at k'_one
        omega
      rw [Finset.sum_eq_single 1]
      · rw [this, mul_one, Nat.cast_one, CharTwo.add_eq_iff_eq_add]
      · intro b _ hb
        rw [b.cases_two.resolve_right hb, mul_zero]
      · exact fun a => a (List.mem_toFinset.mpr k'_one) |>.elim

@[grind]
def Point.IsAdjacent (p1 p2 : Point m n) : Prop :=
  (p1.row = p2.row ∧ (p1.col.val + 1 = p2.col.val ∨ p2.col.val + 1 = p1.col.val)) ∨
  (p1.col = p2.col ∧ (p1.row.val + 1 = p2.row.val ∨ p2.row.val + 1 = p1.row.val))

lemma Point.IsAdjacent.symm {p1 p2 : Point m n} (_ : p1.IsAdjacent p2) :
  p2.IsAdjacent p1 := by grind

@[grind]
def Equiv.Perm.IsAdjacentSwap {m n : PNat} (p : Equiv.Perm (Point m n)) : Prop :=
  let x := p.support
  if h : x.card = 2 then
    have : x.toList.length = 2 := h ▸ Finset.length_toList _
    Point.IsAdjacent x.toList[0] x.toList[1]
  else
    False

lemma Equiv.Perm.IsAdjacentSwap.list_card {m n : PNat} {p : Equiv.Perm (Point m n)}
  (h : p.IsAdjacentSwap) : p.support.toList.length = 2 := by grind

lemma Equiv.Perm.IsAdjacentSwap.isAdjacent {m n : PNat} {p : Equiv.Perm (Point m n)}
  (h : p.IsAdjacentSwap) :
  haveI := h.list_card
  p.support.toList[0].IsAdjacent p.support.toList[1] := by grind

lemma Point.IsAdjacent.lt_or_lt {a b : Point m n} (h2 : a.IsAdjacent b) :
  (a.row ≤ b.row ∧ a.col ≤ b.col) ∨ (b.row ≤ a.row ∧ b.col ≤ a.col) := by grind

lemma Rectangle.swap_iff {s : RectSpin m n} :
    s ∈ SpinSet 1 2 m n ↔ s.r.topLeft.IsAdjacent s.r.bottomRight := by
  have : _ ∧ _ := ⟨s.r.validRow, s.r.validCol⟩
  simp [SpinSet, rectSpinSet_cond_iff, Point.IsAdjacent]
  omega

lemma spin_eq_swap_of_adj {p1 p2 : Point m n} {s : RectSpin m n} (h : p1.IsAdjacent p2)
    (hr : p1 = s.r.topLeft ∧ p2 = s.r.bottomRight) :
    s.α = Equiv.swap p1 p2 := by
  rw [hr.1, hr.2] at h ⊢
  ext j : 1
  simp only [s.h, Rectangle.toSpin, Function.Involutive.coe_toPerm]
  split_ifs with this
  · simp [Equiv.swap, Equiv.swapCore, rotate180, rotateCalc]
    split_ifs with h8 h9
    · simp [h8]
    · grind [s.r.validRow, s.r.validCol]
    · grind [Point.IsInside]
  · grind [Rectangle.corners_inside]

lemma exists_swap_spin_of_adj {p1 p2 : Point m n} (h : p1.IsAdjacent p2) :
    ∃ s : RectSpin m n, s ∈ SpinSet 1 2 m n ∧ s.α = Equiv.swap p1 p2 := by
  rcases h.lt_or_lt with h1 | h1
  · use RectSpin.fromRect ⟨p1, p2, h1.1, h1.2⟩
    exact ⟨Rectangle.swap_iff.mpr h, spin_eq_swap_of_adj h (by trivial)⟩
  · use RectSpin.fromRect ⟨p2, p1, h1.1, h1.2⟩
    rw [Equiv.swap_comm]
    exact ⟨Rectangle.swap_iff.mpr h.symm, spin_eq_swap_of_adj h.symm (by trivial)⟩

lemma List.eq_one_of_two {l : List α} (h1 : l.length = 2) (h2 : x ∈ l) : x = l[0] ∨ x = l[1] :=
  match l with
  | [_, _] => mem_pair.mp h2

lemma Equiv.Perm.swap_support [DecidableEq α] [Fintype α] {p : Perm α}
    (h : p.support.toList.length = 2) :
    p = swap (p.support.toList[0]) (p.support.toList[1]) := by
  have : p.support.card = 2 := h ▸ (Finset.length_toList _).symm
  let ⟨l1, l2, hl1, hl2⟩ : p.IsSwap := card_support_eq_two.mp this
  have : l1 = p.support.toList[0] ∨ l1 = p.support.toList[1] := List.eq_one_of_two h (by simp_all)
  have : l2 = p.support.toList[0] ∨ l2 = p.support.toList[1] := List.eq_one_of_two h (by simp_all)
  grind [swap_comm]

lemma List.map_attach_of_unattach {l : List α} {f : { x // x ∈ l } -> α} :
    f = (fun x => x.1) → l.attach.map f = l := (· ▸ attach_map_subtype_val l)

def mySet (m n : PNat) := (SpinSet 1 1 m n ∪ SpinSet 1 2 m n)
  |>.map ⟨(·.toSpin), RectSpin.toSpin_injective⟩

/-- **Corollary 1**: `S₁ₓ₁ ∪ S₁ₓ₂` generates `Spinₘₓₙ`. -/
lemma spin_s11_s12_closure (m n : PNat) : Subgroup.closure (SetLike.coe (mySet m n)) = ⊤ := by
  let set1 : Set (Equiv.Perm (Point m n)) := SpinSet 1 2 m n |>.image (·.α)

  have set1_swap : ∀ e ∈ set1, e.IsSwap := by
    intro e
    simp only [Finset.coe_image, Set.mem_image, SetLike.mem_coe, forall_exists_index, and_imp, set1]
    rintro s hs1 rfl
    use s.r.topLeft, s.r.bottomRight
    simp [SpinSet, rectSpinSet_cond_iff] at hs1
    grind [spin_eq_swap_of_adj, s.r.validRow, s.r.validCol]

  let x1 : SimpleGraph (Point m n) := SimpleGraph.fromRel (fun x y => Equiv.swap x y ∈ set1)
  have : x1.Connected := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    use ⟨0, 0⟩, fun v => SimpleGraph.Walk.reachable ?_
    by_cases h : v = ⟨0, 0⟩
    · rw [h]

    let rec build_walk_horiz (row col col_end : Nat)
        (hrow : row < m.val := by omega) (hcol : col < n.val := by omega)
        (hcol_end : col_end < n.val := by omega) (hk : col < col_end + 1 := by omega) :
        x1.Walk ⟨⟨row, hrow⟩, ⟨col, hcol⟩⟩ ⟨⟨row, hrow⟩, ⟨col_end, hcol_end⟩⟩ :=
      if ht : col = col_end then
        SimpleGraph.Walk.nil.copy rfl (by simp only [ht])
      else
        let tail := build_walk_horiz row (col + 1) (col_end)
        SimpleGraph.Walk.cons (by simp [x1, set1, exists_swap_spin_of_adj, Point.IsAdjacent]) tail
    decreasing_by omega -- faster than default

    let rec build_walk_full (z : Point m n)
        (hz : z.row.val < v.row.val ∨ (z.row.val = v.row.val ∧ z.col.val ≤ v.col.val) := by omega)
        : x1.Walk z v :=
      if ht : z = v then
        SimpleGraph.Walk.nil.copy rfl (by omega)
      else if hcol : z.col < n.val - 1 then
        let edge := build_walk_horiz z.row z.col (z.col.val + 1) z.row.isLt (by omega) (by omega)
        let walk : x1.Walk z ⟨⟨z.row, _⟩, ⟨↑z.col + 1, _⟩⟩ := edge.copy (by simp) (by simp)
        walk.append (build_walk_full ⟨⟨z.row, _⟩, ⟨z.col + 1, _⟩⟩
          (by simp [Point.ext_iff, Fin.ext_iff] at ht hz ⊢; omega))
      else
        have hcol' : z.col.val = n.val - 1 := by omega
        have : z.row.val < v.row.val := by simp [Point.ext_iff, Fin.ext_iff] at ht; omega

        let b : Point m n := ⟨⟨z.row.val + 1, by omega⟩, z.col⟩
        have adj : z.IsAdjacent b := by right; simp [b]
        have edge : x1.Adj z ⟨⟨z.row.val + 1, _⟩, z.col⟩ := by
          -- grind [SimpleGraph.fromRel_adj, → exists_swap_spin_of_adj]
          refine (SimpleGraph.fromRel_adj ..).mpr ⟨by grind, Or.inl ?_⟩
          simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, set1]
          exact exists_swap_spin_of_adj adj

        let walk_horiz := build_walk_horiz (z.row.val + 1) 0 (n.val - 1)
        let walk_horiz' : x1.Walk ⟨⟨z.row.val + 1, _⟩, 0⟩ ⟨⟨z.row.val + 1, _⟩, z.col⟩ :=
          walk_horiz.copy (by simp) (by simp [Fin.ext_iff, hcol'])
        let tail := walk_horiz'.reverse.append (build_walk_full ⟨⟨z.row.val + 1, _⟩, 0⟩ (by
          have : z.row.val + 1 ≤ v.row.val := by omega
          rcases this.eq_or_lt with h | h <;> simp [h]))

        SimpleGraph.Walk.cons edge tail
    decreasing_by all_goals omega -- faster than default
    exact build_walk_full ⟨⟨0, _⟩, ⟨0, _⟩⟩ (by lia)
  have top := transpositions_generate_symm_group_iff_connected_graph set1_swap |>.mpr this
  rw [Subgroup.eq_top_iff']
  intro s
  have : s.α ∈ Subgroup.closure set1 := by rw [top]; exact trivial
  let ⟨l, hl1, hl2⟩ := Subgroup.exists_list_of_mem_closure.mp this
  replace hl1 : ∀ x ∈ l, x.IsAdjacentSwap := by
    intro x hx
    have : x ∈ set1 := by
      by_contra k
      have := (hl1 x hx).resolve_left k
      rw [isSwap_inv_eq_self' <| set1_swap _ this] at k
      contradiction
    simp only [Equiv.Perm.IsAdjacentSwap, Equiv.Perm.card_support_eq_two, dite_else_false]
    have sw := set1_swap _ this
    use sw
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, set1] at this
    obtain ⟨s, hs1, rfl⟩ := this

    have perm_length : s.α.support.toList.length = 2 :=
      Equiv.Perm.card_support_eq_two.mpr sw ▸ Finset.length_toList _
    have adj := Rectangle.swap_iff.mp hs1
    have r_corners : s.r.topLeft ≠ s.r.bottomRight := by grind
    have := Equiv.Perm.support_swap r_corners
    rw [← spin_eq_swap_of_adj adj (Rectangle.ext_iff.mp rfl)] at this
    have top_in : s.r.topLeft ∈ s.α.support.toList := by simp [this]
    have bot_in : s.r.bottomRight ∈ s.α.support.toList := by simp [this]
    have bot_eq := List.eq_one_of_two perm_length bot_in
    rcases List.eq_one_of_two perm_length top_in with htop | htop
    · have := ne_of_ne_of_eq r_corners.symm htop
      exact bot_eq.resolve_left this ▸ htop ▸ adj
    · have := ne_of_ne_of_eq r_corners.symm htop
      exact bot_eq.resolve_right this ▸ htop ▸ adj.symm

  let ⟨l, hl1, hl2⟩ : ∃ l : List (Spin m n), l.prod.α = s.α ∧ (∀ x ∈ l, x ∈ mySet m n) := by
    use l.attach.map (fun ⟨i, hi⟩ =>
      have := (hl1 _ hi).list_card
      let a := i.support.toList[0]
      let b := i.support.toList[1]
      have adj : a.IsAdjacent b := (hl1 _ hi).isAdjacent
      if h : a.row ≤ b.row ∧ a.col ≤ b.col then
        RectSpin.fromRect ⟨a, b, h.1, h.2⟩
      else
        have := adj.lt_or_lt.resolve_left h
        RectSpin.fromRect ⟨b, a, this.1, this.2⟩
    ) |>.map (·.toSpin) |>.reverse
    constructor
    · simp only [List.map_map, Function.comp_def, spin_prod_perm_eq_perm_prod,
        List.map_reverse, List.reverse_reverse, ← hl2]
      congr
      apply List.map_attach_of_unattach
      funext ⟨x, hx⟩
      have adj := (hl1 _ hx).isAdjacent
      have := Equiv.Perm.swap_support (hl1 _ hx).list_card
      split_ifs
      · convert spin_eq_swap_of_adj adj ?_
        simp
      · convert spin_eq_swap_of_adj adj.symm ?_
        · simpa [Equiv.swap_comm]
        · simp
    · intro x
      simp only [mySet, Finset.mem_map, Finset.mem_union, List.mem_reverse, List.mem_map]
      intro ⟨a, ha1, ha2⟩
      use a, Or.inr ?_, ha2
      simp only [List.mem_attach, true_and, Subtype.exists] at ha1
      obtain ⟨b, hb1, rfl⟩ := ha1
      apply Rectangle.swap_iff.mpr
      split_ifs
      · exact (hl1 _ hb1).isAdjacent
      · exact (hl1 _ hb1).isAdjacent.symm
  apply Subgroup.exists_list_of_mem_closure.mpr
  let k : List (Spin m n) := (.univ : Finset (Point m n)).toList.filterMap fun x =>
    if l.prod.u x ≠ s.u x
    then RectSpin.fromRect ⟨x, x, Fin.le_refl _, Fin.le_refl _⟩ |>.toSpin
    else none

  use l ++ k, fun x hx => Or.inl ?_, Corollary1.aux1 hl1 rfl
  rcases List.mem_append.mp hx with hx | hx
  · exact hl2 x hx
  · simp only [mySet, Finset.map_union, Finset.coe_union, Finset.coe_map,
      Function.Embedding.coeFn_mk, Set.mem_union, Set.mem_image, Finset.mem_coe]
    left
    obtain ⟨c1, -, c3⟩ := List.mem_filterMap.mp hx
    use RectSpin.fromRect ⟨c1, c1, Fin.le_refl _, Fin.le_refl _⟩
    constructor
    · simp [SpinSet, rectSpinSet_cond_iff]
    · rw [Option.ite_none_right_eq_some, Option.some_inj] at c3
      simp only [Rectangle.toSpin, ← c3.2]
