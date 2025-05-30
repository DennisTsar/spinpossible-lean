import Spinpossible.Prop2
import Spinpossible.Lemma1

open scoped CharTwo

def Spin.inv (x : Spin m n) : Spin m n := ⟨x.α.symm, fun i => -x.u (x.α.toFun i)⟩

instance : Inv (Spin m n) := ⟨Spin.inv⟩

lemma Spin.inv_def (x : Spin m n) : x⁻¹ = ⟨x.α.symm, fun i => -x.u (x.α.toFun i)⟩ := rfl

theorem Spin.mul_assoc (x y z : Spin m n) : x * y * z = x * (y * z) := by
  ext
  · rfl
  · exact add_assoc ..

theorem Spin.one_mul (x : Spin m n) : 1 * x = x := by
  ext
  · rfl
  · simp [mul_def]; rfl

theorem Spin.mul_one (x : Spin m n) : x * 1 = x := by
  ext
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
    p.IsInside ⟨a, a, Fin.le_refl _, Fin.le_refl _⟩ ↔ p = a := by
  simp [Point.IsInside, Point.ext_iff]
  omega

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
  have k_refl : ∀ w ∈ k, w.α = Equiv.refl _ := by simp_all
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
    have : l.prod.u i = s.u i ∨ l.prod.u i = s.u i + 1 := by
      cases (l.prod.u i).cases_two <;> cases (s.u i).cases_two <;> simp [*]
    rcases this with h2 | h2
    · have : ∀ e ∈ k, e.u i = 0 := by aesop
      simp [k_prod_refl, h2, bam, List.map_eq_map_iff.mpr this]
    · have k_nodup : k.Nodup := by
        refine hk ▸ List.Nodup.filterMap ?_ (List.nodup_finRange _)
        simp only [Option.mem_def, Option.ite_none_right_eq_some, Option.some_inj]
        intro a1 a2 s hs1 hs2
        have := congr(Spin.u $(hs2.2 ▸ hs1.2) a2)
        simpa only [reduceIte, ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not]

      let x_i_def : Spin m n := ⟨Equiv.refl _, fun j ↦ if i = j then 1 else 0⟩
      have x_i_in_k : x_i_def ∈ k := (hk ▸ List.mem_filterMap).mpr ⟨i, by simp [h2, x_i_def]⟩
      obtain ⟨a, ha1, ha2⟩ := List.getElem_of_mem x_i_in_k

      let k' := List.map (fun x ↦ x.u i) k
      have k_length : k'.length = k.length := List.length_map _
      have k'_cond : ∀ y : Fin k'.length, k'[y.val] = 1 → y = a := by
        intro y hy
        have : k[y.val] = x_i_def := by
          have : k[y.val] ∈ k := List.getElem_mem _
          nth_rw 1 [hk] at this
          simp only [List.mem_filterMap, List.mem_finRange,
            Option.ite_none_right_eq_some, Option.some_inj, true_and] at this
          obtain ⟨x, -, hx⟩ := this
          ext : 1
          · rw [← hx]
          · have : x = i := by
              simp_rw [k', List.getElem_map] at hy
              simpa [hy] using congr(Spin.u $hx i)
            rw [← hx, this]
        contrapose! k_nodup with h
        apply List.not_nodup_of_get_eq_of_ne k ⟨a, ha1⟩ ⟨y, k_length ▸ y.2⟩
        · rw [List.get_eq_getElem, ha2, List.get_eq_getElem, this]
        · exact Fin.ne_of_val_ne h.symm
      simp only [k_prod_refl, Equiv.refl_symm, Equiv.refl_apply, h2, bam, Finset.sum_list_count,
        nsmul_eq_mul]
      have k'_one : 1 ∈ k' := by
        have : k'[a] = 1 := by simp [k', ha2, x_i_def]
        exact this ▸ List.getElem_mem _
      have : List.count 1 k' = 1 := by
        have : ¬List.Duplicate 1 k' := by
          by_contra! h
          obtain ⟨b1, b2, _, hb1, hb2⟩ := List.duplicate_iff_exists_distinct_get.mp h
          have := k'_cond b1 hb1.symm
          have := k'_cond b2 hb2.symm
          omega
        have := List.duplicate_iff_two_le_count.mpr.mt this
        have := List.count_pos_iff.mpr k'_one
        omega
      rw [Finset.sum_eq_single 1]
      · rw [this, mul_one, Nat.cast_one, CharTwo.add_eq_iff_eq_add]
      · intro b _ hb
        rw [b.cases_two.resolve_right hb, mul_zero]
      · exact fun a => a (List.mem_toFinset.mpr k'_one) |>.elim

lemma rotate_around_one_eq_self (h : p.IsInside ⟨a, a, Fin.le_refl _, Fin.le_refl _⟩) :
    rotate180 p ⟨a, a, Fin.le_refl _, Fin.le_refl _⟩ = p := by
  simp only [Point.IsInside] at h
  ext <;> (simp only [rotate180]; omega)

def Point.IsAdjacent (p1 p2 : Point m n) : Prop :=
  (p1.row = p2.row ∧ (p1.col.val + 1 = p2.col.val ∨ p2.col.val + 1 = p1.col.val)) ∨
  (p1.col = p2.col ∧ (p1.row.val + 1 = p2.row.val ∨ p2.row.val + 1 = p1.row.val))

lemma Point.IsAdjacent.symm {p1 p2 : Point m n} (_ : p1.IsAdjacent p2) : p2.IsAdjacent p1 := by
  dsimp only [Point.IsAdjacent] at *
  omega

def Equiv.Perm.IsAdjacentSwap {m n : PNat} (p : Equiv.Perm (Fin (m * n))) : Prop :=
  let x := p.support
  if h : x.card = 2 then
    have : x.toList.length = 2 := h ▸ Finset.length_toList _
    Point.IsAdjacent (to2d x.toList[0]) (to2d x.toList[1])
  else
    False

lemma Equiv.Perm.IsAdjacentSwap.list_card {m n : PNat} {p : Equiv.Perm (Fin (m * n))}
    (h : p.IsAdjacentSwap) : p.support.toList.length = 2 := by
  simp [Equiv.Perm.IsAdjacentSwap] at h
  exact Equiv.Perm.card_support_eq_two.mpr h.choose ▸ Finset.length_toList _

lemma Equiv.Perm.IsAdjacentSwap.isAdjacent {m n : PNat} {p : Equiv.Perm (Fin (m * n))}
    (h : p.IsAdjacentSwap) :
    have := h.list_card
    (to2d p.support.toList[0]).IsAdjacent (to2d p.support.toList[1]) := by
  simp [Equiv.Perm.IsAdjacentSwap] at h
  exact h.choose_spec

lemma Point.IsAdjacent.lt_of_1d_lt {a b : Point m n} (h : (to1d a) ≤ (to1d b)) (h2 : a.IsAdjacent b) :
    a.row ≤ b.row ∧ a.col ≤ b.col := by
  dsimp only [to1d] at h
  cases h2 <;> simp_all

lemma Rectangle.swap_iff {s : RectSpin m n} :
    s ∈ SpinSet 1 2 m n ↔ s.r.topLeft.IsAdjacent s.r.bottomRight := by
  have : _ ∧ _ := ⟨s.r.validRow, s.r.validCol⟩
  simp [SpinSet, rectSpinSet_cond_iff, Point.IsAdjacent]
  omega

lemma spin_eq_swap_of_adj {p1 p2 : Point m n} {s : RectSpin m n} (h : p1.IsAdjacent p2)
    (hr : p1 = s.r.topLeft ∧ p2 = s.r.bottomRight) :
    s.α = Equiv.swap (to1d p1) (to1d p2) := by
  rw [hr.1, hr.2] at h ⊢
  ext j : 1
  simp only [s.h, Rectangle.toSpin, Function.Involutive.coe_toPerm]
  split_ifs with this
  · simp [Equiv.swap, Equiv.swapCore, rotate180, rotateCalc]
    split_ifs with h8 h9
    · simp [h8]
    · have : _ ∧ _ := ⟨s.r.validRow, s.r.validCol⟩
      simp only [h9, to2d_to1d_inverse, to1d_inj]
      ext <;> (simp only; omega)
    · simp_rw [← to2d_injective.ne_iff] at h8 h9
      have : s ∈ SpinSet 1 2 m n := Rectangle.swap_iff.mpr h
      simp [SpinSet, rectSpinSet_cond_iff] at this
      simp [Point.ext_iff, Point.IsInside] at *
      omega
  · rw [Equiv.swap_apply_of_ne_of_ne] <;> (by_contra k; simpa [k, s.r.corners_inside])

lemma exists_swap_spin_of_adj {p1 p2 : Point m n} (h : p1.IsAdjacent p2) :
    ∃ s : RectSpin m n, s ∈ SpinSet 1 2 m n ∧ s.α = Equiv.swap (to1d p1) (to1d p2) := by
  by_cases h1 : (to1d p1) ≤ (to1d p2)
  · have := h.lt_of_1d_lt h1
    use RectSpin.fromRect ⟨p1, p2, this.2, this.1⟩
    exact ⟨Rectangle.swap_iff.mpr h, spin_eq_swap_of_adj h (by trivial)⟩
  · have := h.symm.lt_of_1d_lt (le_of_not_ge h1)
    use RectSpin.fromRect ⟨p2, p1, this.2, this.1⟩
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
  rcases this with rfl | rfl
  · rw [← this.resolve_left hl1, swap_comm, ← hl2]
  · rw [← this.resolve_right hl1, ← hl2]

lemma Nat.mod_succ_le_of_not_dvd {a b : Nat} (h : ¬b ∣ a + 1) (hb : 0 < b) : a % b + 1 < b := by
  apply lt_of_le_of_ne (mod_lt a hb)
  contrapose! h
  simpa [dvd_iff_mod_eq_zero] using congr($h % b)

lemma Nat.mod_succ_of_not_dvd {a b : Nat} (h : ¬b ∣ a + 1) (hb : 0 < b) :
    (a + 1) % b = a % b + 1 := by
  have := mod_succ_le_of_not_dvd h hb
  rw [add_mod, one_mod_eq_one.mpr (by omega), mod_eq_of_lt this]

lemma List.map_attach_of_unattach {l : List α} {f : { x // x ∈ l } -> α} :
    f = (fun x => x.1) → l.attach.map f = l := (· ▸ attach_map_subtype_val l)

def mySet (m n : PNat) := (SpinSet 1 1 m n ∪ SpinSet 1 2 m n)
  |>.map ⟨(·.toSpin), RectSpin.toSpin_injective⟩

lemma spin_s11_s12_closure (m n : PNat) : Subgroup.closure ((mySet m n).toSet) = ⊤ := by
  let set1 : Set (Equiv.Perm (Fin (m * n))) := SpinSet 1 2 m n |>.image (·.α)

  have set1_swap : ∀ e ∈ set1, e.IsSwap := by
    intro e
    simp [set1]
    rintro s hs1 rfl
    use to1d s.r.topLeft, to1d s.r.bottomRight
    simp [SpinSet, rectSpinSet_cond_iff] at hs1
    have : _ ∧ _ := ⟨s.r.validRow, s.r.validCol⟩
    constructor
    · simp [Point.ext_iff]
      omega
    · refine spin_eq_swap_of_adj ?_ ⟨rfl, rfl⟩
      dsimp only [Point.IsAdjacent]
      omega

  let x1 : SimpleGraph (Fin (m * n)) := SimpleGraph.fromRel (fun x y => Equiv.swap x y ∈ set1)
  have : x1.Connected := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    use 0, fun v => SimpleGraph.Walk.reachable ?_
    by_cases h : v = 0
    · rw [h]
    have : n.val ≥ 1 := n.2

    let rec build_walk_horiz (row col col_end : Nat)
        (hrow : row < m.val := by omega) (hcol : col < n.val := by omega)
        (hcol_end : col_end < n.val := by omega) (hk : col < col_end + 1 := by omega) :
        x1.Walk (to1d ⟨⟨row, hrow⟩, ⟨col, hcol⟩⟩) (to1d ⟨⟨row, hrow⟩, ⟨col_end, hcol_end⟩⟩) :=
      if ht : col = col_end then
        SimpleGraph.Walk.nil.copy rfl (by simp only [ht])
      else
        let tail := build_walk_horiz row (col + 1) (col_end)
        SimpleGraph.Walk.cons (by simp [x1, set1, exists_swap_spin_of_adj, Point.IsAdjacent]) tail

    let rec build_walk_full (z : Nat) (hz : z ≤ v.val := by omega) : x1.Walk ⟨z, by omega⟩ v :=
      have hzLt : z < m.val * n.val := by omega
      if ht : z = v.val then
        SimpleGraph.Walk.nil.copy rfl (Fin.eq_of_val_eq ht)
      else if hcol : ¬n.val ∣ z + 1 then
        have : (z + 1) % n.val = z % n.val + 1 := Nat.mod_succ_of_not_dvd hcol n.2
        let edge := build_walk_horiz (z / n) (z % n) ((z + 1) % n)
          (Nat.div_lt_iff_lt_mul n.2 |>.mpr hzLt) (Nat.mod_lt _ n.2) (Nat.mod_lt _ n.2)

        let walk : x1.Walk ⟨z, hzLt⟩ ⟨z + 1, by omega⟩ := edge.copy
          (by simp [to1d, Nat.mod_add_div'])
          (by simp [to1d, this, Nat.add_right_comm _ 1, Nat.mod_add_div'])

        walk.append (build_walk_full (z + 1))
      else
        have hz1Lt : z + 1 < m.val * n.val := by omega
        have : z + n.val < m.val * n.val := by
          rw [mul_comm] at hz1Lt
          obtain ⟨w, hw⟩ := not_not.mp hcol
          have : z + n.val < (w + 1) * n.val := by rw [Nat.mul_comm, Nat.mul_add]; omega
          apply lt_mul_of_lt_mul_right this
          by_contra! k
          have : z + 1 < n.val * w := lt_mul_of_lt_mul_left hz1Lt (Nat.le_of_lt_succ k)
          omega
        let a : Point m n := to2d ⟨z, hzLt⟩
        let b : Point m n := to2d ⟨z + n.val, this⟩
        have adj : a.IsAdjacent b := by right; simp [to2d, a, b]
        have edge : x1.Adj ⟨z, hzLt⟩ ⟨z + n.val, this⟩ := by
          refine (SimpleGraph.fromRel_adj ..).mpr ⟨by simp, Or.inl ?_⟩
          simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, set1]
          convert exists_swap_spin_of_adj adj
          · simp [a]
          · simp [b]

        have _ := Nat.div_mul_cancel (not_not.mp hcol)
        let walk_horiz := build_walk_horiz ((z + 1) / n.val) 0 (n.val - 1)
          (Nat.div_lt_iff_lt_mul n.2 |>.mpr hz1Lt)
        let walk_horiz' : x1.Walk ⟨z + 1, hz1Lt⟩ ⟨z + n.val, this⟩ := walk_horiz.copy
          (by simp [to1d]; omega) (by simp [to1d]; omega)
        let tail := walk_horiz'.reverse.append (build_walk_full (z + 1) (by omega))

        SimpleGraph.Walk.cons edge tail
    exact build_walk_full 0
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
    have r_corners : s.r.topLeft ≠ s.r.bottomRight := by
      dsimp [Point.IsAdjacent] at adj
      simp [Point.ext_iff]
      omega
    have := Equiv.Perm.support_swap (to1d_inj.ne.mpr r_corners)
    rw [← spin_eq_swap_of_adj adj (Rectangle.ext_iff.mp rfl)] at this
    have top_in : to1d s.r.topLeft ∈ s.α.support.toList := by simp [this]
    have bot_in : to1d s.r.bottomRight ∈ s.α.support.toList := by simp [this]
    have bot_eq := List.eq_one_of_two perm_length bot_in
    have := to1d_inj.ne.mpr r_corners
    rcases List.eq_one_of_two perm_length top_in with htop | htop
    · simp only [← htop, to2d_to1d_inverse]
      have := ne_of_ne_of_eq this.symm htop
      exact bot_eq.resolve_left this ▸ to2d_to1d_inverse ▸ adj
    · simp only [← htop, to2d_to1d_inverse]
      have := ne_of_ne_of_eq this.symm htop
      exact bot_eq.resolve_right this ▸ to2d_to1d_inverse ▸ adj.symm

  let ⟨l, hl1, hl2⟩ : ∃ l : List (Spin m n), l.prod.α = s.α ∧ (∀ x ∈ l, x ∈ mySet m n) := by
    use l.attach.map (fun ⟨i, hi⟩ =>
      have := (hl1 _ hi).list_card
      let a := to2d i.support.toList[0]
      let b := to2d i.support.toList[1]
      have adj : a.IsAdjacent b := (hl1 _ hi).isAdjacent
      if h : (to1d a) ≤ (to1d b) then
        have := adj.lt_of_1d_lt h
        RectSpin.fromRect ⟨a, b, this.2, this.1⟩
      else
        have := adj.symm.lt_of_1d_lt (le_of_not_ge h)
        RectSpin.fromRect ⟨b, a, this.2, this.1⟩
    ) |>.map (·.toSpin) |>.reverse
    -- use y
    constructor
    · simp only [to1d_to2d_inverse, List.map_map, Function.comp_def, spin_prod_perm_eq_perm_prod,
        List.map_reverse, List.reverse_reverse, ← hl2]
      congr
      apply List.map_attach_of_unattach
      funext ⟨x, hx⟩
      have adj := (hl1 _ hx).isAdjacent
      have := Equiv.Perm.swap_support (hl1 _ hx).list_card
      split_ifs
      · convert spin_eq_swap_of_adj adj ?_
        · simpa
        · simp
      · convert spin_eq_swap_of_adj adj.symm ?_
        · rw [Equiv.swap_comm]; simpa
        · simp
    · intro x
      simp only [mySet, Finset.mem_map, Finset.mem_union, List.mem_reverse, List.mem_map]
      intro ⟨a, ha1, ha2⟩
      use a, Or.inr ?_, ha2
      simp only [to1d_to2d_inverse, id_eq,
        List.mem_map, List.mem_attach, true_and, Subtype.exists] at ha1
      obtain ⟨b, hb1, rfl⟩ := ha1
      apply Rectangle.swap_iff.mpr
      split_ifs
      · exact (hl1 _ hb1).isAdjacent
      · exact (hl1 _ hb1).isAdjacent.symm
  apply Subgroup.exists_list_of_mem_closure.mpr
  let k : List (Spin m n) := List.finRange (m * n) |>.filterMap (fun isp =>
    if l.prod.u isp ≠ s.u isp then
      some ⟨Equiv.refl _, fun j => if isp = j then 1 else 0⟩
    else
      none
  )

  use l ++ k, fun x hx => Or.inl ?_, Corollary1.aux1 hl1 rfl
  rcases List.mem_append.mp hx with hx | hx
  · exact hl2 x hx
  · simp only [mySet, Finset.map_union, Finset.coe_union, Finset.coe_map,
      Function.Embedding.coeFn_mk, Set.mem_union, Set.mem_image, Finset.mem_coe]
    left
    let ⟨c1, _, c3⟩ := List.mem_filterMap.mp hx
    use RectSpin.fromRect ⟨to2d c1, to2d c1, Fin.le_refl _, Fin.le_refl _⟩
    constructor
    · simp [SpinSet, rectSpinSet_cond_iff]
    · simp only [Option.ite_none_right_eq_some, Option.some_inj] at c3
      simp only [Rectangle.toSpin, ← c3.2]
      ext i
      · simp_all [rotate_around_one_eq_self]
      · refine if_congr ?_ rfl rfl
        rw [Point.isInside_one_iff, to2d_injective.eq_iff, eq_comm]
