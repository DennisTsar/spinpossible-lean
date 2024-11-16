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
  have k_refl : ∀ w ∈ k, w.α = Equiv.refl _ := by simp_all
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
  simp [rotate180, rotateCalc]
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

def Equiv.Perm.IsAdjacentSwap {m n : PNat} (perm: Equiv.Perm (Fin (m * n))) : Prop :=
  let x := perm.support
  if h : x.card = 2 then
    have : x.toList.length = 2 := h ▸ Finset.length_toList _
    have : perm.IsSwap := Equiv.Perm.card_support_eq_two.mp h
    let a := to2d x.toList[0]
    let b := to2d x.toList[1]
    Point.IsAdjacent a b
  else
    False

lemma Equiv.Perm.IsAdjacentSwap.list_card {m n : PNat} {p: Equiv.Perm (Fin (m * n))}
    (h : p.IsAdjacentSwap) : p.support.toList.length = 2 := by
  simp[Equiv.Perm.IsAdjacentSwap] at h;
  exact Equiv.Perm.card_support_eq_two.mpr (h).choose ▸ Finset.length_toList _

lemma Equiv.Perm.IsAdjacentSwap.isAdjacent {m n : PNat} {p: Equiv.Perm (Fin (m * n))}
    (h : p.IsAdjacentSwap) :
    have := h.list_card
    (to2d p.support.toList[0]).IsAdjacent (to2d p.support.toList[1]) := by
  simp [Equiv.Perm.IsAdjacentSwap] at h
  exact h.choose_spec


lemma somethingj {a b : Point m n} (h : (to1d a) ≤ (to1d b)) (h2 : a.IsAdjacent b) :
    a.row ≤ b.row ∧ a.col ≤ b.col := by
  dsimp only [to1d] at h
  cases h2 <;> simp_all


lemma somethingk4 {p1 p2 : Point m n} {r : Rectangle m n} (h : p1.IsAdjacent p2)
    (h4 : r.topLeft = p1 ∧ r.bottomRight = p2) :
    ∀ p3 : Point m n, p3.IsInside r ↔ (p3 = p1 ∨ p3 = p2) := by
  intro p3
  constructor
  · simp [Point.IsAdjacent, h4, Point.IsInside, Point.ext_iff] at *
    omega
  · intro hx
    have : _ ∧ _ := ⟨r.validRow, r.validCol⟩
    simp [Point.IsInside, Point.IsAdjacent, h4] at *
    rcases hx with rfl | rfl <;> omega

lemma somethingk5 {p1 p2 : Point m n} {r : Rectangle m n} (h : p1.IsAdjacent p2)
    (hr : r.topLeft = p1 ∧ r.bottomRight = p2) :
    r.toSpin.α = Equiv.swap (to1d p1) (to1d p2) := by
  rw [Equiv.ext_iff]
  intro j
  simp only [Rectangle.toSpin, Equiv.coe_fn_mk]
  split_ifs with h7
  · simp [Equiv.swap, Equiv.swapCore, rotate180, rotateCalc]
    split_ifs with h8 h9
    · simp [hr, h8]
    · cases r
      simp only [h9, ← hr, to2d_to1d_inverse, to1d_inj]
      ext <;> (simp only; omega)
    · have := somethingk4 h hr (to2d j) |>.mp h7
      rcases this with rfl | rfl
      · simp at h8
      · simp at h9
  · have := somethingk4 h hr (to2d j) |>.mpr.mt h7
    rw [Equiv.swap_apply_of_ne_of_ne] <;> simp_all [to2d_injective.ne_iff.mp]

lemma Rectangle.swap_iff {r : Rectangle m n} :
    r ∈ SpinSet 1 2 m n ↔ r.topLeft.IsAdjacent r.bottomRight := by
  cases r
  simp [SpinSet, rectangleSet_cond_iff, Point.IsAdjacent]
  omega

lemma somethingk52 {p1 p2 : Point m n} (h : p1.IsAdjacent p2) :
    ∃ r : Rectangle m n, r ∈ SpinSet 1 2 m n ∧ r.toSpin.α = Equiv.swap (to1d p1) (to1d p2) := by
  by_cases h1 : (to1d p1) ≤ (to1d p2)
  · have := somethingj h1 h
    use ⟨p1, p2, by omega, by omega⟩
    exact ⟨Rectangle.swap_iff.mpr h, somethingk5 h (by simp)⟩
  · have := somethingj (by omega) h.symm
    use ⟨p2, p1, by omega, by omega⟩
    constructor
    · apply Rectangle.swap_iff.mpr h.symm
    · rw [Equiv.swap_comm]
      exact somethingk5 h.symm (by simp)

lemma blahj {l : List α} {x : α} (h : l.length = 2) (h2 : x ∈ l) : x = l[0] ∨ x = l[1] := by
  let k := [l[0], l[1]]
  have l_eq : l = k := by
    refine List.ext_getElem? ?_
    intro y
    match y with
    | 0 | 1 => simp [k]
    | _ + 2 => simp [k, h]
  have : ∀ e ∈ k, e = l[0] ∨ e = l[1] := fun e a ↦ List.mem_pair.mp a
  exact this _ (l_eq ▸ h2)

lemma somethingk6 [DecidableEq α] [Fintype α] {p : Equiv.Perm α} (h : p.support.toList.length = 2) :
    Equiv.swap (p.support.toList[0]) (p.support.toList[1]) = p := by
  have : p.support.card = 2 := h ▸ (Finset.length_toList _).symm
  let ⟨l1, l2, hl⟩ : p.IsSwap := Equiv.Perm.card_support_eq_two.mp this
  have : l1 = p.support.toList[0] ∨ l1 = p.support.toList[1] := blahj h (by simp_all)
  have : l2 = p.support.toList[0] ∨ l2 = p.support.toList[1] := blahj h (by simp_all)

  rcases this with rfl | rfl
  · rw [Equiv.swap_comm, ← this.resolve_left hl.1]
    exact hl.2.symm
  · rw [← this.resolve_right hl.1]
    exact hl.2.symm

lemma somethink8 (h : r ∈ SpinSet 1 2 m n) (h2 : Point.IsInside p r) :
    r.topLeft = p ∨ r.bottomRight = p := by
  cases r
  simp [SpinSet, rectangleSet_cond_iff] at h
  dsimp [Point.IsInside] at h2
  simp [Point.ext_iff]
  omega

lemma mod_add_one_ne_zero_implies_lt {a b : ℕ} (h : ¬b ∣ (a + 1)) (hb : b > 0) : b > a % b + 1 := by
  let c := a % b
  have h1 : (a + 1) % b = (c + 1) % b := (Nat.mod_add_mod a b 1).symm
  have : c < b := Nat.mod_lt a hb
  have : c + 1 ≤ b := by omega
  cases Nat.lt_or_eq_of_le this with
  | inl h2 => exact h2
  | inr h2 => rw [h2, Nat.mod_self] at h1; omega

lemma mod_lt_succ_mod_add_one {z n : ℕ} (hn : n > 0) (h : ¬n ∣ (z + 1)) :
  (z + 1) % n = z % n + 1 := by
  have := mod_add_one_ne_zero_implies_lt h hn
  rw [Nat.add_mod, Nat.one_mod_eq_one.mpr (by omega), Nat.mod_eq_of_lt]
  omega

lemma goAgain {l : List α} {f : { x // x ∈ l } -> α} :
    f = (fun x => x.1) → l.attach.map f = l := by
  intro a
  simp only [a, List.map_subtype, List.unattach_attach, List.map_id_fun', id_eq]

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
    · apply ha2 ▸ somethingk5
      · dsimp only [Point.IsAdjacent]; omega
      · simp

  let x1 : SimpleGraph (Fin (m * n)) := SimpleGraph.fromRel (fun x y => Equiv.swap x y ∈ set1)
  have ff : x1.Connected := by
    apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
    use 0
    intro v
    refine SimpleGraph.Walk.reachable ?h.p
    by_cases h : v = 0
    · rw [h]
    have q2 : n.val ≥ 1 := NeZero.one_le

    let rec build_walk_horiz (row col col_end : Nat)
        (hrow : row < m.val := by omega) (hcol : col < n.val := by omega)
        (hcol_end : col_end < n.val := by omega) (hk : col < col_end + 1 := by omega) :
        x1.Walk (to1d ⟨⟨row, hrow⟩, ⟨col, hcol⟩⟩) (to1d ⟨⟨row, hrow⟩, ⟨col_end, hcol_end⟩⟩) :=
      if ht : col = col_end then
        SimpleGraph.Walk.nil.copy rfl (by simp only [ht])
      else
        let tail := build_walk_horiz row (col + 1) (col_end)
        SimpleGraph.Walk.cons (by simp [x1, set1, somethingk52, Point.IsAdjacent]) tail

    let rec build_walk_full (z : Nat) (hz : z ≤ v.val := by omega) : x1.Walk ⟨z, by omega⟩ v :=
      have hzLt : z < m.val * n.val := by omega
      if ht : z = v.val then
        SimpleGraph.Walk.nil.copy rfl (by simp [ht])
      else if hcol : ¬n.val ∣ z + 1 then
        have : (z + 1) % n.val = z % n.val + 1 := mod_lt_succ_mod_add_one n.2 hcol
        let edge := build_walk_horiz (z / n.val) (z % n) ((z + 1) % n)
          (Nat.div_lt_iff_lt_mul n.2 |>.mpr hzLt) (Nat.mod_lt _ n.2) (Nat.mod_lt _ n.2)

        let edge' : x1.Walk ⟨z, by omega⟩ ⟨z + 1, by omega⟩ := edge.copy
          (by simp [to1d, Nat.mod_add_div'])
          (by simp [to1d, this, Nat.add_right_comm _ 1, Nat.mod_add_div'])

        edge'.append (build_walk_full (z + 1))
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
          apply (SimpleGraph.fromRel_adj ..).mpr
          refine ⟨by simp, ?_⟩
          left
          simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, set1]
          convert somethingk52 adj
          · simp [a]
          · simp [b]

        have := Nat.div_mul_cancel (not_not.mp hcol)
        let walk_horiz := build_walk_horiz ((z + 1) / n.val) 0 (n.val - 1)
          (Nat.div_lt_iff_lt_mul n.2 |>.mpr hz1Lt)
        let walk_horiz' : x1.Walk ⟨z + 1, by omega⟩ ⟨z + n.val, by omega⟩ := walk_horiz.copy
          (by simp [to1d]; omega) (by simp [to1d]; omega)
        let tail := walk_horiz'.reverse.append (build_walk_full (z + 1) (by omega))

        SimpleGraph.Walk.cons edge tail
    exact build_walk_full 0
  have top := transpositions_generate_symm_group_iff_connected_graph set1_swap |>.mpr ff
  rw [Subgroup.eq_top_iff']
  intro s
  let ⟨l, hl, hl2⟩ : ∃ l : List (Equiv.Perm (Fin (m * n))), (∀ x ∈ l, x.IsAdjacentSwap) ∧ l.prod = s.α := by
    have : (s.α : Equiv.Perm _) ∈ Subgroup.closure set1 := by rw [top]; trivial
    let ⟨l, hl1, hl2⟩ := Subgroup.exists_list_of_mem_closure (s := set1) this
    use l
    refine ⟨?_, hl2⟩
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
    obtain ⟨r, hr1, hr2⟩ := this
    have : x.support.card = 2 := Equiv.Perm.card_support_eq_two.mpr sw
    have : x.support.toList.length = 2 := this ▸ Finset.length_toList _
    set a := to2d x.support.toList[0]
    set b := to2d x.support.toList[1]
    simp only [Rectangle.toSpin, Equiv.ext_iff, Equiv.coe_fn_mk] at hr2

    have ha : a.IsInside r := by
      by_contra k
      have := hr2 (to1d a)
      simp [k] at this
      absurd this.symm
      apply Equiv.Perm.mem_support.mp
      simp only [a, to1d_to2d_inverse]
      exact Finset.mem_toList.mp (List.getElem_mem _)
    have hb : b.IsInside r := by
      by_contra k
      have := hr2 (to1d b)
      simp [k] at this
      absurd this.symm
      apply Equiv.Perm.mem_support.mp
      simp only [b, to1d_to2d_inverse]
      exact Finset.mem_toList.mp (List.getElem_mem _)

    have : (to1d a) ≠ (to1d b) := by
      simp only [to1d_to2d_inverse, ne_eq, a, b]
      exact List.Nodup.getElem_inj_iff (Finset.nodup_toList _) |>.mp.mt (by decide)
    have hab : a ≠ b := by simpa using this
    have ha2 := somethink8 hr1 ha
    have hb2 := somethink8 hr1 hb
    rcases ha2 with ha2 | ha2
    · have := hb2.resolve_left (ne_of_eq_of_ne ha2 hab)
      exact ha2 ▸ this ▸ Rectangle.swap_iff.mp hr1
    · have := hb2.resolve_right (ne_of_eq_of_ne ha2 hab)
      exact ha2 ▸ this ▸ Rectangle.swap_iff.mp hr1 |>.symm

  have ⟨l, hl1, hl2⟩ : ∃ l : List (Spin m n), l.prod.α = s.α ∧ (∀ x ∈ l, x ∈ mySet m n) := by
    let y' : List (Rectangle m n) := l.attach.map (fun ⟨i, hi⟩ =>
      have := (hl _ hi).list_card
      let a := to2d i.support.toList[0]
      let b := to2d i.support.toList[1]
      have adj : a.IsAdjacent b := (hl _ hi).isAdjacent
      if h : (to1d a) ≤ (to1d b) then
        have := somethingj h adj
        ⟨a, b, this.2, this.1⟩
      else
        have : (to1d b) ≤ (to1d a) := le_of_not_ge h
        have := somethingj this adj.symm
        ⟨b, a, this.2, this.1⟩
    )
    -- `reverse` since Equiv.Perm and Spin do multiplication in opposite directions
    let y : List (Spin m n) := y'.map (fun x => x.toSpin) |>.reverse
    use y
    constructor
    · simp only [to1d_to2d_inverse, List.map_map, Function.comp_def, prod_eq_refl_of_refl2,
        List.map_reverse, List.reverse_reverse, ← hl2, y, y']
      congr
      apply goAgain
      funext ⟨x, hx⟩
      have adj := (hl _ hx).isAdjacent
      have := (hl _ hx).list_card
      split_ifs
      · convert somethingk5 adj ?_
        · simp only [to1d_to2d_inverse]
          exact somethingk6 this |>.symm
        · simp
      · convert somethingk5 adj.symm ?_
        · simp only [to1d_to2d_inverse]
          rw [Equiv.swap_comm]
          exact somethingk6 this |>.symm
        · simp
    · intro x hx
      simp only [mySet, Finset.mem_map, Finset.mem_union]
      simp only [List.mem_reverse, List.mem_map, y] at hx
      obtain ⟨a, ha1, ha2⟩ := hx
      use a
      refine ⟨?_, ha2⟩
      right
      simp only [to1d_to2d_inverse, id_eq,
        List.mem_map, List.mem_attach, true_and, Subtype.exists, y'] at ha1
      obtain ⟨b1, b2, hb3⟩ := ha1
      apply Rectangle.swap_iff.mpr
      split_ifs at hb3
      · simp [← hb3];
        exact (hl _ b2).isAdjacent
      · simp [← hb3]
        exact (hl _ b2).isAdjacent.symm
  apply Subgroup.exists_list_of_mem_closure2
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
    · simp only [mySet, Finset.map_union, Finset.coe_union, Finset.coe_map,
        Function.Embedding.coeFn_mk, Set.mem_union, Set.mem_image, Finset.mem_coe]
      left
      let ⟨c1, _, c3⟩ := List.mem_filterMap.mp hx
      use ⟨to2d c1, to2d c1, Fin.le_refl _, Fin.le_refl _⟩
      constructor
      · simp [SpinSet, rectangleSet_cond_iff]
      · simp only [ne_eq, ite_not, Option.ite_none_left_eq_some, Option.some.injEq] at c3
        simp only [Rectangle.toSpin, ← c3.2, Spin.mk.injEq]
        constructor
        · rw [Equiv.ext_iff, Equiv.coe_fn_mk]
          simp_all [blah5]
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
