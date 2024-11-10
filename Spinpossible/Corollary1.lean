import Spinpossible.Prop2

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

example {s : Spin m n} {l k : List (Spin m n)} (hl : l.prod.α = s.α)
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
