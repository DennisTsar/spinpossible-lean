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

lemma feelsomething {l : List (Spin m n)} (h : ∀ w ∈ l, w.α = Equiv.refl _) :
    l.prod.α = Equiv.refl _  := by
  induction' l with head tail ih
  · rfl
  · simp_all [Spin.mul_def, perm.mul_def]

lemma ZMod.cases_two (a : ZMod 2) : a = 0 ∨ a = 1 :=
  match a with
  | 0 => Or.inl rfl
  | 1 => Or.inr rfl

lemma sum_eq_sum_take_add_nthLe_add_sum_drop_succ
  [AddCommMonoid α] (l : List α) (i : ℕ) (h : i < l.length) :
  l.sum = (l.take i).sum + l[i] + (l.drop (i + 1)).sum := by
  rw [← List.sum_take_add_sum_drop l (i + 1), List.sum_take_succ]

lemma hou [AddCommMonoid α] (l : List α) (i : Fin l.length) :
  (l.eraseIdx i).sum + l[i] = l.sum := by
  have h₁ : l.sum = (l.take i).sum + l[i] + (l.drop (i + 1)).sum :=
    sum_eq_sum_take_add_nthLe_add_sum_drop_succ l i i.isLt
  have h₂ : (l.eraseIdx i).sum = (l.take i).sum + (l.drop (i + 1)).sum := by
    rw [List.eraseIdx_eq_take_drop_succ l i, List.sum_append]
  rw [h₁, h₂]
  exact add_right_comm _ _ _

lemma hou2 [AddCommMonoid α] (l : List α) (i : Fin l.length) : l.sum = (l[i] :: l.eraseIdx i).sum := by
  rw [List.sum_cons, add_comm, hou l i]

example {s : Spin m n} {l k : List (Spin m n)} (hl : l.prod.α = s.α)
    (hk : k = (List.finRange (↑m * ↑n)).filterMap (
      fun isp ↦
      if l.prod.u isp ≠ s.u isp
      then some ⟨Equiv.refl _, fun j ↦ if isp = j then 1 else 0⟩
      else none)
    ) : (l ++ k).prod = s := by
  simp [List.prod_append, Spin.mul_def]
  have zx : ∀ w ∈ k, w.α = Equiv.refl _ := by
    intro w hw
    simp [hk] at hw
    aesop
  have asd : k.prod.α = Equiv.refl _ := feelsomething zx
  ext
  · rw [asd]
    exact hl
  · funext i
    simp only [hl, Equiv.refl_symm, Equiv.refl_apply]
    have bam : k.prod.u i = (k.map (fun x => x.u i)).sum := by
      clear hk asd
      induction' k with head tail ih
      · rw [List.prod_nil, Spin.one_def, List.map_nil, List.sum_nil]
      · have : ∀ w ∈ tail, w.α = Equiv.refl _ := by
          intro w hw
          exact zx _ (List.mem_cons_of_mem head hw)
        simp [Spin.mul_def, feelsomething this, ih this]
    have : l.prod.u i = s.u i ∨ l.prod.u i = s.u i + 1 := by
      cases (l.prod.u i).cases_two <;> cases (s.u i).cases_two <;> simp [*]
    rcases this with h2 | h2
    · have : ∀ e ∈ k, e.u i = 0 := by aesop
      simp [asd, h2, bam, List.map_eq_map_iff.mpr this]
    · simp only [asd, Equiv.refl_symm, Equiv.refl_apply, h2, bam]
      apply add_eq_of_eq_add_neg
      simp only [CharTwo.neg_eq, add_right_inj]

      have knodup : k.Nodup := by
        rw [hk]
        refine List.Nodup.filterMap ?_ (List.nodup_finRange _)
        intro a1 a2 s hs1 hs2
        simp only [ne_eq, ite_not, Option.mem_def, Option.ite_none_left_eq_some,
          Option.some.injEq] at hs1 hs2
        have := hs1.2 ▸ hs2.2
        simp only [Spin.mk.injEq, true_and] at this
        replace := congr($this a1)
        symm; simpa

      let x_i_def : Spin m n :=
        { α := Equiv.refl _, u := fun j ↦ if i = j then 1 else 0 }
      have x_i_in_k : x_i_def ∈ k := by
        rw [hk]
        apply List.mem_filterMap.mpr
        use ⟨i, by simp⟩
        simp [h2]

      obtain ⟨p1, ha1, ha2⟩ := List.getElem_of_mem x_i_in_k

      set l3 := List.map (fun x ↦ x.u i) k
      have klength : l3.length = k.length := by simp [l3]
      have cc2 : ∀ (y : Fin k.length), l3[y] = 1 → y = p1 := by
        intro y hy
        have : k[y] = x_i_def := by
          simp [l3] at hy
          have : k[y] ∈ k := by simp
          set hh := k[y]
          simp [hy, hk] at this
          obtain ⟨b1, -, b3⟩ := this
          ext
          · simp [x_i_def, ←b3]
          · simp [x_i_def]
            have := congr(Spin.u $b3)
            simp only at this
            have asd : b1 = i := by
              have := congr(Spin.u $b3)
              rw [funext_iff] at this
              have := this i
              simp at this
              simpa [hy, hh] using this
            exact asd ▸ this.symm
        by_contra! hg
        absurd knodup
        refine List.not_nodup_of_get_eq_of_ne k ⟨p1, ha1⟩ y ?_ (Fin.ne_of_val_ne hg.symm)
        simp [ha2, ← Fin.getElem_fin, this]
      have cc3 : ∀ e ∈ l3, e = 1 → e = l3[p1] := by simp_all [l3]
      rw [@Finset.sum_list_count]
      simp
      set u := l3[p1] with hu
      have hu : u = 1 := by simp [hu, l3, ha2]
      have : ¬List.Duplicate u l3 := by
        by_contra! h
        rw [@List.duplicate_iff_exists_distinct_get] at h
        obtain ⟨u1, u2, u3, u4⟩ := h
        simp [hu] at u4
        have : u1.val < u2.val := by omega
        have q1 := cc2 ⟨u1, klength ▸ u1.2⟩ (by rw [Fin.getElem_fin, u4.1])
        have q2 := cc2 ⟨u2, klength ▸ u2.2⟩ (by rw [Fin.getElem_fin, u4.2])
        simp only at q1 q2
        omega
      have : List.count u l3 = 1 := by
        have := List.duplicate_iff_two_le_count.mpr.mt this
        have : List.count u l3 > 0 := List.count_pos_iff.mpr (List.getElem_mem _)
        omega
      rw [Finset.sum_eq_single u]
      · rw [this, hu]; decide
      · intro b hb hb2
        have ff := cc3 b (List.mem_dedup.mp hb) |>.mt hb2
        have : b = 0 := not_not.mp ((or_iff_not_imp_left.mp b.cases_two).mt ff)
        rw [this, mul_zero]
      · intro h
        absurd h
        exact List.mem_toFinset.mpr (List.getElem_mem _)
