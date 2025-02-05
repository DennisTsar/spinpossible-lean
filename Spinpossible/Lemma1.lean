import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.GroupTheory.Perm.Sign

theorem Subgroup.exists_list_of_mem_closure [Group M] {s : Set M} {a : M} :
    a ∈ Subgroup.closure s ↔ ∃ l : List M, (∀ x ∈ l, x ∈ s ∨ x⁻¹ ∈ s) ∧ l.prod = a := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine Subgroup.closure_induction
      (fun {x} hxs => ⟨[x], List.forall_mem_singleton.2 <| Or.inl hxs, List.prod_singleton⟩)
      ⟨[], List.forall_mem_nil _, rfl⟩ ?_ ?_ h
    · intro a b ha hb ⟨La, _⟩ ⟨Lb, _⟩
      use La ++ Lb
      aesop
    · rintro a _ ⟨L, HL1, rfl⟩
      use L.map (·⁻¹) |>.reverse
      constructor
      · intro w hw
        have : w⁻¹ ∈ L := by simpa using hw
        exact inv_inv w ▸ (HL1 _ this) |>.symm
      · exact List.prod_inv_reverse L |>.symm
  · obtain ⟨l, hl, rfl⟩ := h
    apply list_prod_mem
    intro x hx
    rcases hl x hx with hs | hs
    · exact mem_closure.mpr fun K a => a hs
    · apply (Subgroup.inv_mem_iff _).mp
      exact mem_closure.mpr fun K a => a hs

open Equiv

lemma scanl_last_eq_foldl_perm {α β : Type*} (l : List α) (f : β → α → β) (x : β) :
    (List.scanl f x l)[l.length]'(by simp [List.length_scanl]) = List.foldl f x l := by
  induction' l with head _ ih generalizing x
  · rfl
  · exact ih _

lemma foldl_perm_eq_prod_rev {α : Type*} (l : List (Perm α)) (x : α) :
    List.foldl (fun a τ => τ a) x l = l.reverse.prod x := by
  induction l generalizing x
  · rfl
  · simp_all

lemma isSwap_inv_eq_self [DecidableEq α] {x : Perm α} (h : x.IsSwap) : x = x⁻¹ := by
  let ⟨_, _, _, hswap⟩ := h
  rw [hswap, swap_inv]

lemma isSwap_inv_eq_self' [DecidableEq α] {x : Perm α} (h : x⁻¹.IsSwap) : x = x⁻¹ := by
  let ⟨_, _, _, hswap⟩ := h
  have := congr($hswap⁻¹)
  rwa [inv_inv, swap_inv, ← hswap] at this

lemma isSwap_swap_ne [DecidableEq α] {x y : α} (h : (swap x y).IsSwap) : x ≠ y := by
  by_contra h_eq
  obtain ⟨_, _, h1, hswap⟩ := swap_self y ▸ h_eq ▸ h
  exact h1 (swap_eq_refl_iff.mp hswap.symm)

private lemma graph_connected.aux1 [DecidableEq α]
    {l : List (Perm α)} (hl : ∀ τ ∈ l, τ.IsSwap) (h : l.prod = swap x y) :
    (List.scanl (fun a τ => τ a) x l)[l.length]'(by simp [List.length_scanl]) = y := by
  have h_prod_reverse : l.reverse.prod = l.prod⁻¹ := by
    have : ∀ w ∈ l, w⁻¹ = w := fun w hw => isSwap_inv_eq_self (hl w hw) |>.symm
    simpa [List.map_eq_map_iff.mpr this, List.map_id] using l.prod_reverse_noncomm
  rw [scanl_last_eq_foldl_perm, foldl_perm_eq_prod_rev,
    h_prod_reverse, h, swap_inv, swap_apply_left]

lemma graph_connected [DecidableEq α] [Nonempty α] (E : Set (Perm α))
    (hE : ∀ σ ∈ E, σ.IsSwap) (h_closure : Subgroup.closure E = ⊤) :
    (SimpleGraph.fromRel (fun x y => swap x y ∈ E)).Connected := by
  apply SimpleGraph.Connected.mk
  set G := SimpleGraph.fromRel (fun x y => swap x y ∈ E)
  -- Define the action of the subgroup generated by E on α
  let H := Subgroup.closure E
  have hH_top : H = ⊤ := h_closure
  intro x y
  have h_swap_in_H : swap x y ∈ H := hH_top ▸ Subgroup.mem_top _
  -- Express swap x y as a product of elements from E
  let ⟨l, hlE, hl_prod⟩ : ∃ l : List (Perm α), (∀ τ ∈ l, τ ∈ E) ∧ l.prod = swap x y := by
    let ⟨l, h1, h2⟩ := Subgroup.exists_list_of_mem_closure.mp h_swap_in_H
    use l, fun τ a => ?_, h2
    rcases h1 _ a with h | h
    · exact h
    · rwa [isSwap_inv_eq_self (hE _ h), inv_inv] at h
  -- Build the sequence of vertices starting from x by applying the permutations in l
  let vertices := l.scanl (fun a τ => τ a) x
  have : vertices.length = l.length + 1 := l.length_scanl x
  have h_adj : ∀ i (hi : i < l.length), vertices[i] ≠ vertices[i+1] →
      G.Adj vertices[i] vertices[i+1] := by
    intro i hi hj
    refine (SimpleGraph.fromRel_adj ..).mpr ⟨hj, Or.inl ?_⟩
    let τ := l[i]
    have hτE : τ ∈ E := hlE τ (l.getElem_mem hi)
    obtain ⟨a, b, _, hτ_eq⟩ := hE τ hτE
    have h_next : vertices[i+1] = τ vertices[i] := List.getElem_succ_scanl _
    rw [h_next, hτ_eq]
    by_cases h_case : vertices[i] = a
    · rwa [h_case, swap_apply_left, ← hτ_eq]
    · by_cases h_case' : vertices[i] = b
      · rwa [h_case', swap_apply_right, swap_comm, ← hτ_eq]
      · simp_all [swap_apply_of_ne_of_ne h_case h_case']
  -- Construct the path from x to y using the sequence of vertices
  let rec build_walk (n : Nat) (hn : n ≤ l.length) : G.Walk vertices[n] vertices[l.length] :=
    if h_eq : n = l.length then
      SimpleGraph.Walk.nil.copy rfl (by congr)
    else
      let tail := build_walk (n + 1) (by omega)
      if v_eq : vertices[n] = vertices[n+1] then
        v_eq ▸ tail
      else
        have edge : G.Adj vertices[n] vertices[n+1] := h_adj n (by omega) v_eq
        SimpleGraph.Walk.cons edge tail
  -- Build the walk starting from n = 0
  let walk := build_walk 0 l.length.zero_le
  have h_start : vertices[0] = x := List.getElem_scanl_zero
  have h_end : vertices[l.length] = y := graph_connected.aux1 (fun τ a => hE τ (hlE τ a)) hl_prod
  exact ⟨h_start ▸ h_end ▸ walk⟩

/--
  **Lemma 1**: Let `E ⊆ Perm α` be a set of transpositions acting on a finite type `α`.
  Let `G` be the undirected graph on `α` with edge set `E`.
  Then `E` generates the symmetric group `Perm α` if and only if `G` is connected.
-/
theorem transpositions_generate_symm_group_iff_connected_graph
    {α : Type*} [DecidableEq α] [Finite α] [Nonempty α]
    {E : Set (Perm α)}
    (hE : ∀ σ ∈ E, σ.IsSwap) :
    Subgroup.closure E = ⊤ ↔ (SimpleGraph.fromRel (fun x y => swap x y ∈ E)).Connected := by
  refine ⟨graph_connected E hE, ?_⟩
  intro hG_connected
  apply (Subgroup.eq_top_iff' _).mpr
  intro σ
  induction' σ using Perm.swap_induction_on with τ a b hab hτ
  · exact Subgroup.one_mem _
  · clear hab
    refine Subgroup.mul_mem _ ?_ hτ
    let ⟨p⟩ : (SimpleGraph.fromRel _).Reachable a b := hG_connected a b
    induction' p with a x y z adj_edge _ ih
    · exact swap_self a ▸ Subgroup.one_mem _
    · by_cases h_eq : x = z
      · exact h_eq ▸ swap_self x ▸ Subgroup.one_mem _
      have swap_xy_in_E : swap x y ∈ E := by
        have := (SimpleGraph.fromRel_adj ..).mp adj_edge |>.2
        rwa [swap_comm y x, or_self] at this
      have swap_xz_eq : swap y z * swap x y * swap y z = swap z x :=
        swap_mul_swap_mul_swap (isSwap_swap_ne (hE _ swap_xy_in_E)) h_eq
      rw [swap_comm, ← swap_xz_eq,
        Subgroup.mul_mem_cancel_right _ ih, Subgroup.mul_mem_cancel_left _ ih]
      exact Subgroup.subset_closure swap_xy_in_E
