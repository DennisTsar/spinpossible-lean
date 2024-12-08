import Spinpossible.Definitions
import Mathlib.Data.Matrix.Defs
import Mathlib.Data.ZMod.Basic

inductive orientation
  | positive
  | negative
  deriving DecidableEq, Repr

structure tile where
  id : Nat
  orient : orientation
  deriving DecidableEq, Repr

def board (m n : PNat) := Matrix (Fin m) (Fin n) tile

def Spin.toBoard (s : Spin m n) : board m n :=
  fun i j => {
    id := s.α.symm (to1d ⟨i, j⟩) + 1,
    orient := if s.u (to1d ⟨i, j⟩) = 0 then orientation.positive else orientation.negative
  }

private def Matrix.toList (M : Matrix (Fin m) (Fin n) α) : List α :=
  (List.finRange m).flatMap (fun i => (List.finRange n).map (fun j => M i j))

def board.toSpin (b : board m n) : Spin m n :=
  let tiles_list : List tile := b.toList
  have tiles_list_def : b.toList = tiles_list := rfl
  have : tiles_list.length = m * n := by simp [Matrix.toList, tiles_list, Function.comp_def]

  have fact4 : (tiles_list.map (·.id)).toFinset = Finset.Icc 1 (m.val * n) := sorry

  have fact1 : ∀ x ∈ tiles_list, x.id > 0 ∧ x.id ≤ m * n := by
    intro x hx
    have : x.id ∈ (tiles_list.map (·.id)).toFinset := by
      simp_all [Matrix.toList, -fact4]
      use x
    simp only [fact4, Finset.mem_Icc, and_true] at this
    omega
  have fact2 : ∀ x y : Fin tiles_list.length, tiles_list[x].id = tiles_list[y].id → x = y := by
    intro x y hxy
    ext
    simp_all [Matrix.toList]
    have : (tiles_list.map (·.id)).length =
      (tiles_list.map (·.id)).toFinset.card := by simp_all
    have nodup := Multiset.toFinset_card_eq_card_iff_nodup.mp (this.symm)
    have : (tiles_list.map (·.id))[x] = (tiles_list.map (·.id))[y] := by simp_all
    have := (List.Nodup.get_inj_iff nodup).mp this
    exact Fin.mk.inj_iff.mp this

  let one : Nat := 1 -- Not inlined to prevent coercions to Fin
  {
    α := Equiv.mk
      (fun i => (tiles_list.findIdx (fun j => j.id - one == i.val)))
      (fun i => ((tiles_list[i]).id - one).cast)
      (by
        intro p
        simp only [Fin.getElem_fin, Fin.val_natCast]
        let e := List.findIdx (fun j ↦ j.id - one == p.val) tiles_list
        have : e < tiles_list.length := by
          apply List.findIdx_lt_length_of_exists
          by_contra! ht
          have qwe2 : ∀ x ∈ (tiles_list.map (·.id)).toFinset, x - one ≠ p := by
            intro x hx
            have : ∃ y ∈ tiles_list, y.id = x := by simp_all [-fact4]
            aesop
          have : ∀ x ∈ Finset.range (m.val * n.val), x ≠ p := by
            intro x hx
            have := qwe2 (x + one) (by simp_all; omega)
            simpa
          aesop
        have zx : e < (↑m * ↑n) := by omega
        simp_rw [Nat.mod_eq_of_lt zx]
        suffices tiles_list[e].id - one = p by simp_all [e]
        exact beq_iff_eq.mp <| List.findIdx_getElem (w := this)
      )
      (by
        intro p
        simp only [Fin.val_natCast]
        have : tiles_list[p].id > 0 ∧ tiles_list[p].id ≤ m * n := fact1 _ (List.getElem_mem _)
        rw [Nat.mod_eq_of_lt (by omega)]
        let e := (List.findIdx (fun j ↦ j.id - one == tiles_list[p].id - one) tiles_list)
        have : e < tiles_list.length := by
          apply List.findIdx_lt_length_of_exists
          by_contra! ht
          have qwe2 : ∀ x ∈ (tiles_list.map (·.id)).toFinset, x - one ≠ p := by
            intro x hx
            have : ∃ y ∈ tiles_list, y.id = x := by simp_all [-fact4]
            aesop
          have : ∀ x ∈ Finset.range (m.val * n.val), x ≠ p := by
            intro x hx
            have := qwe2 (x + one) (by simp_all; omega)
            simpa
          aesop
        suffices e = p by simp_all [e]
        have := List.findIdx_getElem (w := this)
        have : tiles_list[e].id - one = tiles_list[p].id - one := beq_iff_eq.mp this
        have : tiles_list[e].id > 0 := fact1 _ (List.getElem_mem _) |>.1
        have := fact2 ⟨e, by omega⟩ ⟨p, by omega⟩ (by simp [one] at *; omega)
        exact Fin.mk.inj_iff.mp this
      ),
    u := fun i => if (b (to2d i).row (to2d i).col).orient = orientation.positive then 0 else 1
  }

def standardBoard (m n : PNat) : board m n := (1 : Spin m n).toBoard

-- Action of Spin(m x n) on a board
def Spin.actionOnBoard {m n : PNat} (s : Spin m n) (b : board m n) : board m n :=
  b.toSpin * s |>.toBoard

-- Function to perform a spin on a board using the defined Spin action
def performSpin (r : Rectangle m n) (b : board m n) : board m n :=
  r.toSpin.actionOnBoard b
