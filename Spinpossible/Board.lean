import Spinpossible.Definitions
import Mathlib.Data.Matrix.Basic

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

def board.toSpin (b : board m n) : Spin m n :=
  let tiles_list : List tile :=
    (List.finRange m).bind (fun i => (List.finRange n).map (fun j => b i j))
  have : tiles_list.length = m * n := by simp [tiles_list, Function.comp_def]
  let one : Nat := 1 -- Not inlined to prevent coercions to Fin
  {
    α := Equiv.mk
      (fun i => (tiles_list.findIdx (fun j => j.id - one == i.val)))
      (fun i => ((tiles_list[i]).id - one).cast)
      (by
        intro p
        simp only [Fin.getElem_fin, Fin.val_natCast]
        let e := List.findIdx (fun j ↦ j.id - one == p.val) tiles_list
         -- True assuming board contains each tile exactly once
        have : e < tiles_list.length := sorry
        have zx : e < (↑m * ↑n) := by omega
        simp_rw [Nat.mod_eq_of_lt zx]
        suffices tiles_list[e].id - one = p by simp_all [e]
        have zx : e % (↑m * ↑n) = e := by simp_all [Nat.mod_eq_of_lt]
        have := @List.findIdx_getElem _ _ _ this
        exact Nat.eq_of_beq_eq_true this
      )
      (by
        -- True assuming board contains proper numbers
        have fact1 : ∀ x ∈ tiles_list, x.id > 0 ∧ x.id < m * n := sorry
         -- True assuming board contains each tile exactly once
        have fact2 : ∀ x y : Fin (tiles_list.length), tiles_list[x].id = tiles_list[y].id → x = y := sorry

        intro p
        simp only [Fin.val_natCast]
        have : tiles_list[p].id > 0 ∧ tiles_list[p].id < m * n := fact1 _ (List.getElem_mem _)
        rw [Nat.mod_eq_of_lt (by omega)]
        let e := (List.findIdx (fun j ↦ j.id - one == tiles_list[↑p].id - one) tiles_list)
         -- True assuming board contains each tile exactly once
        have : e < tiles_list.length := sorry
        suffices e = p by simp_all [e]
        have := @List.findIdx_getElem _ _ _ this
        have : tiles_list[e].id - one = tiles_list[p].id - one := Nat.eq_of_beq_eq_true this
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
