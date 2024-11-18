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
    id := s.α.toFun (to1d ⟨i, j⟩) + 1,
    orient := if s.u (to1d ⟨i, j⟩) = 0 then orientation.positive else orientation.negative
  }

def standardBoard (m n : PNat) : board m n := (1 : Spin m n).toBoard

def orientation.other (o : orientation) : orientation :=
  match o with
  | orientation.positive => orientation.negative
  | orientation.negative => orientation.positive

@[simp]
lemma orientation.other_self (o : orientation) : o.other.other = o :=
  match o with
  | orientation.positive => rfl
  | orientation.negative => rfl

-- Action of Spin(m x n) on a board
-- TODO: define board.toSpin and define this as (s * b.toSpin).toBoard
def Spin.actionOnBoard {m n : PNat} (s : Spin m n) (b : board m n) : board m n :=
  fun i j =>
    let origPos := to1d ⟨i, j⟩
    let newPos := s.α.symm origPos
    let ⟨newI, newJ⟩ := to2d newPos
    let tile := b newI newJ
    if s.u origPos = 1 then { tile with orient := tile.orient.other } else tile

-- Function to perform a spin on a board using the defined Spin action
def performSpin (r : Rectangle m n) (b : board m n) : board m n :=
  r.toSpin.actionOnBoard b
