import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Zmod.Basic

universe u

def perm (N : Nat) := Equiv.Perm (Fin N)

namespace perm

  def action_right {N : Nat} (α β : perm N) : perm N :=
    α.trans β

  instance {N : Nat} : Mul (perm N) :=
    ⟨action_right⟩

end perm

def VN (N : Nat) := Fin N → ZMod 2

namespace VN

  def add {N : Nat} (v w : VN N) : VN N :=
    fun i => v i + w i

  instance {N : Nat} : Add (VN N) :=
    ⟨add⟩

  def action {N : Nat} (v : VN N) (α : perm N) : VN N :=
    fun i => v (α.symm i)

end VN

structure Spin (m n : Nat) where
  (α : perm (m * n))
  (u : VN (m * n))

namespace Spin

  def mul {m n : Nat} (x y : Spin m n) : Spin m n :=
    {
      α := x.α * y.α,
      u := fun i => x.u i + VN.action y.u x.α i
    }

  instance {m n : Nat} : Mul (Spin m n) :=
    ⟨mul⟩

end Spin

inductive orientation
  | positive
  | negative
  deriving DecidableEq, Repr

structure tile where
  id : Nat
  orient : orientation
  deriving DecidableEq, Repr

structure PosNat := (val : Nat) (isPos : val > 0 := by decide)
-- def PosNat := { val : Nat // val > 0 }

instance : Coe PosNat Nat := ⟨fun n => n.val⟩

def board (m n : PosNat) := Matrix (Fin m) (Fin n) tile

-- Step 2: Action of Spin m x n on board

structure Point (m n : Nat) where
  row : Fin m
  col : Fin n

-- Convert 2D coordinates to 1D (flattened)
def to_1d {m n : Nat} (pos : Point m n) : Fin (m * n) := by
  apply Fin.mk
  calc
    pos.1.val * n + pos.2.val < pos.1.val * n + n := add_lt_add_left (Fin.is_lt pos.2) _
    _ = (pos.1.val + 1) * n := by rw [add_mul, one_mul]
    _ ≤ m * n := Nat.mul_le_mul_right n pos.1.is_lt

-- Convert 1D coordinates (flattened) to 2D
def to_2d {m n : PosNat} (pos : Fin (m * n)) : Point m n :=
  ⟨⟨pos.val / n, Nat.div_lt_of_lt_mul (Nat.mul_comm m n ▸ pos.isLt)⟩,
  ⟨pos.val % n, Nat.mod_lt pos n.isPos⟩⟩

def standard_board (m n : PosNat) : board m n :=
  fun i j => {id := to_1d ⟨i, j⟩ + 1, orient := orientation.positive}

-- Action of a permutation on VN to match the paper's notation vα
def action {N : Nat} (v : VN N) (α : perm N) : VN N :=
  fun i => v (α.symm i)

-- Action of Spin(m x n) on a board
def Spin.action_on_board {m n : PosNat} (s : Spin m n) (b : board m n) : board m n :=
  fun i j =>
    let newPos := s.α.symm (to_1d ⟨i, j⟩)
    let ⟨newI, newJ⟩ := to_2d newPos
    let tile := b newI newJ
    if s.u newPos = 1 then
      { tile with orient := if tile.orient = orientation.positive then orientation.negative else orientation.positive }
    else tile

structure Rectangle (m n : Nat) where
  topLeft : Point m n
  bottomRight : Point m n
  validCol : topLeft.col ≤ bottomRight.col := by decide
  validRow : topLeft.row ≤ bottomRight.row := by decide

def isInsideRectangle {m n : Nat} (p : Point m n) (r : Rectangle m n) :=
  p.2 ≥ r.topLeft.col && p.2 ≤ r.bottomRight.col &&
  p.1 ≥ r.topLeft.row && p.1 ≤ r.bottomRight.row

-- Function to calculate the new position after 180 degree rotation around the rectangle center
def rotate180 {m n : Nat} (p : Point m n) (r : Rectangle m n) : Point m n :=
  let new_col := r.bottomRight.col - (p.2 - r.topLeft.col)
  let new_row := r.bottomRight.row - (p.1 - r.topLeft.row)
  ⟨new_row, new_col⟩

def flipOrientation (t : tile) : tile :=
  { t with orient := if t.orient = orientation.positive then orientation.negative else orientation.positive }

-- Define a function to create a Spin element for a rectangle spin
def createRectangleSpin {m n : PosNat} (r : Rectangle m n) : Spin m n :=
  {
    α := Equiv.mk
      (fun pos =>
        let p := to_2d pos
        if isInsideRectangle p r then
          to_1d (rotate180 p r)
        else
          pos
      )
      (fun pos =>
        let p := to_2d pos
        if isInsideRectangle p r then
          to_1d (rotate180 p r)
        else
          pos
      ) sorry sorry, -- Proof of bijectiveness for the permutation
    u := fun pos => if isInsideRectangle (to_2d pos) r then 1 else 0
  }

-- Function to perform a spin on a board using the defined Spin action
def performSpin {m n : PosNat} (r : Rectangle m n) (b : board m n) : board m n :=
  (createRectangleSpin r).action_on_board b

-- these seem useful
-- def is_lowercase_spin {m n : PosNat} (s : Spin m n) : Prop :=
--   ∃ (r : Rectangle m n), s = createRectangleSpin r


-- -- structure LowercaseSpin (m n : PosNat) where
-- --   val : Spin m n
-- --   valid : is_lowercase_spin val

-- -- instance {m n : PosNat} : Coe (LowercaseSpin m n) (Spin m n) := ⟨fun s => s.val⟩

-- def LowercaseSpin (m n : PosNat) := {s : Spin m n // is_lowercase_spin s}
-- instance {m n : PosNat} : Coe (LowercaseSpin m n) (Spin m n) := ⟨fun s => s.val⟩
