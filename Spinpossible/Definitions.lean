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

-- structure PosNat := (val : Nat) (isPos : val > 0 := by decide)
-- -- def PosNat := { val : Nat // val > 0 }

-- instance : Coe PosNat Nat := ⟨fun n => n.val⟩

def board (m n : PNat) := Matrix (Fin m) (Fin n) tile

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
def to_2d {m n : PNat} (pos : Fin (m * n)) : Point m n :=
  ⟨⟨pos.val / n, Nat.div_lt_of_lt_mul (Nat.mul_comm m n ▸ pos.isLt)⟩,
  ⟨pos.val % n, Nat.mod_lt pos n.pos⟩⟩

lemma to_2d_to_1d_inverse : to_2d (to_1d p) = p := by
  simp [to_1d, to_2d, Nat.add_comm, Nat.add_mul_div_right, Nat.div_eq_of_lt, Nat.mod_eq_of_lt]

lemma to_1d_to_2d_inverse : (to_1d (to_2d p)) = p := by
  simp only [to_1d, to_2d, Nat.div_add_mod']

def standard_board (m n : PNat) : board m n :=
  fun i j => {id := to_1d ⟨i, j⟩ + 1, orient := orientation.positive}

-- Action of a permutation on VN to match the paper's notation vα
def action {N : Nat} (v : VN N) (α : perm N) : VN N :=
  fun i => v (α.symm i)

def orientation.other (o : orientation) : orientation :=
  match o with
  | orientation.positive  => orientation.negative
  | orientation.negative  => orientation.positive

-- Action of Spin(m x n) on a board
def Spin.action_on_board {m n : PNat} (s : Spin m n) (b : board m n) : board m n :=
  fun i j =>
    let newPos := s.α.symm (to_1d ⟨i, j⟩)
    let ⟨newI, newJ⟩ := to_2d newPos
    let tile := b newI newJ
    if s.u newPos = 1 then { tile with orient := tile.orient.other } else tile

structure Rectangle (m n : Nat) where
  topLeft : Point m n
  bottomRight : Point m n
  validCol : topLeft.col ≤ bottomRight.col := by decide
  validRow : topLeft.row ≤ bottomRight.row := by decide

-- make this a Prop ( & abbrev) and some problems go away while some others appear
def isInsideRectangle {m n : Nat} (p : Point m n) (r : Rectangle m n) : Bool :=
  p.2.val ≥ r.topLeft.col.val ∧ p.2.val ≤ r.bottomRight.col.val ∧
  p.1.val ≥ r.topLeft.row.val ∧ p.1.val ≤ r.bottomRight.row.val

def rotate_calc (a b c: Fin x) : Fin x :=
  have b2 : a.val - (b.val - c.val) < x := by
    calc
      a.val - (b.val - c.val) ≤ a.val := by
        exact Nat.sub_le a (b.val - c.val)
      _ < x := a.isLt
  ⟨a.val - (b.val - c.val), b2⟩

lemma rotate_calc_twice_inverse (h1 : i ≥ b) (h2 : a ≥ i) : rotate_calc a (rotate_calc a i b) b = i := by
  simp only [rotate_calc, Nat.sub_sub, Nat.sub_add_cancel h1, Nat.sub_sub_self h2]

-- Function to calculate the new position after 180 degree rotation around the rectangle center
def rotate180 {m n : Nat} (p : Point m n) (r : Rectangle m n) : Point m n :=
  ⟨rotate_calc r.bottomRight.row p.1 r.topLeft.row, rotate_calc r.bottomRight.col p.2 r.topLeft.col⟩

lemma rotate180_twice_inverse (h : isInsideRectangle p r) : rotate180 (rotate180 p r) r = p := by
  simp only [isInsideRectangle, Fin.val_fin_le, decide_eq_true_eq] at h  -- TODO: make this unnecessary?
  simp [h, rotate180, rotate_calc_twice_inverse]

lemma spin_stays_inside (h : isInsideRectangle p r) : isInsideRectangle (rotate180 p r) r := by
  simp only [isInsideRectangle, Fin.val_fin_le, decide_eq_true_eq] at h -- TODO: make this unnecessary?
  simp only [isInsideRectangle, rotate180, rotate_calc, tsub_le_iff_right]
  simp [h, tsub_tsub_assoc]

-- Define a function to create a Spin element for a rectangle spin
def createRectangleSpin {m n : PNat} (r : Rectangle m n) : Spin m n :=
  {
    α := Equiv.mk
      (fun pos =>
        let p := to_2d pos
        if isInsideRectangle p r then to_1d (rotate180 p r) else pos
      )
      (fun pos =>
        let p := to_2d pos
        if isInsideRectangle p r then to_1d (rotate180 p r) else pos
      )
      (by
        apply Function.leftInverse_iff_comp.mpr
        funext x
        by_cases h : isInsideRectangle (to_2d x) r
        . simp [h, to_2d_to_1d_inverse, to_1d_to_2d_inverse, spin_stays_inside, rotate180_twice_inverse]
        . simp [h]
      )
      (by
        apply Function.leftInverse_iff_comp.mpr
        funext x
        by_cases h : isInsideRectangle (to_2d x) r
        . simp [h, to_2d_to_1d_inverse, to_1d_to_2d_inverse, spin_stays_inside, rotate180_twice_inverse]
        . simp [h]
      ),
    u := fun pos => if isInsideRectangle (to_2d pos) r then 1 else 0
  }

-- Function to perform a spin on a board using the defined Spin action
def performSpin {m n : PNat} (r : Rectangle m n) (b : board m n) : board m n :=
  (createRectangleSpin r).action_on_board b
