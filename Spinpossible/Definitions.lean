import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

universe u

def perm (N : Nat) := Equiv.Perm (Fin N)

namespace perm

  -- apply α and then β
  def actionRight (α β : perm N) : perm N := α.trans β

  instance : Mul (perm N) := ⟨actionRight⟩

end perm

def VN (N : Nat) := Fin N → ZMod 2

structure Spin (m n : PNat) where
  α : perm (m * n)
  u : VN (m * n)

namespace Spin

  def mul (x y : Spin m n) : Spin m n :=
    {
      α := x.α * y.α,
      u := fun i => x.u (y.α.invFun i) + y.u i
    }

  instance : Mul (Spin m n) := ⟨mul⟩

end Spin

inductive orientation
  | positive
  | negative
  deriving DecidableEq, Repr

structure tile where
  id : Nat
  orient : orientation
  deriving DecidableEq, Repr

def board (m n : PNat) := Matrix (Fin m) (Fin n) tile

-- Step 2: Action of Spin m x n on board

@[ext]
structure Point (m n : PNat) where
  row : Fin m
  col : Fin n

@[simp]
lemma point_eq (p : Point m n) : ⟨p.row, p.col⟩ = p := rfl

-- Convert 2D coordinates to 1D (flattened)
def to1d (pos : Point m n) : Fin (m * n) := by
  apply Fin.mk
  calc
    pos.2.val + pos.1.val * n < n + pos.1.val * n := by apply Nat.add_lt_add_right pos.2.isLt
    _ = (pos.1.val + 1) * n := by rw [Nat.succ_mul, Nat.add_comm]
    _ ≤ m * n := Nat.mul_le_mul_right n pos.1.isLt

-- Convert 1D coordinates (flattened) to 2D
def to2d {m n : PNat} (pos : Fin (m * n)) : Point m n :=
  ⟨⟨pos.val / n, Nat.div_lt_of_lt_mul (Nat.mul_comm m n ▸ pos.isLt)⟩,
  ⟨pos.val % n, Nat.mod_lt pos n.pos⟩⟩

@[simp]
lemma to2d_to1d_inverse : to2d (to1d p) = p := by
  rw [to1d, to2d]
  congr
  · simp [Nat.add_mul_div_right, Nat.div_eq_of_lt]
  · simp [Nat.mod_eq_of_lt]

@[simp]
lemma to1d_to2d_inverse : (to1d (to2d p)) = p := by
  simp only [to1d, to2d, Nat.mod_add_div']

def standardBoard (m n : PNat) : board m n :=
  fun i j => {id := to1d ⟨i, j⟩ + 1, orient := orientation.positive}

def orientation.other (o : orientation) : orientation :=
  match o with
  | orientation.positive => orientation.negative
  | orientation.negative => orientation.positive

lemma orientation.other_self (o : orientation) : o.other.other = o :=
  match o with
  | orientation.positive => rfl
  | orientation.negative => rfl

-- Action of Spin(m x n) on a board
def Spin.actionOnBoard {m n : PNat} (s : Spin m n) (b : board m n) : board m n :=
  fun i j =>
    let origPos := to1d ⟨i, j⟩
    let newPos := s.α.symm origPos
    let ⟨newI, newJ⟩ := to2d newPos
    let tile := b newI newJ
    if s.u origPos = 1 then { tile with orient := tile.orient.other } else tile

@[ext]
structure Rectangle (m n : PNat) where
  topLeft : Point m n
  bottomRight : Point m n
  validCol : topLeft.col ≤ bottomRight.col := by decide
  validRow : topLeft.row ≤ bottomRight.row := by decide

def Point.IsInside (p : Point m n) (r : Rectangle m n) : Prop :=
  r.topLeft.row.val ≤ p.1.val ∧ p.1.val ≤ r.bottomRight.row.val ∧
  r.topLeft.col.val ≤ p.2.val ∧ p.2.val ≤ r.bottomRight.col.val

-- don't know if there is a better way to do this
instance : Decidable (Point.IsInside p r) := And.decidable

def rotateCalc (a b c : Fin n) : Fin n := by
  apply Fin.mk
  calc
    a.val - (b.val - c.val) ≤ a.val := by apply Nat.sub_le
    _                       < n     := a.isLt

lemma rotateCalc_self_inverse (h1 : a ≥ i) (h2 : i ≥ b) : rotateCalc a (rotateCalc a i b) b = i := by
  simp only [rotateCalc, Nat.sub_sub, Nat.sub_sub_self h1, Nat.sub_add_cancel h2]

-- Function to calculate the new position after 180 degree rotation around the rectangle center
def rotate180 (p : Point m n) (r : Rectangle m n) : Point m n :=
  ⟨rotateCalc r.bottomRight.row p.1 r.topLeft.row, rotateCalc r.bottomRight.col p.2 r.topLeft.col⟩

lemma rotate180_self_inverse (h : p.IsInside r) : rotate180 (rotate180 p r) r = p := by
  simp_rw [Point.IsInside, Fin.val_fin_le] at h
  simp [h, rotate180, rotateCalc_self_inverse]

lemma spin_stays_inside (h : p.IsInside r) : (rotate180 p r).IsInside r := by
  simp_rw [Point.IsInside, Fin.val_fin_le] at h
  simp_rw [Point.IsInside, rotate180, rotateCalc, tsub_le_iff_right]
  simp [h, tsub_tsub_assoc]

-- Define a function to create a Spin element for a rectangle spin
def Rectangle.toSpin (r : Rectangle m n) : Spin m n :=
  {
    α := Equiv.mk
      (fun pos =>
        let p := to2d pos
        if p.IsInside r then to1d (rotate180 p r) else pos
      )
      (fun pos =>
        let p := to2d pos
        if p.IsInside r then to1d (rotate180 p r) else pos
      )
      (by
        apply Function.leftInverse_iff_comp.mpr
        funext x
        by_cases h : (to2d x).IsInside r
        · simp [h, spin_stays_inside, rotate180_self_inverse]
        · simp [h]
      )
      (by
        apply Function.leftInverse_iff_comp.mpr
        funext x
        by_cases h : (to2d x).IsInside r
        · simp [h, spin_stays_inside, rotate180_self_inverse]
        · simp [h]
      ),
    u := fun pos => if (to2d pos).IsInside r then 1 else 0
  }

-- Function to perform a spin on a board using the defined Spin action
def performSpin (r : Rectangle m n) (b : board m n) : board m n :=
  r.toSpin.actionOnBoard b
