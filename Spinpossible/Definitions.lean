import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic

def perm (N : Nat) := Equiv.Perm (Fin N)

namespace perm

-- apply α and then β
def actionRight (α β : perm N) : perm N := α.trans β

instance : Mul (perm N) := ⟨actionRight⟩

def mul_def (α β : perm N) : α * β = α.trans β := rfl

end perm

def VN (N : Nat) := Fin N → ZMod 2

instance : DecidableEq (VN N) := inferInstanceAs (DecidableEq (Fin N → ZMod 2))

instance : DecidableEq (perm N) := inferInstanceAs (DecidableEq (Fin N ≃ Fin N))

@[ext]
structure Spin (m n : PNat) where
  α : perm (m * n)
  u : VN (m * n)
  deriving DecidableEq

namespace Spin

def mul (x y : Spin m n) : Spin m n where
  α := x.α * y.α
  u := fun i => x.u (y.α.invFun i) + y.u i

instance : Mul (Spin m n) := ⟨mul⟩

lemma mul_def (x y : Spin m n) : x * y = ⟨x.α * y.α, fun i => x.u (y.α.invFun i) + y.u i⟩ := rfl

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

@[ext, pp_using_anonymous_constructor]
structure Point (m n : PNat) where
  row : Fin m
  col : Fin n
  deriving DecidableEq, Repr

@[simp]
lemma point_eq (p : Point m n) : ⟨p.row, p.col⟩ = p := rfl

-- Convert 2D coordinates to 1D (flattened)
def to1d (pos : Point m n) : Fin (m * n) where
  val := pos.2.val + pos.1.val * n
  isLt := by calc
    pos.2.val + pos.1.val * n < n + pos.1.val * n := by apply Nat.add_lt_add_right pos.2.isLt
    _ = (pos.1.val + 1) * n := by ring
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

@[simp]
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

@[ext, pp_using_anonymous_constructor]
structure Rectangle (m n : PNat) where
  topLeft : Point m n
  bottomRight : Point m n
  validCol : topLeft.col ≤ bottomRight.col := by decide
  validRow : topLeft.row ≤ bottomRight.row := by decide
  deriving DecidableEq, Repr

def Point.IsInside (p : Point m n) (r : Rectangle m n) : Prop :=
  r.topLeft.row.val ≤ p.1.val ∧ p.1.val ≤ r.bottomRight.row.val ∧
  r.topLeft.col.val ≤ p.2.val ∧ p.2.val ≤ r.bottomRight.col.val

-- don't know if there is a better way to do this
instance : Decidable (Point.IsInside p r) := instDecidableAnd

abbrev rotateCalc (a b c : Fin n) : Fin n where
  val := a.val - (b.val - c.val)
  isLt := by omega

-- Function to calculate the new position after 180 degree rotation around the rectangle center
def rotate180 (p : Point m n) (r : Rectangle m n) : Point m n :=
  ⟨rotateCalc r.bottomRight.row p.1 r.topLeft.row, rotateCalc r.bottomRight.col p.2 r.topLeft.col⟩

@[simp]
lemma rotate180_self_inverse (h : p.IsInside r) : rotate180 (rotate180 p r) r = p := by
  dsimp [Point.IsInside, rotate180] at *
  ext <;> simp only [Nat.sub_sub_self] <;> omega

lemma spin_stays_inside (h : p.IsInside r) : (rotate180 p r).IsInside r := by
  dsimp [Point.IsInside, rotate180] at *; omega

-- Define a function to create a Spin element for a rectangle spin
def Rectangle.toSpin (r : Rectangle m n) : Spin m n where
  α := Equiv.mk
    (fun pos =>
      let p := to2d pos
      if p.IsInside r then to1d (rotate180 p r) else pos
    )
    (fun pos =>
      let p := to2d pos
      if p.IsInside r then to1d (rotate180 p r) else pos
    )
    (fun x => by
      by_cases h : (to2d x).IsInside r
      · simp [h, spin_stays_inside]
      · simp [h]
    )
    (fun x => by
      by_cases h : (to2d x).IsInside r
      · simp [h, spin_stays_inside]
      · simp [h]
    )
  u := fun pos => if (to2d pos).IsInside r then 1 else 0

-- Function to perform a spin on a board using the defined Spin action
def performSpin (r : Rectangle m n) (b : board m n) : board m n :=
  r.toSpin.actionOnBoard b
