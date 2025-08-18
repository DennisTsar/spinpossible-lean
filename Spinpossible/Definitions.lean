import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.PNat.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.DeriveFintype

abbrev perm (N : Nat) := Equiv.Perm (Fin N)

abbrev VN (N : Nat) := Fin N → ZMod 2

@[grind ext]
structure Spin (m n : PNat) where
  α : perm (m * n)
  u : VN (m * n)
  deriving DecidableEq, Fintype

-- manually define an `ext` lemma that uses function application
@[ext]
lemma Spin.ext {s1 s2 : Spin m n} (h1 : ∀ x, s1.α x = s2.α x) (h2 : ∀ x, s1.u x = s2.u x)
    : s1 = s2 := by
  obtain ⟨a, b⟩ := s1
  obtain ⟨c, d⟩ := s2
  congr
  · ext x : 1; exact h1 x
  · ext x : 1; exact h2 x

namespace Spin

def mul (x y : Spin m n) : Spin m n where
  α := y.α * x.α -- intentionally reversed
  u i := x.u (y.α.invFun i) + y.u i

instance : Mul (Spin m n) := ⟨mul⟩

lemma mul_def (x y : Spin m n) : x * y = ⟨x.α.trans y.α, fun i => x.u (y.α.invFun i) + y.u i⟩ := rfl

instance : One (Spin m n) := ⟨Equiv.refl _, fun _ => 0⟩

lemma one_def : (1 : Spin m n) = ⟨Equiv.refl _, fun _ => 0⟩ := rfl

end Spin

@[ext, grind ext, pp_using_anonymous_constructor]
structure Point (m n : PNat) where
  row : Fin m
  col : Fin n
  deriving DecidableEq, Fintype, Repr, Nonempty

@[simp]
lemma Point.eta (p : Point m n) : ⟨p.row, p.col⟩ = p := rfl

-- Convert 2D coordinates to 1D (flattened)
def to1d (pos : Point m n) : Fin (m * n) where
  val := pos.col.val + pos.row.val * n
  isLt := by calc
    pos.col.val + pos.row.val * n < 1 * n + pos.row * n := by omega
    _ = (1 + pos.row) * n := (add_mul ..).symm
    _ ≤ m * n := Nat.mul_le_mul_right n (by omega)

-- Convert 1D coordinates (flattened) to 2D
def to2d {m n : PNat} (pos : Fin (m * n)) : Point m n :=
  ⟨⟨pos.val / n, Nat.div_lt_of_lt_mul (Nat.mul_comm m n ▸ pos.isLt)⟩,
  ⟨pos.val % n, Nat.mod_lt pos n.pos⟩⟩

@[simp, grind =]
lemma to2d_to1d_inverse : to2d (to1d p) = p := by
  rw [to1d, to2d]
  congr
  · simp [Nat.add_mul_div_right, Nat.div_eq_of_lt]
  · simp [Nat.mod_eq_of_lt]

@[simp, grind =]
lemma to1d_to2d_inverse : to1d (to2d p) = p := by
  simp only [to1d, to2d, Nat.mod_add_div']

@[ext, pp_using_anonymous_constructor]
structure Rectangle (m n : PNat) where
  topLeft : Point m n
  bottomRight : Point m n
  validCol : topLeft.col ≤ bottomRight.col := by decide
  validRow : topLeft.row ≤ bottomRight.row := by decide
  deriving DecidableEq, Fintype, Repr

def Point.IsInside (p : Point m n) (r : Rectangle m n) : Prop :=
  r.topLeft.row.val ≤ p.1.val ∧ p.1.val ≤ r.bottomRight.row.val ∧
  r.topLeft.col.val ≤ p.2.val ∧ p.2.val ≤ r.bottomRight.col.val
  deriving Decidable

abbrev rotateCalc (a b c : Fin n) : Fin n where
  val := a.val - (b.val - c.val)
  isLt := by omega

-- Function to calculate the new position after 180 degree rotation around the rectangle center
def rotate180 (p : Point m n) (r : Rectangle m n) : Point m n :=
  ⟨rotateCalc r.bottomRight.row p.1 r.topLeft.row, rotateCalc r.bottomRight.col p.2 r.topLeft.col⟩

@[simp, grind =]
lemma rotate180_self_inverse (h : p.IsInside r) : rotate180 (rotate180 p r) r = p := by
  dsimp [Point.IsInside, rotate180] at *
  ext <;> grind

lemma spin_stays_inside (h : p.IsInside r) : (rotate180 p r).IsInside r := by
  dsimp [Point.IsInside, rotate180] at *; grind

grind_pattern spin_stays_inside => (rotate180 p r).IsInside r

-- Define a function to create a Spin element for a rectangle spin
def Rectangle.toSpin (r : Rectangle m n) : Spin m n where
  α := Function.Involutive.toPerm
    (fun pos =>
      let p := to2d pos
      if p.IsInside r then to1d (rotate180 p r) else pos)
    (fun _ => by simp only; split_ifs <;> simp_all [spin_stays_inside])
  u pos := if (to2d pos).IsInside r then 1 else 0
