import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.PNat.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.DeriveFintype

-- In Lean 4.25.0, `get_elem_tactic_extensible` causes performance issues due to trying stuff
-- relating to `Std.Range`, which we don't use, so we redefine it here to improve performance.
macro_rules
  | `(tactic| get_elem_tactic_extensible) => `(tactic| omega)

@[ext, grind ext, pp_using_anonymous_constructor]
structure Point (m n : PNat) where
  row : Fin m
  col : Fin n
  deriving DecidableEq, Fintype, Repr, Nonempty

@[simp]
lemma Point.eta (p : Point m n) : ⟨p.row, p.col⟩ = p := rfl

abbrev perm (m n : PNat) := Equiv.Perm (Point m n)

abbrev VN (m n : PNat) := Point m n → ZMod 2

@[grind ext]
structure Spin (m n : PNat) where
  α : perm m n
  u : VN m n
  deriving DecidableEq, Fintype

-- manually define an `ext` lemma that uses function application
@[ext]
lemma Spin.ext {s1 s2 : Spin m n} (h1 : ∀ x, s1.α x = s2.α x) (h2 : ∀ x, s1.u x = s2.u x)
    : s1 = s2 := by
  obtain ⟨a, b⟩ := s1
  obtain ⟨c, d⟩ := s2
  congr
  · exact Equiv.ext h1
  · exact funext h2

namespace Spin

def mul (x y : Spin m n) : Spin m n where
  α := y.α * x.α -- intentionally reversed
  u i := x.u (y.α.symm i) + y.u i

instance : Mul (Spin m n) := ⟨mul⟩

lemma mul_def (x y : Spin m n) : x * y = ⟨x.α.trans y.α, fun i => x.u (y.α.symm i) + y.u i⟩ := rfl

instance : One (Spin m n) := ⟨Equiv.refl _, fun _ => 0⟩

lemma one_def : (1 : Spin m n) = ⟨Equiv.refl _, fun _ => 0⟩ := rfl

end Spin

@[ext, pp_using_anonymous_constructor]
structure Rectangle (m n : PNat) where
  topLeft : Point m n
  bottomRight : Point m n
  validRow : topLeft.row ≤ bottomRight.row := by decide
  validCol : topLeft.col ≤ bottomRight.col := by decide
  deriving DecidableEq, Fintype, Repr

def Point.IsInside (p : Point m n) (r : Rectangle m n) : Prop :=
  r.topLeft.row.val ≤ p.row.val ∧ p.row.val ≤ r.bottomRight.row.val ∧
  r.topLeft.col.val ≤ p.col.val ∧ p.col.val ≤ r.bottomRight.col.val
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
    (fun p => if p.IsInside r then rotate180 p r else p)
    (fun _ => by grind [spin_stays_inside])
  u p := if p.IsInside r then 1 else 0
