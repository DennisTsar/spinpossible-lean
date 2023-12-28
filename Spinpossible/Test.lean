import Spinpossible.Definitions

def board3by3 := standardBoard 3 3

-- I assume there's something built-in for this, but idk what it is
def boardsEqual (b1 b2 : board m n) : Bool := ∀ i j, b1 i j == b2 i j

namespace Basics

  def perm1 : perm 3 :=
    Equiv.mk
      (fun i => if i = 0 then 1 else if i = 1 then 0 else 2)
      (fun i => if i = 0 then 1 else if i = 1 then 0 else 2)
      (by
        apply Function.leftInverse_iff_comp.mpr
        funext i
        match i with -- I assume this can be shorter, but idk how
        | 0 => rfl
        | 1 => rfl
        | 2 => rfl
      )
      (
        by
          apply Function.rightInverse_iff_comp.mpr
          funext i
          match i with
          | 0 => rfl
          | 1 => rfl
          | 2 => rfl
      )

  def perm2 : perm 3 :=
    Equiv.mk
      (fun i => i + 1)
      (fun i => i - 1)
      (by exact leftInverse_sub_add_left 1)
      (by exact leftInverse_sub_add_left (-1))

  #guard perm1.toFun = ![1, 0, 2]
  #guard perm2.toFun = ![1, 2, 0]
  #guard (perm1 * perm2).toFun = ![2, 1, 0] -- perm1 applied first, then perm2
  #guard (perm2 * perm1).toFun = ![0, 2, 1] -- perm2 applied first, then perm1

end Basics

namespace TestSpinAction

  def samplePerm : perm (3 * 3) :=
    Equiv.mk
      (fun i => if i = 0 then 1 else if i = 1 then 0 else i)
      (fun i => if i = 0 then 1 else if i = 1 then 0 else i)
      (by sorry)
      (by sorry)

  def sampleSpin : Spin (Nat.toPNat 3) (Nat.toPNat 3) :=
    {
      α := samplePerm
      u := fun i => if i = 0 then 1 else 0
    }

  def a := Spin.actionOnBoard sampleSpin (Spin.actionOnBoard sampleSpin board3by3)
  def b := Spin.actionOnBoard (sampleSpin * sampleSpin) board3by3
  def c := (sampleSpin * sampleSpin).actionOnBoard board3by3

  #eval a
  #eval b
  #eval c
  #guard boardsEqual a b && boardsEqual a c && boardsEqual b c

end TestSpinAction

namespace TestRectSpins

  def test_rectangle : Rectangle (3 : PNat) (3 : PNat) :=
    {
      topLeft := {row := 2, col := 0}
      bottomRight := {row := 2, col:= 2}
    }

  def test_rectangle2 : Rectangle (3 : PNat) (3 : PNat) :=
    {
      topLeft := {row := 0, col := 0}
      bottomRight := {row := 2, col:= 1}
    }

  def firstSpinRes := performSpin test_rectangle board3by3
  def secondSpinRes := performSpin test_rectangle2 firstSpinRes

  def combinedSpin := test_rectangle.toSpin * test_rectangle2.toSpin
  def combinedSpinRes := combinedSpin.actionOnBoard board3by3

  #eval firstSpinRes
  #eval secondSpinRes
  #eval combinedSpinRes

  #guard boardsEqual secondSpinRes combinedSpinRes

end TestRectSpins

-- trick to see what partially successful aesop does
-- @[aesop 1% unsafe apply]
-- def sorryeh (A) : A := sorry
-- set_option trace.aesop true
