import Spinpossible.Board
import Spinpossible.Proofs

instance : DecidableEq (board m n) := inferInstanceAs (DecidableEq (Matrix (Fin m) (Fin n) tile))

def board3by3 := standardBoard 3 3

namespace Basics

def perm1 : perm 3 where
  toFun := ![1, 0, 2]
  invFun := ![1, 0, 2]
  left_inv := by decide
  right_inv := by decide

def perm2 : perm 3 where
  toFun := fun i => i + 1
  invFun := fun i => i - 1
  left_inv := by exact leftInverse_sub_add_left 1
  right_inv := by -- or just `by decide`
    apply Function.rightInverse_of_injective_of_leftInverse
    · exact sub_left_injective
    · exact leftInverse_sub_add_left 1

#guard perm1.toFun = ![1, 0, 2]
#guard perm2.toFun = ![1, 2, 0]
#guard (perm1.trans perm2).toFun = ![2, 1, 0] -- perm1 applied first, then perm2
#guard (perm2.trans perm1).toFun = ![0, 2, 1] -- perm2 applied first, then perm1

end Basics

namespace TestSpinAction

def samplePerm : perm (3 * 3) where
  toFun := fun i => if i = 0 then 1 else if i = 1 then 0 else i
  invFun := fun i => if i = 0 then 1 else if i = 1 then 0 else i
  left_inv := by decide
  right_inv := by decide

def sampleSpin : Spin 3 3 :=
  {
    α := samplePerm
    u := fun i => if i = 0 then 1 else 0
  }

def samplePerm2 : perm (3 * 3) where
  toFun := fun i => if i = 4 then 3 else if i = 3 then 1 else if i = 1 then 4 else i
  invFun := fun i => if i = 4 then 1 else if i = 3 then 4 else if i = 1 then 3 else i
  left_inv := by decide
  right_inv := by decide

def sampleSpin2 : Spin 3 3 where
  α := samplePerm2
  u := fun i => if i % 2 = 0 then 1 else 0

def a := Spin.actionOnBoard sampleSpin (Spin.actionOnBoard sampleSpin2 board3by3)
def b := (sampleSpin2 * sampleSpin).actionOnBoard board3by3

-- #eval a
-- #eval b
#guard a = b
#guard sampleSpin.toBoard.toSpin = sampleSpin
#guard (sampleSpin2 * sampleSpin).toBoard.toSpin = sampleSpin2 * sampleSpin
#guard (sampleSpin2 * sampleSpin).toBoard = (sampleSpin2 * sampleSpin).toBoard
#guard ((sampleSpin2 * sampleSpin).actionOnBoard board3by3) =
  (board3by3.toSpin * (sampleSpin2 * sampleSpin)).toBoard


end TestSpinAction

namespace TestRectSpins

def test_rectangle : Rectangle 3 3 where
  topLeft := ⟨2, 0⟩
  bottomRight := ⟨2, 2⟩

def test_rectangle2 : Rectangle 3 3 where
  topLeft := ⟨0, 0⟩
  bottomRight := ⟨2, 1⟩

def firstSpinRes := performSpin test_rectangle board3by3
def secondSpinRes := performSpin test_rectangle2 firstSpinRes

def combinedSpin := test_rectangle.toSpin * test_rectangle2.toSpin
def combinedSpinRes := combinedSpin.actionOnBoard board3by3

-- #eval firstSpinRes
-- #eval secondSpinRes
-- #eval combinedSpinRes

#guard secondSpinRes = combinedSpinRes
#guard combinedSpin = combinedSpin.toBoard.toSpin
#guard (combinedSpin.actionOnBoard board3by3) = (board3by3.toSpin * combinedSpin).toBoard

end TestRectSpins
