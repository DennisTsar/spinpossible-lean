import Spinpossible.Definitions

def board3by3 := standardBoard 3 3

-- I assume there's something built-in for this, but idk what it is
def boardsEqual {m n : PNat} (b1 b2 : board m n) : Bool :=
  ∀ i j, b1 i j == b2 i j

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

  def test_rectangle : Rectangle (Nat.toPNat 3) (Nat.toPNat 3) :=
    {
      topLeft := {row := 2, col := 0}
      bottomRight := {row := 2, col:= 2}
    }

  def test_rectangle2 : Rectangle (Nat.toPNat 3) (Nat.toPNat 3) :=
    {
      topLeft := {row := 0, col := 0}
      bottomRight := {row := 2, col:= 1}
    }

  def firstSpinRes := performSpin test_rectangle board3by3
  def secondSpinRes := performSpin test_rectangle2 firstSpinRes

  def combinedSpin := createRectangleSpin test_rectangle * createRectangleSpin test_rectangle2
  def combinedSpinRes := combinedSpin.actionOnBoard board3by3

  #eval firstSpinRes
  #eval secondSpinRes
  #eval combinedSpinRes

  #guard boardsEqual secondSpinRes combinedSpinRes

end TestRectSpins
