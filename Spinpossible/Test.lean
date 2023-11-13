import Spinpossible.Definitions

def board_3_by_3 := standard_board 3 3

-- I assume there's something built-in for this, but idk what it is
def boardsEqual {m n : PNat} (b1 b2 : board m n) : Bool :=
  ∀ i j, b1 i j == b2 i j

namespace TestSpinAction
  def sample_perm : perm (3 * 3) :=
    Equiv.mk
      (fun i => if i = 0 then 1 else if i = 1 then 0 else i)
      (fun i => if i = 0 then 1 else if i = 1 then 0 else i)
      (by sorry)
      (by sorry)

  def sample_spin : Spin (Nat.toPNat 3) (Nat.toPNat 3) :=
    {
      α := sample_perm
      u := fun i => if i = 0 then 1 else 0
    }

  def a := Spin.action_on_board sample_spin (Spin.action_on_board sample_spin board_3_by_3)
  def b := Spin.action_on_board (sample_spin * sample_spin) board_3_by_3
  def c := (sample_spin * sample_spin).action_on_board board_3_by_3

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

  def first_spin_res := performSpin test_rectangle board_3_by_3
  def second_spin_res := performSpin test_rectangle2 first_spin_res

  def combined_spin := createRectangleSpin test_rectangle * createRectangleSpin test_rectangle2
  def combined_spin_res := combined_spin.action_on_board board_3_by_3

  #eval first_spin_res
  #eval second_spin_res
  #eval combined_spin_res

  #guard boardsEqual second_spin_res combined_spin_res

end TestRectSpins
