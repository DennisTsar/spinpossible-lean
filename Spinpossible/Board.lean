import Spinpossible.Definitions
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Order.Interval.Finset.Nat

inductive orientation
  | positive
  | negative
  deriving DecidableEq, Repr

structure tile where
  id : Nat
  orient : orientation
  deriving DecidableEq, Repr

def board (m n : PNat) := Matrix (Fin m) (Fin n) tile
  deriving DecidableEq

private def to1d (pos : Point m n) : Fin (m * n) where
  val := pos.col.val + pos.row.val * n
  isLt := by calc
    pos.col.val + pos.row.val * n < 1 * n + pos.row * n := by omega
    _ = (1 + pos.row) * n := (add_mul ..).symm
    _ ≤ m * n := Nat.mul_le_mul_right n (by omega)

private def to2d {m n : PNat} (pos : Fin (m * n)) : Point m n :=
  ⟨⟨pos.val / n, Nat.div_lt_of_lt_mul (Nat.mul_comm m n ▸ pos.isLt)⟩,
  ⟨pos.val % n, Nat.mod_lt pos n.pos⟩⟩

private lemma to2d_to1d_inverse : to2d (to1d p) = p := by
  rw [to1d, to2d]
  congr
  · simp [Nat.add_mul_div_right, Nat.div_eq_of_lt]
  · simp [Nat.mod_eq_of_lt]

private lemma to1d_to2d_inverse : to1d (to2d p) = p := by
  simp only [to1d, to2d, Nat.mod_add_div']

private lemma to1d_injective : Function.Injective (to1d : Point m n -> _)
  | p1, p2, h => by simpa only [to2d_to1d_inverse] using congr(to2d $h)

private lemma to1d_inj : to1d p1 = to1d p2 ↔ p1 = p2 := to1d_injective.eq_iff

def Spin.toBoard (s : Spin m n) : board m n :=
  fun i j => {
    id := to1d (s.α.symm ⟨i, j⟩) + 1,
    orient := if s.u ⟨i, j⟩ = 0 then orientation.positive else orientation.negative
  }

private def Matrix.toList (M : Matrix (Fin m) (Fin n) α) : List α :=
  (List.finRange m).flatMap (fun i => (List.finRange n).map (fun j => M i j))

attribute [- grind] Fin.ext -- seems like a Lean bug
def board.toSpin (b : board m n) : Spin m n :=
  let tiles_list : List tile := b.toList
  have tiles_list_def : b.toList = tiles_list := rfl
  have : tiles_list.length = m * n := by simp [Matrix.toList, tiles_list]

  have fact4 : (tiles_list.map (·.id)).toFinset = Finset.Icc 1 (m.val * n) := sorry

  have fact1 : ∀ x ∈ tiles_list, x.id > 0 ∧ x.id ≤ m * n := by
    intro x hx
    have : x.id ∈ (tiles_list.map (·.id)).toFinset := by
      simp only [List.mem_toFinset, List.mem_map]
      use x
    grind [Finset.mem_Icc]
  have fact2 : ∀ x y : Fin tiles_list.length,
      tiles_list[x.val].id = tiles_list[y.val].id → x = y := by
    intro x y hxy
    have : (tiles_list.map (·.id)).length =
      (tiles_list.map (·.id)).toFinset.card := by grind [Nat.card_Icc]
    have nodup := Multiset.toFinset_card_eq_card_iff_nodup.mp this.symm
    have : (tiles_list.map (·.id))[x.val] = (tiles_list.map (·.id))[y.val] := by
      rw [List.getElem_map, List.getElem_map, hxy]
    exact Fin.ext <| (List.Nodup.getElem_inj_iff nodup).mp this

  {
    α := Equiv.mk
      (fun i => to2d <| Fin.ofNat _ (tiles_list.findIdx (fun j => j.id - 1 == (to1d i).val)))
      (fun i => to2d <| Fin.ofNat _ ((tiles_list[to1d i]).id - 1))
      (fun p => by
        simp only [Fin.ofNat_eq_cast, to1d_to2d_inverse, ← to1d_inj, Fin.getElem_fin]
        let e := tiles_list.findIdx (fun j => j.id - 1 == (to1d p).val)
        refold_let e -- why can't I do this one step with `set`?
        have : e < tiles_list.length := List.findIdx_lt_length_of_exists <| by
          by_contra!
          have (x : Nat) : x ∈ (tiles_list.map (·.id)).toFinset → x - 1 ≠ to1d p := by
            grind [List.mem_toFinset]
          have (x) (hx : x ∈ Finset.range (m.val * n.val)) : x + 1 - 1 ≠ to1d p :=
            this (x + 1) (by grind [Finset.mem_Icc])
          grind
        grind [Fin.cast_val_eq_self, Nat.mod_eq_of_lt, = Fin.val_natCast]
      )
      (fun p => by
        simp only [Fin.ofNat_eq_cast, to1d_to2d_inverse, ← to1d_inj, Fin.val_natCast]
        have := fact1 tiles_list[to1d p] (List.getElem_mem _)
        let (eq := he) e := tiles_list.findIdx (fun j => j.id - 1 == tiles_list[to1d p].id - 1)
        suffices e = to1d p by rw [Nat.mod_eq_of_lt (by omega), ← he, this, Fin.cast_val_eq_self]
        apply Fin.mk.inj (fact2 ⟨e, ?_⟩ ⟨to1d p, ?_⟩ ?_) <;> grind [=> Fin.getElem_fin]
      ),
    u i := if (b i.row i.col).orient = orientation.positive then 0 else 1
  }

def standardBoard (m n : PNat) : board m n := (1 : Spin m n).toBoard

-- Action of Spin(m x n) on a board
def Spin.actionOnBoard {m n : PNat} (s : Spin m n) (b : board m n) : board m n :=
  b.toSpin * s |>.toBoard

-- Function to perform a spin on a board using the defined Spin action
def performSpin (r : Rectangle m n) (b : board m n) : board m n :=
  r.toSpin.actionOnBoard b
