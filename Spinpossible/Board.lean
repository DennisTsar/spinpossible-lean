import Spinpossible.Definitions
import Mathlib.Data.Matrix.Defs
import Mathlib.Data.ZMod.Basic

inductive orientation
  | positive
  | negative
  deriving DecidableEq, Repr

structure tile where
  id : Nat
  orient : orientation
  deriving DecidableEq, Repr

def board (m n : PNat) := Matrix (Fin m) (Fin n) tile

def Spin.toBoard (s : Spin m n) : board m n :=
  fun i j => {
    id := s.α.symm (to1d ⟨i, j⟩) + 1,
    orient := if s.u (to1d ⟨i, j⟩) = 0 then orientation.positive else orientation.negative
  }

private def Matrix.toList (M : Matrix (Fin m) (Fin n) α) : List α :=
  (List.finRange m).flatMap (fun i => (List.finRange n).map (fun j => M i j))

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
    ext
    have : (tiles_list.map (·.id)).length =
      (tiles_list.map (·.id)).toFinset.card := by grind [Nat.card_Icc]
    have nodup := Multiset.toFinset_card_eq_card_iff_nodup.mp (this.symm)
    have : (tiles_list.map (·.id))[x.val] = (tiles_list.map (·.id))[y.val] := by
      rw [List.getElem_map, List.getElem_map, hxy]
    exact (List.Nodup.getElem_inj_iff nodup).mp this

  {
    α := Equiv.mk
      (fun i => Fin.ofNat _ (tiles_list.findIdx (fun j => j.id - 1 == i.val)))
      (fun i => Fin.ofNat _ ((tiles_list[i]).id - 1))
      (by
        intro p
        simp only [Fin.ofNat_eq_cast, Fin.getElem_fin, Fin.val_natCast]
        let e := tiles_list.findIdx (fun j => j.id - 1 == p.val)
        refold_let e -- why can't I do this one step with `set`?
        have : e < tiles_list.length := by
          apply List.findIdx_lt_length_of_exists
          by_contra! ht
          have qwe2 (x : Nat) : x ∈ (tiles_list.map (·.id)).toFinset → x - 1 ≠ p := by
            grind [List.mem_toFinset]
          have (x) (hx : x ∈ Finset.range (m.val * n.val)) : (x + 1) - 1 ≠ p :=
            qwe2 (x + 1) (by grind [Finset.mem_Icc])
          grind
        grind [Fin.cast_val_eq_self, Nat.mod_eq_of_lt]
      )
      (by
        intro p
        simp only [Fin.ofNat_eq_cast, Fin.val_natCast]
        have : tiles_list[p].id > 0 ∧ tiles_list[p].id ≤ m * n := fact1 _ (List.getElem_mem _)
        let (eq := he) e := tiles_list.findIdx (fun j => j.id - 1 == tiles_list[p].id - 1)
        have : e < tiles_list.length := by
          apply List.findIdx_lt_length_of_exists
          by_contra! ht
          have (x) (hx : x ∈ Finset.range (m.val * n.val)) : x ≠ p := by
            rw [Fin.getElem_fin] at ht
            grind
          grind
        suffices e = p by rw [Nat.mod_eq_of_lt (by omega), ← he, this, Fin.cast_val_eq_self]
        have : tiles_list[e].id - 1 = tiles_list[p].id - 1 :=
          beq_iff_eq.mp (List.findIdx_getElem (w := this))
        have : tiles_list[e].id > 0 := fact1 _ (List.getElem_mem _) |>.1
        have := fact2 ⟨e, by omega⟩ ⟨p, by omega⟩ (by simp_rw [← Fin.getElem_fin]; grind)
        exact Fin.mk.inj_iff.mp this
      ),
    u i := if (b (to2d i).row (to2d i).col).orient = orientation.positive then 0 else 1
  }

def standardBoard (m n : PNat) : board m n := (1 : Spin m n).toBoard

-- Action of Spin(m x n) on a board
def Spin.actionOnBoard {m n : PNat} (s : Spin m n) (b : board m n) : board m n :=
  b.toSpin * s |>.toBoard

-- Function to perform a spin on a board using the defined Spin action
def performSpin (r : Rectangle m n) (b : board m n) : board m n :=
  r.toSpin.actionOnBoard b
