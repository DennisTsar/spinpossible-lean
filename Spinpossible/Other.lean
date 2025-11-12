import Mathlib.Tactic

-- I don't need these anymore, but don't want to delete them.

lemma Nat.mod_succ_le_of_not_dvd {a b : Nat} (h : ¬b ∣ a + 1) (hb : 0 < b) : a % b + 1 < b := by
  apply lt_of_le_of_ne (mod_lt a hb)
  contrapose! h
  simpa [dvd_iff_mod_eq_zero] using congr($h % b)

lemma Nat.mod_succ_of_not_dvd {a b : Nat} (h : ¬b ∣ a + 1) (hb : 0 < b) :
    (a + 1) % b = a % b + 1 := by
  have := mod_succ_le_of_not_dvd h hb
  rw [add_mod, one_mod_eq_one.mpr (by omega), mod_eq_of_lt this]
