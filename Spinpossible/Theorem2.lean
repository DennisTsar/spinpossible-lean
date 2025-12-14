import Mathlib.Analysis.SpecialFunctions.Stirling
import Spinpossible.SolutionBounds

lemma Spin.card_eq : Fintype.card (Spin m n) = 2 ^ (m.val * n) * Nat.factorial (m.val * n) := by
  simp [mul_comm, Fintype.ofEquiv_card, Fintype.card_equiv 1]

noncomputable instance : Fintype <| ⋃ s : Spin m n, {l | Spin.IsSolution l s} := by
  refine (Set.finite_iUnion fun s => ?_).fintype
  have ⟨x, hx⟩ := every_board_has_solution s
  apply Set.Finite.subset (List.finite_length_le _ x.length)
  grind [Spin.IsSolution]

/-- Let `k(m, n)` denote the maximum length of a solution to a board in `Spinₘₓₙ`. -/
noncomputable def k (m n : PNat) : Nat :=
  ⋃ s : Spin m n, {l | Spin.IsSolution l s} |>.toFinset.sup (·.length)

-- Argument and original proof from GPT-5 Thinking
lemma List.card_le_of_length_le (α k) [Fintype α] :
    (List.finite_length_le α k).toFinset.card ≤ (Fintype.card α + 1) ^ k := by
  generalize_proofs s
  let := s.fintype
  rw [Set.Finite.card_toFinset, ← Fintype.card_option, ← card_vector]
  refine Fintype.card_le_of_surjective
    (fun l => ⟨l.1.filterMap id, by simpa [l.2] using l.1.length_filterMap_le _⟩) fun l => ?_
  use ⟨l.1.map some ++ .replicate (k - l.1.length) none, by grind⟩
  simp

-- only need `k = 2` case but why not prove the general version
lemma Nat.choose_succ_lt_pow {n k : Nat} (hn : 2 ≤ n) (hk : 2 ≤ k) : (n + 1).choose k < n ^ k := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hdesc : (s + 2).factorial * (n + 1).choose (s + 2) ≤ (n + 1) * n ^ (s + 1) := by
    grw [← descFactorial_eq_factorial_mul_choose, succ_descFactorial_succ, descFactorial_le_pow]
  grw [← self_le_factorial] at hdesc
  have : n < n ^ 2 := lt_self_pow₀ hn (by simp)
  have : n * n ^ s < n ^ 2 * n ^ s := mul_lt_mul_of_pos_right this (by positivity)
  grind -ring -linarith only [Nat.pow_add_one] -- in `4.25.0`, a plain `grind` worked

private lemma Stirling.le_log_factorial_stirling' {n : Nat} (hn : n ≠ 0) :
    Real.log (n.factorial) > n * Real.log n - n + (1 : Real) / 2 * Real.log n := by
  have : 0 < Real.log (2 * Real.pi) / 2 := by grw [← Real.two_le_pi]; positivity
  grind [Stirling.le_log_factorial_stirling]

instance : Nonempty (RectSpin m n) := .intro (RectSpin.fromRect default)

theorem theorem2_1 (m n : PNat) :
    Fintype.card (Spin m n) ≤ (Fintype.card (RectSpin m n) + 1) ^ k m n := by
  apply Nat.le_trans ?_ (List.card_le_of_length_le _ _)
  let := List.finite_length_le (RectSpin m n) (k m n) |>.fintype
  rw [Set.Finite.toFinset_eq_toFinset, Set.toFinset_card]
  refine Fintype.card_le_of_surjective (fun x => (x.1.map RectSpin.toSpin).prod) fun b => ?_
  have ⟨a, ha⟩ := every_board_has_solution b⁻¹
  use ⟨a, Set.mem_setOf_eq ▸ Finset.le_sup ?_⟩, (inv_inv b ▸ ha.1)
  simpa using .intro b⁻¹ ha

theorem theorem2_2 {m n : PNat} (hmn : m.val * n > 1) :
    k m n ≥ (m * n) / 2 - (1 - Real.log 2) / 2 * ((m * n) / Real.log (m * n)) + 1 / 4 := by
  have : 1 ≤ (m.val * n) ^ 2 := one_le_pow₀ (le_of_lt hmn)
  have : 1 < Fintype.card (RectSpin m n) + 1 := Nat.AtLeastTwo.one_lt
  -- NOTE: original proof says `N^2 > c` but I believe it should be `N^2 ≥ c`
  -- Suppose `m=2, n=1`, then `N^2=4` and `c=choose(3,2)*choose(2,2)+1=4`
  have : Fintype.card (RectSpin m n) + 1 ≤ (m.val * n) ^ 2 := by
    rw [show Fintype.card (RectSpin m n) =
      (m.val + 1).choose 2 * (n.val + 1).choose 2 from total_valid_spins_card]
    rcases eq_or_lt_of_le <| @NeZero.one_le m _ with h1 | h1 <;>
    rcases eq_or_lt_of_le <| @NeZero.one_le n _ with h2 | h2
    · lia
    · grind -ring -linarith [Nat.choose_self, Nat.choose_succ_lt_pow]
    · grind -ring -linarith [Nat.choose_self, Nat.choose_succ_lt_pow]
    · grw [Nat.choose_succ_lt_pow h1 (Nat.le_refl _),
        Nat.le_sub_one_of_lt (Nat.choose_succ_lt_pow h2 (Nat.le_refl _)), Nat.mul_sub_one]
      lia

  have bound := theorem2_1 m n
  grw [Spin.card_eq, ← Nat.clog_le_iff_le_pow Nat.AtLeastTwo.one_lt, this,
    ← Real.natCeil_logb_natCast, Nat.ceil_le] at bound <;> try assumption
  grw [← bound]
  simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, one_div, ge_iff_le, ]
  conv_rhs => rw [← Real.log_div_log, Real.log_mul (by positivity) (by positivity)]

  have : Real.log (m * n) ≠ 0 := by
    rw [← Nat.cast_mul]
    exact Real.log_ne_zero_of_pos_of_ne_one (by positivity) (ne_of_gt (Nat.one_lt_cast.mpr hmn))
  grw [Stirling.le_log_factorial_stirling' (by omega)]
  · simp only [Real.log_pow, Nat.cast_mul, one_div, Nat.cast_ofNat, ge_iff_le]
    field_simp
    lia
  · exact Real.log_nonneg (by norm_cast0; assumption)
