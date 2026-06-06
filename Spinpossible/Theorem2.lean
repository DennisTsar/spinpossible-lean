module

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Spinpossible.SolutionBounds

lemma Spin.card_eq : Fintype.card (Spin m n) = 2 ^ (m.val * n) * Nat.factorial (m.val * n) := by
  simp [mul_comm, Fintype.ofEquiv_card, Fintype.card_equiv 1]

noncomputable instance : Fintype <| ⋃ s : Spin m n, {l | Spin.IsSolution l s} := by
  refine (Set.finite_iUnion fun s => ?_).fintype
  have ⟨x, hx⟩ := every_board_has_solution s
  apply Set.Finite.subset (List.finite_length_le _ x.length)
  grind [Spin.IsSolution]

/-- Let `k(m, n)` denote the maximum length of a solution to a board in `Spinₘₓₙ`. -/
public noncomputable def k (m n : PNat) : Nat :=
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

public theorem theorem2_1 (m n : PNat) :
    Fintype.card (Spin m n) ≤ (Fintype.card (RectSpin m n) + 1) ^ k m n := by
  apply Nat.le_trans ?_ (List.card_le_of_length_le _ _)
  let := List.finite_length_le (RectSpin m n) (k m n) |>.fintype
  rw [Set.Finite.toFinset_eq_toFinset, Set.toFinset_card]
  refine Fintype.card_le_of_surjective (fun x => (x.1.map RectSpin.toSpin).prod) fun b => ?_
  have ⟨a, ha⟩ := every_board_has_solution b⁻¹
  use ⟨a, Set.mem_setOf_eq ▸ Finset.le_sup ?_⟩, (inv_inv b ▸ ha.1)
  simpa using .intro b⁻¹ ha

public theorem theorem2_2 {m n : PNat} (hmn : m.val * n > 1) :
    k m n ≥ (m * n) / 2 - (1 - Real.log 2) / 2 * ((m * n) / Real.log (m * n)) + 1 / 4 := by
  have : 1 ≤ (m.val * n) ^ 2 := one_le_pow₀ hmn.le
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
    · grw [Nat.choose_succ_lt_pow h1 le_rfl,
        Nat.le_sub_one_of_lt (Nat.choose_succ_lt_pow h2 le_rfl), Nat.mul_sub_one]
      lia

  have bound := theorem2_1 m n
  grw [Spin.card_eq, ← Nat.clog_le_iff_le_pow Nat.AtLeastTwo.one_lt, this,
    ← Real.natCeil_logb_natCast, Nat.ceil_le] at bound
  grw [← bound]
  simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, one_div, ge_iff_le, ]
  conv_rhs => rw [← Real.log_div_log, Real.log_mul (by positivity) (by positivity)]

  have : Real.log (m * n) ≠ 0 := Real.log_pos (mod_cast hmn) |>.ne'
  grw [Stirling.le_log_factorial_stirling' (by omega)]
  · simp [Real.log_pow, field]; grind
  · exact Real.log_nonneg (by norm_cast0; assumption)

lemma k_upper_bound (m n) : k m n ≤ 3 * m * n - (m + n) := by
  simp only [k, Finset.sup_le_iff, Set.mem_toFinset, Set.mem_iUnion, forall_exists_index]
  exact fun b s hs => theorem1 s b hs

private lemma eventually_error_lt_mul (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : Nat, ∀ {m n : PNat}, (N₀ : ℝ) < (m * n) →
      (1 - Real.log 2) / 2 * ((m * n) / Real.log (m * n)) - 1 / 4 < ε * (m * n) := by
  obtain ⟨R, hR⟩ := Real.tendsto_log_atTop.eventually_gt_atTop (((1 - Real.log 2) / 2) / ε)
    |>.exists_forall_of_atTop
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt R
  use N₀, fun {m n} hN => ?_
  have : 1 - Real.log 2 > 0 := by grw [Real.log_two_lt_d9]; positivity
  grw [← hR (m * n) (by linarith)]
  simp [field]

/-- **Corollary 2**: The asymptotic growth of `k(m, n)` is linear in `N = mn`.
    Note: The paper says `(1 / 2 + ε)` instead of `(1 / 2 - ε)`, but that is incorrect
    (See the example below).
-/
theorem corollary_2 : ∀ ε > 0, ∃ N₀ : Nat, ∀ {m n : PNat}, N₀ < m * n →
    ((1 / 2 : ℝ) - ε) * (m * n) < (k m n : ℝ) ∧ (k m n : ℝ) ≤ 3 * (m * n) := by
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := eventually_error_lt_mul ε hε
  use max N₁ 1, fun hN => ⟨?_, ?_⟩
  · linarith [theorem2_2 <| hN.trans_le' <| by simp, hN₁ <| mod_cast hN.trans_le' <| by simp]
  · grw [k_upper_bound, Nat.sub_le, mul_assoc]; norm_cast

-- It is *not* true that `k(m, n)` grows asymptotically like `(1 / 2 + ε) * N` for any `ε > 0`.
example (h : ∀ ε > 0, ∃ N₀ : Nat, ∀ {m n : PNat}, N₀ < m * n →
    ((1 / 2 : ℝ) + ε) * (m * n) < (k m n : ℝ)) : False := by
  obtain ⟨N₀, hN₀⟩ := h 3 (by norm_num)
  absurd hN₀ (m := ⟨N₀ + 2, by omega⟩) (n := 1) (by simp)
  grw [k_upper_bound, Nat.sub_le, mul_assoc]
  simp [- PNat.mk_coe]
