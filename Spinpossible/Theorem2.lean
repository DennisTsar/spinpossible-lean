import Mathlib
import Spinpossible.SolutionBounds

-- TODO: delete when upgrading mathlib
-- https://github.com/leanprover-community/mathlib4/blob/586e9c386274d740624bd33abe9a67f7365a92fc/Mathlib/Analysis/SpecialFunctions/Stirling.lean#L242

open Filter Real in
theorem Stirling.sqrt_pi_le_stirlingSeq {n : ℕ} (hn : n ≠ 0) : √π ≤ stirlingSeq n :=
  match n, hn with
  | n + 1, _ =>
    stirlingSeq'_antitone.le_of_tendsto (b := n) <|
      tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1)

open scoped Nat in
open Real in
theorem Stirling.le_factorial_stirling (n : ℕ) : √(2 * π * n) * (n / exp 1) ^ n ≤ n ! := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  have : √(2 * π * n) * (n / exp 1) ^ n = √π * (√(2 * n) * (n / exp 1) ^ n) := by
    simp [sqrt_mul']; ring
  rw [this, ← le_div_iff₀ (by positivity)]
  exact sqrt_pi_le_stirlingSeq hn

open scoped Nat in
open Real in
theorem Stirling.le_log_factorial_stirling {n : ℕ} (hn : n ≠ 0) :
    n * log n - n + log n / 2 + log (2 * π) / 2 ≤ log n ! := by
  calc
    _ = (log (2 * π) + log n) / 2 + n * (log n - 1) := by ring
    _ = log (√(2 * π * n) * (n / rexp 1) ^ n) := by
      rw [log_mul (x := √_), log_sqrt, log_mul (x := 2 * π), log_pow, log_div, log_exp] <;>
      positivity
    _ ≤ _ := log_le_log (by positivity) (le_factorial_stirling n)

-- end delete

lemma exists_uniform_bound_min_witness :
  ∃ z : ℕ,
    ∀ (x : List (RectSpin m n)) (x₁ : Spin m n),
      ((List.map RectSpin.toSpin x).prod = x₁⁻¹ ∧
        ∀ (l' : List (RectSpin m n)),
          (List.map RectSpin.toSpin l').prod = x₁⁻¹ → x.length ≤ l'.length) →
      x.length ≤ z := by
  classical
  let zOf : Spin m n → ℕ := fun s =>
    if h : ∃ x : List (RectSpin m n),
        (List.map RectSpin.toSpin x).prod = s⁻¹
    then
      have : ∃ k, ∃ x : List (RectSpin m n),
          (List.map RectSpin.toSpin x).prod = s⁻¹ ∧ x.length = k := by
        rcases h with ⟨x0, hx0⟩
        exact ⟨x0.length, x0, hx0, rfl⟩
      Nat.find this
    else 0
  let z : ℕ := (Finset.univ : Finset (Spin m n)).sup zOf
  refine ⟨z, ?_⟩
  intro x s hx
  have hxw : ∃ x : List (RectSpin m n),
      (List.map RectSpin.toSpin x).prod = s⁻¹ := ⟨x, hx.1⟩
  have hQ :
      ∃ k, ∃ y : List (RectSpin m n),
        (List.map RectSpin.toSpin y).prod = s⁻¹ ∧ y.length = k := by
    rcases hxw with ⟨x0, hx0⟩
    exact ⟨x0.length, x0, hx0, rfl⟩
  have hlen_eq :
      x.length = Nat.find hQ := by
    obtain ⟨x0, hx0P, hx0len⟩ := Nat.find_spec hQ
    have h1 : x.length ≤ x0.length := hx.2 _ hx0P
    have h2 : Nat.find hQ ≤ x.length := by
      have : ∃ y, (List.map RectSpin.toSpin y).prod = s⁻¹ ∧ y.length = x.length :=
        ⟨x, hx.1, rfl⟩
      simpa using (Nat.find_min' hQ this)
    exact Nat.le_antisymm (by simpa [hx0len] using h1) h2
  have hx_le_zOf : x.length ≤ zOf s := by
    simp [zOf, dif_pos hxw, hlen_eq]
  have zOf_le_z : zOf s ≤ z := by
    simpa [z] using Finset.le_sup (s := (Finset.univ : Finset (Spin m n))) (by simp)
  exact hx_le_zOf.trans zOf_le_z

lemma a1 :
    Fintype.card (Spin m n) = 2 ^ (m.val * n) * Nat.factorial (m.val * n) := by
  simp [mul_comm (2 ^ _), Fintype.ofEquiv_card, Fintype.card_equiv 1]

/-- Let `k(m, n)` denote the maximum length of a solution to a board in `Spinₘₓₙ`. -/
noncomputable def k (m n : PNat) : Nat :=
  letI s := {l | ∃ s : Spin m n, Spin.IsSolution l s}
  haveI : s.Finite := by
    have ⟨z, hz⟩ : ∃ z, ∀ x ∈ s, x.length ≤ z := by
      simp [Spin.IsSolution, ge_iff_le, Set.mem_setOf_eq, -and_imp, -forall_and_index, s]
      apply exists_uniform_bound_min_witness
    let x := {l : List (RectSpin m n) | l.length ≤ z}
    have : x.Finite := List.finite_length_le _ z
    apply Set.Finite.subset this
    intro a ha
    exact hz a ha
  letI := this.fintype
  s.toFinset.sup (·.length)

-- credit to GPT-5 Thinking
lemma card_lists_len_le_pow [Fintype α] (k : ℕ) :
  let s := {l : List α | l.length ≤ k}
  have sf : s.Finite := List.finite_length_le _ k
  sf.toFinset.card
    ≤ (Fintype.card α + 1) ^ k := by
  intro s sf
  simp [Set.Finite.toFinset, s]
  classical

  let s2 := {v : List (Option α) | v.length = k}
  have sf2 : s2.Finite := by
    have : {v : List (Option α) | v.length = k}.Finite :=
      List.finite_length_eq _ k
    apply Set.Finite.subset this
    intro a ha
    exact ha
  -- Domain we'll count: fixed-length lists (= vectors) over `Option α`
  have card_domain :
      sf2.toFinset.card
        = (Fintype.card (Option α)) ^ k := by
    simp [Set.Finite.toFinset, s2]
    rw [← Fintype.card_option, ← card_vector]
    convert (Fintype.card_congr' rfl)
    exact Vector.fintype

  -- Surjection `g`: drop all `none`s (i.e. keep only `some a`) → a list over `α`
  let g :
      {v : List (Option α) // v.length = k} →
      {l : List α // l.length ≤ k} :=
    fun v => ⟨v.1.filterMap id, by simpa [v.2] using List.length_filterMap_le id v.1⟩

  have g_surj : Function.Surjective g := by
    intro l
    let l' := l.1.map some
    let l'' : List (Option α) := (List.replicate (k - l.1.length) none)
    use ⟨l' ++ l'', ?_⟩
    · simp [l', l'', g]
    · simp [l', l'']
      omega


  -- From a surjection `g : X ↠ Y`, we get `|Y| ≤ |X|`
  have hle :
      sf.toFinset.card
        ≤ sf2.toFinset.card := by
    simp [Set.Finite.toFinset, s, s2]
    let _ : Fintype { v : List (Option α) // v.length = k } := sf2.fintype
    let _ : Fintype { v : List α  // v.length ≤ k } := sf.fintype
    convert Fintype.card_le_of_surjective g g_surj

  simp [card_domain, Fintype.card_option] at hle
  -- Combine with the domain cardinality and `card_option`
  simpa [card_domain, Fintype.card_option, Set.Finite.toFinset, sf] using hle

private lemma choose2_le_sq_sub_one {k : ℕ} (hk : 2 ≤ k) :
  (k + 1).choose 2 ≤ k^2 - 1 := by
  refine Nat.le_sub_one_of_lt ?_
  simp [Nat.choose_two_right]
  have : (k + 1) * k < k ^ 2 * 2 := by
    rw [show k ^2 * 2 = k * k + k * k by group, show (k + 1) * k = k * k + k by group]
    exact Nat.add_lt_add_left (Nat.lt_mul_self_iff.mpr hk) (k * k)
  omega

lemma jo {n : Nat} (hn : n ≠ 0) :
    Real.log (n.factorial) ≥ n * Real.log n - n + (1 : Real) / 2 * Real.log n := by
  have := Stirling.le_log_factorial_stirling hn
  have : Real.log (2 * Real.pi) / 2 > 0 := by
    have := Real.two_le_pi
    bound
  grind

theorem theorem2 {m n : PNat} (hmn : m.val * n > 1) :
  (k m n) ≥ (m * n : Real) / 2 - (1 - Real.log 2) / 2 * ((m * n : Real) / Real.log (m * n)) + 1 / 4 := by
  have t1 : 2 ≤ m.val ∨ 2 ≤ n.val := by
    grind [PNat.pos]

  let s := {l : List (RectSpin m n) | l.length ≤ k m n}
  have sf : s.Finite := List.finite_length_le _ (k m n)
  have f1 : sf.toFinset.card ≤ (Fintype.card (RectSpin m n) + 1) ^ (k m n) := by
    apply card_lists_len_le_pow
  have f2 : sf.toFinset.card ≥ Fintype.card (Spin m n) := by
    simp [Set.Finite.toFinset, s]
    let _ : Fintype { x : List (RectSpin m n) // x.length ≤ k m n } := sf.fintype
    refine Fintype.card_le_of_surjective (fun x => (x.1.map RectSpin.toSpin).prod) fun b => ?_
    refine Subtype.exists.mpr ?_
    simp [k]
    let yo := {l | Spin.IsSolution l b⁻¹}
    have ⟨a, ha⟩ : Nonempty yo := by
      simp [yo]
      apply every_board_has_solution
    use a
    simp [yo] at ha

    let d := {l : List (RectSpin m n) | ∃ s, Spin.IsSolution l s}
    have : a ∈ d := by use b⁻¹
    have : d.Finite := by
      simp [d]
      have ⟨z, hz⟩ : ∃ z, ∀ x ∈ d, x.length ≤ z := by
        simp [d, Spin.IsSolution, ge_iff_le, Set.mem_setOf_eq, -and_imp, -forall_and_index]
        apply exists_uniform_bound_min_witness
      let x := {l : List (RectSpin m n) | l.length ≤ z}
      have : x.Finite := List.finite_length_le _ z
      apply Set.Finite.subset this
      intro a ha
      exact hz a ha
    let _ := this.fintype
    simp [Spin.IsSolution] at ha
    simp_all only [and_true, s]
    apply Finset.le_sup
    exact Set.mem_toFinset.mpr this
  have : Fintype.card (Spin m n) ≤ (Fintype.card (RectSpin m n) + 1) ^ (k m n) := Nat.le_trans f2 f1
  have cc : Fintype.card (RectSpin m n) = (m.val + 1).choose 2 * (n.val + 1).choose 2 := by
    simpa [validSpins] using total_valid_spins_card
  have _ : 1 ≤ Fintype.card (RectSpin m n):= by
    rw [cc]
    have := m.1
    have := n.1
    refine Nat.one_le_iff_ne_zero.mpr ?_
    apply Nat.mul_ne_zero
    · refine Nat.choose_ne_zero ?_
      exact Nat.AtLeastTwo.prop
    · refine Nat.choose_ne_zero ?_
      exact Nat.AtLeastTwo.prop
  have this2 := this
  rw [Nat.le_pow_iff_clog_le (by omega)] at this
  rw [a1, cc] at this
  rw [← Real.natCeil_logb_natCast] at this
  simp at this
  rw [← Real.log_div_log] at this

  clear this

  -- NOTE: original proof says `N^2 > c` but I believe it should be `N^2 ≥ c`
  -- Suppose `m=2, n=1`, then `N^2=4` and `c=choose(3,2)*choose(2,2)+1=4`
  have : (Fintype.card (RectSpin m n) + 1) ≤ (m.val * n) ^ 2 := by
    rw [cc]
    rcases t1 with h1 | h1
    · by_cases h2 : 2 ≤ n.val
      · grw [choose2_le_sq_sub_one h1]
        grw [choose2_le_sq_sub_one h2]
        have : (m.val ^ 2 - 1) * (n.val ^ 2 - 1) + 1 = m.val ^ 2 * n.val ^ 2 - (m.val ^ 2 + n.val ^ 2) + 2 := by
          rw [Nat.sub_one_mul (↑m ^ 2) (↑n ^ 2 - 1)]
          rw [Nat.mul_sub_one (↑m ^ 2) (↑n ^ 2)]
          rw [Nat.sub_sub_right (↑m ^ 2 * ↑n ^ 2 - ↑m ^ 2) (NeZero.one_le)]
          group
          rw [← Nat.add_sub_assoc ?_ 1]
          · simp [← add_assoc]
            rw [← Nat.Simproc.add_sub_add_ge 2 (↑n ^ 2) ?_]
            · group
              rw [← Nat.add_sub_assoc ?_ 2]
              apply Nat.add_le_mul
              · have := Nat.pow_le_pow_left h1 2
                exact Nat.le_of_add_left_le this
              · have := Nat.pow_le_pow_left h2 2
                exact Nat.le_of_add_left_le this
            · apply Nat.le_mul_of_pos_right
              positivity
          · set x := m.val ^ 2
            set y := n.val ^ 2
            rw [← Nat.mul_sub_one x y]
            have : 4 ≤ x := Nat.pow_le_pow_left h1 2
            have : y ≤ x * (y - 1) := by
              grw [← this]
              have : 4 ≤ y := Nat.pow_le_pow_left h2 2
              omega
            omega
        rw [this]
        rw [show (m.val * n) ^ 2 = m.val ^ 2 * n.val ^ 2 by ring]
        rw [← tsub_tsub_assoc ?_ ?_]
        · apply Nat.sub_le
        · refine Nat.add_le_mul ?_ ?_
          · grind
          · grind
        · grind
      · have : n.val > 0 := n.2
        have : n.val = 1 := by omega
        simp [this]
        simp [Nat.choose_two_right]
        simp [add_mul]
        have : 4 ≤ m.val ^ 2 := Nat.pow_le_pow_left h1 2
        set x := m.val
        have hmul : 0 ≤ 2 * (x : ℤ)^2 - (x : ℤ) * (x : ℤ) - (x : ℤ) - 2 := by
          nlinarith
        grind
    · by_cases h2 : 2 ≤ m.val
      · grw [choose2_le_sq_sub_one h1, choose2_le_sq_sub_one h2]
        have : (m.val ^ 2 - 1) * (n.val ^ 2 - 1) + 1 = m.val ^ 2 * n.val ^ 2 - (m.val ^ 2 + n.val ^ 2) + 2 := by
          rw [Nat.sub_one_mul (↑m ^ 2) (↑n ^ 2 - 1)]
          rw [Nat.mul_sub_one (↑m ^ 2) (↑n ^ 2)]
          rw [Nat.sub_sub_right (↑m ^ 2 * ↑n ^ 2 - ↑m ^ 2) (NeZero.one_le)]
          group
          rw [← Nat.add_sub_assoc ?_ 1]
          · simp [← add_assoc]
            rw [← Nat.Simproc.add_sub_add_ge 2 (↑n ^ 2) ?_]
            · group
              rw [← Nat.add_sub_assoc ?_ 2]
              apply Nat.add_le_mul
              · have := Nat.pow_le_pow_left h2 2
                exact Nat.le_of_add_left_le this
              · have := Nat.pow_le_pow_left h1 2
                exact Nat.le_of_add_left_le this
            · apply Nat.le_mul_of_pos_right
              positivity
          · set x := m.val ^ 2
            set y := n.val ^ 2
            rw [← Nat.mul_sub_one x y]
            have : 4 ≤ x := Nat.pow_le_pow_left h2 2
            have : y ≤ x * (y - 1) := by
              grw [← this]
              have : 4 ≤ y := Nat.pow_le_pow_left h1 2
              omega
            omega
        rw [this]
        rw [show (m.val * n) ^ 2 = m.val ^ 2 * n.val ^ 2 by ring]
        rw [← tsub_tsub_assoc ?_ ?_]
        · apply Nat.sub_le
        · refine Nat.add_le_mul ?_ ?_
          · grind
          · grind
        · grind
      · have : m.val > 0 := m.2
        have : m.val = 1 := by omega
        simp [this]
        simp [Nat.choose_two_right]
        simp [add_mul]
        have : 4 ≤ n.val ^ 2 := Nat.pow_le_pow_left h1 2
        set x := n.val
        have hmul : 0 ≤ 2 * (x : ℤ)^2 - (x : ℤ) * (x : ℤ) - (x : ℤ) - 2 := by
          nlinarith
        grind
  grw [this, ← Nat.pow_mul] at this2

  have : 1 ≤ m.val * n.val := by
    have : 1 ≤ m.val := m.2
    have : 1 ≤ n.val := n.2
    grind
  have : 1 < m.val * n := by grind

  rw [Nat.le_pow_iff_clog_le this] at this2
  rw [a1] at this2
  -- grw [← Nat.log_le_clog] at this
  rw [← Real.natCeil_logb_natCast] at this2
  simp at this2
  rw [← Real.log_div_log] at this2
  rw [Real.log_mul (by positivity) (by positivity)] at this2
  grw [jo (by omega)] at this2
  · simp at this2
    norm_cast at this2
    ring_nf at this2
    field_simp at this2
    have : Real.log ↑↑(m * n) ≠ 0 := by
      refine Real.log_ne_zero_of_pos_of_ne_one ?_ ?_
      · norm_cast
      · norm_cast
        exact ne_of_gt this
    rw [add_div (↑↑(m * n) * (Real.log 2 + (Real.log ↑↑(m * n) - 1)) * 2) (Real.log ↑↑(m * n))
        (Real.log ↑↑(m * n) * 2)] at this2
    rw [div_mul_cancel_left₀ this 2] at this2
    rw [mul_div_mul_right (↑↑(m * n) * (Real.log 2 + (Real.log ↑↑(m * n) - 1))) (Real.log ↑↑(m * n))
        (by grind)] at this2
    rw [mul_div_right_comm (↑↑(m * n)) (Real.log 2 + (Real.log ↑↑(m * n) - 1))
        (Real.log ↑↑(m * n))] at this2
    have : Real.log 2 + (Real.log ↑↑(m * n) - 1)
        = Real.log ↑↑(m * n) - (1 - Real.log 2) := by ring
    rw [this] at this2
    rw [mul_sub (↑↑(m * n) / Real.log ↑↑(m * n)) (Real.log ↑↑(m * n)) _] at this2
    rw [div_mul_cancel₀ _ (by assumption)] at this2
    simp at this2
    linarith
  · apply Real.log_nonneg (by norm_cast)
