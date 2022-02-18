import Mathbin.Analysis.SpecialFunctions.Exponential
import Mathbin.Combinatorics.Derangements.Finite
import Mathbin.Order.Filter.Basic

/-!
# Derangement exponential series

This file proves that the probability of a permutation on n elements being a derangement is 1/e.
The specific lemma is `num_derangements_tendsto_inv_e`.
-/


open Filter

open_locale BigOperators

open_locale TopologicalSpace

theorem num_derangements_tendsto_inv_e :
    Tendsto (fun n => (numDerangements n : ℝ) / n.factorial) atTop (𝓝 (Real.exp (-1))) := by
  let s : ℕ → ℝ := fun n => ∑ k in Finset.range n, (-1 : ℝ) ^ k / k.factorial
  suffices ∀ n : ℕ, (numDerangements n : ℝ) / n.factorial = s (n + 1) by
    simp_rw [this]
    rw [tendsto_add_at_top_iff_nat 1]
    apply HasSum.tendsto_sum_nat
    rw [Real.exp_eq_exp_ℝ_ℝ]
    exact exp_series_field_has_sum_exp (-1 : ℝ)
  intro n
  rw [← Int.cast_coe_nat, num_derangements_sum]
  push_cast
  rw [Finset.sum_div]
  refine' Finset.sum_congr (refl _) _
  intro k hk
  have h_le : k ≤ n := finset.mem_range_succ_iff.mp hk
  rw [Nat.asc_factorial_eq_div, add_tsub_cancel_of_le h_le]
  push_cast [Nat.factorial_dvd_factorial h_le]
  field_simp [Nat.factorial_ne_zero]
  ring

