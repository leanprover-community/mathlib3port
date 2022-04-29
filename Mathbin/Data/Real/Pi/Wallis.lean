/-
Copyright (c) 2021 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import Mathbin.Analysis.SpecialFunctions.Integrals

/-! ### The Wallis Product for Pi -/


namespace Real

open Real TopologicalSpace BigOperators

open Filter Finset intervalIntegral

theorem integral_sin_pow_div_tendsto_one :
    Tendsto (fun k => (∫ x in 0 ..π, sin x ^ (2 * k + 1)) / ∫ x in 0 ..π, sin x ^ (2 * k)) atTop (𝓝 1) := by
  have h₃ : ∀ n, ((∫ x in 0 ..π, sin x ^ (2 * n + 1)) / ∫ x in 0 ..π, sin x ^ (2 * n)) ≤ 1 := fun n =>
    (div_le_one (integral_sin_pow_pos _)).mpr (integral_sin_pow_succ_le _)
  have h₄ : ∀ n, ((∫ x in 0 ..π, sin x ^ (2 * n + 1)) / ∫ x in 0 ..π, sin x ^ (2 * n)) ≥ 2 * n / (2 * n + 1) := by
    rintro ⟨n⟩
    · have : 0 ≤ (1 + 1) / π :=
        div_nonneg
          (by
            norm_num)
          pi_pos.le
      simp [this]
      
    calc
      ((∫ x in 0 ..π, sin x ^ (2 * n.succ + 1)) / ∫ x in 0 ..π, sin x ^ (2 * n.succ)) ≥
          (∫ x in 0 ..π, sin x ^ (2 * n.succ + 1)) / ∫ x in 0 ..π, sin x ^ (2 * n + 1) :=
        by
        refine' div_le_div (integral_sin_pow_pos _).le le_rfl (integral_sin_pow_pos _) _
        convert integral_sin_pow_succ_le (2 * n + 1) using 1_ = 2 * ↑n.succ / (2 * ↑n.succ + 1) := by
        rw [div_eq_iff (integral_sin_pow_pos (2 * n + 1)).ne']
        convert integral_sin_pow (2 * n + 1)
        simp' with field_simps
        norm_cast
  refine' tendsto_of_tendsto_of_tendsto_of_le_of_le _ _ (fun n => (h₄ n).le) fun n => h₃ n
  · refine' metric.tendsto_at_top.mpr fun ε hε => ⟨⌈1 / ε⌉₊, fun n hn => _⟩
    have h : (2 : ℝ) * n / (2 * n + 1) - 1 = -1 / (2 * n + 1) := by
      conv_lhs =>
        congr skip rw [←
          @div_self _ _ ((2 : ℝ) * n + 1)
            (by
              norm_cast
              linarith)]
      rw [← sub_div, ← sub_sub, sub_self, zero_sub]
    have hpos : (0 : ℝ) < 2 * n + 1 := by
      norm_cast
      norm_num
    rw [dist_eq, h, abs_div, abs_neg, abs_one, abs_of_pos hpos, one_div_lt hpos hε]
    calc 1 / ε ≤ ⌈1 / ε⌉₊ := Nat.le_ceil _ _ ≤ n := by
        exact_mod_cast hn.le _ < 2 * n + 1 := by
        norm_cast
        linarith
    
  · exact tendsto_const_nhds
    

/-- This theorem establishes the Wallis Product for `π`. Our proof is largely about analyzing
  the behavior of the ratio of the integral of `sin x ^ n` as `n → ∞`.
  See: https://en.wikipedia.org/wiki/Wallis_product

  The proof can be broken down into two pieces.
  (Pieces involving general properties of the integral of `sin x ^n` can be found
  in `analysis.special_functions.integrals`.) First, we use integration by parts to obtain a
  recursive formula for `∫ x in 0..π, sin x ^ (n + 2)` in terms of `∫ x in 0..π, sin x ^ n`.
  From this we can obtain closed form products of `∫ x in 0..π, sin x ^ (2 * n)` and
  `∫ x in 0..π, sin x ^ (2 * n + 1)` via induction. Next, we study the behavior of the ratio
  `∫ (x : ℝ) in 0..π, sin x ^ (2 * k + 1)) / ∫ (x : ℝ) in 0..π, sin x ^ (2 * k)` and prove that
  it converges to one using the squeeze theorem. The final product for `π` is obtained after some
  algebraic manipulation. -/
theorem tendsto_prod_pi_div_two :
    Tendsto (fun k => ∏ i in range k, ((2 : ℝ) * i + 2) / (2 * i + 1) * ((2 * i + 2) / (2 * i + 3))) atTop
      (𝓝 (π / 2)) :=
  by
  suffices h :
    tendsto (fun k => 2 / π * ∏ i in range k, ((2 : ℝ) * i + 2) / (2 * i + 1) * ((2 * i + 2) / (2 * i + 3))) at_top
      (𝓝 1)
  · have := tendsto.const_mul (π / 2) h
    have h : π / 2 ≠ 0
    norm_num [pi_ne_zero]
    simp only [← mul_assoc, ← @inv_div _ _ π 2, mul_inv_cancel h, one_mulₓ, mul_oneₓ] at this
    exact this
    
  have h :
    (fun k : ℕ => (2 : ℝ) / π * ∏ i : ℕ in range k, (2 * i + 2) / (2 * i + 1) * ((2 * i + 2) / (2 * i + 3))) = fun k =>
      (2 * ∏ i in range k, (2 * i + 2) / (2 * i + 3)) / (π * ∏ i : ℕ in range k, (2 * i + 1) / (2 * i + 2)) :=
    by
    funext
    have h :
      (∏ i : ℕ in range k, ((2 : ℝ) * ↑i + 2) / (2 * ↑i + 1)) = 1 / ∏ i : ℕ in range k, (2 * ↑i + 1) / (2 * ↑i + 2) :=
      by
      rw [one_div, ← Finset.prod_inv_distrib']
      refine' prod_congr rfl fun x hx => _
      field_simp
    rw [prod_mul_distrib, h]
    field_simp
  simp only [h, ← integral_sin_pow_even, ← integral_sin_pow_odd]
  exact integral_sin_pow_div_tendsto_one

end Real

