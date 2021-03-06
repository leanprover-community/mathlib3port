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
    Tendsto (fun k => (â« x in 0 ..Ï, sin x ^ (2 * k + 1)) / â« x in 0 ..Ï, sin x ^ (2 * k)) atTop (ð 1) := by
  have hâ : â n, ((â« x in 0 ..Ï, sin x ^ (2 * n + 1)) / â« x in 0 ..Ï, sin x ^ (2 * n)) â¤ 1 := fun n =>
    (div_le_one (integral_sin_pow_pos _)).mpr (integral_sin_pow_succ_le _)
  have hâ : â n, ((â« x in 0 ..Ï, sin x ^ (2 * n + 1)) / â« x in 0 ..Ï, sin x ^ (2 * n)) â¥ 2 * n / (2 * n + 1) := by
    rintro â¨nâ©
    Â· have : 0 â¤ (1 + 1) / Ï :=
        div_nonneg
          (by
            norm_num)
          pi_pos.le
      simp [â this]
      
    calc
      ((â« x in 0 ..Ï, sin x ^ (2 * n.succ + 1)) / â« x in 0 ..Ï, sin x ^ (2 * n.succ)) â¥
          (â« x in 0 ..Ï, sin x ^ (2 * n.succ + 1)) / â« x in 0 ..Ï, sin x ^ (2 * n + 1) :=
        by
        refine' div_le_div (integral_sin_pow_pos _).le le_rfl (integral_sin_pow_pos _) _
        convert integral_sin_pow_succ_le (2 * n + 1) using 1_ = 2 * ân.succ / (2 * ân.succ + 1) := by
        rw [div_eq_iff (integral_sin_pow_pos (2 * n + 1)).ne']
        convert integral_sin_pow (2 * n + 1)
        simp' with field_simps
        norm_cast
  refine' tendsto_of_tendsto_of_tendsto_of_le_of_le _ _ (fun n => (hâ n).le) fun n => hâ n
  Â· refine' metric.tendsto_at_top.mpr fun Îµ hÎµ => â¨â1 / Îµââ, fun n hn => _â©
    have h : (2 : â) * n / (2 * n + 1) - 1 = -1 / (2 * n + 1) := by
      conv_lhs =>
        congr skip rw [â
          @div_self _ _ ((2 : â) * n + 1)
            (by
              norm_cast
              linarith)]
      rw [â sub_div, â sub_sub, sub_self, zero_sub]
    have hpos : (0 : â) < 2 * n + 1 := by
      norm_cast
      norm_num
    rw [dist_eq, h, abs_div, abs_neg, abs_one, abs_of_pos hpos, one_div_lt hpos hÎµ]
    calc 1 / Îµ â¤ â1 / Îµââ := Nat.le_ceil _ _ â¤ n := by
        exact_mod_cast hn.le _ < 2 * n + 1 := by
        norm_cast
        linarith
    
  Â· exact tendsto_const_nhds
    

/-- This theorem establishes the Wallis Product for `Ï`. Our proof is largely about analyzing
  the behavior of the ratio of the integral of `sin x ^ n` as `n â â`.
  See: https://en.wikipedia.org/wiki/Wallis_product

  The proof can be broken down into two pieces.
  (Pieces involving general properties of the integral of `sin x ^n` can be found
  in `analysis.special_functions.integrals`.) First, we use integration by parts to obtain a
  recursive formula for `â« x in 0..Ï, sin x ^ (n + 2)` in terms of `â« x in 0..Ï, sin x ^ n`.
  From this we can obtain closed form products of `â« x in 0..Ï, sin x ^ (2 * n)` and
  `â« x in 0..Ï, sin x ^ (2 * n + 1)` via induction. Next, we study the behavior of the ratio
  `â« (x : â) in 0..Ï, sin x ^ (2 * k + 1)) / â« (x : â) in 0..Ï, sin x ^ (2 * k)` and prove that
  it converges to one using the squeeze theorem. The final product for `Ï` is obtained after some
  algebraic manipulation. -/
theorem tendsto_prod_pi_div_two :
    Tendsto (fun k => â i in range k, ((2 : â) * i + 2) / (2 * i + 1) * ((2 * i + 2) / (2 * i + 3))) atTop
      (ð (Ï / 2)) :=
  by
  suffices h :
    tendsto (fun k => (Ï / 2)â»Â¹ * â i in range k, (2 * i + 2) / (2 * i + 1) * ((2 * i + 2) / (2 * i + 3))) at_top (ð 1)
  Â· convert h.const_mul (Ï / 2)
    Â· simp_rw
        [mul_inv_cancel_leftâ
          (show Ï / 2 â  0 by
            norm_num [â pi_ne_zero])]
      
    Â· rw [mul_oneâ]
      
    
  convert integral_sin_pow_div_tendsto_one
  funext
  rw [integral_sin_pow_even, integral_sin_pow_odd, mul_div_mul_comm, â prod_div_distrib, inv_div]
  congr with i
  rw [div_div_div_comm, div_div_eq_mul_div, mul_div_assoc]

end Real

