/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel

! This file was ported from Lean 3 source module analysis.convex.specific_functions
! leanprover-community/mathlib commit 247a102b14f3cebfee126293341af5f6bed00237
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Calculus.MeanValue
import Mathbin.Analysis.SpecialFunctions.PowDeriv
import Mathbin.Analysis.SpecialFunctions.Sqrt

/-!
# Collection of convex functions

In this file we prove that the following functions are convex:

* `strict_convex_on_exp` : The exponential function is strictly convex.
* `even.convex_on_pow`, `even.strict_convex_on_pow` : For an even `n : ℕ`, `λ x, x ^ n` is convex
  and strictly convex when `2 ≤ n`.
* `convex_on_pow`, `strict_convex_on_pow` : For `n : ℕ`, `λ x, x ^ n` is convex on $[0, +∞)$ and
  strictly convex when `2 ≤ n`.
* `convex_on_zpow`, `strict_convex_on_zpow` : For `m : ℤ`, `λ x, x ^ m` is convex on $[0, +∞)$ and
  strictly convex when `m ≠ 0, 1`.
* `convex_on_rpow`, `strict_convex_on_rpow` : For `p : ℝ`, `λ x, x ^ p` is convex on $[0, +∞)$ when
  `1 ≤ p` and strictly convex when `1 < p`.
* `strict_concave_on_log_Ioi`, `strict_concave_on_log_Iio`: `real.log` is strictly concave on
  $(0, +∞)$ and $(-∞, 0)$ respectively.

## TODO

For `p : ℝ`, prove that `λ x, x ^ p` is concave when `0 ≤ p ≤ 1` and strictly concave when
`0 < p < 1`.
-/


open Real Set

open BigOperators Nnreal

/-- `exp` is strictly convex on the whole real line. -/
theorem strict_convex_on_exp : StrictConvexOn ℝ univ exp :=
  strict_convex_on_univ_of_deriv2_pos continuous_exp fun x => (iter_deriv_exp 2).symm ▸ exp_pos x
#align strict_convex_on_exp strict_convex_on_exp

/-- `exp` is convex on the whole real line. -/
theorem convex_on_exp : ConvexOn ℝ univ exp :=
  strict_convex_on_exp.ConvexOn
#align convex_on_exp convex_on_exp

/-- `x^n`, `n : ℕ` is convex on the whole real line whenever `n` is even -/
theorem Even.convex_on_pow {n : ℕ} (hn : Even n) : ConvexOn ℝ Set.univ fun x : ℝ => x ^ n :=
  by
  apply convex_on_univ_of_deriv2_nonneg (differentiable_pow n)
  · simp only [deriv_pow', Differentiable.mul, differentiable_const, differentiable_pow]
  · intro x
    obtain ⟨k, hk⟩ := (hn.tsub <| even_bit0 _).exists_two_nsmul _
    rw [iter_deriv_pow, Finset.prod_range_cast_nat_sub, hk, nsmul_eq_mul, pow_mul']
    exact mul_nonneg (Nat.cast_nonneg _) (pow_two_nonneg _)
#align even.convex_on_pow Even.convex_on_pow

/-- `x^n`, `n : ℕ` is strictly convex on the whole real line whenever `n ≠ 0` is even. -/
theorem Even.strict_convex_on_pow {n : ℕ} (hn : Even n) (h : n ≠ 0) :
    StrictConvexOn ℝ Set.univ fun x : ℝ => x ^ n :=
  by
  apply StrictMono.strict_convex_on_univ_of_deriv (continuous_pow n)
  rw [deriv_pow']
  replace h := Nat.pos_of_ne_zero h
  exact
    StrictMono.const_mul (Odd.strictMono_pow <| Nat.Even.sub_odd h hn <| Nat.odd_iff.2 rfl)
      (Nat.cast_pos.2 h)
#align even.strict_convex_on_pow Even.strict_convex_on_pow

/-- `x^n`, `n : ℕ` is convex on `[0, +∞)` for all `n` -/
theorem convex_on_pow (n : ℕ) : ConvexOn ℝ (Ici 0) fun x : ℝ => x ^ n :=
  by
  apply
    convex_on_of_deriv2_nonneg (convex_Ici _) (continuous_pow n).ContinuousOn
      (differentiable_on_pow n)
  · simp only [deriv_pow']
    exact (@differentiable_on_pow ℝ _ _ _).const_mul (n : ℝ)
  · intro x hx
    rw [iter_deriv_pow, Finset.prod_range_cast_nat_sub]
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (interior_subset hx) _)
#align convex_on_pow convex_on_pow

/-- `x^n`, `n : ℕ` is strictly convex on `[0, +∞)` for all `n` greater than `2`. -/
theorem strict_convex_on_pow {n : ℕ} (hn : 2 ≤ n) : StrictConvexOn ℝ (Ici 0) fun x : ℝ => x ^ n :=
  by
  apply StrictMonoOn.strict_convex_on_of_deriv (convex_Ici _) (continuous_on_pow _)
  rw [deriv_pow', interior_Ici]
  exact fun x (hx : 0 < x) y hy hxy =>
    mul_lt_mul_of_pos_left (pow_lt_pow_of_lt_left hxy hx.le <| Nat.sub_pos_of_lt hn)
      (Nat.cast_pos.2 <| zero_lt_two.trans_le hn)
#align strict_convex_on_pow strict_convex_on_pow

/-- Specific case of Jensen's inequality for sums of powers -/
theorem Real.pow_sum_div_card_le_sum_pow {α : Type _} {s : Finset α} {f : α → ℝ} (n : ℕ)
    (hf : ∀ a ∈ s, 0 ≤ f a) : (∑ x in s, f x) ^ (n + 1) / s.card ^ n ≤ ∑ x in s, f x ^ (n + 1) :=
  by
  rcases s.eq_empty_or_nonempty with (rfl | hs)
  · simp_rw [Finset.sum_empty, zero_pow' _ (Nat.succ_ne_zero n), zero_div]
  · have hs0 : 0 < (s.card : ℝ) := Nat.cast_pos.2 hs.card_pos
    suffices (∑ x in s, f x / s.card) ^ (n + 1) ≤ ∑ x in s, f x ^ (n + 1) / s.card by
      rwa [← Finset.sum_div, ← Finset.sum_div, div_pow, pow_succ' (s.card : ℝ), ← div_div,
        div_le_iff hs0, div_mul, div_self hs0.ne', div_one] at this
    have :=
      @ConvexOn.map_sum_le ℝ ℝ ℝ α _ _ _ _ _ _ (Set.Ici 0) (fun x => x ^ (n + 1)) s
        (fun _ => 1 / s.card) (coe ∘ f) (convex_on_pow (n + 1)) _ _ fun i hi =>
        Set.mem_Ici.2 (hf i hi)
    · simpa only [inv_mul_eq_div, one_div, Algebra.id.smul_eq_mul] using this
    · simp only [one_div, inv_nonneg, Nat.cast_nonneg, imp_true_iff]
    · simpa only [one_div, Finset.sum_const, nsmul_eq_mul] using mul_inv_cancel hs0.ne'
#align real.pow_sum_div_card_le_sum_pow Real.pow_sum_div_card_le_sum_pow

theorem Nnreal.pow_sum_div_card_le_sum_pow {α : Type _} (s : Finset α) (f : α → ℝ≥0) (n : ℕ) :
    (∑ x in s, f x) ^ (n + 1) / s.card ^ n ≤ ∑ x in s, f x ^ (n + 1) := by
  simpa only [← Nnreal.coe_le_coe, Nnreal.coe_sum, Nonneg.coe_div, Nnreal.coe_pow] using
    @Real.pow_sum_div_card_le_sum_pow α s (coe ∘ f) n fun _ _ => Nnreal.coe_nonneg _
#align nnreal.pow_sum_div_card_le_sum_pow Nnreal.pow_sum_div_card_le_sum_pow

theorem Finset.prod_nonneg_of_card_nonpos_even {α β : Type _} [LinearOrderedCommRing β] {f : α → β}
    [DecidablePred fun x => f x ≤ 0] {s : Finset α} (h0 : Even (s.filter fun x => f x ≤ 0).card) :
    0 ≤ ∏ x in s, f x :=
  calc
    0 ≤ ∏ x in s, (if f x ≤ 0 then (-1 : β) else 1) * f x :=
      Finset.prod_nonneg fun x _ => by
        split_ifs with hx hx
        · simp [hx]
        simp at hx⊢
        exact le_of_lt hx
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_ite, Finset.prod_const_one, mul_one,
        Finset.prod_const, neg_one_pow_eq_pow_mod_two, Nat.even_iff.1 h0, pow_zero, one_mul]
    
#align finset.prod_nonneg_of_card_nonpos_even Finset.prod_nonneg_of_card_nonpos_even

theorem int_prod_range_nonneg (m : ℤ) (n : ℕ) (hn : Even n) : 0 ≤ ∏ k in Finset.range n, m - k :=
  by
  rcases hn with ⟨n, rfl⟩
  induction' n with n ihn; · simp
  rw [← two_mul] at ihn
  rw [← two_mul, Nat.succ_eq_add_one, mul_add, mul_one, bit0, ← add_assoc, Finset.prod_range_succ,
    Finset.prod_range_succ, mul_assoc]
  refine' mul_nonneg ihn _; generalize (1 + 1) * n = k
  cases' le_or_lt m k with hmk hmk
  · have : m ≤ k + 1 := hmk.trans (lt_add_one ↑k).le
    convert mul_nonneg_of_nonpos_of_nonpos (sub_nonpos_of_le hmk) _
    convert sub_nonpos_of_le this
  · exact mul_nonneg (sub_nonneg_of_le hmk.le) (sub_nonneg_of_le hmk)
#align int_prod_range_nonneg int_prod_range_nonneg

theorem int_prod_range_pos {m : ℤ} {n : ℕ} (hn : Even n) (hm : m ∉ Ico (0 : ℤ) n) :
    0 < ∏ k in Finset.range n, m - k :=
  by
  refine' (int_prod_range_nonneg m n hn).lt_of_ne fun h => hm _
  rw [eq_comm, Finset.prod_eq_zero_iff] at h
  obtain ⟨a, ha, h⟩ := h
  rw [sub_eq_zero.1 h]
  exact ⟨Int.ofNat_zero_le _, Int.ofNat_lt.2 <| Finset.mem_range.1 ha⟩
#align int_prod_range_pos int_prod_range_pos

/-- `x^m`, `m : ℤ` is convex on `(0, +∞)` for all `m` -/
theorem convex_on_zpow (m : ℤ) : ConvexOn ℝ (Ioi 0) fun x : ℝ => x ^ m :=
  by
  have : ∀ n : ℤ, DifferentiableOn ℝ (fun x => x ^ n) (Ioi (0 : ℝ)) := fun n =>
    differentiable_on_zpow _ _ (Or.inl <| lt_irrefl _)
  apply convex_on_of_deriv2_nonneg (convex_Ioi 0) <;> try simp only [interior_Ioi, deriv_zpow']
  · exact (this _).ContinuousOn
  · exact this _
  · exact (this _).const_mul _
  · intro x hx
    rw [iter_deriv_zpow]
    refine' mul_nonneg _ (zpow_nonneg (le_of_lt hx) _)
    exact_mod_cast int_prod_range_nonneg _ _ (even_bit0 1)
#align convex_on_zpow convex_on_zpow

/-- `x^m`, `m : ℤ` is convex on `(0, +∞)` for all `m` except `0` and `1`. -/
theorem strict_convex_on_zpow {m : ℤ} (hm₀ : m ≠ 0) (hm₁ : m ≠ 1) :
    StrictConvexOn ℝ (Ioi 0) fun x : ℝ => x ^ m :=
  by
  apply strict_convex_on_of_deriv2_pos' (convex_Ioi 0)
  · exact (continuous_on_zpow₀ m).mono fun x hx => ne_of_gt hx
  intro x hx
  rw [iter_deriv_zpow]
  refine' mul_pos _ (zpow_pos_of_pos hx _)
  exact_mod_cast int_prod_range_pos (even_bit0 1) fun hm => _
  norm_cast  at hm
  rw [← Finset.coe_Ico] at hm
  fin_cases hm <;> cc
#align strict_convex_on_zpow strict_convex_on_zpow

theorem convex_on_rpow {p : ℝ} (hp : 1 ≤ p) : ConvexOn ℝ (Ici 0) fun x : ℝ => x ^ p :=
  by
  have A : (deriv fun x : ℝ => x ^ p) = fun x => p * x ^ (p - 1) :=
    by
    ext x
    simp [hp]
  apply convex_on_of_deriv2_nonneg (convex_Ici 0)
  · exact continuous_on_id.rpow_const fun x _ => Or.inr (zero_le_one.trans hp)
  · exact (differentiable_rpow_const hp).DifferentiableOn
  · rw [A]
    intro x hx
    replace hx : x ≠ 0
    · simp at hx
      exact ne_of_gt hx
    simp [DifferentiableAt.differentiable_within_at, hx]
  · intro x hx
    replace hx : 0 < x
    · simpa using hx
    suffices 0 ≤ p * ((p - 1) * x ^ (p - 1 - 1)) by simpa [ne_of_gt hx, A]
    apply mul_nonneg (le_trans zero_le_one hp)
    exact mul_nonneg (sub_nonneg_of_le hp) (rpow_nonneg_of_nonneg hx.le _)
#align convex_on_rpow convex_on_rpow

theorem strict_convex_on_rpow {p : ℝ} (hp : 1 < p) : StrictConvexOn ℝ (Ici 0) fun x : ℝ => x ^ p :=
  by
  have A : (deriv fun x : ℝ => x ^ p) = fun x => p * x ^ (p - 1) :=
    by
    ext x
    simp [hp.le]
  apply strict_convex_on_of_deriv2_pos (convex_Ici 0)
  · exact continuous_on_id.rpow_const fun x _ => Or.inr (zero_le_one.trans hp.le)
  rw [interior_Ici]
  rintro x (hx : 0 < x)
  suffices 0 < p * ((p - 1) * x ^ (p - 1 - 1)) by simpa [ne_of_gt hx, A]
  exact mul_pos (zero_lt_one.trans hp) (mul_pos (sub_pos_of_lt hp) (rpow_pos_of_pos hx _))
#align strict_convex_on_rpow strict_convex_on_rpow

theorem strict_concave_on_log_Ioi : StrictConcaveOn ℝ (Ioi 0) log :=
  by
  have h₁ : Ioi 0 ⊆ ({0} : Set ℝ)ᶜ := fun x (hx : 0 < x) (hx' : x = 0) => hx.ne' hx'
  refine'
    strict_concave_on_of_deriv2_neg' (convex_Ioi 0) (continuous_on_log.mono h₁)
      fun x (hx : 0 < x) => _
  rw [Function.iterate_succ, Function.iterate_one]
  change (deriv (deriv log)) x < 0
  rw [deriv_log', deriv_inv]
  exact neg_neg_of_pos (inv_pos.2 <| sq_pos_of_ne_zero _ hx.ne')
#align strict_concave_on_log_Ioi strict_concave_on_log_Ioi

theorem strict_concave_on_log_Iio : StrictConcaveOn ℝ (Iio 0) log :=
  by
  have h₁ : Iio 0 ⊆ ({0} : Set ℝ)ᶜ := fun x (hx : x < 0) (hx' : x = 0) => hx.Ne hx'
  refine'
    strict_concave_on_of_deriv2_neg' (convex_Iio 0) (continuous_on_log.mono h₁)
      fun x (hx : x < 0) => _
  rw [Function.iterate_succ, Function.iterate_one]
  change (deriv (deriv log)) x < 0
  rw [deriv_log', deriv_inv]
  exact neg_neg_of_pos (inv_pos.2 <| sq_pos_of_ne_zero _ hx.ne)
#align strict_concave_on_log_Iio strict_concave_on_log_Iio

section SqrtMulLog

theorem has_deriv_at_sqrt_mul_log {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun x => sqrt x * log x) ((2 + log x) / (2 * sqrt x)) x :=
  by
  convert (has_deriv_at_sqrt hx).mul (has_deriv_at_log hx)
  rw [add_div, div_mul_right (sqrt x) two_ne_zero, ← div_eq_mul_inv, sqrt_div_self', add_comm,
    div_eq_mul_one_div, mul_comm]
#align has_deriv_at_sqrt_mul_log has_deriv_at_sqrt_mul_log

theorem deriv_sqrt_mul_log (x : ℝ) :
    deriv (fun x => sqrt x * log x) x = (2 + log x) / (2 * sqrt x) :=
  by
  cases' lt_or_le 0 x with hx hx
  · exact (has_deriv_at_sqrt_mul_log hx.ne').deriv
  · rw [sqrt_eq_zero_of_nonpos hx, mul_zero, div_zero]
    refine' HasDerivWithinAt.deriv_eq_zero _ (unique_diff_on_Iic 0 x hx)
    refine' (has_deriv_within_at_const x _ 0).congr_of_mem (fun x hx => _) hx
    rw [sqrt_eq_zero_of_nonpos hx, zero_mul]
#align deriv_sqrt_mul_log deriv_sqrt_mul_log

theorem deriv_sqrt_mul_log' :
    (deriv fun x => sqrt x * log x) = fun x => (2 + log x) / (2 * sqrt x) :=
  funext deriv_sqrt_mul_log
#align deriv_sqrt_mul_log' deriv_sqrt_mul_log'

theorem deriv2_sqrt_mul_log (x : ℝ) :
    (deriv^[2]) (fun x => sqrt x * log x) x = -log x / (4 * sqrt x ^ 3) :=
  by
  simp only [Nat.iterate, deriv_sqrt_mul_log']
  cases' le_or_lt x 0 with hx hx
  · rw [sqrt_eq_zero_of_nonpos hx, zero_pow zero_lt_three, mul_zero, div_zero]
    refine' HasDerivWithinAt.deriv_eq_zero _ (unique_diff_on_Iic 0 x hx)
    refine' (has_deriv_within_at_const _ _ 0).congr_of_mem (fun x hx => _) hx
    rw [sqrt_eq_zero_of_nonpos hx, mul_zero, div_zero]
  · have h₀ : sqrt x ≠ 0 := sqrt_ne_zero'.2 hx
    convert
      (((has_deriv_at_log hx.ne').const_add 2).div ((has_deriv_at_sqrt hx.ne').const_mul 2) <|
          mul_ne_zero two_ne_zero h₀).deriv using
      1
    nth_rw 3 [← mul_self_sqrt hx.le]
    field_simp
    ring
#align deriv2_sqrt_mul_log deriv2_sqrt_mul_log

theorem strict_concave_on_sqrt_mul_log_Ioi :
    StrictConcaveOn ℝ (Set.Ioi 1) fun x => sqrt x * log x :=
  by
  apply strict_concave_on_of_deriv2_neg' (convex_Ioi 1) _ fun x hx => _
  ·
    exact
      continuous_sqrt.continuous_on.mul
        (continuous_on_log.mono fun x hx => ne_of_gt (zero_lt_one.trans hx))
  · rw [deriv2_sqrt_mul_log x]
    exact
      div_neg_of_neg_of_pos (neg_neg_of_pos (log_pos hx))
        (mul_pos four_pos (pow_pos (sqrt_pos.mpr (zero_lt_one.trans hx)) 3))
#align strict_concave_on_sqrt_mul_log_Ioi strict_concave_on_sqrt_mul_log_Ioi

end SqrtMulLog

open Real

theorem strict_concave_on_sin_Icc : StrictConcaveOn ℝ (Icc 0 π) sin :=
  by
  apply strict_concave_on_of_deriv2_neg (convex_Icc _ _) continuous_on_sin fun x hx => _
  rw [interior_Icc] at hx
  simp [sin_pos_of_mem_Ioo hx]
#align strict_concave_on_sin_Icc strict_concave_on_sin_Icc

theorem strict_concave_on_cos_Icc : StrictConcaveOn ℝ (Icc (-(π / 2)) (π / 2)) cos :=
  by
  apply strict_concave_on_of_deriv2_neg (convex_Icc _ _) continuous_on_cos fun x hx => _
  rw [interior_Icc] at hx
  simp [cos_pos_of_mem_Ioo hx]
#align strict_concave_on_cos_Icc strict_concave_on_cos_Icc

