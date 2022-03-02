/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathbin.Analysis.SpecificLimits
import Mathbin.Analysis.Analytic.Basic
import Mathbin.Analysis.Complex.Basic
import Mathbin.Data.Nat.Choose.Cast

/-!
# Exponential in a Banach algebra

In this file, we define `exp 𝕂 𝔸`, the exponential map in a normed algebra `𝔸` over a nondiscrete
normed field `𝕂`. Although the definition doesn't require `𝔸` to be complete, we need to assume it
for most results.

We then prove some basic results, but we avoid importing derivatives here to minimize dependencies.
Results involving derivatives and comparisons with `real.exp` and `complex.exp` can be found in
`analysis/special_functions/exponential`.

## Main results

We prove most result for an arbitrary field `𝕂`, and then specialize to `𝕂 = ℝ` or `𝕂 = ℂ`.

### General case

- `exp_add_of_commute_of_lt_radius` : if `𝕂` has characteristic zero, then given two commuting
  elements `x` and `y` in the disk of convergence, we have
  `exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`
- `exp_add_of_lt_radius` : if `𝕂` has characteristic zero and `𝔸` is commutative, then given two
  elements `x` and `y` in the disk of convergence, we have
  `exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`

### `𝕂 = ℝ` or `𝕂 = ℂ`

- `exp_series_radius_eq_top` : the `formal_multilinear_series` defining `exp 𝕂 𝔸` has infinite
  radius of convergence
- `exp_add_of_commute` : given two commuting elements `x` and `y`, we have
  `exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`
- `exp_add` : if `𝔸` is commutative, then we have `exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`
  for any `x` and `y`

### Other useful compatibility results

- `exp_eq_exp` : if `𝔸` is a normed algebra over two fields `𝕂` and `𝕂'`, then `exp 𝕂 𝔸 = exp 𝕂' 𝔸`

-/


open Filter IsROrC ContinuousMultilinearMap NormedField Asymptotics

open_locale Nat TopologicalSpace BigOperators Ennreal

section AnyFieldAnyAlgebra

variable (𝕂 𝔸 : Type _) [NondiscreteNormedField 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]

/-- In a Banach algebra `𝔸` over a normed field `𝕂`, `exp_series 𝕂 𝔸` is the
`formal_multilinear_series` whose `n`-th term is the map `(xᵢ) : 𝔸ⁿ ↦ (1/n! : 𝕂) • ∏ xᵢ`.
Its sum is the exponential map `exp 𝕂 𝔸 : 𝔸 → 𝔸`. -/
def expSeries : FormalMultilinearSeries 𝕂 𝔸 𝔸 := fun n => (1 / n ! : 𝕂) • ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 n 𝔸

/-- In a Banach algebra `𝔸` over a normed field `𝕂`, `exp 𝕂 𝔸 : 𝔸 → 𝔸` is the exponential map
determined by the action of `𝕂` on `𝔸`.
It is defined as the sum of the `formal_multilinear_series` `exp_series 𝕂 𝔸`. -/
noncomputable def exp (x : 𝔸) : 𝔸 :=
  (expSeries 𝕂 𝔸).Sum x

variable {𝕂 𝔸}

theorem exp_series_apply_eq (x : 𝔸) (n : ℕ) : (expSeries 𝕂 𝔸 n fun _ => x) = (1 / n ! : 𝕂) • x ^ n := by
  simp [expSeries]

theorem exp_series_apply_eq' (x : 𝔸) : (fun n => expSeries 𝕂 𝔸 n fun _ => x) = fun n => (1 / n ! : 𝕂) • x ^ n :=
  funext (exp_series_apply_eq x)

theorem exp_series_apply_eq_field (x : 𝕂) (n : ℕ) : (expSeries 𝕂 𝕂 n fun _ => x) = x ^ n / n ! := by
  rw [div_eq_inv_mul, ← smul_eq_mul, inv_eq_one_div]
  exact exp_series_apply_eq x n

theorem exp_series_apply_eq_field' (x : 𝕂) : (fun n => expSeries 𝕂 𝕂 n fun _ => x) = fun n => x ^ n / n ! :=
  funext (exp_series_apply_eq_field x)

theorem exp_series_sum_eq (x : 𝔸) : (expSeries 𝕂 𝔸).Sum x = ∑' n : ℕ, (1 / n ! : 𝕂) • x ^ n :=
  tsum_congr fun n => exp_series_apply_eq x n

theorem exp_series_sum_eq_field (x : 𝕂) : (expSeries 𝕂 𝕂).Sum x = ∑' n : ℕ, x ^ n / n ! :=
  tsum_congr fun n => exp_series_apply_eq_field x n

theorem exp_eq_tsum : exp 𝕂 𝔸 = fun x : 𝔸 => ∑' n : ℕ, (1 / n ! : 𝕂) • x ^ n :=
  funext exp_series_sum_eq

theorem exp_eq_tsum_field : exp 𝕂 𝕂 = fun x : 𝕂 => ∑' n : ℕ, x ^ n / n ! :=
  funext exp_series_sum_eq_field

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (n «expr ∉ » ({0} : finset exprℕ()))
theorem exp_zero : exp 𝕂 𝔸 0 = 1 := by
  suffices (fun x : 𝔸 => ∑' n : ℕ, (1 / n ! : 𝕂) • x ^ n) 0 = ∑' n : ℕ, if n = 0 then 1 else 0 by
    have key : ∀ n _ : n ∉ ({0} : Finset ℕ), (if n = 0 then (1 : 𝔸) else 0) = 0 := fun n hn =>
      if_neg (finset.not_mem_singleton.mp hn)
    rw [exp_eq_tsum, this, tsum_eq_sum key, Finset.sum_singleton]
    simp
  refine' tsum_congr fun n => _
  split_ifs with h h <;> simp [h]

theorem norm_exp_series_summable_of_mem_ball (x : 𝔸) (hx : x ∈ Emetric.Ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => ∥expSeries 𝕂 𝔸 n fun _ => x∥ :=
  (expSeries 𝕂 𝔸).summable_norm_apply hx

theorem norm_exp_series_summable_of_mem_ball' (x : 𝔸) (hx : x ∈ Emetric.Ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => ∥(1 / n ! : 𝕂) • x ^ n∥ := by
  change Summable (norm ∘ _)
  rw [← exp_series_apply_eq']
  exact norm_exp_series_summable_of_mem_ball x hx

theorem norm_exp_series_field_summable_of_mem_ball (x : 𝕂) (hx : x ∈ Emetric.Ball (0 : 𝕂) (expSeries 𝕂 𝕂).radius) :
    Summable fun n => ∥x ^ n / n !∥ := by
  change Summable (norm ∘ _)
  rw [← exp_series_apply_eq_field']
  exact norm_exp_series_summable_of_mem_ball x hx

section CompleteAlgebra

variable [CompleteSpace 𝔸]

theorem exp_series_summable_of_mem_ball (x : 𝔸) (hx : x ∈ Emetric.Ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => expSeries 𝕂 𝔸 n fun _ => x :=
  summable_of_summable_norm (norm_exp_series_summable_of_mem_ball x hx)

theorem exp_series_summable_of_mem_ball' (x : 𝔸) (hx : x ∈ Emetric.Ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => (1 / n ! : 𝕂) • x ^ n :=
  summable_of_summable_norm (norm_exp_series_summable_of_mem_ball' x hx)

theorem exp_series_field_summable_of_mem_ball [CompleteSpace 𝕂] (x : 𝕂)
    (hx : x ∈ Emetric.Ball (0 : 𝕂) (expSeries 𝕂 𝕂).radius) : Summable fun n => x ^ n / n ! :=
  summable_of_summable_norm (norm_exp_series_field_summable_of_mem_ball x hx)

theorem exp_series_has_sum_exp_of_mem_ball (x : 𝔸) (hx : x ∈ Emetric.Ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasSum (fun n => expSeries 𝕂 𝔸 n fun _ => x) (exp 𝕂 𝔸 x) :=
  FormalMultilinearSeries.has_sum (expSeries 𝕂 𝔸) hx

theorem exp_series_has_sum_exp_of_mem_ball' (x : 𝔸) (hx : x ∈ Emetric.Ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasSum (fun n => (1 / n ! : 𝕂) • x ^ n) (exp 𝕂 𝔸 x) := by
  rw [← exp_series_apply_eq']
  exact exp_series_has_sum_exp_of_mem_ball x hx

theorem exp_series_field_has_sum_exp_of_mem_ball [CompleteSpace 𝕂] (x : 𝕂)
    (hx : x ∈ Emetric.Ball (0 : 𝕂) (expSeries 𝕂 𝕂).radius) : HasSum (fun n => x ^ n / n !) (exp 𝕂 𝕂 x) := by
  rw [← exp_series_apply_eq_field']
  exact exp_series_has_sum_exp_of_mem_ball x hx

theorem has_fpower_series_on_ball_exp_of_radius_pos (h : 0 < (expSeries 𝕂 𝔸).radius) :
    HasFpowerSeriesOnBall (exp 𝕂 𝔸) (expSeries 𝕂 𝔸) 0 (expSeries 𝕂 𝔸).radius :=
  (expSeries 𝕂 𝔸).HasFpowerSeriesOnBall h

theorem has_fpower_series_at_exp_zero_of_radius_pos (h : 0 < (expSeries 𝕂 𝔸).radius) :
    HasFpowerSeriesAt (exp 𝕂 𝔸) (expSeries 𝕂 𝔸) 0 :=
  (has_fpower_series_on_ball_exp_of_radius_pos h).HasFpowerSeriesAt

theorem continuous_on_exp : ContinuousOn (exp 𝕂 𝔸) (Emetric.Ball 0 (expSeries 𝕂 𝔸).radius) :=
  FormalMultilinearSeries.continuous_on

theorem analytic_at_exp_of_mem_ball (x : 𝔸) (hx : x ∈ Emetric.Ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    AnalyticAt 𝕂 (exp 𝕂 𝔸) x := by
  by_cases' h : (expSeries 𝕂 𝔸).radius = 0
  · rw [h] at hx
    exact (Ennreal.not_lt_zero hx).elim
    
  · have h := pos_iff_ne_zero.mpr h
    exact (has_fpower_series_on_ball_exp_of_radius_pos h).analytic_at_of_mem hx
    

/-- In a Banach-algebra `𝔸` over a normed field `𝕂` of characteristic zero, if `x` and `y` are
in the disk of convergence and commute, then `exp 𝕂 𝔸 (x + y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`. -/
theorem exp_add_of_commute_of_mem_ball [CharZero 𝕂] {x y : 𝔸} (hxy : Commute x y)
    (hx : x ∈ Emetric.Ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) (hy : y ∈ Emetric.Ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    exp 𝕂 𝔸 (x + y) = exp 𝕂 𝔸 x * exp 𝕂 𝔸 y := by
  rw [exp_eq_tsum,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (norm_exp_series_summable_of_mem_ball' x hx)
      (norm_exp_series_summable_of_mem_ball' y hy)]
  dsimp only
  conv_lhs => congr ext rw [hxy.add_pow' _, Finset.smul_sum]
  refine' tsum_congr fun n => (Finset.sum_congr rfl) fun kl hkl => _
  rw [nsmul_eq_smul_cast 𝕂, smul_smul, smul_mul_smul, ← finset.nat.mem_antidiagonal.mp hkl, Nat.cast_add_choose,
    finset.nat.mem_antidiagonal.mp hkl]
  congr 1
  have : (n ! : 𝕂) ≠ 0 := nat.cast_ne_zero.mpr n.factorial_ne_zero
  field_simp [this]

end CompleteAlgebra

end AnyFieldAnyAlgebra

section AnyFieldCommAlgebra

variable {𝕂 𝔸 : Type _} [NondiscreteNormedField 𝕂] [NormedCommRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-- In a commutative Banach-algebra `𝔸` over a normed field `𝕂` of characteristic zero,
`exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)` for all `x`, `y` in the disk of convergence. -/
theorem exp_add_of_mem_ball [CharZero 𝕂] {x y : 𝔸} (hx : x ∈ Emetric.Ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius)
    (hy : y ∈ Emetric.Ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : exp 𝕂 𝔸 (x + y) = exp 𝕂 𝔸 x * exp 𝕂 𝔸 y :=
  exp_add_of_commute_of_mem_ball (Commute.all x y) hx hy

end AnyFieldCommAlgebra

section IsROrC

section AnyAlgebra

variable (𝕂 𝔸 : Type _) [IsROrC 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]

/-- In a normed algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, the series defining the exponential map
has an infinite radius of convergence. -/
theorem exp_series_radius_eq_top : (expSeries 𝕂 𝔸).radius = ∞ := by
  refine' (expSeries 𝕂 𝔸).radius_eq_top_of_summable_norm fun r => _
  refine' summable_of_norm_bounded_eventually _ (Real.summable_pow_div_factorial r) _
  filter_upwards [eventually_cofinite_ne 0] with n hn
  rw [norm_mul, norm_norm (expSeries 𝕂 𝔸 n), expSeries, norm_smul, norm_div, norm_one, norm_pow, Nnreal.norm_eq,
    norm_eq_abs, abs_cast_nat, mul_comm, ← mul_assoc, ← mul_div_assoc, mul_oneₓ]
  have : ∥ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 n 𝔸∥ ≤ 1 :=
    norm_mk_pi_algebra_fin_le_of_pos (Nat.pos_of_ne_zeroₓ hn)
  exact mul_le_of_le_one_right (div_nonneg (pow_nonneg r.coe_nonneg n) n !.cast_nonneg) this

theorem exp_series_radius_pos : 0 < (expSeries 𝕂 𝔸).radius := by
  rw [exp_series_radius_eq_top]
  exact WithTop.zero_lt_top

variable {𝕂 𝔸}

section CompleteAlgebra

theorem norm_exp_series_summable (x : 𝔸) : Summable fun n => ∥expSeries 𝕂 𝔸 n fun _ => x∥ :=
  norm_exp_series_summable_of_mem_ball x ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

theorem norm_exp_series_summable' (x : 𝔸) : Summable fun n => ∥(1 / n ! : 𝕂) • x ^ n∥ :=
  norm_exp_series_summable_of_mem_ball' x ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

theorem norm_exp_series_field_summable (x : 𝕂) : Summable fun n => ∥x ^ n / n !∥ :=
  norm_exp_series_field_summable_of_mem_ball x ((exp_series_radius_eq_top 𝕂 𝕂).symm ▸ edist_lt_top _ _)

variable [CompleteSpace 𝔸]

theorem exp_series_summable (x : 𝔸) : Summable fun n => expSeries 𝕂 𝔸 n fun _ => x :=
  summable_of_summable_norm (norm_exp_series_summable x)

theorem exp_series_summable' (x : 𝔸) : Summable fun n => (1 / n ! : 𝕂) • x ^ n :=
  summable_of_summable_norm (norm_exp_series_summable' x)

theorem exp_series_field_summable (x : 𝕂) : Summable fun n => x ^ n / n ! :=
  summable_of_summable_norm (norm_exp_series_field_summable x)

theorem exp_series_has_sum_exp (x : 𝔸) : HasSum (fun n => expSeries 𝕂 𝔸 n fun _ => x) (exp 𝕂 𝔸 x) :=
  exp_series_has_sum_exp_of_mem_ball x ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

theorem exp_series_has_sum_exp' (x : 𝔸) : HasSum (fun n => (1 / n ! : 𝕂) • x ^ n) (exp 𝕂 𝔸 x) :=
  exp_series_has_sum_exp_of_mem_ball' x ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

theorem exp_series_field_has_sum_exp (x : 𝕂) : HasSum (fun n => x ^ n / n !) (exp 𝕂 𝕂 x) :=
  exp_series_field_has_sum_exp_of_mem_ball x ((exp_series_radius_eq_top 𝕂 𝕂).symm ▸ edist_lt_top _ _)

theorem exp_has_fpower_series_on_ball : HasFpowerSeriesOnBall (exp 𝕂 𝔸) (expSeries 𝕂 𝔸) 0 ∞ :=
  exp_series_radius_eq_top 𝕂 𝔸 ▸ has_fpower_series_on_ball_exp_of_radius_pos (exp_series_radius_pos _ _)

theorem exp_has_fpower_series_at_zero : HasFpowerSeriesAt (exp 𝕂 𝔸) (expSeries 𝕂 𝔸) 0 :=
  exp_has_fpower_series_on_ball.HasFpowerSeriesAt

theorem exp_continuous : Continuous (exp 𝕂 𝔸) := by
  rw [continuous_iff_continuous_on_univ, ← Metric.eball_top_eq_univ (0 : 𝔸), ← exp_series_radius_eq_top 𝕂 𝔸]
  exact continuous_on_exp

theorem exp_analytic (x : 𝔸) : AnalyticAt 𝕂 (exp 𝕂 𝔸) x :=
  analytic_at_exp_of_mem_ball x ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

end CompleteAlgebra

/-- In a Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, if `x` and `y` commute, then
`exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`. -/
theorem exp_add_of_commute [CompleteSpace 𝔸] {x y : 𝔸} (hxy : Commute x y) : exp 𝕂 𝔸 (x + y) = exp 𝕂 𝔸 x * exp 𝕂 𝔸 y :=
  exp_add_of_commute_of_mem_ball hxy ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
    ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

end AnyAlgebra

section CommAlgebra

variable {𝕂 𝔸 : Type _} [IsROrC 𝕂] [NormedCommRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-- In a commutative Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`,
`exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`. -/
theorem exp_add {x y : 𝔸} : exp 𝕂 𝔸 (x + y) = exp 𝕂 𝔸 x * exp 𝕂 𝔸 y :=
  exp_add_of_mem_ball ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
    ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

end CommAlgebra

end IsROrC

section ScalarTower

variable (𝕂 𝕂' 𝔸 : Type _) [NondiscreteNormedField 𝕂] [NondiscreteNormedField 𝕂'] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  [NormedAlgebra 𝕂' 𝔸]

/-- If a normed ring `𝔸` is a normed algebra over two fields, then they define the same
`exp_series` on `𝔸`. -/
theorem exp_series_eq_exp_series (n : ℕ) (x : 𝔸) : (expSeries 𝕂 𝔸 n fun _ => x) = expSeries 𝕂' 𝔸 n fun _ => x := by
  rw [expSeries, expSeries, smul_apply, mk_pi_algebra_fin_apply, List.of_fn_const, List.prod_repeat, smul_apply,
    mk_pi_algebra_fin_apply, List.of_fn_const, List.prod_repeat, one_div, one_div, inv_nat_cast_smul_eq 𝕂 𝕂']

/-- If a normed ring `𝔸` is a normed algebra over two fields, then they define the same
exponential function on `𝔸`. -/
theorem exp_eq_exp : exp 𝕂 𝔸 = exp 𝕂' 𝔸 := by
  ext
  rw [exp, exp]
  refine' tsum_congr fun n => _
  rw [exp_series_eq_exp_series 𝕂 𝕂' 𝔸 n x]

theorem exp_ℝ_ℂ_eq_exp_ℂ_ℂ : exp ℝ ℂ = exp ℂ ℂ :=
  exp_eq_exp ℝ ℂ ℂ

end ScalarTower

