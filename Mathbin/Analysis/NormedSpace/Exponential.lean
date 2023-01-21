/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Eric Wieser

! This file was ported from Lean 3 source module analysis.normed_space.exponential
! leanprover-community/mathlib commit 2445c98ae4b87eabebdde552593519b9b6dc350c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Analytic.Basic
import Mathbin.Analysis.Complex.Basic
import Mathbin.Analysis.Normed.Field.InfiniteSum
import Mathbin.Data.Nat.Choose.Cast
import Mathbin.Data.Finset.NoncommProd
import Mathbin.Topology.Algebra.Algebra

/-!
# Exponential in a Banach algebra

In this file, we define `exp 𝕂 : 𝔸 → 𝔸`, the exponential map in a topological algebra `𝔸` over a
field `𝕂`.

While for most interesting results we need `𝔸` to be normed algebra, we do not require this in the
definition in order to make `exp` independent of a particular choice of norm. The definition also
does not require that `𝔸` be complete, but we need to assume it for most results.

We then prove some basic results, but we avoid importing derivatives here to minimize dependencies.
Results involving derivatives and comparisons with `real.exp` and `complex.exp` can be found in
`analysis/special_functions/exponential`.

## Main results

We prove most result for an arbitrary field `𝕂`, and then specialize to `𝕂 = ℝ` or `𝕂 = ℂ`.

### General case

- `exp_add_of_commute_of_mem_ball` : if `𝕂` has characteristic zero, then given two commuting
  elements `x` and `y` in the disk of convergence, we have
  `exp 𝕂 (x+y) = (exp 𝕂 x) * (exp 𝕂 y)`
- `exp_add_of_mem_ball` : if `𝕂` has characteristic zero and `𝔸` is commutative, then given two
  elements `x` and `y` in the disk of convergence, we have
  `exp 𝕂 (x+y) = (exp 𝕂 x) * (exp 𝕂 y)`
- `exp_neg_of_mem_ball` : if `𝕂` has characteristic zero and `𝔸` is a division ring, then given an
  element `x` in the disk of convergence, we have `exp 𝕂 (-x) = (exp 𝕂 x)⁻¹`.

### `𝕂 = ℝ` or `𝕂 = ℂ`

- `exp_series_radius_eq_top` : the `formal_multilinear_series` defining `exp 𝕂` has infinite
  radius of convergence
- `exp_add_of_commute` : given two commuting elements `x` and `y`, we have
  `exp 𝕂 (x+y) = (exp 𝕂 x) * (exp 𝕂 y)`
- `exp_add` : if `𝔸` is commutative, then we have `exp 𝕂 (x+y) = (exp 𝕂 x) * (exp 𝕂 y)`
  for any `x` and `y`
- `exp_neg` : if `𝔸` is a division ring, then we have `exp 𝕂 (-x) = (exp 𝕂 x)⁻¹`.
- `exp_sum_of_commute` : the analogous result to `exp_add_of_commute` for `finset.sum`.
- `exp_sum` : the analogous result to `exp_add` for `finset.sum`.
- `exp_nsmul` : repeated addition in the domain corresponds to repeated multiplication in the
  codomain.
- `exp_zsmul` : repeated addition in the domain corresponds to repeated multiplication in the
  codomain.

### Other useful compatibility results

- `exp_eq_exp` : if `𝔸` is a normed algebra over two fields `𝕂` and `𝕂'`, then `exp 𝕂 = exp 𝕂' 𝔸`

-/


open Filter IsROrC ContinuousMultilinearMap NormedField Asymptotics

open Nat TopologicalSpace BigOperators Ennreal

section TopologicalAlgebra

variable (𝕂 𝔸 : Type _) [Field 𝕂] [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [TopologicalRing 𝔸]

/-- `exp_series 𝕂 𝔸` is the `formal_multilinear_series` whose `n`-th term is the map
`(xᵢ) : 𝔸ⁿ ↦ (1/n! : 𝕂) • ∏ xᵢ`. Its sum is the exponential map `exp 𝕂 : 𝔸 → 𝔸`. -/
def expSeries : FormalMultilinearSeries 𝕂 𝔸 𝔸 := fun n =>
  (n !⁻¹ : 𝕂) • ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 n 𝔸
#align exp_series expSeries

variable {𝔸}

/-- `exp 𝕂 : 𝔸 → 𝔸` is the exponential map determined by the action of `𝕂` on `𝔸`.
It is defined as the sum of the `formal_multilinear_series` `exp_series 𝕂 𝔸`.

Note that when `𝔸 = matrix n n 𝕂`, this is the **Matrix Exponential**; see
[`analysis.normed_space.matrix_exponential`](../matrix_exponential) for lemmas specific to that
case. -/
noncomputable def exp (x : 𝔸) : 𝔸 :=
  (expSeries 𝕂 𝔸).Sum x
#align exp exp

variable {𝕂}

theorem expSeries_apply_eq (x : 𝔸) (n : ℕ) : (expSeries 𝕂 𝔸 n fun _ => x) = (n !⁻¹ : 𝕂) • x ^ n :=
  by simp [expSeries]
#align exp_series_apply_eq expSeries_apply_eq

theorem expSeries_apply_eq' (x : 𝔸) :
    (fun n => expSeries 𝕂 𝔸 n fun _ => x) = fun n => (n !⁻¹ : 𝕂) • x ^ n :=
  funext (expSeries_apply_eq x)
#align exp_series_apply_eq' expSeries_apply_eq'

theorem expSeries_sum_eq (x : 𝔸) : (expSeries 𝕂 𝔸).Sum x = ∑' n : ℕ, (n !⁻¹ : 𝕂) • x ^ n :=
  tsum_congr fun n => expSeries_apply_eq x n
#align exp_series_sum_eq expSeries_sum_eq

theorem exp_eq_tsum : exp 𝕂 = fun x : 𝔸 => ∑' n : ℕ, (n !⁻¹ : 𝕂) • x ^ n :=
  funext expSeries_sum_eq
#align exp_eq_tsum exp_eq_tsum

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (n «expr ∉ » ({0} : finset exprℕ())) -/
@[simp]
theorem exp_zero [T2Space 𝔸] : exp 𝕂 (0 : 𝔸) = 1 :=
  by
  suffices (fun x : 𝔸 => ∑' n : ℕ, (n !⁻¹ : 𝕂) • x ^ n) 0 = ∑' n : ℕ, if n = 0 then 1 else 0
    by
    have key : ∀ (n) (_ : n ∉ ({0} : Finset ℕ)), (if n = 0 then (1 : 𝔸) else 0) = 0 := fun n hn =>
      if_neg (finset.not_mem_singleton.mp hn)
    rw [exp_eq_tsum, this, tsum_eq_sum key, Finset.sum_singleton]
    simp
  refine' tsum_congr fun n => _
  split_ifs with h h <;> simp [h]
#align exp_zero exp_zero

@[simp]
theorem exp_op [T2Space 𝔸] (x : 𝔸) : exp 𝕂 (MulOpposite.op x) = MulOpposite.op (exp 𝕂 x) := by
  simp_rw [exp, expSeries_sum_eq, ← MulOpposite.op_pow, ← MulOpposite.op_smul, tsum_op]
#align exp_op exp_op

@[simp]
theorem exp_unop [T2Space 𝔸] (x : 𝔸ᵐᵒᵖ) : exp 𝕂 (MulOpposite.unop x) = MulOpposite.unop (exp 𝕂 x) :=
  by simp_rw [exp, expSeries_sum_eq, ← MulOpposite.unop_pow, ← MulOpposite.unop_smul, tsum_unop]
#align exp_unop exp_unop

theorem star_exp [T2Space 𝔸] [StarRing 𝔸] [HasContinuousStar 𝔸] (x : 𝔸) :
    star (exp 𝕂 x) = exp 𝕂 (star x) := by
  simp_rw [exp_eq_tsum, ← star_pow, ← star_inv_nat_cast_smul, ← tsum_star]
#align star_exp star_exp

variable (𝕂)

theorem Commute.exp_right [T2Space 𝔸] {x y : 𝔸} (h : Commute x y) : Commute x (exp 𝕂 y) :=
  by
  rw [exp_eq_tsum]
  exact Commute.tsum_right x fun n => (h.pow_right n).smul_right _
#align commute.exp_right Commute.exp_right

theorem Commute.exp_left [T2Space 𝔸] {x y : 𝔸} (h : Commute x y) : Commute (exp 𝕂 x) y :=
  (h.symm.exp_right 𝕂).symm
#align commute.exp_left Commute.exp_left

theorem Commute.exp [T2Space 𝔸] {x y : 𝔸} (h : Commute x y) : Commute (exp 𝕂 x) (exp 𝕂 y) :=
  (h.exp_left _).exp_right _
#align commute.exp Commute.exp

end TopologicalAlgebra

section TopologicalDivisionAlgebra

variable {𝕂 𝔸 : Type _} [Field 𝕂] [DivisionRing 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸]
  [TopologicalRing 𝔸]

theorem expSeries_apply_eq_div (x : 𝔸) (n : ℕ) : (expSeries 𝕂 𝔸 n fun _ => x) = x ^ n / n ! := by
  rw [div_eq_mul_inv, ← (Nat.cast_commute n ! (x ^ n)).inv_left₀.Eq, ← smul_eq_mul,
    expSeries_apply_eq, inv_nat_cast_smul_eq _ _ _ _]
#align exp_series_apply_eq_div expSeries_apply_eq_div

theorem expSeries_apply_eq_div' (x : 𝔸) :
    (fun n => expSeries 𝕂 𝔸 n fun _ => x) = fun n => x ^ n / n ! :=
  funext (expSeries_apply_eq_div x)
#align exp_series_apply_eq_div' expSeries_apply_eq_div'

theorem expSeries_sum_eq_div (x : 𝔸) : (expSeries 𝕂 𝔸).Sum x = ∑' n : ℕ, x ^ n / n ! :=
  tsum_congr (expSeries_apply_eq_div x)
#align exp_series_sum_eq_div expSeries_sum_eq_div

theorem exp_eq_tsum_div : exp 𝕂 = fun x : 𝔸 => ∑' n : ℕ, x ^ n / n ! :=
  funext expSeries_sum_eq_div
#align exp_eq_tsum_div exp_eq_tsum_div

end TopologicalDivisionAlgebra

section Normed

section AnyFieldAnyAlgebra

variable {𝕂 𝔸 𝔹 : Type _} [NontriviallyNormedField 𝕂]

variable [NormedRing 𝔸] [NormedRing 𝔹] [NormedAlgebra 𝕂 𝔸] [NormedAlgebra 𝕂 𝔹]

theorem norm_expSeries_summable_of_mem_ball (x : 𝔸)
    (hx : x ∈ Emetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => ‖expSeries 𝕂 𝔸 n fun _ => x‖ :=
  (expSeries 𝕂 𝔸).summable_norm_apply hx
#align norm_exp_series_summable_of_mem_ball norm_expSeries_summable_of_mem_ball

theorem norm_expSeries_summable_of_mem_ball' (x : 𝔸)
    (hx : x ∈ Emetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => ‖(n !⁻¹ : 𝕂) • x ^ n‖ :=
  by
  change Summable (norm ∘ _)
  rw [← expSeries_apply_eq']
  exact norm_expSeries_summable_of_mem_ball x hx
#align norm_exp_series_summable_of_mem_ball' norm_expSeries_summable_of_mem_ball'

section CompleteAlgebra

variable [CompleteSpace 𝔸]

theorem expSeries_summable_of_mem_ball (x : 𝔸)
    (hx : x ∈ Emetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => expSeries 𝕂 𝔸 n fun _ => x :=
  summable_of_summable_norm (norm_expSeries_summable_of_mem_ball x hx)
#align exp_series_summable_of_mem_ball expSeries_summable_of_mem_ball

theorem expSeries_summable_of_mem_ball' (x : 𝔸)
    (hx : x ∈ Emetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => (n !⁻¹ : 𝕂) • x ^ n :=
  summable_of_summable_norm (norm_expSeries_summable_of_mem_ball' x hx)
#align exp_series_summable_of_mem_ball' expSeries_summable_of_mem_ball'

theorem expSeries_hasSum_exp_of_mem_ball (x : 𝔸)
    (hx : x ∈ Emetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasSum (fun n => expSeries 𝕂 𝔸 n fun _ => x) (exp 𝕂 x) :=
  FormalMultilinearSeries.hasSum (expSeries 𝕂 𝔸) hx
#align exp_series_has_sum_exp_of_mem_ball expSeries_hasSum_exp_of_mem_ball

theorem expSeries_hasSum_exp_of_mem_ball' (x : 𝔸)
    (hx : x ∈ Emetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasSum (fun n => (n !⁻¹ : 𝕂) • x ^ n) (exp 𝕂 x) :=
  by
  rw [← expSeries_apply_eq']
  exact expSeries_hasSum_exp_of_mem_ball x hx
#align exp_series_has_sum_exp_of_mem_ball' expSeries_hasSum_exp_of_mem_ball'

theorem hasFpowerSeriesOnBallExpOfRadiusPos (h : 0 < (expSeries 𝕂 𝔸).radius) :
    HasFpowerSeriesOnBall (exp 𝕂) (expSeries 𝕂 𝔸) 0 (expSeries 𝕂 𝔸).radius :=
  (expSeries 𝕂 𝔸).HasFpowerSeriesOnBall h
#align has_fpower_series_on_ball_exp_of_radius_pos hasFpowerSeriesOnBallExpOfRadiusPos

theorem hasFpowerSeriesAtExpZeroOfRadiusPos (h : 0 < (expSeries 𝕂 𝔸).radius) :
    HasFpowerSeriesAt (exp 𝕂) (expSeries 𝕂 𝔸) 0 :=
  (hasFpowerSeriesOnBallExpOfRadiusPos h).HasFpowerSeriesAt
#align has_fpower_series_at_exp_zero_of_radius_pos hasFpowerSeriesAtExpZeroOfRadiusPos

theorem continuousOn_exp : ContinuousOn (exp 𝕂 : 𝔸 → 𝔸) (Emetric.ball 0 (expSeries 𝕂 𝔸).radius) :=
  FormalMultilinearSeries.continuousOn
#align continuous_on_exp continuousOn_exp

theorem analyticAt_exp_of_mem_ball (x : 𝔸) (hx : x ∈ Emetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    AnalyticAt 𝕂 (exp 𝕂) x := by
  by_cases h : (expSeries 𝕂 𝔸).radius = 0
  · rw [h] at hx
    exact (Ennreal.not_lt_zero hx).elim
  · have h := pos_iff_ne_zero.mpr h
    exact (hasFpowerSeriesOnBallExpOfRadiusPos h).analytic_at_of_mem hx
#align analytic_at_exp_of_mem_ball analyticAt_exp_of_mem_ball

/-- In a Banach-algebra `𝔸` over a normed field `𝕂` of characteristic zero, if `x` and `y` are
in the disk of convergence and commute, then `exp 𝕂 (x + y) = (exp 𝕂 x) * (exp 𝕂 y)`. -/
theorem exp_add_of_commute_of_mem_ball [CharZero 𝕂] {x y : 𝔸} (hxy : Commute x y)
    (hx : x ∈ Emetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius)
    (hy : y ∈ Emetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : exp 𝕂 (x + y) = exp 𝕂 x * exp 𝕂 y :=
  by
  rw [exp_eq_tsum,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
      (norm_expSeries_summable_of_mem_ball' x hx) (norm_expSeries_summable_of_mem_ball' y hy)]
  dsimp only
  conv_lhs =>
    congr
    ext
    rw [hxy.add_pow' _, Finset.smul_sum]
  refine' tsum_congr fun n => Finset.sum_congr rfl fun kl hkl => _
  rw [nsmul_eq_smul_cast 𝕂, smul_smul, smul_mul_smul, ← finset.nat.mem_antidiagonal.mp hkl,
    Nat.cast_add_choose, finset.nat.mem_antidiagonal.mp hkl]
  congr 1
  have : (n ! : 𝕂) ≠ 0 := nat.cast_ne_zero.mpr n.factorial_ne_zero
  field_simp [this]
#align exp_add_of_commute_of_mem_ball exp_add_of_commute_of_mem_ball

/-- `exp 𝕂 x` has explicit two-sided inverse `exp 𝕂 (-x)`. -/
noncomputable def invertibleExpOfMemBall [CharZero 𝕂] {x : 𝔸}
    (hx : x ∈ Emetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : Invertible (exp 𝕂 x)
    where
  invOf := exp 𝕂 (-x)
  inv_of_mul_self :=
    by
    have hnx : -x ∈ Emetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius :=
      by
      rw [Emetric.mem_ball, ← neg_zero, edist_neg_neg]
      exact hx
    rw [← exp_add_of_commute_of_mem_ball (Commute.neg_left <| Commute.refl x) hnx hx, neg_add_self,
      exp_zero]
  mul_inv_of_self :=
    by
    have hnx : -x ∈ Emetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius :=
      by
      rw [Emetric.mem_ball, ← neg_zero, edist_neg_neg]
      exact hx
    rw [← exp_add_of_commute_of_mem_ball (Commute.neg_right <| Commute.refl x) hx hnx, add_neg_self,
      exp_zero]
#align invertible_exp_of_mem_ball invertibleExpOfMemBall

theorem isUnit_exp_of_mem_ball [CharZero 𝕂] {x : 𝔸}
    (hx : x ∈ Emetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : IsUnit (exp 𝕂 x) :=
  @isUnit_of_invertible _ _ _ (invertibleExpOfMemBall hx)
#align is_unit_exp_of_mem_ball isUnit_exp_of_mem_ball

theorem invOf_exp_of_mem_ball [CharZero 𝕂] {x : 𝔸}
    (hx : x ∈ Emetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) [Invertible (exp 𝕂 x)] :
    ⅟ (exp 𝕂 x) = exp 𝕂 (-x) := by
  letI := invertibleExpOfMemBall hx
  convert (rfl : ⅟ (exp 𝕂 x) = _)
#align inv_of_exp_of_mem_ball invOf_exp_of_mem_ball

/-- Any continuous ring homomorphism commutes with `exp`. -/
theorem map_exp_of_mem_ball {F} [RingHomClass F 𝔸 𝔹] (f : F) (hf : Continuous f) (x : 𝔸)
    (hx : x ∈ Emetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : f (exp 𝕂 x) = exp 𝕂 (f x) :=
  by
  rw [exp_eq_tsum, exp_eq_tsum]
  refine' ((expSeries_summable_of_mem_ball' _ hx).HasSum.map f hf).tsum_eq.symm.trans _
  dsimp only [Function.comp]
  simp_rw [one_div, map_inv_nat_cast_smul f 𝕂 𝕂, map_pow]
#align map_exp_of_mem_ball map_exp_of_mem_ball

end CompleteAlgebra

theorem algebraMap_exp_comm_of_mem_ball [CompleteSpace 𝕂] (x : 𝕂)
    (hx : x ∈ Emetric.ball (0 : 𝕂) (expSeries 𝕂 𝕂).radius) :
    algebraMap 𝕂 𝔸 (exp 𝕂 x) = exp 𝕂 (algebraMap 𝕂 𝔸 x) :=
  map_exp_of_mem_ball _ (continuous_algebraMap 𝕂 𝔸) _ hx
#align algebra_map_exp_comm_of_mem_ball algebraMap_exp_comm_of_mem_ball

end AnyFieldAnyAlgebra

section AnyFieldDivisionAlgebra

variable {𝕂 𝔸 : Type _} [NontriviallyNormedField 𝕂] [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸]

variable (𝕂)

theorem norm_expSeries_div_summable_of_mem_ball (x : 𝔸)
    (hx : x ∈ Emetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : Summable fun n => ‖x ^ n / n !‖ :=
  by
  change Summable (norm ∘ _)
  rw [← expSeries_apply_eq_div' x]
  exact norm_expSeries_summable_of_mem_ball x hx
#align norm_exp_series_div_summable_of_mem_ball norm_expSeries_div_summable_of_mem_ball

theorem expSeries_div_summable_of_mem_ball [CompleteSpace 𝔸] (x : 𝔸)
    (hx : x ∈ Emetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : Summable fun n => x ^ n / n ! :=
  summable_of_summable_norm (norm_expSeries_div_summable_of_mem_ball 𝕂 x hx)
#align exp_series_div_summable_of_mem_ball expSeries_div_summable_of_mem_ball

theorem expSeries_div_hasSum_exp_of_mem_ball [CompleteSpace 𝔸] (x : 𝔸)
    (hx : x ∈ Emetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasSum (fun n => x ^ n / n !) (exp 𝕂 x) :=
  by
  rw [← expSeries_apply_eq_div' x]
  exact expSeries_hasSum_exp_of_mem_ball x hx
#align exp_series_div_has_sum_exp_of_mem_ball expSeries_div_hasSum_exp_of_mem_ball

variable {𝕂}

theorem exp_neg_of_mem_ball [CharZero 𝕂] [CompleteSpace 𝔸] {x : 𝔸}
    (hx : x ∈ Emetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : exp 𝕂 (-x) = (exp 𝕂 x)⁻¹ :=
  letI := invertibleExpOfMemBall hx
  invOf_eq_inv (exp 𝕂 x)
#align exp_neg_of_mem_ball exp_neg_of_mem_ball

end AnyFieldDivisionAlgebra

section AnyFieldCommAlgebra

variable {𝕂 𝔸 : Type _} [NontriviallyNormedField 𝕂] [NormedCommRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  [CompleteSpace 𝔸]

/-- In a commutative Banach-algebra `𝔸` over a normed field `𝕂` of characteristic zero,
`exp 𝕂 (x+y) = (exp 𝕂 x) * (exp 𝕂 y)` for all `x`, `y` in the disk of convergence. -/
theorem exp_add_of_mem_ball [CharZero 𝕂] {x y : 𝔸}
    (hx : x ∈ Emetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius)
    (hy : y ∈ Emetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : exp 𝕂 (x + y) = exp 𝕂 x * exp 𝕂 y :=
  exp_add_of_commute_of_mem_ball (Commute.all x y) hx hy
#align exp_add_of_mem_ball exp_add_of_mem_ball

end AnyFieldCommAlgebra

section IsROrC

section AnyAlgebra

variable (𝕂 𝔸 𝔹 : Type _) [IsROrC 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]

variable [NormedRing 𝔹] [NormedAlgebra 𝕂 𝔹]

/-- In a normed algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, the series defining the exponential map
has an infinite radius of convergence. -/
theorem expSeries_radius_eq_top : (expSeries 𝕂 𝔸).radius = ∞ :=
  by
  refine' (expSeries 𝕂 𝔸).radius_eq_top_of_summable_norm fun r => _
  refine' summable_of_norm_bounded_eventually _ (Real.summable_pow_div_factorial r) _
  filter_upwards [eventually_cofinite_ne 0] with n hn
  rw [norm_mul, norm_norm (expSeries 𝕂 𝔸 n), expSeries, norm_smul, norm_inv, norm_pow,
    Nnreal.norm_eq, norm_eq_abs, abs_cast_nat, mul_comm, ← mul_assoc, ← div_eq_mul_inv]
  have : ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 n 𝔸‖ ≤ 1 :=
    norm_mk_pi_algebra_fin_le_of_pos (Nat.pos_of_ne_zero hn)
  exact mul_le_of_le_one_right (div_nonneg (pow_nonneg r.coe_nonneg n) n !.cast_nonneg) this
#align exp_series_radius_eq_top expSeries_radius_eq_top

theorem expSeries_radius_pos : 0 < (expSeries 𝕂 𝔸).radius :=
  by
  rw [expSeries_radius_eq_top]
  exact WithTop.zero_lt_top
#align exp_series_radius_pos expSeries_radius_pos

variable {𝕂 𝔸 𝔹}

theorem norm_expSeries_summable (x : 𝔸) : Summable fun n => ‖expSeries 𝕂 𝔸 n fun _ => x‖ :=
  norm_expSeries_summable_of_mem_ball x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
#align norm_exp_series_summable norm_expSeries_summable

theorem norm_exp_series_summable' (x : 𝔸) : Summable fun n => ‖(n !⁻¹ : 𝕂) • x ^ n‖ :=
  norm_expSeries_summable_of_mem_ball' x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
#align norm_exp_series_summable' norm_exp_series_summable'

section CompleteAlgebra

variable [CompleteSpace 𝔸]

theorem expSeries_summable (x : 𝔸) : Summable fun n => expSeries 𝕂 𝔸 n fun _ => x :=
  summable_of_summable_norm (norm_expSeries_summable x)
#align exp_series_summable expSeries_summable

theorem exp_series_summable' (x : 𝔸) : Summable fun n => (n !⁻¹ : 𝕂) • x ^ n :=
  summable_of_summable_norm (norm_exp_series_summable' x)
#align exp_series_summable' exp_series_summable'

theorem expSeries_hasSum_exp (x : 𝔸) : HasSum (fun n => expSeries 𝕂 𝔸 n fun _ => x) (exp 𝕂 x) :=
  expSeries_hasSum_exp_of_mem_ball x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
#align exp_series_has_sum_exp expSeries_hasSum_exp

theorem exp_series_hasSum_exp' (x : 𝔸) : HasSum (fun n => (n !⁻¹ : 𝕂) • x ^ n) (exp 𝕂 x) :=
  expSeries_hasSum_exp_of_mem_ball' x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
#align exp_series_has_sum_exp' exp_series_hasSum_exp'

theorem expHasFpowerSeriesOnBall : HasFpowerSeriesOnBall (exp 𝕂) (expSeries 𝕂 𝔸) 0 ∞ :=
  expSeries_radius_eq_top 𝕂 𝔸 ▸ hasFpowerSeriesOnBallExpOfRadiusPos (expSeries_radius_pos _ _)
#align exp_has_fpower_series_on_ball expHasFpowerSeriesOnBall

theorem expHasFpowerSeriesAtZero : HasFpowerSeriesAt (exp 𝕂) (expSeries 𝕂 𝔸) 0 :=
  expHasFpowerSeriesOnBall.HasFpowerSeriesAt
#align exp_has_fpower_series_at_zero expHasFpowerSeriesAtZero

theorem exp_continuous : Continuous (exp 𝕂 : 𝔸 → 𝔸) :=
  by
  rw [continuous_iff_continuousOn_univ, ← Metric.eball_top_eq_univ (0 : 𝔸), ←
    expSeries_radius_eq_top 𝕂 𝔸]
  exact continuousOn_exp
#align exp_continuous exp_continuous

theorem exp_analytic (x : 𝔸) : AnalyticAt 𝕂 (exp 𝕂) x :=
  analyticAt_exp_of_mem_ball x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
#align exp_analytic exp_analytic

/-- In a Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, if `x` and `y` commute, then
`exp 𝕂 (x+y) = (exp 𝕂 x) * (exp 𝕂 y)`. -/
theorem exp_add_of_commute {x y : 𝔸} (hxy : Commute x y) : exp 𝕂 (x + y) = exp 𝕂 x * exp 𝕂 y :=
  exp_add_of_commute_of_mem_ball hxy ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
#align exp_add_of_commute exp_add_of_commute

section

variable (𝕂)

/-- `exp 𝕂 x` has explicit two-sided inverse `exp 𝕂 (-x)`. -/
noncomputable def invertibleExp (x : 𝔸) : Invertible (exp 𝕂 x) :=
  invertibleExpOfMemBall <| (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _
#align invertible_exp invertibleExp

theorem isUnit_exp (x : 𝔸) : IsUnit (exp 𝕂 x) :=
  isUnit_exp_of_mem_ball <| (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _
#align is_unit_exp isUnit_exp

theorem invOf_exp (x : 𝔸) [Invertible (exp 𝕂 x)] : ⅟ (exp 𝕂 x) = exp 𝕂 (-x) :=
  invOf_exp_of_mem_ball <| (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _
#align inv_of_exp invOf_exp

theorem Ring.inverse_exp (x : 𝔸) : Ring.inverse (exp 𝕂 x) = exp 𝕂 (-x) :=
  letI := invertibleExp 𝕂 x
  Ring.inverse_invertible _
#align ring.inverse_exp Ring.inverse_exp

end

/-- In a Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, if a family of elements `f i` mutually
commute then `exp 𝕂 (∑ i, f i) = ∏ i, exp 𝕂 (f i)`. -/
theorem exp_sum_of_commute {ι} (s : Finset ι) (f : ι → 𝔸)
    (h : (s : Set ι).Pairwise fun i j => Commute (f i) (f j)) :
    exp 𝕂 (∑ i in s, f i) =
      s.noncommProd (fun i => exp 𝕂 (f i)) fun i hi j hj _ => (h.of_refl hi hj).exp 𝕂 :=
  by
  classical
    induction' s using Finset.induction_on with a s ha ih
    · simp
    rw [Finset.noncommProd_insert_of_not_mem _ _ _ _ ha, Finset.sum_insert ha, exp_add_of_commute,
      ih (h.mono <| Finset.subset_insert _ _)]
    refine' Commute.sum_right _ _ _ fun i hi => _
    exact h.of_refl (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hi)
#align exp_sum_of_commute exp_sum_of_commute

theorem exp_nsmul (n : ℕ) (x : 𝔸) : exp 𝕂 (n • x) = exp 𝕂 x ^ n :=
  by
  induction' n with n ih
  · rw [zero_smul, pow_zero, exp_zero]
  · rw [succ_nsmul, pow_succ, exp_add_of_commute ((Commute.refl x).smul_right n), ih]
#align exp_nsmul exp_nsmul

variable (𝕂)

/-- Any continuous ring homomorphism commutes with `exp`. -/
theorem map_exp {F} [RingHomClass F 𝔸 𝔹] (f : F) (hf : Continuous f) (x : 𝔸) :
    f (exp 𝕂 x) = exp 𝕂 (f x) :=
  map_exp_of_mem_ball f hf x <| (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _
#align map_exp map_exp

theorem exp_smul {G} [Monoid G] [MulSemiringAction G 𝔸] [HasContinuousConstSmul G 𝔸] (g : G)
    (x : 𝔸) : exp 𝕂 (g • x) = g • exp 𝕂 x :=
  (map_exp 𝕂 (MulSemiringAction.toRingHom G 𝔸 g) (continuous_const_smul _) x).symm
#align exp_smul exp_smul

theorem exp_units_conj (y : 𝔸ˣ) (x : 𝔸) : exp 𝕂 (y * x * ↑y⁻¹ : 𝔸) = y * exp 𝕂 x * ↑y⁻¹ :=
  exp_smul _ (ConjAct.toConjAct y) x
#align exp_units_conj exp_units_conj

theorem exp_units_conj' (y : 𝔸ˣ) (x : 𝔸) : exp 𝕂 (↑y⁻¹ * x * y) = ↑y⁻¹ * exp 𝕂 x * y :=
  exp_units_conj _ _ _
#align exp_units_conj' exp_units_conj'

@[simp]
theorem Prod.fst_exp [CompleteSpace 𝔹] (x : 𝔸 × 𝔹) : (exp 𝕂 x).fst = exp 𝕂 x.fst :=
  map_exp _ (RingHom.fst 𝔸 𝔹) continuous_fst x
#align prod.fst_exp Prod.fst_exp

@[simp]
theorem Prod.snd_exp [CompleteSpace 𝔹] (x : 𝔸 × 𝔹) : (exp 𝕂 x).snd = exp 𝕂 x.snd :=
  map_exp _ (RingHom.snd 𝔸 𝔹) continuous_snd x
#align prod.snd_exp Prod.snd_exp

@[simp]
theorem Pi.exp_apply {ι : Type _} {𝔸 : ι → Type _} [Fintype ι] [∀ i, NormedRing (𝔸 i)]
    [∀ i, NormedAlgebra 𝕂 (𝔸 i)] [∀ i, CompleteSpace (𝔸 i)] (x : ∀ i, 𝔸 i) (i : ι) :
    exp 𝕂 x i = exp 𝕂 (x i) :=
  letI-- Lean struggles to infer this instance due to it wanting `[Π i, semi_normed_ring (𝔸 i)]`
   : NormedAlgebra 𝕂 (∀ i, 𝔸 i) := Pi.normedAlgebra _
  map_exp _ (Pi.evalRingHom 𝔸 i) (continuous_apply _) x
#align pi.exp_apply Pi.exp_apply

theorem Pi.exp_def {ι : Type _} {𝔸 : ι → Type _} [Fintype ι] [∀ i, NormedRing (𝔸 i)]
    [∀ i, NormedAlgebra 𝕂 (𝔸 i)] [∀ i, CompleteSpace (𝔸 i)] (x : ∀ i, 𝔸 i) :
    exp 𝕂 x = fun i => exp 𝕂 (x i) :=
  funext <| Pi.exp_apply 𝕂 x
#align pi.exp_def Pi.exp_def

theorem Function.update_exp {ι : Type _} {𝔸 : ι → Type _} [Fintype ι] [DecidableEq ι]
    [∀ i, NormedRing (𝔸 i)] [∀ i, NormedAlgebra 𝕂 (𝔸 i)] [∀ i, CompleteSpace (𝔸 i)] (x : ∀ i, 𝔸 i)
    (j : ι) (xj : 𝔸 j) : Function.update (exp 𝕂 x) j (exp 𝕂 xj) = exp 𝕂 (Function.update x j xj) :=
  by
  ext i
  simp_rw [Pi.exp_def]
  exact (Function.apply_update (fun i => exp 𝕂) x j xj i).symm
#align function.update_exp Function.update_exp

end CompleteAlgebra

theorem algebraMap_exp_comm (x : 𝕂) : algebraMap 𝕂 𝔸 (exp 𝕂 x) = exp 𝕂 (algebraMap 𝕂 𝔸 x) :=
  algebraMap_exp_comm_of_mem_ball x <| (expSeries_radius_eq_top 𝕂 𝕂).symm ▸ edist_lt_top _ _
#align algebra_map_exp_comm algebraMap_exp_comm

end AnyAlgebra

section DivisionAlgebra

variable {𝕂 𝔸 : Type _} [IsROrC 𝕂] [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸]

variable (𝕂)

theorem norm_exp_series_div_summable (x : 𝔸) : Summable fun n => ‖x ^ n / n !‖ :=
  norm_expSeries_div_summable_of_mem_ball 𝕂 x
    ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
#align norm_exp_series_div_summable norm_exp_series_div_summable

variable [CompleteSpace 𝔸]

theorem exp_series_div_summable (x : 𝔸) : Summable fun n => x ^ n / n ! :=
  summable_of_summable_norm (norm_exp_series_div_summable 𝕂 x)
#align exp_series_div_summable exp_series_div_summable

theorem exp_series_div_hasSum_exp (x : 𝔸) : HasSum (fun n => x ^ n / n !) (exp 𝕂 x) :=
  expSeries_div_hasSum_exp_of_mem_ball 𝕂 x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
#align exp_series_div_has_sum_exp exp_series_div_hasSum_exp

variable {𝕂}

theorem exp_neg (x : 𝔸) : exp 𝕂 (-x) = (exp 𝕂 x)⁻¹ :=
  exp_neg_of_mem_ball <| (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _
#align exp_neg exp_neg

theorem exp_zsmul (z : ℤ) (x : 𝔸) : exp 𝕂 (z • x) = exp 𝕂 x ^ z :=
  by
  obtain ⟨n, rfl | rfl⟩ := z.eq_coe_or_neg
  · rw [zpow_ofNat, coe_nat_zsmul, exp_nsmul]
  · rw [zpow_neg, zpow_ofNat, neg_smul, exp_neg, coe_nat_zsmul, exp_nsmul]
#align exp_zsmul exp_zsmul

theorem exp_conj (y : 𝔸) (x : 𝔸) (hy : y ≠ 0) : exp 𝕂 (y * x * y⁻¹) = y * exp 𝕂 x * y⁻¹ :=
  exp_units_conj _ (Units.mk0 y hy) x
#align exp_conj exp_conj

theorem exp_conj' (y : 𝔸) (x : 𝔸) (hy : y ≠ 0) : exp 𝕂 (y⁻¹ * x * y) = y⁻¹ * exp 𝕂 x * y :=
  exp_units_conj' _ (Units.mk0 y hy) x
#align exp_conj' exp_conj'

end DivisionAlgebra

section CommAlgebra

variable {𝕂 𝔸 : Type _} [IsROrC 𝕂] [NormedCommRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-- In a commutative Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`,
`exp 𝕂 (x+y) = (exp 𝕂 x) * (exp 𝕂 y)`. -/
theorem exp_add {x y : 𝔸} : exp 𝕂 (x + y) = exp 𝕂 x * exp 𝕂 y :=
  exp_add_of_mem_ball ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
#align exp_add exp_add

/-- A version of `exp_sum_of_commute` for a commutative Banach-algebra. -/
theorem exp_sum {ι} (s : Finset ι) (f : ι → 𝔸) : exp 𝕂 (∑ i in s, f i) = ∏ i in s, exp 𝕂 (f i) :=
  by
  rw [exp_sum_of_commute, Finset.noncommProd_eq_prod]
  exact fun i hi j hj _ => Commute.all _ _
#align exp_sum exp_sum

end CommAlgebra

end IsROrC

end Normed

section ScalarTower

variable (𝕂 𝕂' 𝔸 : Type _) [Field 𝕂] [Field 𝕂'] [Ring 𝔸] [Algebra 𝕂 𝔸] [Algebra 𝕂' 𝔸]
  [TopologicalSpace 𝔸] [TopologicalRing 𝔸]

/-- If a normed ring `𝔸` is a normed algebra over two fields, then they define the same
`exp_series` on `𝔸`. -/
theorem expSeries_eq_expSeries (n : ℕ) (x : 𝔸) :
    (expSeries 𝕂 𝔸 n fun _ => x) = expSeries 𝕂' 𝔸 n fun _ => x := by
  rw [expSeries_apply_eq, expSeries_apply_eq, inv_nat_cast_smul_eq 𝕂 𝕂']
#align exp_series_eq_exp_series expSeries_eq_expSeries

/-- If a normed ring `𝔸` is a normed algebra over two fields, then they define the same
exponential function on `𝔸`. -/
theorem exp_eq_exp : (exp 𝕂 : 𝔸 → 𝔸) = exp 𝕂' :=
  by
  ext
  rw [exp, exp]
  refine' tsum_congr fun n => _
  rw [expSeries_eq_expSeries 𝕂 𝕂' 𝔸 n x]
#align exp_eq_exp exp_eq_exp

theorem exp_ℝ_ℂ_eq_exp_ℂ_ℂ : (exp ℝ : ℂ → ℂ) = exp ℂ :=
  exp_eq_exp ℝ ℂ ℂ
#align exp_ℝ_ℂ_eq_exp_ℂ_ℂ exp_ℝ_ℂ_eq_exp_ℂ_ℂ

end ScalarTower

