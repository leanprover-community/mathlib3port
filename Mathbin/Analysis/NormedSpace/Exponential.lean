/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Eric Wieser
-/
import Analysis.Analytic.Basic
import Analysis.Complex.Basic
import Analysis.Normed.Field.InfiniteSum
import Data.Nat.Choose.Cast
import Data.Finset.NoncommProd
import Topology.Algebra.Algebra

#align_import analysis.normed_space.exponential from "leanprover-community/mathlib"@"af471b9e3ce868f296626d33189b4ce730fa4c00"

/-!
# Exponential in a Banach algebra

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

open scoped Nat Topology BigOperators ENNReal

section TopologicalAlgebra

variable (𝕂 𝔸 : Type _) [Field 𝕂] [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [TopologicalRing 𝔸]

#print NormedSpace.expSeries /-
/-- `exp_series 𝕂 𝔸` is the `formal_multilinear_series` whose `n`-th term is the map
`(xᵢ) : 𝔸ⁿ ↦ (1/n! : 𝕂) • ∏ xᵢ`. Its sum is the exponential map `exp 𝕂 : 𝔸 → 𝔸`. -/
def NormedSpace.expSeries : FormalMultilinearSeries 𝕂 𝔸 𝔸 := fun n =>
  (n !⁻¹ : 𝕂) • ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 n 𝔸
#align exp_series NormedSpace.expSeries
-/

variable {𝔸}

#print NormedSpace.exp /-
/-- `exp 𝕂 : 𝔸 → 𝔸` is the exponential map determined by the action of `𝕂` on `𝔸`.
It is defined as the sum of the `formal_multilinear_series` `exp_series 𝕂 𝔸`.

Note that when `𝔸 = matrix n n 𝕂`, this is the **Matrix Exponential**; see
[`analysis.normed_space.matrix_exponential`](../matrix_exponential) for lemmas specific to that
case. -/
noncomputable def NormedSpace.exp (x : 𝔸) : 𝔸 :=
  (NormedSpace.expSeries 𝕂 𝔸).Sum x
#align exp NormedSpace.exp
-/

variable {𝕂}

#print NormedSpace.expSeries_apply_eq /-
theorem NormedSpace.expSeries_apply_eq (x : 𝔸) (n : ℕ) :
    (NormedSpace.expSeries 𝕂 𝔸 n fun _ => x) = (n !⁻¹ : 𝕂) • x ^ n := by
  simp [NormedSpace.expSeries]
#align exp_series_apply_eq NormedSpace.expSeries_apply_eq
-/

#print NormedSpace.expSeries_apply_eq' /-
theorem NormedSpace.expSeries_apply_eq' (x : 𝔸) :
    (fun n => NormedSpace.expSeries 𝕂 𝔸 n fun _ => x) = fun n => (n !⁻¹ : 𝕂) • x ^ n :=
  funext (NormedSpace.expSeries_apply_eq x)
#align exp_series_apply_eq' NormedSpace.expSeries_apply_eq'
-/

#print NormedSpace.expSeries_sum_eq /-
theorem NormedSpace.expSeries_sum_eq (x : 𝔸) :
    (NormedSpace.expSeries 𝕂 𝔸).Sum x = ∑' n : ℕ, (n !⁻¹ : 𝕂) • x ^ n :=
  tsum_congr fun n => NormedSpace.expSeries_apply_eq x n
#align exp_series_sum_eq NormedSpace.expSeries_sum_eq
-/

#print NormedSpace.exp_eq_tsum /-
theorem NormedSpace.exp_eq_tsum : NormedSpace.exp 𝕂 = fun x : 𝔸 => ∑' n : ℕ, (n !⁻¹ : 𝕂) • x ^ n :=
  funext NormedSpace.expSeries_sum_eq
#align exp_eq_tsum NormedSpace.exp_eq_tsum
-/

#print NormedSpace.expSeries_apply_zero /-
theorem NormedSpace.expSeries_apply_zero (n : ℕ) :
    (NormedSpace.expSeries 𝕂 𝔸 n fun _ => (0 : 𝔸)) = Pi.single 0 1 n :=
  by
  rw [NormedSpace.expSeries_apply_eq]
  cases n
  · rw [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, Pi.single_eq_same]
  · rw [zero_pow (Nat.succ_pos _), smul_zero, Pi.single_eq_of_ne n.succ_ne_zero]
#align exp_series_apply_zero NormedSpace.expSeries_apply_zero
-/

#print NormedSpace.exp_zero /-
@[simp]
theorem NormedSpace.exp_zero [T2Space 𝔸] : NormedSpace.exp 𝕂 (0 : 𝔸) = 1 := by
  simp_rw [NormedSpace.exp_eq_tsum, ← NormedSpace.expSeries_apply_eq,
    NormedSpace.expSeries_apply_zero, tsum_pi_single]
#align exp_zero NormedSpace.exp_zero
-/

#print NormedSpace.exp_op /-
@[simp]
theorem NormedSpace.exp_op [T2Space 𝔸] (x : 𝔸) :
    NormedSpace.exp 𝕂 (MulOpposite.op x) = MulOpposite.op (NormedSpace.exp 𝕂 x) := by
  simp_rw [NormedSpace.exp, NormedSpace.expSeries_sum_eq, ← MulOpposite.op_pow, ←
    MulOpposite.op_smul, tsum_op]
#align exp_op NormedSpace.exp_op
-/

#print NormedSpace.exp_unop /-
@[simp]
theorem NormedSpace.exp_unop [T2Space 𝔸] (x : 𝔸ᵐᵒᵖ) :
    NormedSpace.exp 𝕂 (MulOpposite.unop x) = MulOpposite.unop (NormedSpace.exp 𝕂 x) := by
  simp_rw [NormedSpace.exp, NormedSpace.expSeries_sum_eq, ← MulOpposite.unop_pow, ←
    MulOpposite.unop_smul, tsum_unop]
#align exp_unop NormedSpace.exp_unop
-/

#print NormedSpace.star_exp /-
theorem NormedSpace.star_exp [T2Space 𝔸] [StarRing 𝔸] [ContinuousStar 𝔸] (x : 𝔸) :
    star (NormedSpace.exp 𝕂 x) = NormedSpace.exp 𝕂 (star x) := by
  simp_rw [NormedSpace.exp_eq_tsum, ← star_pow, ← star_inv_nat_cast_smul, ← tsum_star]
#align star_exp NormedSpace.star_exp
-/

variable (𝕂)

#print IsSelfAdjoint.exp /-
theorem IsSelfAdjoint.exp [T2Space 𝔸] [StarRing 𝔸] [ContinuousStar 𝔸] {x : 𝔸}
    (h : IsSelfAdjoint x) : IsSelfAdjoint (NormedSpace.exp 𝕂 x) :=
  (NormedSpace.star_exp x).trans <| h.symm ▸ rfl
#align is_self_adjoint.exp IsSelfAdjoint.exp
-/

#print Commute.exp_right /-
theorem Commute.exp_right [T2Space 𝔸] {x y : 𝔸} (h : Commute x y) :
    Commute x (NormedSpace.exp 𝕂 y) :=
  by
  rw [NormedSpace.exp_eq_tsum]
  exact Commute.tsum_right x fun n => (h.pow_right n).smul_right _
#align commute.exp_right Commute.exp_right
-/

#print Commute.exp_left /-
theorem Commute.exp_left [T2Space 𝔸] {x y : 𝔸} (h : Commute x y) :
    Commute (NormedSpace.exp 𝕂 x) y :=
  (h.symm.exp_right 𝕂).symm
#align commute.exp_left Commute.exp_left
-/

#print Commute.exp /-
theorem Commute.exp [T2Space 𝔸] {x y : 𝔸} (h : Commute x y) :
    Commute (NormedSpace.exp 𝕂 x) (NormedSpace.exp 𝕂 y) :=
  (h.exp_left _).exp_right _
#align commute.exp Commute.exp
-/

end TopologicalAlgebra

section TopologicalDivisionAlgebra

variable {𝕂 𝔸 : Type _} [Field 𝕂] [DivisionRing 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸]
  [TopologicalRing 𝔸]

#print NormedSpace.expSeries_apply_eq_div /-
theorem NormedSpace.expSeries_apply_eq_div (x : 𝔸) (n : ℕ) :
    (NormedSpace.expSeries 𝕂 𝔸 n fun _ => x) = x ^ n / n ! := by
  rw [div_eq_mul_inv, ← (Nat.cast_commute n ! (x ^ n)).inv_left₀.Eq, ← smul_eq_mul,
    NormedSpace.expSeries_apply_eq, inv_nat_cast_smul_eq _ _ _ _]
#align exp_series_apply_eq_div NormedSpace.expSeries_apply_eq_div
-/

#print NormedSpace.expSeries_apply_eq_div' /-
theorem NormedSpace.expSeries_apply_eq_div' (x : 𝔸) :
    (fun n => NormedSpace.expSeries 𝕂 𝔸 n fun _ => x) = fun n => x ^ n / n ! :=
  funext (NormedSpace.expSeries_apply_eq_div x)
#align exp_series_apply_eq_div' NormedSpace.expSeries_apply_eq_div'
-/

#print NormedSpace.expSeries_sum_eq_div /-
theorem NormedSpace.expSeries_sum_eq_div (x : 𝔸) :
    (NormedSpace.expSeries 𝕂 𝔸).Sum x = ∑' n : ℕ, x ^ n / n ! :=
  tsum_congr (NormedSpace.expSeries_apply_eq_div x)
#align exp_series_sum_eq_div NormedSpace.expSeries_sum_eq_div
-/

#print NormedSpace.exp_eq_tsum_div /-
theorem NormedSpace.exp_eq_tsum_div : NormedSpace.exp 𝕂 = fun x : 𝔸 => ∑' n : ℕ, x ^ n / n ! :=
  funext NormedSpace.expSeries_sum_eq_div
#align exp_eq_tsum_div NormedSpace.exp_eq_tsum_div
-/

end TopologicalDivisionAlgebra

section Normed

section AnyFieldAnyAlgebra

variable {𝕂 𝔸 𝔹 : Type _} [NontriviallyNormedField 𝕂]

variable [NormedRing 𝔸] [NormedRing 𝔹] [NormedAlgebra 𝕂 𝔸] [NormedAlgebra 𝕂 𝔹]

#print NormedSpace.norm_expSeries_summable_of_mem_ball /-
theorem NormedSpace.norm_expSeries_summable_of_mem_ball (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (NormedSpace.expSeries 𝕂 𝔸).radius) :
    Summable fun n => ‖NormedSpace.expSeries 𝕂 𝔸 n fun _ => x‖ :=
  (NormedSpace.expSeries 𝕂 𝔸).summable_norm_apply hx
#align norm_exp_series_summable_of_mem_ball NormedSpace.norm_expSeries_summable_of_mem_ball
-/

#print NormedSpace.norm_expSeries_summable_of_mem_ball' /-
theorem NormedSpace.norm_expSeries_summable_of_mem_ball' (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (NormedSpace.expSeries 𝕂 𝔸).radius) :
    Summable fun n => ‖(n !⁻¹ : 𝕂) • x ^ n‖ :=
  by
  change Summable (norm ∘ _)
  rw [← NormedSpace.expSeries_apply_eq']
  exact NormedSpace.norm_expSeries_summable_of_mem_ball x hx
#align norm_exp_series_summable_of_mem_ball' NormedSpace.norm_expSeries_summable_of_mem_ball'
-/

section CompleteAlgebra

variable [CompleteSpace 𝔸]

#print NormedSpace.expSeries_summable_of_mem_ball /-
theorem NormedSpace.expSeries_summable_of_mem_ball (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (NormedSpace.expSeries 𝕂 𝔸).radius) :
    Summable fun n => NormedSpace.expSeries 𝕂 𝔸 n fun _ => x :=
  Summable.of_norm (NormedSpace.norm_expSeries_summable_of_mem_ball x hx)
#align exp_series_summable_of_mem_ball NormedSpace.expSeries_summable_of_mem_ball
-/

#print NormedSpace.expSeries_summable_of_mem_ball' /-
theorem NormedSpace.expSeries_summable_of_mem_ball' (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (NormedSpace.expSeries 𝕂 𝔸).radius) :
    Summable fun n => (n !⁻¹ : 𝕂) • x ^ n :=
  Summable.of_norm (NormedSpace.norm_expSeries_summable_of_mem_ball' x hx)
#align exp_series_summable_of_mem_ball' NormedSpace.expSeries_summable_of_mem_ball'
-/

#print NormedSpace.expSeries_hasSum_exp_of_mem_ball /-
theorem NormedSpace.expSeries_hasSum_exp_of_mem_ball (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (NormedSpace.expSeries 𝕂 𝔸).radius) :
    HasSum (fun n => NormedSpace.expSeries 𝕂 𝔸 n fun _ => x) (NormedSpace.exp 𝕂 x) :=
  FormalMultilinearSeries.hasSum (NormedSpace.expSeries 𝕂 𝔸) hx
#align exp_series_has_sum_exp_of_mem_ball NormedSpace.expSeries_hasSum_exp_of_mem_ball
-/

#print NormedSpace.expSeries_hasSum_exp_of_mem_ball' /-
theorem NormedSpace.expSeries_hasSum_exp_of_mem_ball' (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (NormedSpace.expSeries 𝕂 𝔸).radius) :
    HasSum (fun n => (n !⁻¹ : 𝕂) • x ^ n) (NormedSpace.exp 𝕂 x) :=
  by
  rw [← NormedSpace.expSeries_apply_eq']
  exact NormedSpace.expSeries_hasSum_exp_of_mem_ball x hx
#align exp_series_has_sum_exp_of_mem_ball' NormedSpace.expSeries_hasSum_exp_of_mem_ball'
-/

#print NormedSpace.hasFPowerSeriesOnBall_exp_of_radius_pos /-
theorem NormedSpace.hasFPowerSeriesOnBall_exp_of_radius_pos
    (h : 0 < (NormedSpace.expSeries 𝕂 𝔸).radius) :
    HasFPowerSeriesOnBall (NormedSpace.exp 𝕂) (NormedSpace.expSeries 𝕂 𝔸) 0
      (NormedSpace.expSeries 𝕂 𝔸).radius :=
  (NormedSpace.expSeries 𝕂 𝔸).HasFPowerSeriesOnBall h
#align has_fpower_series_on_ball_exp_of_radius_pos NormedSpace.hasFPowerSeriesOnBall_exp_of_radius_pos
-/

#print NormedSpace.hasFPowerSeriesAt_exp_zero_of_radius_pos /-
theorem NormedSpace.hasFPowerSeriesAt_exp_zero_of_radius_pos
    (h : 0 < (NormedSpace.expSeries 𝕂 𝔸).radius) :
    HasFPowerSeriesAt (NormedSpace.exp 𝕂) (NormedSpace.expSeries 𝕂 𝔸) 0 :=
  (NormedSpace.hasFPowerSeriesOnBall_exp_of_radius_pos h).HasFPowerSeriesAt
#align has_fpower_series_at_exp_zero_of_radius_pos NormedSpace.hasFPowerSeriesAt_exp_zero_of_radius_pos
-/

#print NormedSpace.continuousOn_exp /-
theorem NormedSpace.continuousOn_exp :
    ContinuousOn (NormedSpace.exp 𝕂 : 𝔸 → 𝔸) (EMetric.ball 0 (NormedSpace.expSeries 𝕂 𝔸).radius) :=
  FormalMultilinearSeries.continuousOn
#align continuous_on_exp NormedSpace.continuousOn_exp
-/

#print NormedSpace.analyticAt_exp_of_mem_ball /-
theorem NormedSpace.analyticAt_exp_of_mem_ball (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (NormedSpace.expSeries 𝕂 𝔸).radius) :
    AnalyticAt 𝕂 (NormedSpace.exp 𝕂) x :=
  by
  by_cases h : (NormedSpace.expSeries 𝕂 𝔸).radius = 0
  · rw [h] at hx ; exact (ENNReal.not_lt_zero hx).elim
  · have h := pos_iff_ne_zero.mpr h
    exact (NormedSpace.hasFPowerSeriesOnBall_exp_of_radius_pos h).analyticAt_of_mem hx
#align analytic_at_exp_of_mem_ball NormedSpace.analyticAt_exp_of_mem_ball
-/

#print NormedSpace.exp_add_of_commute_of_mem_ball /-
/-- In a Banach-algebra `𝔸` over a normed field `𝕂` of characteristic zero, if `x` and `y` are
in the disk of convergence and commute, then `exp 𝕂 (x + y) = (exp 𝕂 x) * (exp 𝕂 y)`. -/
theorem NormedSpace.exp_add_of_commute_of_mem_ball [CharZero 𝕂] {x y : 𝔸} (hxy : Commute x y)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (NormedSpace.expSeries 𝕂 𝔸).radius)
    (hy : y ∈ EMetric.ball (0 : 𝔸) (NormedSpace.expSeries 𝕂 𝔸).radius) :
    NormedSpace.exp 𝕂 (x + y) = NormedSpace.exp 𝕂 x * NormedSpace.exp 𝕂 y :=
  by
  rw [NormedSpace.exp_eq_tsum,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
      (NormedSpace.norm_expSeries_summable_of_mem_ball' x hx)
      (NormedSpace.norm_expSeries_summable_of_mem_ball' y hy)]
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
#align exp_add_of_commute_of_mem_ball NormedSpace.exp_add_of_commute_of_mem_ball
-/

#print NormedSpace.invertibleExpOfMemBall /-
/-- `exp 𝕂 x` has explicit two-sided inverse `exp 𝕂 (-x)`. -/
noncomputable def NormedSpace.invertibleExpOfMemBall [CharZero 𝕂] {x : 𝔸}
    (hx : x ∈ EMetric.ball (0 : 𝔸) (NormedSpace.expSeries 𝕂 𝔸).radius) :
    Invertible (NormedSpace.exp 𝕂 x)
    where
  invOf := NormedSpace.exp 𝕂 (-x)
  invOf_hMul_self :=
    by
    have hnx : -x ∈ EMetric.ball (0 : 𝔸) (NormedSpace.expSeries 𝕂 𝔸).radius :=
      by
      rw [EMetric.mem_ball, ← neg_zero, edist_neg_neg]
      exact hx
    rw [← NormedSpace.exp_add_of_commute_of_mem_ball (Commute.neg_left <| Commute.refl x) hnx hx,
      neg_add_self, NormedSpace.exp_zero]
  hMul_invOf_self :=
    by
    have hnx : -x ∈ EMetric.ball (0 : 𝔸) (NormedSpace.expSeries 𝕂 𝔸).radius :=
      by
      rw [EMetric.mem_ball, ← neg_zero, edist_neg_neg]
      exact hx
    rw [← NormedSpace.exp_add_of_commute_of_mem_ball (Commute.neg_right <| Commute.refl x) hx hnx,
      add_neg_self, NormedSpace.exp_zero]
#align invertible_exp_of_mem_ball NormedSpace.invertibleExpOfMemBall
-/

#print NormedSpace.isUnit_exp_of_mem_ball /-
theorem NormedSpace.isUnit_exp_of_mem_ball [CharZero 𝕂] {x : 𝔸}
    (hx : x ∈ EMetric.ball (0 : 𝔸) (NormedSpace.expSeries 𝕂 𝔸).radius) :
    IsUnit (NormedSpace.exp 𝕂 x) :=
  @isUnit_of_invertible _ _ _ (NormedSpace.invertibleExpOfMemBall hx)
#align is_unit_exp_of_mem_ball NormedSpace.isUnit_exp_of_mem_ball
-/

#print NormedSpace.invOf_exp_of_mem_ball /-
theorem NormedSpace.invOf_exp_of_mem_ball [CharZero 𝕂] {x : 𝔸}
    (hx : x ∈ EMetric.ball (0 : 𝔸) (NormedSpace.expSeries 𝕂 𝔸).radius)
    [Invertible (NormedSpace.exp 𝕂 x)] : ⅟ (NormedSpace.exp 𝕂 x) = NormedSpace.exp 𝕂 (-x) := by
  letI := NormedSpace.invertibleExpOfMemBall hx; convert (rfl : ⅟ (NormedSpace.exp 𝕂 x) = _)
#align inv_of_exp_of_mem_ball NormedSpace.invOf_exp_of_mem_ball
-/

#print NormedSpace.map_exp_of_mem_ball /-
/-- Any continuous ring homomorphism commutes with `exp`. -/
theorem NormedSpace.map_exp_of_mem_ball {F} [RingHomClass F 𝔸 𝔹] (f : F) (hf : Continuous f) (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (NormedSpace.expSeries 𝕂 𝔸).radius) :
    f (NormedSpace.exp 𝕂 x) = NormedSpace.exp 𝕂 (f x) :=
  by
  rw [NormedSpace.exp_eq_tsum, NormedSpace.exp_eq_tsum]
  refine' ((NormedSpace.expSeries_summable_of_mem_ball' _ hx).HasSum.map f hf).tsum_eq.symm.trans _
  dsimp only [Function.comp]
  simp_rw [one_div, map_inv_nat_cast_smul f 𝕂 𝕂, map_pow]
#align map_exp_of_mem_ball NormedSpace.map_exp_of_mem_ball
-/

end CompleteAlgebra

#print NormedSpace.algebraMap_exp_comm_of_mem_ball /-
theorem NormedSpace.algebraMap_exp_comm_of_mem_ball [CompleteSpace 𝕂] (x : 𝕂)
    (hx : x ∈ EMetric.ball (0 : 𝕂) (NormedSpace.expSeries 𝕂 𝕂).radius) :
    algebraMap 𝕂 𝔸 (NormedSpace.exp 𝕂 x) = NormedSpace.exp 𝕂 (algebraMap 𝕂 𝔸 x) :=
  NormedSpace.map_exp_of_mem_ball _ (continuous_algebraMap 𝕂 𝔸) _ hx
#align algebra_map_exp_comm_of_mem_ball NormedSpace.algebraMap_exp_comm_of_mem_ball
-/

end AnyFieldAnyAlgebra

section AnyFieldDivisionAlgebra

variable {𝕂 𝔸 : Type _} [NontriviallyNormedField 𝕂] [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸]

variable (𝕂)

#print NormedSpace.norm_expSeries_div_summable_of_mem_ball /-
theorem NormedSpace.norm_expSeries_div_summable_of_mem_ball (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (NormedSpace.expSeries 𝕂 𝔸).radius) :
    Summable fun n => ‖x ^ n / n !‖ :=
  by
  change Summable (norm ∘ _)
  rw [← NormedSpace.expSeries_apply_eq_div' x]
  exact NormedSpace.norm_expSeries_summable_of_mem_ball x hx
#align norm_exp_series_div_summable_of_mem_ball NormedSpace.norm_expSeries_div_summable_of_mem_ball
-/

#print NormedSpace.expSeries_div_summable_of_mem_ball /-
theorem NormedSpace.expSeries_div_summable_of_mem_ball [CompleteSpace 𝔸] (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (NormedSpace.expSeries 𝕂 𝔸).radius) :
    Summable fun n => x ^ n / n ! :=
  Summable.of_norm (NormedSpace.norm_expSeries_div_summable_of_mem_ball 𝕂 x hx)
#align exp_series_div_summable_of_mem_ball NormedSpace.expSeries_div_summable_of_mem_ball
-/

#print NormedSpace.expSeries_div_hasSum_exp_of_mem_ball /-
theorem NormedSpace.expSeries_div_hasSum_exp_of_mem_ball [CompleteSpace 𝔸] (x : 𝔸)
    (hx : x ∈ EMetric.ball (0 : 𝔸) (NormedSpace.expSeries 𝕂 𝔸).radius) :
    HasSum (fun n => x ^ n / n !) (NormedSpace.exp 𝕂 x) :=
  by
  rw [← NormedSpace.expSeries_apply_eq_div' x]
  exact NormedSpace.expSeries_hasSum_exp_of_mem_ball x hx
#align exp_series_div_has_sum_exp_of_mem_ball NormedSpace.expSeries_div_hasSum_exp_of_mem_ball
-/

variable {𝕂}

#print NormedSpace.exp_neg_of_mem_ball /-
theorem NormedSpace.exp_neg_of_mem_ball [CharZero 𝕂] [CompleteSpace 𝔸] {x : 𝔸}
    (hx : x ∈ EMetric.ball (0 : 𝔸) (NormedSpace.expSeries 𝕂 𝔸).radius) :
    NormedSpace.exp 𝕂 (-x) = (NormedSpace.exp 𝕂 x)⁻¹ :=
  letI := NormedSpace.invertibleExpOfMemBall hx
  invOf_eq_inv (NormedSpace.exp 𝕂 x)
#align exp_neg_of_mem_ball NormedSpace.exp_neg_of_mem_ball
-/

end AnyFieldDivisionAlgebra

section AnyFieldCommAlgebra

variable {𝕂 𝔸 : Type _} [NontriviallyNormedField 𝕂] [NormedCommRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  [CompleteSpace 𝔸]

#print NormedSpace.exp_add_of_mem_ball /-
/-- In a commutative Banach-algebra `𝔸` over a normed field `𝕂` of characteristic zero,
`exp 𝕂 (x+y) = (exp 𝕂 x) * (exp 𝕂 y)` for all `x`, `y` in the disk of convergence. -/
theorem NormedSpace.exp_add_of_mem_ball [CharZero 𝕂] {x y : 𝔸}
    (hx : x ∈ EMetric.ball (0 : 𝔸) (NormedSpace.expSeries 𝕂 𝔸).radius)
    (hy : y ∈ EMetric.ball (0 : 𝔸) (NormedSpace.expSeries 𝕂 𝔸).radius) :
    NormedSpace.exp 𝕂 (x + y) = NormedSpace.exp 𝕂 x * NormedSpace.exp 𝕂 y :=
  NormedSpace.exp_add_of_commute_of_mem_ball (Commute.all x y) hx hy
#align exp_add_of_mem_ball NormedSpace.exp_add_of_mem_ball
-/

end AnyFieldCommAlgebra

section IsROrC

section AnyAlgebra

variable (𝕂 𝔸 𝔹 : Type _) [IsROrC 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]

variable [NormedRing 𝔹] [NormedAlgebra 𝕂 𝔹]

#print NormedSpace.expSeries_radius_eq_top /-
/-- In a normed algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, the series defining the exponential map
has an infinite radius of convergence. -/
theorem NormedSpace.expSeries_radius_eq_top : (NormedSpace.expSeries 𝕂 𝔸).radius = ∞ :=
  by
  refine' (NormedSpace.expSeries 𝕂 𝔸).radius_eq_top_of_summable_norm fun r => _
  refine' Summable.of_norm_bounded_eventually _ (Real.summable_pow_div_factorial r) _
  filter_upwards [eventually_cofinite_ne 0] with n hn
  rw [norm_mul, norm_norm (NormedSpace.expSeries 𝕂 𝔸 n), NormedSpace.expSeries, norm_smul, norm_inv,
    norm_pow, NNReal.norm_eq, norm_nat_cast, mul_comm, ← mul_assoc, ← div_eq_mul_inv]
  have : ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 n 𝔸‖ ≤ 1 :=
    norm_mk_pi_algebra_fin_le_of_pos (Nat.pos_of_ne_zero hn)
  exact mul_le_of_le_one_right (div_nonneg (pow_nonneg r.coe_nonneg n) n !.cast_nonneg) this
#align exp_series_radius_eq_top NormedSpace.expSeries_radius_eq_top
-/

#print NormedSpace.expSeries_radius_pos /-
theorem NormedSpace.expSeries_radius_pos : 0 < (NormedSpace.expSeries 𝕂 𝔸).radius :=
  by
  rw [NormedSpace.expSeries_radius_eq_top]
  exact WithTop.zero_lt_top
#align exp_series_radius_pos NormedSpace.expSeries_radius_pos
-/

variable {𝕂 𝔸 𝔹}

#print NormedSpace.norm_expSeries_summable /-
theorem NormedSpace.norm_expSeries_summable (x : 𝔸) :
    Summable fun n => ‖NormedSpace.expSeries 𝕂 𝔸 n fun _ => x‖ :=
  NormedSpace.norm_expSeries_summable_of_mem_ball x
    ((NormedSpace.expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
#align norm_exp_series_summable NormedSpace.norm_expSeries_summable
-/

#print NormedSpace.norm_expSeries_summable' /-
theorem NormedSpace.norm_expSeries_summable' (x : 𝔸) : Summable fun n => ‖(n !⁻¹ : 𝕂) • x ^ n‖ :=
  NormedSpace.norm_expSeries_summable_of_mem_ball' x
    ((NormedSpace.expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
#align norm_exp_series_summable' NormedSpace.norm_expSeries_summable'
-/

section CompleteAlgebra

variable [CompleteSpace 𝔸]

#print NormedSpace.expSeries_summable /-
theorem NormedSpace.expSeries_summable (x : 𝔸) :
    Summable fun n => NormedSpace.expSeries 𝕂 𝔸 n fun _ => x :=
  Summable.of_norm (NormedSpace.norm_expSeries_summable x)
#align exp_series_summable NormedSpace.expSeries_summable
-/

#print NormedSpace.expSeries_summable' /-
theorem NormedSpace.expSeries_summable' (x : 𝔸) : Summable fun n => (n !⁻¹ : 𝕂) • x ^ n :=
  Summable.of_norm (NormedSpace.norm_expSeries_summable' x)
#align exp_series_summable' NormedSpace.expSeries_summable'
-/

#print NormedSpace.expSeries_hasSum_exp /-
theorem NormedSpace.expSeries_hasSum_exp (x : 𝔸) :
    HasSum (fun n => NormedSpace.expSeries 𝕂 𝔸 n fun _ => x) (NormedSpace.exp 𝕂 x) :=
  NormedSpace.expSeries_hasSum_exp_of_mem_ball x
    ((NormedSpace.expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
#align exp_series_has_sum_exp NormedSpace.expSeries_hasSum_exp
-/

#print NormedSpace.exp_series_hasSum_exp' /-
theorem NormedSpace.exp_series_hasSum_exp' (x : 𝔸) :
    HasSum (fun n => (n !⁻¹ : 𝕂) • x ^ n) (NormedSpace.exp 𝕂 x) :=
  NormedSpace.expSeries_hasSum_exp_of_mem_ball' x
    ((NormedSpace.expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
#align exp_series_has_sum_exp' NormedSpace.exp_series_hasSum_exp'
-/

#print NormedSpace.exp_hasFPowerSeriesOnBall /-
theorem NormedSpace.exp_hasFPowerSeriesOnBall :
    HasFPowerSeriesOnBall (NormedSpace.exp 𝕂) (NormedSpace.expSeries 𝕂 𝔸) 0 ∞ :=
  NormedSpace.expSeries_radius_eq_top 𝕂 𝔸 ▸
    NormedSpace.hasFPowerSeriesOnBall_exp_of_radius_pos (NormedSpace.expSeries_radius_pos _ _)
#align exp_has_fpower_series_on_ball NormedSpace.exp_hasFPowerSeriesOnBall
-/

#print NormedSpace.exp_hasFPowerSeriesAt_zero /-
theorem NormedSpace.exp_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt (NormedSpace.exp 𝕂) (NormedSpace.expSeries 𝕂 𝔸) 0 :=
  NormedSpace.exp_hasFPowerSeriesOnBall.HasFPowerSeriesAt
#align exp_has_fpower_series_at_zero NormedSpace.exp_hasFPowerSeriesAt_zero
-/

#print NormedSpace.exp_continuous /-
@[continuity]
theorem NormedSpace.exp_continuous : Continuous (NormedSpace.exp 𝕂 : 𝔸 → 𝔸) :=
  by
  rw [continuous_iff_continuousOn_univ, ← Metric.eball_top_eq_univ (0 : 𝔸), ←
    NormedSpace.expSeries_radius_eq_top 𝕂 𝔸]
  exact NormedSpace.continuousOn_exp
#align exp_continuous NormedSpace.exp_continuous
-/

#print NormedSpace.exp_analytic /-
theorem NormedSpace.exp_analytic (x : 𝔸) : AnalyticAt 𝕂 (NormedSpace.exp 𝕂) x :=
  NormedSpace.analyticAt_exp_of_mem_ball x
    ((NormedSpace.expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
#align exp_analytic NormedSpace.exp_analytic
-/

#print NormedSpace.exp_add_of_commute /-
/-- In a Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, if `x` and `y` commute, then
`exp 𝕂 (x+y) = (exp 𝕂 x) * (exp 𝕂 y)`. -/
theorem NormedSpace.exp_add_of_commute {x y : 𝔸} (hxy : Commute x y) :
    NormedSpace.exp 𝕂 (x + y) = NormedSpace.exp 𝕂 x * NormedSpace.exp 𝕂 y :=
  NormedSpace.exp_add_of_commute_of_mem_ball hxy
    ((NormedSpace.expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
    ((NormedSpace.expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
#align exp_add_of_commute NormedSpace.exp_add_of_commute
-/

section

variable (𝕂)

#print NormedSpace.invertibleExp /-
/-- `exp 𝕂 x` has explicit two-sided inverse `exp 𝕂 (-x)`. -/
noncomputable def NormedSpace.invertibleExp (x : 𝔸) : Invertible (NormedSpace.exp 𝕂 x) :=
  NormedSpace.invertibleExpOfMemBall <|
    (NormedSpace.expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _
#align invertible_exp NormedSpace.invertibleExp
-/

#print NormedSpace.isUnit_exp /-
theorem NormedSpace.isUnit_exp (x : 𝔸) : IsUnit (NormedSpace.exp 𝕂 x) :=
  NormedSpace.isUnit_exp_of_mem_ball <|
    (NormedSpace.expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _
#align is_unit_exp NormedSpace.isUnit_exp
-/

#print NormedSpace.invOf_exp /-
theorem NormedSpace.invOf_exp (x : 𝔸) [Invertible (NormedSpace.exp 𝕂 x)] :
    ⅟ (NormedSpace.exp 𝕂 x) = NormedSpace.exp 𝕂 (-x) :=
  NormedSpace.invOf_exp_of_mem_ball <|
    (NormedSpace.expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _
#align inv_of_exp NormedSpace.invOf_exp
-/

#print Ring.inverse_exp /-
theorem Ring.inverse_exp (x : 𝔸) : Ring.inverse (NormedSpace.exp 𝕂 x) = NormedSpace.exp 𝕂 (-x) :=
  letI := NormedSpace.invertibleExp 𝕂 x
  Ring.inverse_invertible _
#align ring.inverse_exp Ring.inverse_exp
-/

#print NormedSpace.exp_mem_unitary_of_mem_skewAdjoint /-
theorem NormedSpace.exp_mem_unitary_of_mem_skewAdjoint [StarRing 𝔸] [ContinuousStar 𝔸] {x : 𝔸}
    (h : x ∈ skewAdjoint 𝔸) : NormedSpace.exp 𝕂 x ∈ unitary 𝔸 := by
  rw [unitary.mem_iff, NormedSpace.star_exp, skew_adjoint.mem_iff.mp h, ←
    NormedSpace.exp_add_of_commute (Commute.refl x).neg_left, ←
    NormedSpace.exp_add_of_commute (Commute.refl x).neg_right, add_left_neg, add_right_neg,
    NormedSpace.exp_zero, and_self_iff]
#align exp_mem_unitary_of_mem_skew_adjoint NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
-/

end

#print NormedSpace.exp_sum_of_commute /-
/-- In a Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, if a family of elements `f i` mutually
commute then `exp 𝕂 (∑ i, f i) = ∏ i, exp 𝕂 (f i)`. -/
theorem NormedSpace.exp_sum_of_commute {ι} (s : Finset ι) (f : ι → 𝔸)
    (h : (s : Set ι).Pairwise fun i j => Commute (f i) (f j)) :
    NormedSpace.exp 𝕂 (∑ i in s, f i) =
      s.noncommProd (fun i => NormedSpace.exp 𝕂 (f i)) fun i hi j hj _ => (h.of_refl hi hj).exp 𝕂 :=
  by
  classical
  induction' s using Finset.induction_on with a s ha ih
  · simp
  rw [Finset.noncommProd_insert_of_not_mem _ _ _ _ ha, Finset.sum_insert ha,
    NormedSpace.exp_add_of_commute, ih (h.mono <| Finset.subset_insert _ _)]
  refine' Commute.sum_right _ _ _ fun i hi => _
  exact h.of_refl (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hi)
#align exp_sum_of_commute NormedSpace.exp_sum_of_commute
-/

#print NormedSpace.exp_nsmul /-
theorem NormedSpace.exp_nsmul (n : ℕ) (x : 𝔸) :
    NormedSpace.exp 𝕂 (n • x) = NormedSpace.exp 𝕂 x ^ n :=
  by
  induction' n with n ih
  · rw [zero_smul, pow_zero, NormedSpace.exp_zero]
  · rw [succ_nsmul, pow_succ, NormedSpace.exp_add_of_commute ((Commute.refl x).smul_right n), ih]
#align exp_nsmul NormedSpace.exp_nsmul
-/

variable (𝕂)

#print NormedSpace.map_exp /-
/-- Any continuous ring homomorphism commutes with `exp`. -/
theorem NormedSpace.map_exp {F} [RingHomClass F 𝔸 𝔹] (f : F) (hf : Continuous f) (x : 𝔸) :
    f (NormedSpace.exp 𝕂 x) = NormedSpace.exp 𝕂 (f x) :=
  NormedSpace.map_exp_of_mem_ball f hf x <|
    (NormedSpace.expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _
#align map_exp NormedSpace.map_exp
-/

#print NormedSpace.exp_smul /-
theorem NormedSpace.exp_smul {G} [Monoid G] [MulSemiringAction G 𝔸] [ContinuousConstSMul G 𝔸]
    (g : G) (x : 𝔸) : NormedSpace.exp 𝕂 (g • x) = g • NormedSpace.exp 𝕂 x :=
  (NormedSpace.map_exp 𝕂 (MulSemiringAction.toRingHom G 𝔸 g) (continuous_const_smul _) x).symm
#align exp_smul NormedSpace.exp_smul
-/

#print NormedSpace.exp_units_conj /-
theorem NormedSpace.exp_units_conj (y : 𝔸ˣ) (x : 𝔸) :
    NormedSpace.exp 𝕂 (y * x * ↑y⁻¹ : 𝔸) = y * NormedSpace.exp 𝕂 x * ↑y⁻¹ :=
  NormedSpace.exp_smul _ (ConjAct.toConjAct y) x
#align exp_units_conj NormedSpace.exp_units_conj
-/

#print NormedSpace.exp_units_conj' /-
theorem NormedSpace.exp_units_conj' (y : 𝔸ˣ) (x : 𝔸) :
    NormedSpace.exp 𝕂 (↑y⁻¹ * x * y) = ↑y⁻¹ * NormedSpace.exp 𝕂 x * y :=
  NormedSpace.exp_units_conj _ _ _
#align exp_units_conj' NormedSpace.exp_units_conj'
-/

#print Prod.fst_exp /-
@[simp]
theorem Prod.fst_exp [CompleteSpace 𝔹] (x : 𝔸 × 𝔹) :
    (NormedSpace.exp 𝕂 x).fst = NormedSpace.exp 𝕂 x.fst :=
  NormedSpace.map_exp _ (RingHom.fst 𝔸 𝔹) continuous_fst x
#align prod.fst_exp Prod.fst_exp
-/

#print Prod.snd_exp /-
@[simp]
theorem Prod.snd_exp [CompleteSpace 𝔹] (x : 𝔸 × 𝔹) :
    (NormedSpace.exp 𝕂 x).snd = NormedSpace.exp 𝕂 x.snd :=
  NormedSpace.map_exp _ (RingHom.snd 𝔸 𝔹) continuous_snd x
#align prod.snd_exp Prod.snd_exp
-/

#print Pi.exp_apply /-
@[simp]
theorem Pi.exp_apply {ι : Type _} {𝔸 : ι → Type _} [Fintype ι] [∀ i, NormedRing (𝔸 i)]
    [∀ i, NormedAlgebra 𝕂 (𝔸 i)] [∀ i, CompleteSpace (𝔸 i)] (x : ∀ i, 𝔸 i) (i : ι) :
    NormedSpace.exp 𝕂 x i = NormedSpace.exp 𝕂 (x i) :=
  letI : NormedAlgebra 𝕂 (∀ i, 𝔸 i) := Pi.normedAlgebra _
  NormedSpace.map_exp _ (Pi.evalRingHom 𝔸 i) (continuous_apply _) x
#align pi.exp_apply Pi.exp_apply
-/

#print Pi.exp_def /-
theorem Pi.exp_def {ι : Type _} {𝔸 : ι → Type _} [Fintype ι] [∀ i, NormedRing (𝔸 i)]
    [∀ i, NormedAlgebra 𝕂 (𝔸 i)] [∀ i, CompleteSpace (𝔸 i)] (x : ∀ i, 𝔸 i) :
    NormedSpace.exp 𝕂 x = fun i => NormedSpace.exp 𝕂 (x i) :=
  funext <| Pi.exp_apply 𝕂 x
#align pi.exp_def Pi.exp_def
-/

#print Function.update_exp /-
theorem Function.update_exp {ι : Type _} {𝔸 : ι → Type _} [Fintype ι] [DecidableEq ι]
    [∀ i, NormedRing (𝔸 i)] [∀ i, NormedAlgebra 𝕂 (𝔸 i)] [∀ i, CompleteSpace (𝔸 i)] (x : ∀ i, 𝔸 i)
    (j : ι) (xj : 𝔸 j) :
    Function.update (NormedSpace.exp 𝕂 x) j (NormedSpace.exp 𝕂 xj) =
      NormedSpace.exp 𝕂 (Function.update x j xj) :=
  by
  ext i
  simp_rw [Pi.exp_def]
  exact (Function.apply_update (fun i => NormedSpace.exp 𝕂) x j xj i).symm
#align function.update_exp Function.update_exp
-/

end CompleteAlgebra

#print NormedSpace.algebraMap_exp_comm /-
theorem NormedSpace.algebraMap_exp_comm (x : 𝕂) :
    algebraMap 𝕂 𝔸 (NormedSpace.exp 𝕂 x) = NormedSpace.exp 𝕂 (algebraMap 𝕂 𝔸 x) :=
  NormedSpace.algebraMap_exp_comm_of_mem_ball x <|
    (NormedSpace.expSeries_radius_eq_top 𝕂 𝕂).symm ▸ edist_lt_top _ _
#align algebra_map_exp_comm NormedSpace.algebraMap_exp_comm
-/

end AnyAlgebra

section DivisionAlgebra

variable {𝕂 𝔸 : Type _} [IsROrC 𝕂] [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸]

variable (𝕂)

#print NormedSpace.norm_expSeries_div_summable /-
theorem NormedSpace.norm_expSeries_div_summable (x : 𝔸) : Summable fun n => ‖x ^ n / n !‖ :=
  NormedSpace.norm_expSeries_div_summable_of_mem_ball 𝕂 x
    ((NormedSpace.expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
#align norm_exp_series_div_summable NormedSpace.norm_expSeries_div_summable
-/

variable [CompleteSpace 𝔸]

#print NormedSpace.expSeries_div_summable /-
theorem NormedSpace.expSeries_div_summable (x : 𝔸) : Summable fun n => x ^ n / n ! :=
  Summable.of_norm (NormedSpace.norm_expSeries_div_summable 𝕂 x)
#align exp_series_div_summable NormedSpace.expSeries_div_summable
-/

#print NormedSpace.expSeries_div_hasSum_exp /-
theorem NormedSpace.expSeries_div_hasSum_exp (x : 𝔸) :
    HasSum (fun n => x ^ n / n !) (NormedSpace.exp 𝕂 x) :=
  NormedSpace.expSeries_div_hasSum_exp_of_mem_ball 𝕂 x
    ((NormedSpace.expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
#align exp_series_div_has_sum_exp NormedSpace.expSeries_div_hasSum_exp
-/

variable {𝕂}

#print NormedSpace.exp_neg /-
theorem NormedSpace.exp_neg (x : 𝔸) : NormedSpace.exp 𝕂 (-x) = (NormedSpace.exp 𝕂 x)⁻¹ :=
  NormedSpace.exp_neg_of_mem_ball <|
    (NormedSpace.expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _
#align exp_neg NormedSpace.exp_neg
-/

#print NormedSpace.exp_zsmul /-
theorem NormedSpace.exp_zsmul (z : ℤ) (x : 𝔸) :
    NormedSpace.exp 𝕂 (z • x) = NormedSpace.exp 𝕂 x ^ z :=
  by
  obtain ⟨n, rfl | rfl⟩ := z.eq_coe_or_neg
  · rw [zpow_ofNat, coe_nat_zsmul, NormedSpace.exp_nsmul]
  · rw [zpow_neg, zpow_ofNat, neg_smul, NormedSpace.exp_neg, coe_nat_zsmul, NormedSpace.exp_nsmul]
#align exp_zsmul NormedSpace.exp_zsmul
-/

#print NormedSpace.exp_conj /-
theorem NormedSpace.exp_conj (y : 𝔸) (x : 𝔸) (hy : y ≠ 0) :
    NormedSpace.exp 𝕂 (y * x * y⁻¹) = y * NormedSpace.exp 𝕂 x * y⁻¹ :=
  NormedSpace.exp_units_conj _ (Units.mk0 y hy) x
#align exp_conj NormedSpace.exp_conj
-/

#print NormedSpace.exp_conj' /-
theorem NormedSpace.exp_conj' (y : 𝔸) (x : 𝔸) (hy : y ≠ 0) :
    NormedSpace.exp 𝕂 (y⁻¹ * x * y) = y⁻¹ * NormedSpace.exp 𝕂 x * y :=
  NormedSpace.exp_units_conj' _ (Units.mk0 y hy) x
#align exp_conj' NormedSpace.exp_conj'
-/

end DivisionAlgebra

section CommAlgebra

variable {𝕂 𝔸 : Type _} [IsROrC 𝕂] [NormedCommRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

#print NormedSpace.exp_add /-
/-- In a commutative Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`,
`exp 𝕂 (x+y) = (exp 𝕂 x) * (exp 𝕂 y)`. -/
theorem NormedSpace.exp_add {x y : 𝔸} :
    NormedSpace.exp 𝕂 (x + y) = NormedSpace.exp 𝕂 x * NormedSpace.exp 𝕂 y :=
  NormedSpace.exp_add_of_mem_ball
    ((NormedSpace.expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
    ((NormedSpace.expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
#align exp_add NormedSpace.exp_add
-/

#print NormedSpace.exp_sum /-
/-- A version of `exp_sum_of_commute` for a commutative Banach-algebra. -/
theorem NormedSpace.exp_sum {ι} (s : Finset ι) (f : ι → 𝔸) :
    NormedSpace.exp 𝕂 (∑ i in s, f i) = ∏ i in s, NormedSpace.exp 𝕂 (f i) :=
  by
  rw [NormedSpace.exp_sum_of_commute, Finset.noncommProd_eq_prod]
  exact fun i hi j hj _ => Commute.all _ _
#align exp_sum NormedSpace.exp_sum
-/

end CommAlgebra

end IsROrC

end Normed

section ScalarTower

variable (𝕂 𝕂' 𝔸 : Type _) [Field 𝕂] [Field 𝕂'] [Ring 𝔸] [Algebra 𝕂 𝔸] [Algebra 𝕂' 𝔸]
  [TopologicalSpace 𝔸] [TopologicalRing 𝔸]

#print NormedSpace.expSeries_eq_expSeries /-
/-- If a normed ring `𝔸` is a normed algebra over two fields, then they define the same
`exp_series` on `𝔸`. -/
theorem NormedSpace.expSeries_eq_expSeries (n : ℕ) (x : 𝔸) :
    (NormedSpace.expSeries 𝕂 𝔸 n fun _ => x) = NormedSpace.expSeries 𝕂' 𝔸 n fun _ => x := by
  rw [NormedSpace.expSeries_apply_eq, NormedSpace.expSeries_apply_eq, inv_nat_cast_smul_eq 𝕂 𝕂']
#align exp_series_eq_exp_series NormedSpace.expSeries_eq_expSeries
-/

#print NormedSpace.exp_eq_exp /-
/-- If a normed ring `𝔸` is a normed algebra over two fields, then they define the same
exponential function on `𝔸`. -/
theorem NormedSpace.exp_eq_exp : (NormedSpace.exp 𝕂 : 𝔸 → 𝔸) = NormedSpace.exp 𝕂' :=
  by
  ext
  rw [NormedSpace.exp, NormedSpace.exp]
  refine' tsum_congr fun n => _
  rw [NormedSpace.expSeries_eq_expSeries 𝕂 𝕂' 𝔸 n x]
#align exp_eq_exp NormedSpace.exp_eq_exp
-/

#print NormedSpace.exp_ℝ_ℂ_eq_exp_ℂ_ℂ /-
theorem NormedSpace.exp_ℝ_ℂ_eq_exp_ℂ_ℂ : (NormedSpace.exp ℝ : ℂ → ℂ) = NormedSpace.exp ℂ :=
  NormedSpace.exp_eq_exp ℝ ℂ ℂ
#align exp_ℝ_ℂ_eq_exp_ℂ_ℂ NormedSpace.exp_ℝ_ℂ_eq_exp_ℂ_ℂ
-/

#print NormedSpace.of_real_exp_ℝ_ℝ /-
/-- A version of `complex.of_real_exp` for `exp` instead of `complex.exp` -/
@[simp, norm_cast]
theorem NormedSpace.of_real_exp_ℝ_ℝ (r : ℝ) : ↑(NormedSpace.exp ℝ r) = NormedSpace.exp ℂ (r : ℂ) :=
  (NormedSpace.map_exp ℝ (algebraMap ℝ ℂ) (continuous_algebraMap _ _) r).trans
    (congr_fun NormedSpace.exp_ℝ_ℂ_eq_exp_ℂ_ℂ _)
#align of_real_exp_ℝ_ℝ NormedSpace.of_real_exp_ℝ_ℝ
-/

end ScalarTower

