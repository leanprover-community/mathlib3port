/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Eric Wieser
-/
import Mathbin.Analysis.SpecificLimits.Basic
import Mathbin.Analysis.Analytic.Basic
import Mathbin.Analysis.Complex.Basic
import Mathbin.Data.Nat.Choose.Cast
import Mathbin.Data.Finset.NoncommProd

/-!
# Exponential in a Banach algebra

In this file, we define `exp ๐ : ๐ธ โ ๐ธ`, the exponential map in a topological algebra `๐ธ` over a
field `๐`.

While for most interesting results we need `๐ธ` to be normed algebra, we do not require this in the
definition in order to make `exp` independent of a particular choice of norm. The definition also
does not require that `๐ธ` be complete, but we need to assume it for most results.

We then prove some basic results, but we avoid importing derivatives here to minimize dependencies.
Results involving derivatives and comparisons with `real.exp` and `complex.exp` can be found in
`analysis/special_functions/exponential`.

## Main results

We prove most result for an arbitrary field `๐`, and then specialize to `๐ = โ` or `๐ = โ`.

### General case

- `exp_add_of_commute_of_mem_ball` : if `๐` has characteristic zero, then given two commuting
  elements `x` and `y` in the disk of convergence, we have
  `exp ๐ (x+y) = (exp ๐ x) * (exp ๐ y)`
- `exp_add_of_mem_ball` : if `๐` has characteristic zero and `๐ธ` is commutative, then given two
  elements `x` and `y` in the disk of convergence, we have
  `exp ๐ (x+y) = (exp ๐ x) * (exp ๐ y)`
- `exp_neg_of_mem_ball` : if `๐` has characteristic zero and `๐ธ` is a division ring, then given an
  element `x` in the disk of convergence, we have `exp ๐ (-x) = (exp ๐ x)โปยน`.

### `๐ = โ` or `๐ = โ`

- `exp_series_radius_eq_top` : the `formal_multilinear_series` defining `exp ๐` has infinite
  radius of convergence
- `exp_add_of_commute` : given two commuting elements `x` and `y`, we have
  `exp ๐ (x+y) = (exp ๐ x) * (exp ๐ y)`
- `exp_add` : if `๐ธ` is commutative, then we have `exp ๐ (x+y) = (exp ๐ x) * (exp ๐ y)`
  for any `x` and `y`
- `exp_neg` : if `๐ธ` is a division ring, then we have `exp ๐ (-x) = (exp ๐ x)โปยน`.
- `exp_sum_of_commute` : the analogous result to `exp_add_of_commute` for `finset.sum`.
- `exp_sum` : the analogous result to `exp_add` for `finset.sum`.
- `exp_nsmul` : repeated addition in the domain corresponds to repeated multiplication in the
  codomain.
- `exp_zsmul` : repeated addition in the domain corresponds to repeated multiplication in the
  codomain.

### Other useful compatibility results

- `exp_eq_exp` : if `๐ธ` is a normed algebra over two fields `๐` and `๐'`, then `exp ๐ = exp ๐' ๐ธ`

-/


open Filter IsROrC ContinuousMultilinearMap NormedField Asymptotics

open Nat TopologicalSpace BigOperators Ennreal

section TopologicalAlgebra

variable (๐ ๐ธ : Type _) [Field ๐] [Ringโ ๐ธ] [Algebra ๐ ๐ธ] [TopologicalSpace ๐ธ] [TopologicalRing ๐ธ]

/-- `exp_series ๐ ๐ธ` is the `formal_multilinear_series` whose `n`-th term is the map
`(xแตข) : ๐ธโฟ โฆ (1/n! : ๐) โข โ xแตข`. Its sum is the exponential map `exp ๐ : ๐ธ โ ๐ธ`. -/
def expSeries : FormalMultilinearSeries ๐ ๐ธ ๐ธ := fun n => (n !โปยน : ๐) โข ContinuousMultilinearMap.mkPiAlgebraFin ๐ n ๐ธ

variable {๐ธ}

/-- `exp ๐ : ๐ธ โ ๐ธ` is the exponential map determined by the action of `๐` on `๐ธ`.
It is defined as the sum of the `formal_multilinear_series` `exp_series ๐ ๐ธ`.

Note that when `๐ธ = matrix n n ๐`, this is the **Matrix Exponential**; see
[`analysis.normed_space.matrix_exponential`](../matrix_exponential) for lemmas specific to that
case. -/
noncomputable def exp (x : ๐ธ) : ๐ธ :=
  (expSeries ๐ ๐ธ).Sum x

variable {๐}

theorem exp_series_apply_eq (x : ๐ธ) (n : โ) : (expSeries ๐ ๐ธ n fun _ => x) = (n !โปยน : ๐) โข x ^ n := by
  simp [โ expSeries]

theorem exp_series_apply_eq' (x : ๐ธ) : (fun n => expSeries ๐ ๐ธ n fun _ => x) = fun n => (n !โปยน : ๐) โข x ^ n :=
  funext (exp_series_apply_eq x)

theorem exp_series_sum_eq (x : ๐ธ) : (expSeries ๐ ๐ธ).Sum x = โ' n : โ, (n !โปยน : ๐) โข x ^ n :=
  tsum_congr fun n => exp_series_apply_eq x n

theorem exp_eq_tsum : exp ๐ = fun x : ๐ธ => โ' n : โ, (n !โปยน : ๐) โข x ^ n :=
  funext exp_series_sum_eq

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (n ยซexpr โ ยป ({0} : finset exprโ()))
@[simp]
theorem exp_zero [T2Space ๐ธ] : exp ๐ (0 : ๐ธ) = 1 := by
  suffices (fun x : ๐ธ => โ' n : โ, (n !โปยน : ๐) โข x ^ n) 0 = โ' n : โ, if n = 0 then 1 else 0 by
    have key : โ (n) (_ : n โ ({0} : Finset โ)), (if n = 0 then (1 : ๐ธ) else 0) = 0 := fun n hn =>
      if_neg (finset.not_mem_singleton.mp hn)
    rw [exp_eq_tsum, this, tsum_eq_sum key, Finset.sum_singleton]
    simp
  refine' tsum_congr fun n => _
  split_ifs with h h <;> simp [โ h]

@[simp]
theorem exp_op [T2Space ๐ธ] (x : ๐ธ) : exp ๐ (MulOpposite.op x) = MulOpposite.op (exp ๐ x) := by
  simp_rw [exp, exp_series_sum_eq, โ MulOpposite.op_pow, โ MulOpposite.op_smul, tsum_op]

@[simp]
theorem exp_unop [T2Space ๐ธ] (x : ๐ธแตแตแต) : exp ๐ (MulOpposite.unop x) = MulOpposite.unop (exp ๐ x) := by
  simp_rw [exp, exp_series_sum_eq, โ MulOpposite.unop_pow, โ MulOpposite.unop_smul, tsum_unop]

theorem star_exp [T2Space ๐ธ] [StarRing ๐ธ] [HasContinuousStar ๐ธ] (x : ๐ธ) : star (exp ๐ x) = exp ๐ (star x) := by
  simp_rw [exp_eq_tsum, โ star_pow, โ star_inv_nat_cast_smul, โ tsum_star]

variable (๐)

theorem Commute.exp_right [T2Space ๐ธ] {x y : ๐ธ} (h : Commute x y) : Commute x (exp ๐ y) := by
  rw [exp_eq_tsum]
  exact Commute.tsum_right x fun n => (h.pow_right n).smul_right _

theorem Commute.exp_left [T2Space ๐ธ] {x y : ๐ธ} (h : Commute x y) : Commute (exp ๐ x) y :=
  (h.symm.exp_right ๐).symm

theorem Commute.exp [T2Space ๐ธ] {x y : ๐ธ} (h : Commute x y) : Commute (exp ๐ x) (exp ๐ y) :=
  (h.exp_left _).exp_right _

end TopologicalAlgebra

section TopologicalDivisionAlgebra

variable {๐ ๐ธ : Type _} [Field ๐] [DivisionRing ๐ธ] [Algebra ๐ ๐ธ] [TopologicalSpace ๐ธ] [TopologicalRing ๐ธ]

theorem exp_series_apply_eq_div (x : ๐ธ) (n : โ) : (expSeries ๐ ๐ธ n fun _ => x) = x ^ n / n ! := by
  rw [div_eq_mul_inv, โ (Nat.cast_commute n ! (x ^ n)).inv_leftโ.Eq, โ smul_eq_mul, exp_series_apply_eq,
    inv_nat_cast_smul_eq _ _ _ _]

theorem exp_series_apply_eq_div' (x : ๐ธ) : (fun n => expSeries ๐ ๐ธ n fun _ => x) = fun n => x ^ n / n ! :=
  funext (exp_series_apply_eq_div x)

theorem exp_series_sum_eq_div (x : ๐ธ) : (expSeries ๐ ๐ธ).Sum x = โ' n : โ, x ^ n / n ! :=
  tsum_congr (exp_series_apply_eq_div x)

theorem exp_eq_tsum_div : exp ๐ = fun x : ๐ธ => โ' n : โ, x ^ n / n ! :=
  funext exp_series_sum_eq_div

end TopologicalDivisionAlgebra

section Normed

section AnyFieldAnyAlgebra

variable {๐ ๐ธ ๐น : Type _} [NondiscreteNormedField ๐]

variable [NormedRing ๐ธ] [NormedRing ๐น] [NormedAlgebra ๐ ๐ธ] [NormedAlgebra ๐ ๐น]

theorem norm_exp_series_summable_of_mem_ball (x : ๐ธ) (hx : x โ Emetric.Ball (0 : ๐ธ) (expSeries ๐ ๐ธ).radius) :
    Summable fun n => โฅexpSeries ๐ ๐ธ n fun _ => xโฅ :=
  (expSeries ๐ ๐ธ).summable_norm_apply hx

theorem norm_exp_series_summable_of_mem_ball' (x : ๐ธ) (hx : x โ Emetric.Ball (0 : ๐ธ) (expSeries ๐ ๐ธ).radius) :
    Summable fun n => โฅ(n !โปยน : ๐) โข x ^ nโฅ := by
  change Summable (norm โ _)
  rw [โ exp_series_apply_eq']
  exact norm_exp_series_summable_of_mem_ball x hx

section CompleteAlgebra

variable [CompleteSpace ๐ธ]

theorem exp_series_summable_of_mem_ball (x : ๐ธ) (hx : x โ Emetric.Ball (0 : ๐ธ) (expSeries ๐ ๐ธ).radius) :
    Summable fun n => expSeries ๐ ๐ธ n fun _ => x :=
  summable_of_summable_norm (norm_exp_series_summable_of_mem_ball x hx)

theorem exp_series_summable_of_mem_ball' (x : ๐ธ) (hx : x โ Emetric.Ball (0 : ๐ธ) (expSeries ๐ ๐ธ).radius) :
    Summable fun n => (n !โปยน : ๐) โข x ^ n :=
  summable_of_summable_norm (norm_exp_series_summable_of_mem_ball' x hx)

theorem exp_series_has_sum_exp_of_mem_ball (x : ๐ธ) (hx : x โ Emetric.Ball (0 : ๐ธ) (expSeries ๐ ๐ธ).radius) :
    HasSum (fun n => expSeries ๐ ๐ธ n fun _ => x) (exp ๐ x) :=
  FormalMultilinearSeries.has_sum (expSeries ๐ ๐ธ) hx

theorem exp_series_has_sum_exp_of_mem_ball' (x : ๐ธ) (hx : x โ Emetric.Ball (0 : ๐ธ) (expSeries ๐ ๐ธ).radius) :
    HasSum (fun n => (n !โปยน : ๐) โข x ^ n) (exp ๐ x) := by
  rw [โ exp_series_apply_eq']
  exact exp_series_has_sum_exp_of_mem_ball x hx

theorem has_fpower_series_on_ball_exp_of_radius_pos (h : 0 < (expSeries ๐ ๐ธ).radius) :
    HasFpowerSeriesOnBall (exp ๐) (expSeries ๐ ๐ธ) 0 (expSeries ๐ ๐ธ).radius :=
  (expSeries ๐ ๐ธ).HasFpowerSeriesOnBall h

theorem has_fpower_series_at_exp_zero_of_radius_pos (h : 0 < (expSeries ๐ ๐ธ).radius) :
    HasFpowerSeriesAt (exp ๐) (expSeries ๐ ๐ธ) 0 :=
  (has_fpower_series_on_ball_exp_of_radius_pos h).HasFpowerSeriesAt

theorem continuous_on_exp : ContinuousOn (exp ๐ : ๐ธ โ ๐ธ) (Emetric.Ball 0 (expSeries ๐ ๐ธ).radius) :=
  FormalMultilinearSeries.continuous_on

theorem analytic_at_exp_of_mem_ball (x : ๐ธ) (hx : x โ Emetric.Ball (0 : ๐ธ) (expSeries ๐ ๐ธ).radius) :
    AnalyticAt ๐ (exp ๐) x := by
  by_cases' h : (expSeries ๐ ๐ธ).radius = 0
  ยท rw [h] at hx
    exact (Ennreal.not_lt_zero hx).elim
    
  ยท have h := pos_iff_ne_zero.mpr h
    exact (has_fpower_series_on_ball_exp_of_radius_pos h).analytic_at_of_mem hx
    

/-- In a Banach-algebra `๐ธ` over a normed field `๐` of characteristic zero, if `x` and `y` are
in the disk of convergence and commute, then `exp ๐ (x + y) = (exp ๐ x) * (exp ๐ y)`. -/
theorem exp_add_of_commute_of_mem_ball [CharZero ๐] {x y : ๐ธ} (hxy : Commute x y)
    (hx : x โ Emetric.Ball (0 : ๐ธ) (expSeries ๐ ๐ธ).radius) (hy : y โ Emetric.Ball (0 : ๐ธ) (expSeries ๐ ๐ธ).radius) :
    exp ๐ (x + y) = exp ๐ x * exp ๐ y := by
  rw [exp_eq_tsum,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (norm_exp_series_summable_of_mem_ball' x hx)
      (norm_exp_series_summable_of_mem_ball' y hy)]
  dsimp' only
  conv_lhs => congr ext rw [hxy.add_pow' _, Finset.smul_sum]
  refine' tsum_congr fun n => (Finset.sum_congr rfl) fun kl hkl => _
  rw [nsmul_eq_smul_cast ๐, smul_smul, smul_mul_smul, โ finset.nat.mem_antidiagonal.mp hkl, Nat.cast_add_choose,
    finset.nat.mem_antidiagonal.mp hkl]
  congr 1
  have : (n ! : ๐) โ? 0 := nat.cast_ne_zero.mpr n.factorial_ne_zero
  field_simp [โ this]

/-- `exp ๐ x` has explicit two-sided inverse `exp ๐ (-x)`. -/
noncomputable def invertibleExpOfMemBall [CharZero ๐] {x : ๐ธ} (hx : x โ Emetric.Ball (0 : ๐ธ) (expSeries ๐ ๐ธ).radius) :
    Invertible (exp ๐ x) where
  invOf := exp ๐ (-x)
  inv_of_mul_self := by
    have hnx : -x โ Emetric.Ball (0 : ๐ธ) (expSeries ๐ ๐ธ).radius := by
      rw [Emetric.mem_ball, โ neg_zero, edist_neg_neg]
      exact hx
    rw [โ exp_add_of_commute_of_mem_ball (Commute.neg_left <| Commute.refl x) hnx hx, neg_add_selfโ, exp_zero]
  mul_inv_of_self := by
    have hnx : -x โ Emetric.Ball (0 : ๐ธ) (expSeries ๐ ๐ธ).radius := by
      rw [Emetric.mem_ball, โ neg_zero, edist_neg_neg]
      exact hx
    rw [โ exp_add_of_commute_of_mem_ball (Commute.neg_right <| Commute.refl x) hx hnx, add_neg_selfโ, exp_zero]

theorem is_unit_exp_of_mem_ball [CharZero ๐] {x : ๐ธ} (hx : x โ Emetric.Ball (0 : ๐ธ) (expSeries ๐ ๐ธ).radius) :
    IsUnit (exp ๐ x) :=
  @is_unit_of_invertible _ _ _ (invertibleExpOfMemBall hx)

theorem inv_of_exp_of_mem_ball [CharZero ๐] {x : ๐ธ} (hx : x โ Emetric.Ball (0 : ๐ธ) (expSeries ๐ ๐ธ).radius)
    [Invertible (exp ๐ x)] : โ (exp ๐ x) = exp ๐ (-x) := by
  let this := invertibleExpOfMemBall hx
  convert (rfl : โ (exp ๐ x) = _)

/-- Any continuous ring homomorphism commutes with `exp`. -/
theorem map_exp_of_mem_ball {F} [RingHomClass F ๐ธ ๐น] (f : F) (hf : Continuous f) (x : ๐ธ)
    (hx : x โ Emetric.Ball (0 : ๐ธ) (expSeries ๐ ๐ธ).radius) : f (exp ๐ x) = exp ๐ (f x) := by
  rw [exp_eq_tsum, exp_eq_tsum]
  refine' ((exp_series_summable_of_mem_ball' _ hx).HasSum.map f hf).tsum_eq.symm.trans _
  dsimp' only [โ Function.comp]
  simp_rw [one_div, map_inv_nat_cast_smul f ๐ ๐, map_pow]

end CompleteAlgebra

theorem algebra_map_exp_comm_of_mem_ball [CompleteSpace ๐] (x : ๐)
    (hx : x โ Emetric.Ball (0 : ๐) (expSeries ๐ ๐).radius) : algebraMap ๐ ๐ธ (exp ๐ x) = exp ๐ (algebraMap ๐ ๐ธ x) :=
  map_exp_of_mem_ball _ (algebraMapClm _ _).Continuous _ hx

end AnyFieldAnyAlgebra

section AnyFieldDivisionAlgebra

variable {๐ ๐ธ : Type _} [NondiscreteNormedField ๐] [NormedDivisionRing ๐ธ] [NormedAlgebra ๐ ๐ธ]

variable (๐)

theorem norm_exp_series_div_summable_of_mem_ball (x : ๐ธ) (hx : x โ Emetric.Ball (0 : ๐ธ) (expSeries ๐ ๐ธ).radius) :
    Summable fun n => โฅx ^ n / n !โฅ := by
  change Summable (norm โ _)
  rw [โ exp_series_apply_eq_div' x]
  exact norm_exp_series_summable_of_mem_ball x hx

theorem exp_series_div_summable_of_mem_ball [CompleteSpace ๐ธ] (x : ๐ธ)
    (hx : x โ Emetric.Ball (0 : ๐ธ) (expSeries ๐ ๐ธ).radius) : Summable fun n => x ^ n / n ! :=
  summable_of_summable_norm (norm_exp_series_div_summable_of_mem_ball ๐ x hx)

theorem exp_series_div_has_sum_exp_of_mem_ball [CompleteSpace ๐ธ] (x : ๐ธ)
    (hx : x โ Emetric.Ball (0 : ๐ธ) (expSeries ๐ ๐ธ).radius) : HasSum (fun n => x ^ n / n !) (exp ๐ x) := by
  rw [โ exp_series_apply_eq_div' x]
  exact exp_series_has_sum_exp_of_mem_ball x hx

variable {๐}

theorem exp_neg_of_mem_ball [CharZero ๐] [CompleteSpace ๐ธ] {x : ๐ธ}
    (hx : x โ Emetric.Ball (0 : ๐ธ) (expSeries ๐ ๐ธ).radius) : exp ๐ (-x) = (exp ๐ x)โปยน := by
  let this := invertibleExpOfMemBall hx
  exact inv_of_eq_inv (exp ๐ x)

end AnyFieldDivisionAlgebra

section AnyFieldCommAlgebra

variable {๐ ๐ธ : Type _} [NondiscreteNormedField ๐] [NormedCommRing ๐ธ] [NormedAlgebra ๐ ๐ธ] [CompleteSpace ๐ธ]

/-- In a commutative Banach-algebra `๐ธ` over a normed field `๐` of characteristic zero,
`exp ๐ (x+y) = (exp ๐ x) * (exp ๐ y)` for all `x`, `y` in the disk of convergence. -/
theorem exp_add_of_mem_ball [CharZero ๐] {x y : ๐ธ} (hx : x โ Emetric.Ball (0 : ๐ธ) (expSeries ๐ ๐ธ).radius)
    (hy : y โ Emetric.Ball (0 : ๐ธ) (expSeries ๐ ๐ธ).radius) : exp ๐ (x + y) = exp ๐ x * exp ๐ y :=
  exp_add_of_commute_of_mem_ball (Commute.all x y) hx hy

end AnyFieldCommAlgebra

section IsROrC

section AnyAlgebra

variable (๐ ๐ธ ๐น : Type _) [IsROrC ๐] [NormedRing ๐ธ] [NormedAlgebra ๐ ๐ธ]

variable [NormedRing ๐น] [NormedAlgebra ๐ ๐น]

/-- In a normed algebra `๐ธ` over `๐ = โ` or `๐ = โ`, the series defining the exponential map
has an infinite radius of convergence. -/
theorem exp_series_radius_eq_top : (expSeries ๐ ๐ธ).radius = โ := by
  refine' (expSeries ๐ ๐ธ).radius_eq_top_of_summable_norm fun r => _
  refine' summable_of_norm_bounded_eventually _ (Real.summable_pow_div_factorial r) _
  filter_upwards [eventually_cofinite_ne 0] with n hn
  rw [norm_mul, norm_norm (expSeries ๐ ๐ธ n), expSeries, norm_smul, norm_inv, norm_pow, Nnreal.norm_eq, norm_eq_abs,
    abs_cast_nat, mul_comm, โ mul_assoc, โ div_eq_mul_inv]
  have : โฅContinuousMultilinearMap.mkPiAlgebraFin ๐ n ๐ธโฅ โค 1 :=
    norm_mk_pi_algebra_fin_le_of_pos (Nat.pos_of_ne_zeroโ hn)
  exact mul_le_of_le_one_right (div_nonneg (pow_nonneg r.coe_nonneg n) n !.cast_nonneg) this

theorem exp_series_radius_pos : 0 < (expSeries ๐ ๐ธ).radius := by
  rw [exp_series_radius_eq_top]
  exact WithTop.zero_lt_top

variable {๐ ๐ธ ๐น}

theorem norm_exp_series_summable (x : ๐ธ) : Summable fun n => โฅexpSeries ๐ ๐ธ n fun _ => xโฅ :=
  norm_exp_series_summable_of_mem_ball x ((exp_series_radius_eq_top ๐ ๐ธ).symm โธ edist_lt_top _ _)

theorem norm_exp_series_summable' (x : ๐ธ) : Summable fun n => โฅ(n !โปยน : ๐) โข x ^ nโฅ :=
  norm_exp_series_summable_of_mem_ball' x ((exp_series_radius_eq_top ๐ ๐ธ).symm โธ edist_lt_top _ _)

section CompleteAlgebra

variable [CompleteSpace ๐ธ]

theorem exp_series_summable (x : ๐ธ) : Summable fun n => expSeries ๐ ๐ธ n fun _ => x :=
  summable_of_summable_norm (norm_exp_series_summable x)

theorem exp_series_summable' (x : ๐ธ) : Summable fun n => (n !โปยน : ๐) โข x ^ n :=
  summable_of_summable_norm (norm_exp_series_summable' x)

theorem exp_series_has_sum_exp (x : ๐ธ) : HasSum (fun n => expSeries ๐ ๐ธ n fun _ => x) (exp ๐ x) :=
  exp_series_has_sum_exp_of_mem_ball x ((exp_series_radius_eq_top ๐ ๐ธ).symm โธ edist_lt_top _ _)

theorem exp_series_has_sum_exp' (x : ๐ธ) : HasSum (fun n => (n !โปยน : ๐) โข x ^ n) (exp ๐ x) :=
  exp_series_has_sum_exp_of_mem_ball' x ((exp_series_radius_eq_top ๐ ๐ธ).symm โธ edist_lt_top _ _)

theorem exp_has_fpower_series_on_ball : HasFpowerSeriesOnBall (exp ๐) (expSeries ๐ ๐ธ) 0 โ :=
  exp_series_radius_eq_top ๐ ๐ธ โธ has_fpower_series_on_ball_exp_of_radius_pos (exp_series_radius_pos _ _)

theorem exp_has_fpower_series_at_zero : HasFpowerSeriesAt (exp ๐) (expSeries ๐ ๐ธ) 0 :=
  exp_has_fpower_series_on_ball.HasFpowerSeriesAt

theorem exp_continuous : Continuous (exp ๐ : ๐ธ โ ๐ธ) := by
  rw [continuous_iff_continuous_on_univ, โ Metric.eball_top_eq_univ (0 : ๐ธ), โ exp_series_radius_eq_top ๐ ๐ธ]
  exact continuous_on_exp

theorem exp_analytic (x : ๐ธ) : AnalyticAt ๐ (exp ๐) x :=
  analytic_at_exp_of_mem_ball x ((exp_series_radius_eq_top ๐ ๐ธ).symm โธ edist_lt_top _ _)

/-- In a Banach-algebra `๐ธ` over `๐ = โ` or `๐ = โ`, if `x` and `y` commute, then
`exp ๐ (x+y) = (exp ๐ x) * (exp ๐ y)`. -/
theorem exp_add_of_commute {x y : ๐ธ} (hxy : Commute x y) : exp ๐ (x + y) = exp ๐ x * exp ๐ y :=
  exp_add_of_commute_of_mem_ball hxy ((exp_series_radius_eq_top ๐ ๐ธ).symm โธ edist_lt_top _ _)
    ((exp_series_radius_eq_top ๐ ๐ธ).symm โธ edist_lt_top _ _)

section

variable (๐)

/-- `exp ๐ x` has explicit two-sided inverse `exp ๐ (-x)`. -/
noncomputable def invertibleExp (x : ๐ธ) : Invertible (exp ๐ x) :=
  invertibleExpOfMemBall <| (exp_series_radius_eq_top ๐ ๐ธ).symm โธ edist_lt_top _ _

theorem is_unit_exp (x : ๐ธ) : IsUnit (exp ๐ x) :=
  is_unit_exp_of_mem_ball <| (exp_series_radius_eq_top ๐ ๐ธ).symm โธ edist_lt_top _ _

theorem inv_of_exp (x : ๐ธ) [Invertible (exp ๐ x)] : โ (exp ๐ x) = exp ๐ (-x) :=
  inv_of_exp_of_mem_ball <| (exp_series_radius_eq_top ๐ ๐ธ).symm โธ edist_lt_top _ _

theorem Ringโ.inverse_exp (x : ๐ธ) : Ring.inverse (exp ๐ x) = exp ๐ (-x) := by
  let this := invertibleExp ๐ x
  exact Ringโ.inverse_invertible _

end

/-- In a Banach-algebra `๐ธ` over `๐ = โ` or `๐ = โ`, if a family of elements `f i` mutually
commute then `exp ๐ (โ i, f i) = โ i, exp ๐ (f i)`. -/
theorem exp_sum_of_commute {ฮน} (s : Finset ฮน) (f : ฮน โ ๐ธ) (h : โ, โ i โ s, โ, โ j โ s, โ, Commute (f i) (f j)) :
    exp ๐ (โ i in s, f i) = s.noncommProd (fun i => exp ๐ (f i)) fun i hi j hj => (h i hi j hj).exp ๐ := by
  classical
  induction' s using Finset.induction_on with a s ha ih
  ยท simp
    
  rw [Finset.noncomm_prod_insert_of_not_mem _ _ _ _ ha, Finset.sum_insert ha, exp_add_of_commute, ih]
  refine' Commute.sum_right _ _ _ _
  intro i hi
  exact h _ (Finset.mem_insert_self _ _) _ (Finset.mem_insert_of_mem hi)

theorem exp_nsmul (n : โ) (x : ๐ธ) : exp ๐ (n โข x) = exp ๐ x ^ n := by
  induction' n with n ih
  ยท rw [zero_smul, pow_zeroโ, exp_zero]
    
  ยท rw [succ_nsmul, pow_succโ, exp_add_of_commute ((Commute.refl x).smul_right n), ih]
    

variable (๐)

/-- Any continuous ring homomorphism commutes with `exp`. -/
theorem map_exp {F} [RingHomClass F ๐ธ ๐น] (f : F) (hf : Continuous f) (x : ๐ธ) : f (exp ๐ x) = exp ๐ (f x) :=
  map_exp_of_mem_ball f hf x <| (exp_series_radius_eq_top ๐ ๐ธ).symm โธ edist_lt_top _ _

theorem exp_smul {G} [Monoidโ G] [MulSemiringAction G ๐ธ] [HasContinuousConstSmul G ๐ธ] (g : G) (x : ๐ธ) :
    exp ๐ (g โข x) = g โข exp ๐ x :=
  (map_exp ๐ (MulSemiringAction.toRingHom G ๐ธ g) (continuous_const_smul _) x).symm

theorem exp_units_conj (y : ๐ธหฃ) (x : ๐ธ) : exp ๐ (y * x * โyโปยน : ๐ธ) = y * exp ๐ x * โyโปยน :=
  exp_smul _ (ConjAct.toConjAct y) x

theorem exp_units_conj' (y : ๐ธหฃ) (x : ๐ธ) : exp ๐ (โyโปยน * x * y) = โyโปยน * exp ๐ x * y :=
  exp_units_conj _ _ _

@[simp]
theorem Prod.fst_exp [CompleteSpace ๐น] (x : ๐ธ ร ๐น) : (exp ๐ x).fst = exp ๐ x.fst :=
  map_exp _ (RingHom.fst ๐ธ ๐น) continuous_fst x

@[simp]
theorem Prod.snd_exp [CompleteSpace ๐น] (x : ๐ธ ร ๐น) : (exp ๐ x).snd = exp ๐ x.snd :=
  map_exp _ (RingHom.snd ๐ธ ๐น) continuous_snd x

@[simp]
theorem Pi.exp_apply {ฮน : Type _} {๐ธ : ฮน โ Type _} [Fintype ฮน] [โ i, NormedRing (๐ธ i)] [โ i, NormedAlgebra ๐ (๐ธ i)]
    [โ i, CompleteSpace (๐ธ i)] (x : โ i, ๐ธ i) (i : ฮน) : exp ๐ x i = exp ๐ (x i) := by
  -- Lean struggles to infer this instance due to it wanting `[ฮ? i, semi_normed_ring (๐ธ i)]`
  let this : NormedAlgebra ๐ (โ i, ๐ธ i) := Pi.normedAlgebra _
  exact map_exp _ (Pi.evalRingHom ๐ธ i) (continuous_apply _) x

theorem Pi.exp_def {ฮน : Type _} {๐ธ : ฮน โ Type _} [Fintype ฮน] [โ i, NormedRing (๐ธ i)] [โ i, NormedAlgebra ๐ (๐ธ i)]
    [โ i, CompleteSpace (๐ธ i)] (x : โ i, ๐ธ i) : exp ๐ x = fun i => exp ๐ (x i) :=
  funext <| Pi.exp_apply ๐ x

theorem Function.update_exp {ฮน : Type _} {๐ธ : ฮน โ Type _} [Fintype ฮน] [DecidableEq ฮน] [โ i, NormedRing (๐ธ i)]
    [โ i, NormedAlgebra ๐ (๐ธ i)] [โ i, CompleteSpace (๐ธ i)] (x : โ i, ๐ธ i) (j : ฮน) (xj : ๐ธ j) :
    Function.update (exp ๐ x) j (exp ๐ xj) = exp ๐ (Function.update x j xj) := by
  ext i
  simp_rw [Pi.exp_def]
  exact (Function.apply_update (fun i => exp ๐) x j xj i).symm

end CompleteAlgebra

theorem algebra_map_exp_comm (x : ๐) : algebraMap ๐ ๐ธ (exp ๐ x) = exp ๐ (algebraMap ๐ ๐ธ x) :=
  algebra_map_exp_comm_of_mem_ball x <| (exp_series_radius_eq_top ๐ ๐).symm โธ edist_lt_top _ _

end AnyAlgebra

section DivisionAlgebra

variable {๐ ๐ธ : Type _} [IsROrC ๐] [NormedDivisionRing ๐ธ] [NormedAlgebra ๐ ๐ธ]

variable (๐)

theorem norm_exp_series_div_summable (x : ๐ธ) : Summable fun n => โฅx ^ n / n !โฅ :=
  norm_exp_series_div_summable_of_mem_ball ๐ x ((exp_series_radius_eq_top ๐ ๐ธ).symm โธ edist_lt_top _ _)

variable [CompleteSpace ๐ธ]

theorem exp_series_div_summable (x : ๐ธ) : Summable fun n => x ^ n / n ! :=
  summable_of_summable_norm (norm_exp_series_div_summable ๐ x)

theorem exp_series_div_has_sum_exp (x : ๐ธ) : HasSum (fun n => x ^ n / n !) (exp ๐ x) :=
  exp_series_div_has_sum_exp_of_mem_ball ๐ x ((exp_series_radius_eq_top ๐ ๐ธ).symm โธ edist_lt_top _ _)

variable {๐}

theorem exp_neg (x : ๐ธ) : exp ๐ (-x) = (exp ๐ x)โปยน :=
  exp_neg_of_mem_ball <| (exp_series_radius_eq_top ๐ ๐ธ).symm โธ edist_lt_top _ _

theorem exp_zsmul (z : โค) (x : ๐ธ) : exp ๐ (z โข x) = exp ๐ x ^ z := by
  obtain โจn, rfl | rflโฉ := z.eq_coe_or_neg
  ยท rw [zpow_coe_nat, coe_nat_zsmul, exp_nsmul]
    
  ยท rw [zpow_neg, zpow_coe_nat, neg_smul, exp_neg, coe_nat_zsmul, exp_nsmul]
    

theorem exp_conj (y : ๐ธ) (x : ๐ธ) (hy : y โ? 0) : exp ๐ (y * x * yโปยน) = y * exp ๐ x * yโปยน :=
  exp_units_conj _ (Units.mk0 y hy) x

theorem exp_conj' (y : ๐ธ) (x : ๐ธ) (hy : y โ? 0) : exp ๐ (yโปยน * x * y) = yโปยน * exp ๐ x * y :=
  exp_units_conj' _ (Units.mk0 y hy) x

end DivisionAlgebra

section CommAlgebra

variable {๐ ๐ธ : Type _} [IsROrC ๐] [NormedCommRing ๐ธ] [NormedAlgebra ๐ ๐ธ] [CompleteSpace ๐ธ]

/-- In a commutative Banach-algebra `๐ธ` over `๐ = โ` or `๐ = โ`,
`exp ๐ (x+y) = (exp ๐ x) * (exp ๐ y)`. -/
theorem exp_add {x y : ๐ธ} : exp ๐ (x + y) = exp ๐ x * exp ๐ y :=
  exp_add_of_mem_ball ((exp_series_radius_eq_top ๐ ๐ธ).symm โธ edist_lt_top _ _)
    ((exp_series_radius_eq_top ๐ ๐ธ).symm โธ edist_lt_top _ _)

/-- A version of `exp_sum_of_commute` for a commutative Banach-algebra. -/
theorem exp_sum {ฮน} (s : Finset ฮน) (f : ฮน โ ๐ธ) : exp ๐ (โ i in s, f i) = โ i in s, exp ๐ (f i) := by
  rw [exp_sum_of_commute, Finset.noncomm_prod_eq_prod]
  exact fun i hi j hj => Commute.all _ _

end CommAlgebra

end IsROrC

end Normed

section ScalarTower

variable (๐ ๐' ๐ธ : Type _) [Field ๐] [Field ๐'] [Ringโ ๐ธ] [Algebra ๐ ๐ธ] [Algebra ๐' ๐ธ] [TopologicalSpace ๐ธ]
  [TopologicalRing ๐ธ]

/-- If a normed ring `๐ธ` is a normed algebra over two fields, then they define the same
`exp_series` on `๐ธ`. -/
theorem exp_series_eq_exp_series (n : โ) (x : ๐ธ) : (expSeries ๐ ๐ธ n fun _ => x) = expSeries ๐' ๐ธ n fun _ => x := by
  rw [exp_series_apply_eq, exp_series_apply_eq, inv_nat_cast_smul_eq ๐ ๐']

/-- If a normed ring `๐ธ` is a normed algebra over two fields, then they define the same
exponential function on `๐ธ`. -/
theorem exp_eq_exp : (exp ๐ : ๐ธ โ ๐ธ) = exp ๐' := by
  ext
  rw [exp, exp]
  refine' tsum_congr fun n => _
  rw [exp_series_eq_exp_series ๐ ๐' ๐ธ n x]

theorem exp_โ_โ_eq_exp_โ_โ : (exp โ : โ โ โ) = exp โ :=
  exp_eq_exp โ โ โ

end ScalarTower

