/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathbin.Analysis.NormedSpace.Exponential
import Mathbin.Analysis.Calculus.FderivAnalytic
import Mathbin.Data.Complex.Exponential
import Mathbin.Topology.MetricSpace.CauSeqFilter

/-!
# Calculus results on exponential in a Banach algebra

In this file, we prove basic properties about the derivative of the exponential map `exp π`
in a Banach algebra `πΈ` over a field `π`. We keep them separate from the main file
`analysis/normed_space/exponential` in order to minimize dependencies.

## Main results

We prove most result for an arbitrary field `π`, and then specialize to `π = β` or `π = β`.

### General case

- `has_strict_fderiv_at_exp_zero_of_radius_pos` : `exp π` has strict FrΓ©chet-derivative
  `1 : πΈ βL[π] πΈ` at zero, as long as it converges on a neighborhood of zero
  (see also `has_strict_deriv_at_exp_zero_of_radius_pos` for the case `πΈ = π`)
- `has_strict_fderiv_at_exp_of_lt_radius` : if `π` has characteristic zero and `πΈ` is commutative,
  then given a point `x` in the disk of convergence, `exp π` as strict FrΓ©chet-derivative
  `exp π x β’ 1 : πΈ βL[π] πΈ` at x (see also `has_strict_deriv_at_exp_of_lt_radius` for the case
  `πΈ = π`)

### `π = β` or `π = β`

- `has_strict_fderiv_at_exp_zero` : `exp π` has strict FrΓ©chet-derivative `1 : πΈ βL[π] πΈ` at zero
  (see also `has_strict_deriv_at_exp_zero` for the case `πΈ = π`)
- `has_strict_fderiv_at_exp` : if `πΈ` is commutative, then given any point `x`, `exp π` as strict
  FrΓ©chet-derivative `exp π x β’ 1 : πΈ βL[π] πΈ` at x (see also `has_strict_deriv_at_exp` for the
  case `πΈ = π`)

### Compatibilty with `real.exp` and `complex.exp`

- `complex.exp_eq_exp_β` : `complex.exp = exp β β`
- `real.exp_eq_exp_β` : `real.exp = exp β β`

-/


open Filter IsROrC ContinuousMultilinearMap NormedField Asymptotics

open Nat TopologicalSpace BigOperators Ennreal

section AnyFieldAnyAlgebra

variable {π πΈ : Type _} [NondiscreteNormedField π] [NormedRing πΈ] [NormedAlgebra π πΈ] [CompleteSpace πΈ]

/-- The exponential in a Banach-algebra `πΈ` over a normed field `π` has strict FrΓ©chet-derivative
`1 : πΈ βL[π] πΈ` at zero, as long as it converges on a neighborhood of zero. -/
theorem has_strict_fderiv_at_exp_zero_of_radius_pos (h : 0 < (expSeries π πΈ).radius) :
    HasStrictFderivAt (exp π) (1 : πΈ βL[π] πΈ) 0 := by
  convert (has_fpower_series_at_exp_zero_of_radius_pos h).HasStrictFderivAt
  ext x
  change x = expSeries π πΈ 1 fun _ => x
  simp [β exp_series_apply_eq]

/-- The exponential in a Banach-algebra `πΈ` over a normed field `π` has FrΓ©chet-derivative
`1 : πΈ βL[π] πΈ` at zero, as long as it converges on a neighborhood of zero. -/
theorem has_fderiv_at_exp_zero_of_radius_pos (h : 0 < (expSeries π πΈ).radius) : HasFderivAt (exp π) (1 : πΈ βL[π] πΈ) 0 :=
  (has_strict_fderiv_at_exp_zero_of_radius_pos h).HasFderivAt

end AnyFieldAnyAlgebra

section AnyFieldCommAlgebra

variable {π πΈ : Type _} [NondiscreteNormedField π] [NormedCommRing πΈ] [NormedAlgebra π πΈ] [CompleteSpace πΈ]

/-- The exponential map in a commutative Banach-algebra `πΈ` over a normed field `π` of
characteristic zero has FrΓ©chet-derivative `exp π x β’ 1 : πΈ βL[π] πΈ` at any point `x` in the
disk of convergence. -/
theorem has_fderiv_at_exp_of_mem_ball [CharZero π] {x : πΈ} (hx : x β Emetric.Ball (0 : πΈ) (expSeries π πΈ).radius) :
    HasFderivAt (exp π) (exp π x β’ 1 : πΈ βL[π] πΈ) x := by
  have hpos : 0 < (expSeries π πΈ).radius := (zero_le _).trans_lt hx
  rw [has_fderiv_at_iff_is_o_nhds_zero]
  suffices
    (fun h => exp π x * (exp π (0 + h) - exp π 0 - ContinuousLinearMap.id π πΈ h)) =αΆ [π 0] fun h =>
      exp π (x + h) - exp π x - exp π x β’ ContinuousLinearMap.id π πΈ h
    by
    refine' (is_o.const_mul_left _ _).congr' this (eventually_eq.refl _ _)
    rw [β has_fderiv_at_iff_is_o_nhds_zero]
    exact has_fderiv_at_exp_zero_of_radius_pos hpos
  have : βαΆ  h in π (0 : πΈ), h β Emetric.Ball (0 : πΈ) (expSeries π πΈ).radius := Emetric.ball_mem_nhds _ hpos
  filter_upwards [this] with _ hh
  rw [exp_add_of_mem_ball hx hh, exp_zero, zero_addβ, ContinuousLinearMap.id_apply, smul_eq_mul]
  ring

/-- The exponential map in a commutative Banach-algebra `πΈ` over a normed field `π` of
characteristic zero has strict FrΓ©chet-derivative `exp π x β’ 1 : πΈ βL[π] πΈ` at any point `x` in
the disk of convergence. -/
theorem has_strict_fderiv_at_exp_of_mem_ball [CharZero π] {x : πΈ}
    (hx : x β Emetric.Ball (0 : πΈ) (expSeries π πΈ).radius) : HasStrictFderivAt (exp π) (exp π x β’ 1 : πΈ βL[π] πΈ) x :=
  let β¨p, hpβ© := analytic_at_exp_of_mem_ball x hx
  hp.HasFderivAt.unique (has_fderiv_at_exp_of_mem_ball hx) βΈ hp.HasStrictFderivAt

end AnyFieldCommAlgebra

section deriv

variable {π : Type _} [NondiscreteNormedField π] [CompleteSpace π]

/-- The exponential map in a complete normed field `π` of characteristic zero has strict derivative
`exp π x` at any point `x` in the disk of convergence. -/
theorem has_strict_deriv_at_exp_of_mem_ball [CharZero π] {x : π}
    (hx : x β Emetric.Ball (0 : π) (expSeries π π).radius) : HasStrictDerivAt (exp π) (exp π x) x := by
  simpa using (has_strict_fderiv_at_exp_of_mem_ball hx).HasStrictDerivAt

/-- The exponential map in a complete normed field `π` of characteristic zero has derivative
`exp π x` at any point `x` in the disk of convergence. -/
theorem has_deriv_at_exp_of_mem_ball [CharZero π] {x : π} (hx : x β Emetric.Ball (0 : π) (expSeries π π).radius) :
    HasDerivAt (exp π) (exp π x) x :=
  (has_strict_deriv_at_exp_of_mem_ball hx).HasDerivAt

/-- The exponential map in a complete normed field `π` of characteristic zero has strict derivative
`1` at zero, as long as it converges on a neighborhood of zero. -/
theorem has_strict_deriv_at_exp_zero_of_radius_pos (h : 0 < (expSeries π π).radius) :
    HasStrictDerivAt (exp π) (1 : π) 0 :=
  (has_strict_fderiv_at_exp_zero_of_radius_pos h).HasStrictDerivAt

/-- The exponential map in a complete normed field `π` of characteristic zero has derivative
`1` at zero, as long as it converges on a neighborhood of zero. -/
theorem has_deriv_at_exp_zero_of_radius_pos (h : 0 < (expSeries π π).radius) : HasDerivAt (exp π) (1 : π) 0 :=
  (has_strict_deriv_at_exp_zero_of_radius_pos h).HasDerivAt

end deriv

section IsROrCAnyAlgebra

variable {π πΈ : Type _} [IsROrC π] [NormedRing πΈ] [NormedAlgebra π πΈ] [CompleteSpace πΈ]

/-- The exponential in a Banach-algebra `πΈ` over `π = β` or `π = β` has strict FrΓ©chet-derivative
`1 : πΈ βL[π] πΈ` at zero. -/
theorem has_strict_fderiv_at_exp_zero : HasStrictFderivAt (exp π) (1 : πΈ βL[π] πΈ) 0 :=
  has_strict_fderiv_at_exp_zero_of_radius_pos (exp_series_radius_pos π πΈ)

/-- The exponential in a Banach-algebra `πΈ` over `π = β` or `π = β` has FrΓ©chet-derivative
`1 : πΈ βL[π] πΈ` at zero. -/
theorem has_fderiv_at_exp_zero : HasFderivAt (exp π) (1 : πΈ βL[π] πΈ) 0 :=
  has_strict_fderiv_at_exp_zero.HasFderivAt

end IsROrCAnyAlgebra

section IsROrCCommAlgebra

variable {π πΈ : Type _} [IsROrC π] [NormedCommRing πΈ] [NormedAlgebra π πΈ] [CompleteSpace πΈ]

/-- The exponential map in a commutative Banach-algebra `πΈ` over `π = β` or `π = β` has strict
FrΓ©chet-derivative `exp π x β’ 1 : πΈ βL[π] πΈ` at any point `x`. -/
theorem has_strict_fderiv_at_exp {x : πΈ} : HasStrictFderivAt (exp π) (exp π x β’ 1 : πΈ βL[π] πΈ) x :=
  has_strict_fderiv_at_exp_of_mem_ball ((exp_series_radius_eq_top π πΈ).symm βΈ edist_lt_top _ _)

/-- The exponential map in a commutative Banach-algebra `πΈ` over `π = β` or `π = β` has
FrΓ©chet-derivative `exp π x β’ 1 : πΈ βL[π] πΈ` at any point `x`. -/
theorem has_fderiv_at_exp {x : πΈ} : HasFderivAt (exp π) (exp π x β’ 1 : πΈ βL[π] πΈ) x :=
  has_strict_fderiv_at_exp.HasFderivAt

end IsROrCCommAlgebra

section DerivROrC

variable {π : Type _} [IsROrC π]

/-- The exponential map in `π = β` or `π = β` has strict derivative `exp π x` at any point
`x`. -/
theorem has_strict_deriv_at_exp {x : π} : HasStrictDerivAt (exp π) (exp π x) x :=
  has_strict_deriv_at_exp_of_mem_ball ((exp_series_radius_eq_top π π).symm βΈ edist_lt_top _ _)

/-- The exponential map in `π = β` or `π = β` has derivative `exp π x` at any point `x`. -/
theorem has_deriv_at_exp {x : π} : HasDerivAt (exp π) (exp π x) x :=
  has_strict_deriv_at_exp.HasDerivAt

/-- The exponential map in `π = β` or `π = β` has strict derivative `1` at zero. -/
theorem has_strict_deriv_at_exp_zero : HasStrictDerivAt (exp π) (1 : π) 0 :=
  has_strict_deriv_at_exp_zero_of_radius_pos (exp_series_radius_pos π π)

/-- The exponential map in `π = β` or `π = β` has derivative `1` at zero. -/
theorem has_deriv_at_exp_zero : HasDerivAt (exp π) (1 : π) 0 :=
  has_strict_deriv_at_exp_zero.HasDerivAt

end DerivROrC

section Complex

theorem Complex.exp_eq_exp_β : Complex.exp = exp β := by
  refine' funext fun x => _
  rw [Complex.exp, exp_eq_tsum_div]
  exact tendsto_nhds_unique x.exp'.tendsto_limit (exp_series_div_summable β x).HasSum.tendsto_sum_nat

end Complex

section Real

theorem Real.exp_eq_exp_β : Real.exp = exp β := by
  refine' funext fun x => _
  rw [Real.exp, Complex.exp_eq_exp_β, β exp_β_β_eq_exp_β_β, exp_eq_tsum, exp_eq_tsum_div, β re_to_complex, β
    re_clm_apply, re_clm.map_tsum (exp_series_summable' (x : β))]
  refine' tsum_congr fun n => _
  rw [re_clm.map_smul, β Complex.of_real_pow, re_clm_apply, re_to_complex, Complex.of_real_re, smul_eq_mul,
    div_eq_inv_mul]

end Real

