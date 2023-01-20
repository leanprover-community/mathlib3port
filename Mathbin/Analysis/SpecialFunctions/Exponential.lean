/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker

! This file was ported from Lean 3 source module analysis.special_functions.exponential
! leanprover-community/mathlib commit 1126441d6bccf98c81214a0780c73d499f6721fe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.NormedSpace.Exponential
import Mathbin.Analysis.Calculus.FderivAnalytic
import Mathbin.Data.Complex.Exponential
import Mathbin.Topology.MetricSpace.CauSeqFilter

/-!
# Calculus results on exponential in a Banach algebra

In this file, we prove basic properties about the derivative of the exponential map `exp 𝕂`
in a Banach algebra `𝔸` over a field `𝕂`. We keep them separate from the main file
`analysis/normed_space/exponential` in order to minimize dependencies.

## Main results

We prove most result for an arbitrary field `𝕂`, and then specialize to `𝕂 = ℝ` or `𝕂 = ℂ`.

### General case

- `has_strict_fderiv_at_exp_zero_of_radius_pos` : `exp 𝕂` has strict Fréchet-derivative
  `1 : 𝔸 →L[𝕂] 𝔸` at zero, as long as it converges on a neighborhood of zero
  (see also `has_strict_deriv_at_exp_zero_of_radius_pos` for the case `𝔸 = 𝕂`)
- `has_strict_fderiv_at_exp_of_lt_radius` : if `𝕂` has characteristic zero and `𝔸` is commutative,
  then given a point `x` in the disk of convergence, `exp 𝕂` as strict Fréchet-derivative
  `exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸` at x (see also `has_strict_deriv_at_exp_of_lt_radius` for the case
  `𝔸 = 𝕂`)

### `𝕂 = ℝ` or `𝕂 = ℂ`

- `has_strict_fderiv_at_exp_zero` : `exp 𝕂` has strict Fréchet-derivative `1 : 𝔸 →L[𝕂] 𝔸` at zero
  (see also `has_strict_deriv_at_exp_zero` for the case `𝔸 = 𝕂`)
- `has_strict_fderiv_at_exp` : if `𝔸` is commutative, then given any point `x`, `exp 𝕂` as strict
  Fréchet-derivative `exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸` at x (see also `has_strict_deriv_at_exp` for the
  case `𝔸 = 𝕂`)

### Compatibilty with `real.exp` and `complex.exp`

- `complex.exp_eq_exp_ℂ` : `complex.exp = exp ℂ ℂ`
- `real.exp_eq_exp_ℝ` : `real.exp = exp ℝ ℝ`

-/


open Filter IsROrC ContinuousMultilinearMap NormedField Asymptotics

open Nat TopologicalSpace BigOperators Ennreal

section AnyFieldAnyAlgebra

variable {𝕂 𝔸 : Type _} [NontriviallyNormedField 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  [CompleteSpace 𝔸]

/-- The exponential in a Banach-algebra `𝔸` over a normed field `𝕂` has strict Fréchet-derivative
`1 : 𝔸 →L[𝕂] 𝔸` at zero, as long as it converges on a neighborhood of zero. -/
theorem hasStrictFderivAtExpZeroOfRadiusPos (h : 0 < (expSeries 𝕂 𝔸).radius) :
    HasStrictFderivAt (exp 𝕂) (1 : 𝔸 →L[𝕂] 𝔸) 0 :=
  by
  convert (hasFpowerSeriesAtExpZeroOfRadiusPos h).HasStrictFderivAt
  ext x
  change x = expSeries 𝕂 𝔸 1 fun _ => x
  simp [exp_series_apply_eq]
#align has_strict_fderiv_at_exp_zero_of_radius_pos hasStrictFderivAtExpZeroOfRadiusPos

/-- The exponential in a Banach-algebra `𝔸` over a normed field `𝕂` has Fréchet-derivative
`1 : 𝔸 →L[𝕂] 𝔸` at zero, as long as it converges on a neighborhood of zero. -/
theorem hasFderivAtExpZeroOfRadiusPos (h : 0 < (expSeries 𝕂 𝔸).radius) :
    HasFderivAt (exp 𝕂) (1 : 𝔸 →L[𝕂] 𝔸) 0 :=
  (hasStrictFderivAtExpZeroOfRadiusPos h).HasFderivAt
#align has_fderiv_at_exp_zero_of_radius_pos hasFderivAtExpZeroOfRadiusPos

end AnyFieldAnyAlgebra

section AnyFieldCommAlgebra

variable {𝕂 𝔸 : Type _} [NontriviallyNormedField 𝕂] [NormedCommRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  [CompleteSpace 𝔸]

/-- The exponential map in a commutative Banach-algebra `𝔸` over a normed field `𝕂` of
characteristic zero has Fréchet-derivative `exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸` at any point `x` in the
disk of convergence. -/
theorem hasFderivAtExpOfMemBall [CharZero 𝕂] {x : 𝔸}
    (hx : x ∈ Emetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasFderivAt (exp 𝕂) (exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸) x :=
  by
  have hpos : 0 < (expSeries 𝕂 𝔸).radius := (zero_le _).trans_lt hx
  rw [has_fderiv_at_iff_is_o_nhds_zero]
  suffices
    (fun h => exp 𝕂 x * (exp 𝕂 (0 + h) - exp 𝕂 0 - ContinuousLinearMap.id 𝕂 𝔸 h)) =ᶠ[𝓝 0] fun h =>
      exp 𝕂 (x + h) - exp 𝕂 x - exp 𝕂 x • ContinuousLinearMap.id 𝕂 𝔸 h
    by
    refine' (is_o.const_mul_left _ _).congr' this (eventually_eq.refl _ _)
    rw [← has_fderiv_at_iff_is_o_nhds_zero]
    exact hasFderivAtExpZeroOfRadiusPos hpos
  have : ∀ᶠ h in 𝓝 (0 : 𝔸), h ∈ Emetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius :=
    Emetric.ball_mem_nhds _ hpos
  filter_upwards [this] with _ hh
  rw [exp_add_of_mem_ball hx hh, exp_zero, zero_add, ContinuousLinearMap.id_apply, smul_eq_mul]
  ring
#align has_fderiv_at_exp_of_mem_ball hasFderivAtExpOfMemBall

/-- The exponential map in a commutative Banach-algebra `𝔸` over a normed field `𝕂` of
characteristic zero has strict Fréchet-derivative `exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸` at any point `x` in
the disk of convergence. -/
theorem hasStrictFderivAtExpOfMemBall [CharZero 𝕂] {x : 𝔸}
    (hx : x ∈ Emetric.ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasStrictFderivAt (exp 𝕂) (exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸) x :=
  let ⟨p, hp⟩ := analytic_at_exp_of_mem_ball x hx
  hp.HasFderivAt.unique (hasFderivAtExpOfMemBall hx) ▸ hp.HasStrictFderivAt
#align has_strict_fderiv_at_exp_of_mem_ball hasStrictFderivAtExpOfMemBall

end AnyFieldCommAlgebra

section deriv

variable {𝕂 : Type _} [NontriviallyNormedField 𝕂] [CompleteSpace 𝕂]

/-- The exponential map in a complete normed field `𝕂` of characteristic zero has strict derivative
`exp 𝕂 x` at any point `x` in the disk of convergence. -/
theorem has_strict_deriv_at_exp_of_mem_ball [CharZero 𝕂] {x : 𝕂}
    (hx : x ∈ Emetric.ball (0 : 𝕂) (expSeries 𝕂 𝕂).radius) : HasStrictDerivAt (exp 𝕂) (exp 𝕂 x) x :=
  by simpa using (hasStrictFderivAtExpOfMemBall hx).HasStrictDerivAt
#align has_strict_deriv_at_exp_of_mem_ball has_strict_deriv_at_exp_of_mem_ball

/-- The exponential map in a complete normed field `𝕂` of characteristic zero has derivative
`exp 𝕂 x` at any point `x` in the disk of convergence. -/
theorem has_deriv_at_exp_of_mem_ball [CharZero 𝕂] {x : 𝕂}
    (hx : x ∈ Emetric.ball (0 : 𝕂) (expSeries 𝕂 𝕂).radius) : HasDerivAt (exp 𝕂) (exp 𝕂 x) x :=
  (has_strict_deriv_at_exp_of_mem_ball hx).HasDerivAt
#align has_deriv_at_exp_of_mem_ball has_deriv_at_exp_of_mem_ball

/-- The exponential map in a complete normed field `𝕂` of characteristic zero has strict derivative
`1` at zero, as long as it converges on a neighborhood of zero. -/
theorem has_strict_deriv_at_exp_zero_of_radius_pos (h : 0 < (expSeries 𝕂 𝕂).radius) :
    HasStrictDerivAt (exp 𝕂) (1 : 𝕂) 0 :=
  (hasStrictFderivAtExpZeroOfRadiusPos h).HasStrictDerivAt
#align has_strict_deriv_at_exp_zero_of_radius_pos has_strict_deriv_at_exp_zero_of_radius_pos

/-- The exponential map in a complete normed field `𝕂` of characteristic zero has derivative
`1` at zero, as long as it converges on a neighborhood of zero. -/
theorem has_deriv_at_exp_zero_of_radius_pos (h : 0 < (expSeries 𝕂 𝕂).radius) :
    HasDerivAt (exp 𝕂) (1 : 𝕂) 0 :=
  (has_strict_deriv_at_exp_zero_of_radius_pos h).HasDerivAt
#align has_deriv_at_exp_zero_of_radius_pos has_deriv_at_exp_zero_of_radius_pos

end deriv

section IsROrCAnyAlgebra

variable {𝕂 𝔸 : Type _} [IsROrC 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-- The exponential in a Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ` has strict Fréchet-derivative
`1 : 𝔸 →L[𝕂] 𝔸` at zero. -/
theorem hasStrictFderivAtExpZero : HasStrictFderivAt (exp 𝕂) (1 : 𝔸 →L[𝕂] 𝔸) 0 :=
  hasStrictFderivAtExpZeroOfRadiusPos (exp_series_radius_pos 𝕂 𝔸)
#align has_strict_fderiv_at_exp_zero hasStrictFderivAtExpZero

/-- The exponential in a Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ` has Fréchet-derivative
`1 : 𝔸 →L[𝕂] 𝔸` at zero. -/
theorem hasFderivAtExpZero : HasFderivAt (exp 𝕂) (1 : 𝔸 →L[𝕂] 𝔸) 0 :=
  hasStrictFderivAtExpZero.HasFderivAt
#align has_fderiv_at_exp_zero hasFderivAtExpZero

end IsROrCAnyAlgebra

section IsROrCCommAlgebra

variable {𝕂 𝔸 : Type _} [IsROrC 𝕂] [NormedCommRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-- The exponential map in a commutative Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ` has strict
Fréchet-derivative `exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸` at any point `x`. -/
theorem hasStrictFderivAtExp {x : 𝔸} : HasStrictFderivAt (exp 𝕂) (exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸) x :=
  hasStrictFderivAtExpOfMemBall ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
#align has_strict_fderiv_at_exp hasStrictFderivAtExp

/-- The exponential map in a commutative Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ` has
Fréchet-derivative `exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸` at any point `x`. -/
theorem hasFderivAtExp {x : 𝔸} : HasFderivAt (exp 𝕂) (exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸) x :=
  hasStrictFderivAtExp.HasFderivAt
#align has_fderiv_at_exp hasFderivAtExp

end IsROrCCommAlgebra

section DerivROrC

variable {𝕂 : Type _} [IsROrC 𝕂]

/-- The exponential map in `𝕂 = ℝ` or `𝕂 = ℂ` has strict derivative `exp 𝕂 x` at any point
`x`. -/
theorem has_strict_deriv_at_exp {x : 𝕂} : HasStrictDerivAt (exp 𝕂) (exp 𝕂 x) x :=
  has_strict_deriv_at_exp_of_mem_ball ((exp_series_radius_eq_top 𝕂 𝕂).symm ▸ edist_lt_top _ _)
#align has_strict_deriv_at_exp has_strict_deriv_at_exp

/-- The exponential map in `𝕂 = ℝ` or `𝕂 = ℂ` has derivative `exp 𝕂 x` at any point `x`. -/
theorem has_deriv_at_exp {x : 𝕂} : HasDerivAt (exp 𝕂) (exp 𝕂 x) x :=
  has_strict_deriv_at_exp.HasDerivAt
#align has_deriv_at_exp has_deriv_at_exp

/-- The exponential map in `𝕂 = ℝ` or `𝕂 = ℂ` has strict derivative `1` at zero. -/
theorem has_strict_deriv_at_exp_zero : HasStrictDerivAt (exp 𝕂) (1 : 𝕂) 0 :=
  has_strict_deriv_at_exp_zero_of_radius_pos (exp_series_radius_pos 𝕂 𝕂)
#align has_strict_deriv_at_exp_zero has_strict_deriv_at_exp_zero

/-- The exponential map in `𝕂 = ℝ` or `𝕂 = ℂ` has derivative `1` at zero. -/
theorem has_deriv_at_exp_zero : HasDerivAt (exp 𝕂) (1 : 𝕂) 0 :=
  has_strict_deriv_at_exp_zero.HasDerivAt
#align has_deriv_at_exp_zero has_deriv_at_exp_zero

end DerivROrC

section Complex

theorem Complex.exp_eq_exp_ℂ : Complex.exp = exp ℂ :=
  by
  refine' funext fun x => _
  rw [Complex.exp, exp_eq_tsum_div]
  exact
    tendsto_nhds_unique x.exp'.tendsto_limit (exp_series_div_summable ℝ x).HasSum.tendsto_sum_nat
#align complex.exp_eq_exp_ℂ Complex.exp_eq_exp_ℂ

end Complex

section Real

theorem Real.exp_eq_exp_ℝ : Real.exp = exp ℝ :=
  by
  refine' funext fun x => _
  rw [Real.exp, Complex.exp_eq_exp_ℂ, ← exp_ℝ_ℂ_eq_exp_ℂ_ℂ, exp_eq_tsum, exp_eq_tsum_div, ←
    re_to_complex, ← re_clm_apply, re_clm.map_tsum (exp_series_summable' (x : ℂ))]
  refine' tsum_congr fun n => _
  rw [re_clm.map_smul, ← Complex.of_real_pow, re_clm_apply, re_to_complex, Complex.of_real_re,
    smul_eq_mul, div_eq_inv_mul]
#align real.exp_eq_exp_ℝ Real.exp_eq_exp_ℝ

end Real

