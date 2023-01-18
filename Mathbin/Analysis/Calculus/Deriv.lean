/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sébastien Gouëzel

! This file was ported from Lean 3 source module analysis.calculus.deriv
! leanprover-community/mathlib commit 008205aa645b3f194c1da47025c5f110c8406eab
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Calculus.Fderiv
import Mathbin.Data.Polynomial.Derivative
import Mathbin.LinearAlgebra.AffineSpace.Slope

/-!

# One-dimensional derivatives

This file defines the derivative of a function `f : 𝕜 → F` where `𝕜` is a
normed field and `F` is a normed space over this field. The derivative of
such a function `f` at a point `x` is given by an element `f' : F`.

The theory is developed analogously to the [Fréchet
derivatives](./fderiv.html). We first introduce predicates defined in terms
of the corresponding predicates for Fréchet derivatives:

 - `has_deriv_at_filter f f' x L` states that the function `f` has the
    derivative `f'` at the point `x` as `x` goes along the filter `L`.

 - `has_deriv_within_at f f' s x` states that the function `f` has the
    derivative `f'` at the point `x` within the subset `s`.

 - `has_deriv_at f f' x` states that the function `f` has the derivative `f'`
    at the point `x`.

 - `has_strict_deriv_at f f' x` states that the function `f` has the derivative `f'`
    at the point `x` in the sense of strict differentiability, i.e.,
   `f y - f z = (y - z) • f' + o (y - z)` as `y, z → x`.

For the last two notions we also define a functional version:

  - `deriv_within f s x` is a derivative of `f` at `x` within `s`. If the
    derivative does not exist, then `deriv_within f s x` equals zero.

  - `deriv f x` is a derivative of `f` at `x`. If the derivative does not
    exist, then `deriv f x` equals zero.

The theorems `fderiv_within_deriv_within` and `fderiv_deriv` show that the
one-dimensional derivatives coincide with the general Fréchet derivatives.

We also show the existence and compute the derivatives of:
  - constants
  - the identity function
  - linear maps
  - addition
  - sum of finitely many functions
  - negation
  - subtraction
  - multiplication
  - inverse `x → x⁻¹`
  - multiplication of two functions in `𝕜 → 𝕜`
  - multiplication of a function in `𝕜 → 𝕜` and of a function in `𝕜 → E`
  - composition of a function in `𝕜 → F` with a function in `𝕜 → 𝕜`
  - composition of a function in `F → E` with a function in `𝕜 → F`
  - inverse function (assuming that it exists; the inverse function theorem is in `inverse.lean`)
  - division
  - polynomials

For most binary operations we also define `const_op` and `op_const` theorems for the cases when
the first or second argument is a constant. This makes writing chains of `has_deriv_at`'s easier,
and they more frequently lead to the desired result.

We set up the simplifier so that it can compute the derivative of simple functions. For instance,
```lean
example (x : ℝ) : deriv (λ x, cos (sin x) * exp x) x = (cos(sin(x))-sin(sin(x))*cos(x))*exp(x) :=
by { simp, ring }
```

## Implementation notes

Most of the theorems are direct restatements of the corresponding theorems
for Fréchet derivatives.

The strategy to construct simp lemmas that give the simplifier the possibility to compute
derivatives is the same as the one for differentiability statements, as explained in `fderiv.lean`.
See the explanations there.
-/


universe u v w

noncomputable section

open Classical TopologicalSpace BigOperators Filter Ennreal Polynomial

open Filter Asymptotics Set

open ContinuousLinearMap (smul_right smul_right_one_eq_iff)

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

section

variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- `f` has the derivative `f'` at the point `x` as `x` goes along the filter `L`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges along the filter `L`.
-/
def HasDerivAtFilter (f : 𝕜 → F) (f' : F) (x : 𝕜) (L : Filter 𝕜) :=
  HasFderivAtFilter f (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') x L
#align has_deriv_at_filter HasDerivAtFilter

/-- `f` has the derivative `f'` at the point `x` within the subset `s`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges to `x` inside `s`.
-/
def HasDerivWithinAt (f : 𝕜 → F) (f' : F) (s : Set 𝕜) (x : 𝕜) :=
  HasDerivAtFilter f f' x (𝓝[s] x)
#align has_deriv_within_at HasDerivWithinAt

/-- `f` has the derivative `f'` at the point `x`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges to `x`.
-/
def HasDerivAt (f : 𝕜 → F) (f' : F) (x : 𝕜) :=
  HasDerivAtFilter f f' x (𝓝 x)
#align has_deriv_at HasDerivAt

/-- `f` has the derivative `f'` at the point `x` in the sense of strict differentiability.

That is, `f y - f z = (y - z) • f' + o(y - z)` as `y, z → x`. -/
def HasStrictDerivAt (f : 𝕜 → F) (f' : F) (x : 𝕜) :=
  HasStrictFderivAt f (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') x
#align has_strict_deriv_at HasStrictDerivAt

/-- Derivative of `f` at the point `x` within the set `s`, if it exists.  Zero otherwise.

If the derivative exists (i.e., `∃ f', has_deriv_within_at f f' s x`), then
`f x' = f x + (x' - x) • deriv_within f s x + o(x' - x)` where `x'` converges to `x` inside `s`.
-/
def derivWithin (f : 𝕜 → F) (s : Set 𝕜) (x : 𝕜) :=
  fderivWithin 𝕜 f s x 1
#align deriv_within derivWithin

/-- Derivative of `f` at the point `x`, if it exists.  Zero otherwise.

If the derivative exists (i.e., `∃ f', has_deriv_at f f' x`), then
`f x' = f x + (x' - x) • deriv f x + o(x' - x)` where `x'` converges to `x`.
-/
def deriv (f : 𝕜 → F) (x : 𝕜) :=
  fderiv 𝕜 f x 1
#align deriv deriv

variable {f f₀ f₁ g : 𝕜 → F}

variable {f' f₀' f₁' g' : F}

variable {x : 𝕜}

variable {s t : Set 𝕜}

variable {L L₁ L₂ : Filter 𝕜}

/-- Expressing `has_fderiv_at_filter f f' x L` in terms of `has_deriv_at_filter` -/
theorem has_fderiv_at_filter_iff_has_deriv_at_filter {f' : 𝕜 →L[𝕜] F} :
    HasFderivAtFilter f f' x L ↔ HasDerivAtFilter f (f' 1) x L := by simp [HasDerivAtFilter]
#align has_fderiv_at_filter_iff_has_deriv_at_filter has_fderiv_at_filter_iff_has_deriv_at_filter

theorem HasFderivAtFilter.has_deriv_at_filter {f' : 𝕜 →L[𝕜] F} :
    HasFderivAtFilter f f' x L → HasDerivAtFilter f (f' 1) x L :=
  has_fderiv_at_filter_iff_has_deriv_at_filter.mp
#align has_fderiv_at_filter.has_deriv_at_filter HasFderivAtFilter.has_deriv_at_filter

/-- Expressing `has_fderiv_within_at f f' s x` in terms of `has_deriv_within_at` -/
theorem has_fderiv_within_at_iff_has_deriv_within_at {f' : 𝕜 →L[𝕜] F} :
    HasFderivWithinAt f f' s x ↔ HasDerivWithinAt f (f' 1) s x :=
  has_fderiv_at_filter_iff_has_deriv_at_filter
#align has_fderiv_within_at_iff_has_deriv_within_at has_fderiv_within_at_iff_has_deriv_within_at

/-- Expressing `has_deriv_within_at f f' s x` in terms of `has_fderiv_within_at` -/
theorem has_deriv_within_at_iff_has_fderiv_within_at {f' : F} :
    HasDerivWithinAt f f' s x ↔ HasFderivWithinAt f (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') s x :=
  Iff.rfl
#align has_deriv_within_at_iff_has_fderiv_within_at has_deriv_within_at_iff_has_fderiv_within_at

theorem HasFderivWithinAt.has_deriv_within_at {f' : 𝕜 →L[𝕜] F} :
    HasFderivWithinAt f f' s x → HasDerivWithinAt f (f' 1) s x :=
  has_fderiv_within_at_iff_has_deriv_within_at.mp
#align has_fderiv_within_at.has_deriv_within_at HasFderivWithinAt.has_deriv_within_at

theorem HasDerivWithinAt.hasFderivWithinAt {f' : F} :
    HasDerivWithinAt f f' s x → HasFderivWithinAt f (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') s x :=
  has_deriv_within_at_iff_has_fderiv_within_at.mp
#align has_deriv_within_at.has_fderiv_within_at HasDerivWithinAt.hasFderivWithinAt

/-- Expressing `has_fderiv_at f f' x` in terms of `has_deriv_at` -/
theorem has_fderiv_at_iff_has_deriv_at {f' : 𝕜 →L[𝕜] F} :
    HasFderivAt f f' x ↔ HasDerivAt f (f' 1) x :=
  has_fderiv_at_filter_iff_has_deriv_at_filter
#align has_fderiv_at_iff_has_deriv_at has_fderiv_at_iff_has_deriv_at

theorem HasFderivAt.has_deriv_at {f' : 𝕜 →L[𝕜] F} : HasFderivAt f f' x → HasDerivAt f (f' 1) x :=
  has_fderiv_at_iff_has_deriv_at.mp
#align has_fderiv_at.has_deriv_at HasFderivAt.has_deriv_at

theorem has_strict_fderiv_at_iff_has_strict_deriv_at {f' : 𝕜 →L[𝕜] F} :
    HasStrictFderivAt f f' x ↔ HasStrictDerivAt f (f' 1) x := by
  simp [HasStrictDerivAt, HasStrictFderivAt]
#align has_strict_fderiv_at_iff_has_strict_deriv_at has_strict_fderiv_at_iff_has_strict_deriv_at

protected theorem HasStrictFderivAt.has_strict_deriv_at {f' : 𝕜 →L[𝕜] F} :
    HasStrictFderivAt f f' x → HasStrictDerivAt f (f' 1) x :=
  has_strict_fderiv_at_iff_has_strict_deriv_at.mp
#align has_strict_fderiv_at.has_strict_deriv_at HasStrictFderivAt.has_strict_deriv_at

theorem has_strict_deriv_at_iff_has_strict_fderiv_at :
    HasStrictDerivAt f f' x ↔ HasStrictFderivAt f (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') x :=
  Iff.rfl
#align has_strict_deriv_at_iff_has_strict_fderiv_at has_strict_deriv_at_iff_has_strict_fderiv_at

alias has_strict_deriv_at_iff_has_strict_fderiv_at ↔ HasStrictDerivAt.hasStrictFderivAt _
#align has_strict_deriv_at.has_strict_fderiv_at HasStrictDerivAt.hasStrictFderivAt

/-- Expressing `has_deriv_at f f' x` in terms of `has_fderiv_at` -/
theorem has_deriv_at_iff_has_fderiv_at {f' : F} :
    HasDerivAt f f' x ↔ HasFderivAt f (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') x :=
  Iff.rfl
#align has_deriv_at_iff_has_fderiv_at has_deriv_at_iff_has_fderiv_at

alias has_deriv_at_iff_has_fderiv_at ↔ HasDerivAt.hasFderivAt _
#align has_deriv_at.has_fderiv_at HasDerivAt.hasFderivAt

theorem deriv_within_zero_of_not_differentiable_within_at (h : ¬DifferentiableWithinAt 𝕜 f s x) :
    derivWithin f s x = 0 := by
  unfold derivWithin
  rw [fderiv_within_zero_of_not_differentiable_within_at]
  simp
  assumption
#align
  deriv_within_zero_of_not_differentiable_within_at deriv_within_zero_of_not_differentiable_within_at

theorem differentiable_within_at_of_deriv_within_ne_zero (h : derivWithin f s x ≠ 0) :
    DifferentiableWithinAt 𝕜 f s x :=
  not_imp_comm.1 deriv_within_zero_of_not_differentiable_within_at h
#align
  differentiable_within_at_of_deriv_within_ne_zero differentiable_within_at_of_deriv_within_ne_zero

theorem deriv_zero_of_not_differentiable_at (h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0 :=
  by
  unfold deriv
  rw [fderiv_zero_of_not_differentiable_at]
  simp
  assumption
#align deriv_zero_of_not_differentiable_at deriv_zero_of_not_differentiable_at

theorem differentiable_at_of_deriv_ne_zero (h : deriv f x ≠ 0) : DifferentiableAt 𝕜 f x :=
  not_imp_comm.1 deriv_zero_of_not_differentiable_at h
#align differentiable_at_of_deriv_ne_zero differentiable_at_of_deriv_ne_zero

theorem UniqueDiffWithinAt.eq_deriv (s : Set 𝕜) (H : UniqueDiffWithinAt 𝕜 s x)
    (h : HasDerivWithinAt f f' s x) (h₁ : HasDerivWithinAt f f₁' s x) : f' = f₁' :=
  smul_right_one_eq_iff.mp <| UniqueDiffWithinAt.eq H h h₁
#align unique_diff_within_at.eq_deriv UniqueDiffWithinAt.eq_deriv

theorem has_deriv_at_filter_iff_is_o :
    HasDerivAtFilter f f' x L ↔ (fun x' : 𝕜 => f x' - f x - (x' - x) • f') =o[L] fun x' => x' - x :=
  Iff.rfl
#align has_deriv_at_filter_iff_is_o has_deriv_at_filter_iff_is_o

theorem has_deriv_at_filter_iff_tendsto :
    HasDerivAtFilter f f' x L ↔
      Tendsto (fun x' : 𝕜 => ‖x' - x‖⁻¹ * ‖f x' - f x - (x' - x) • f'‖) L (𝓝 0) :=
  has_fderiv_at_filter_iff_tendsto
#align has_deriv_at_filter_iff_tendsto has_deriv_at_filter_iff_tendsto

theorem has_deriv_within_at_iff_is_o :
    HasDerivWithinAt f f' s x ↔
      (fun x' : 𝕜 => f x' - f x - (x' - x) • f') =o[𝓝[s] x] fun x' => x' - x :=
  Iff.rfl
#align has_deriv_within_at_iff_is_o has_deriv_within_at_iff_is_o

theorem has_deriv_within_at_iff_tendsto :
    HasDerivWithinAt f f' s x ↔
      Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - (x' - x) • f'‖) (𝓝[s] x) (𝓝 0) :=
  has_fderiv_at_filter_iff_tendsto
#align has_deriv_within_at_iff_tendsto has_deriv_within_at_iff_tendsto

theorem has_deriv_at_iff_is_o :
    HasDerivAt f f' x ↔ (fun x' : 𝕜 => f x' - f x - (x' - x) • f') =o[𝓝 x] fun x' => x' - x :=
  Iff.rfl
#align has_deriv_at_iff_is_o has_deriv_at_iff_is_o

theorem has_deriv_at_iff_tendsto :
    HasDerivAt f f' x ↔ Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - (x' - x) • f'‖) (𝓝 x) (𝓝 0) :=
  has_fderiv_at_filter_iff_tendsto
#align has_deriv_at_iff_tendsto has_deriv_at_iff_tendsto

theorem HasStrictDerivAt.has_deriv_at (h : HasStrictDerivAt f f' x) : HasDerivAt f f' x :=
  h.HasFderivAt
#align has_strict_deriv_at.has_deriv_at HasStrictDerivAt.has_deriv_at

/-- If the domain has dimension one, then Fréchet derivative is equivalent to the classical
definition with a limit. In this version we have to take the limit along the subset `-{x}`,
because for `y=x` the slope equals zero due to the convention `0⁻¹=0`. -/
theorem has_deriv_at_filter_iff_tendsto_slope {x : 𝕜} {L : Filter 𝕜} :
    HasDerivAtFilter f f' x L ↔ Tendsto (slope f x) (L ⊓ 𝓟 ({x}ᶜ)) (𝓝 f') :=
  by
  conv_lhs =>
    simp only [has_deriv_at_filter_iff_tendsto, (norm_inv _).symm, (norm_smul _ _).symm,
      tendsto_zero_iff_norm_tendsto_zero.symm]
  conv_rhs => rw [← nhds_translation_sub f', tendsto_comap_iff]
  refine' (tendsto_inf_principal_nhds_iff_of_forall_eq <| by simp).symm.trans (tendsto_congr' _)
  refine' (eventually_principal.2 fun z hz => _).filter_mono inf_le_right
  simp only [(· ∘ ·)]
  rw [smul_sub, ← mul_smul, inv_mul_cancel (sub_ne_zero.2 hz), one_smul, slope_def_module]
#align has_deriv_at_filter_iff_tendsto_slope has_deriv_at_filter_iff_tendsto_slope

theorem has_deriv_within_at_iff_tendsto_slope :
    HasDerivWithinAt f f' s x ↔ Tendsto (slope f x) (𝓝[s \ {x}] x) (𝓝 f') :=
  by
  simp only [HasDerivWithinAt, nhdsWithin, diff_eq, inf_assoc.symm, inf_principal.symm]
  exact has_deriv_at_filter_iff_tendsto_slope
#align has_deriv_within_at_iff_tendsto_slope has_deriv_within_at_iff_tendsto_slope

theorem has_deriv_within_at_iff_tendsto_slope' (hs : x ∉ s) :
    HasDerivWithinAt f f' s x ↔ Tendsto (slope f x) (𝓝[s] x) (𝓝 f') :=
  by
  convert ← has_deriv_within_at_iff_tendsto_slope
  exact diff_singleton_eq_self hs
#align has_deriv_within_at_iff_tendsto_slope' has_deriv_within_at_iff_tendsto_slope'

theorem has_deriv_at_iff_tendsto_slope : HasDerivAt f f' x ↔ Tendsto (slope f x) (𝓝[≠] x) (𝓝 f') :=
  has_deriv_at_filter_iff_tendsto_slope
#align has_deriv_at_iff_tendsto_slope has_deriv_at_iff_tendsto_slope

theorem has_deriv_within_at_congr_set {s t u : Set 𝕜} (hu : u ∈ 𝓝 x) (h : s ∩ u = t ∩ u) :
    HasDerivWithinAt f f' s x ↔ HasDerivWithinAt f f' t x := by
  simp_rw [HasDerivWithinAt, nhds_within_eq_nhds_within' hu h]
#align has_deriv_within_at_congr_set has_deriv_within_at_congr_set

alias has_deriv_within_at_congr_set ↔ HasDerivWithinAt.congr_set _
#align has_deriv_within_at.congr_set HasDerivWithinAt.congr_set

@[simp]
theorem has_deriv_within_at_diff_singleton :
    HasDerivWithinAt f f' (s \ {x}) x ↔ HasDerivWithinAt f f' s x := by
  simp only [has_deriv_within_at_iff_tendsto_slope, sdiff_idem]
#align has_deriv_within_at_diff_singleton has_deriv_within_at_diff_singleton

@[simp]
theorem has_deriv_within_at_Ioi_iff_Ici [PartialOrder 𝕜] :
    HasDerivWithinAt f f' (Ioi x) x ↔ HasDerivWithinAt f f' (Ici x) x := by
  rw [← Ici_diff_left, has_deriv_within_at_diff_singleton]
#align has_deriv_within_at_Ioi_iff_Ici has_deriv_within_at_Ioi_iff_Ici

alias has_deriv_within_at_Ioi_iff_Ici ↔ HasDerivWithinAt.Ici_of_Ioi HasDerivWithinAt.Ioi_of_Ici
#align has_deriv_within_at.Ici_of_Ioi HasDerivWithinAt.Ici_of_Ioi
#align has_deriv_within_at.Ioi_of_Ici HasDerivWithinAt.Ioi_of_Ici

@[simp]
theorem has_deriv_within_at_Iio_iff_Iic [PartialOrder 𝕜] :
    HasDerivWithinAt f f' (Iio x) x ↔ HasDerivWithinAt f f' (Iic x) x := by
  rw [← Iic_diff_right, has_deriv_within_at_diff_singleton]
#align has_deriv_within_at_Iio_iff_Iic has_deriv_within_at_Iio_iff_Iic

alias has_deriv_within_at_Iio_iff_Iic ↔ HasDerivWithinAt.Iic_of_Iio HasDerivWithinAt.Iio_of_Iic
#align has_deriv_within_at.Iic_of_Iio HasDerivWithinAt.Iic_of_Iio
#align has_deriv_within_at.Iio_of_Iic HasDerivWithinAt.Iio_of_Iic

theorem HasDerivWithinAt.Ioi_iff_Ioo [LinearOrder 𝕜] [OrderClosedTopology 𝕜] {x y : 𝕜} (h : x < y) :
    HasDerivWithinAt f f' (Ioo x y) x ↔ HasDerivWithinAt f f' (Ioi x) x :=
  has_deriv_within_at_congr_set (is_open_Iio.mem_nhds h) <|
    by
    rw [Ioi_inter_Iio, inter_eq_left_iff_subset]
    exact Ioo_subset_Iio_self
#align has_deriv_within_at.Ioi_iff_Ioo HasDerivWithinAt.Ioi_iff_Ioo

alias HasDerivWithinAt.Ioi_iff_Ioo ↔ HasDerivWithinAt.Ioi_of_Ioo HasDerivWithinAt.Ioo_of_Ioi
#align has_deriv_within_at.Ioi_of_Ioo HasDerivWithinAt.Ioi_of_Ioo
#align has_deriv_within_at.Ioo_of_Ioi HasDerivWithinAt.Ioo_of_Ioi

theorem has_deriv_at_iff_is_o_nhds_zero :
    HasDerivAt f f' x ↔ (fun h => f (x + h) - f x - h • f') =o[𝓝 0] fun h => h :=
  has_fderiv_at_iff_is_o_nhds_zero
#align has_deriv_at_iff_is_o_nhds_zero has_deriv_at_iff_is_o_nhds_zero

theorem HasDerivAtFilter.mono (h : HasDerivAtFilter f f' x L₂) (hst : L₁ ≤ L₂) :
    HasDerivAtFilter f f' x L₁ :=
  HasFderivAtFilter.mono h hst
#align has_deriv_at_filter.mono HasDerivAtFilter.mono

theorem HasDerivWithinAt.mono (h : HasDerivWithinAt f f' t x) (hst : s ⊆ t) :
    HasDerivWithinAt f f' s x :=
  HasFderivWithinAt.mono h hst
#align has_deriv_within_at.mono HasDerivWithinAt.mono

theorem HasDerivAt.has_deriv_at_filter (h : HasDerivAt f f' x) (hL : L ≤ 𝓝 x) :
    HasDerivAtFilter f f' x L :=
  HasFderivAt.hasFderivAtFilter h hL
#align has_deriv_at.has_deriv_at_filter HasDerivAt.has_deriv_at_filter

theorem HasDerivAt.has_deriv_within_at (h : HasDerivAt f f' x) : HasDerivWithinAt f f' s x :=
  HasFderivAt.hasFderivWithinAt h
#align has_deriv_at.has_deriv_within_at HasDerivAt.has_deriv_within_at

theorem HasDerivWithinAt.differentiable_within_at (h : HasDerivWithinAt f f' s x) :
    DifferentiableWithinAt 𝕜 f s x :=
  HasFderivWithinAt.differentiable_within_at h
#align has_deriv_within_at.differentiable_within_at HasDerivWithinAt.differentiable_within_at

theorem HasDerivAt.differentiable_at (h : HasDerivAt f f' x) : DifferentiableAt 𝕜 f x :=
  HasFderivAt.differentiable_at h
#align has_deriv_at.differentiable_at HasDerivAt.differentiable_at

@[simp]
theorem has_deriv_within_at_univ : HasDerivWithinAt f f' univ x ↔ HasDerivAt f f' x :=
  has_fderiv_within_at_univ
#align has_deriv_within_at_univ has_deriv_within_at_univ

theorem HasDerivAt.unique (h₀ : HasDerivAt f f₀' x) (h₁ : HasDerivAt f f₁' x) : f₀' = f₁' :=
  smul_right_one_eq_iff.mp <| h₀.HasFderivAt.unique h₁
#align has_deriv_at.unique HasDerivAt.unique

theorem has_deriv_within_at_inter' (h : t ∈ 𝓝[s] x) :
    HasDerivWithinAt f f' (s ∩ t) x ↔ HasDerivWithinAt f f' s x :=
  has_fderiv_within_at_inter' h
#align has_deriv_within_at_inter' has_deriv_within_at_inter'

theorem has_deriv_within_at_inter (h : t ∈ 𝓝 x) :
    HasDerivWithinAt f f' (s ∩ t) x ↔ HasDerivWithinAt f f' s x :=
  has_fderiv_within_at_inter h
#align has_deriv_within_at_inter has_deriv_within_at_inter

theorem HasDerivWithinAt.union (hs : HasDerivWithinAt f f' s x) (ht : HasDerivWithinAt f f' t x) :
    HasDerivWithinAt f f' (s ∪ t) x :=
  hs.HasFderivWithinAt.union ht.HasFderivWithinAt
#align has_deriv_within_at.union HasDerivWithinAt.union

theorem HasDerivWithinAt.nhds_within (h : HasDerivWithinAt f f' s x) (ht : s ∈ 𝓝[t] x) :
    HasDerivWithinAt f f' t x :=
  (has_deriv_within_at_inter' ht).1 (h.mono (inter_subset_right _ _))
#align has_deriv_within_at.nhds_within HasDerivWithinAt.nhds_within

theorem HasDerivWithinAt.has_deriv_at (h : HasDerivWithinAt f f' s x) (hs : s ∈ 𝓝 x) :
    HasDerivAt f f' x :=
  HasFderivWithinAt.hasFderivAt h hs
#align has_deriv_within_at.has_deriv_at HasDerivWithinAt.has_deriv_at

theorem DifferentiableWithinAt.has_deriv_within_at (h : DifferentiableWithinAt 𝕜 f s x) :
    HasDerivWithinAt f (derivWithin f s x) s x :=
  h.HasFderivWithinAt.HasDerivWithinAt
#align differentiable_within_at.has_deriv_within_at DifferentiableWithinAt.has_deriv_within_at

theorem DifferentiableAt.has_deriv_at (h : DifferentiableAt 𝕜 f x) : HasDerivAt f (deriv f x) x :=
  h.HasFderivAt.HasDerivAt
#align differentiable_at.has_deriv_at DifferentiableAt.has_deriv_at

@[simp]
theorem has_deriv_at_deriv_iff : HasDerivAt f (deriv f x) x ↔ DifferentiableAt 𝕜 f x :=
  ⟨fun h => h.DifferentiableAt, fun h => h.HasDerivAt⟩
#align has_deriv_at_deriv_iff has_deriv_at_deriv_iff

@[simp]
theorem has_deriv_within_at_deriv_within_iff :
    HasDerivWithinAt f (derivWithin f s x) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  ⟨fun h => h.DifferentiableWithinAt, fun h => h.HasDerivWithinAt⟩
#align has_deriv_within_at_deriv_within_iff has_deriv_within_at_deriv_within_iff

theorem DifferentiableOn.has_deriv_at (h : DifferentiableOn 𝕜 f s) (hs : s ∈ 𝓝 x) :
    HasDerivAt f (deriv f x) x :=
  (h.HasFderivAt hs).HasDerivAt
#align differentiable_on.has_deriv_at DifferentiableOn.has_deriv_at

theorem HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x = f' :=
  h.DifferentiableAt.HasDerivAt.unique h
#align has_deriv_at.deriv HasDerivAt.deriv

theorem deriv_eq {f' : 𝕜 → F} (h : ∀ x, HasDerivAt f (f' x) x) : deriv f = f' :=
  funext fun x => (h x).deriv
#align deriv_eq deriv_eq

theorem HasDerivWithinAt.deriv_within (h : HasDerivWithinAt f f' s x)
    (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f' :=
  hxs.eq_deriv _ h.DifferentiableWithinAt.HasDerivWithinAt h
#align has_deriv_within_at.deriv_within HasDerivWithinAt.deriv_within

theorem fderiv_within_deriv_within : (fderivWithin 𝕜 f s x : 𝕜 → F) 1 = derivWithin f s x :=
  rfl
#align fderiv_within_deriv_within fderiv_within_deriv_within

theorem deriv_within_fderiv_within :
    smulRight (1 : 𝕜 →L[𝕜] 𝕜) (derivWithin f s x) = fderivWithin 𝕜 f s x := by simp [derivWithin]
#align deriv_within_fderiv_within deriv_within_fderiv_within

theorem fderiv_deriv : (fderiv 𝕜 f x : 𝕜 → F) 1 = deriv f x :=
  rfl
#align fderiv_deriv fderiv_deriv

theorem deriv_fderiv : smulRight (1 : 𝕜 →L[𝕜] 𝕜) (deriv f x) = fderiv 𝕜 f x := by simp [deriv]
#align deriv_fderiv deriv_fderiv

theorem DifferentiableAt.deriv_within (h : DifferentiableAt 𝕜 f x)
    (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = deriv f x :=
  by
  unfold derivWithin deriv
  rw [h.fderiv_within hxs]
#align differentiable_at.deriv_within DifferentiableAt.deriv_within

theorem HasDerivWithinAt.deriv_eq_zero (hd : HasDerivWithinAt f 0 s x)
    (H : UniqueDiffWithinAt 𝕜 s x) : deriv f x = 0 :=
  (em' (DifferentiableAt 𝕜 f x)).elim deriv_zero_of_not_differentiable_at fun h =>
    H.eq_deriv _ h.HasDerivAt.HasDerivWithinAt hd
#align has_deriv_within_at.deriv_eq_zero HasDerivWithinAt.deriv_eq_zero

theorem deriv_within_subset (st : s ⊆ t) (ht : UniqueDiffWithinAt 𝕜 s x)
    (h : DifferentiableWithinAt 𝕜 f t x) : derivWithin f s x = derivWithin f t x :=
  ((DifferentiableWithinAt.has_deriv_within_at h).mono st).derivWithin ht
#align deriv_within_subset deriv_within_subset

@[simp]
theorem deriv_within_univ : derivWithin f univ = deriv f :=
  by
  ext
  unfold derivWithin deriv
  rw [fderiv_within_univ]
#align deriv_within_univ deriv_within_univ

theorem deriv_within_inter (ht : t ∈ 𝓝 x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin f (s ∩ t) x = derivWithin f s x :=
  by
  unfold derivWithin
  rw [fderiv_within_inter ht hs]
#align deriv_within_inter deriv_within_inter

theorem deriv_within_of_open (hs : IsOpen s) (hx : x ∈ s) : derivWithin f s x = deriv f x :=
  by
  unfold derivWithin
  rw [fderiv_within_of_open hs hx]
  rfl
#align deriv_within_of_open deriv_within_of_open

theorem deriv_mem_iff {f : 𝕜 → F} {s : Set F} {x : 𝕜} :
    deriv f x ∈ s ↔
      DifferentiableAt 𝕜 f x ∧ deriv f x ∈ s ∨ ¬DifferentiableAt 𝕜 f x ∧ (0 : F) ∈ s :=
  by by_cases hx : DifferentiableAt 𝕜 f x <;> simp [deriv_zero_of_not_differentiable_at, *]
#align deriv_mem_iff deriv_mem_iff

theorem deriv_within_mem_iff {f : 𝕜 → F} {t : Set 𝕜} {s : Set F} {x : 𝕜} :
    derivWithin f t x ∈ s ↔
      DifferentiableWithinAt 𝕜 f t x ∧ derivWithin f t x ∈ s ∨
        ¬DifferentiableWithinAt 𝕜 f t x ∧ (0 : F) ∈ s :=
  by
  by_cases hx : DifferentiableWithinAt 𝕜 f t x <;>
    simp [deriv_within_zero_of_not_differentiable_within_at, *]
#align deriv_within_mem_iff deriv_within_mem_iff

theorem differentiable_within_at_Ioi_iff_Ici [PartialOrder 𝕜] :
    DifferentiableWithinAt 𝕜 f (Ioi x) x ↔ DifferentiableWithinAt 𝕜 f (Ici x) x :=
  ⟨fun h => h.HasDerivWithinAt.Ici_of_Ioi.DifferentiableWithinAt, fun h =>
    h.HasDerivWithinAt.Ioi_of_Ici.DifferentiableWithinAt⟩
#align differentiable_within_at_Ioi_iff_Ici differentiable_within_at_Ioi_iff_Ici

theorem deriv_within_Ioi_eq_Ici {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E)
    (x : ℝ) : derivWithin f (Ioi x) x = derivWithin f (Ici x) x :=
  by
  by_cases H : DifferentiableWithinAt ℝ f (Ioi x) x
  · have A := H.has_deriv_within_at.Ici_of_Ioi
    have B := (differentiable_within_at_Ioi_iff_Ici.1 H).HasDerivWithinAt
    simpa using (unique_diff_on_Ici x).Eq le_rfl A B
  · rw [deriv_within_zero_of_not_differentiable_within_at H,
      deriv_within_zero_of_not_differentiable_within_at]
    rwa [differentiable_within_at_Ioi_iff_Ici] at H
#align deriv_within_Ioi_eq_Ici deriv_within_Ioi_eq_Ici

section congr

/-! ### Congruence properties of derivatives -/


theorem Filter.EventuallyEq.has_deriv_at_filter_iff (h₀ : f₀ =ᶠ[L] f₁) (hx : f₀ x = f₁ x)
    (h₁ : f₀' = f₁') : HasDerivAtFilter f₀ f₀' x L ↔ HasDerivAtFilter f₁ f₁' x L :=
  h₀.has_fderiv_at_filter_iff hx (by simp [h₁])
#align filter.eventually_eq.has_deriv_at_filter_iff Filter.EventuallyEq.has_deriv_at_filter_iff

theorem HasDerivAtFilter.congr_of_eventually_eq (h : HasDerivAtFilter f f' x L) (hL : f₁ =ᶠ[L] f)
    (hx : f₁ x = f x) : HasDerivAtFilter f₁ f' x L := by rwa [hL.has_deriv_at_filter_iff hx rfl]
#align has_deriv_at_filter.congr_of_eventually_eq HasDerivAtFilter.congr_of_eventually_eq

theorem HasDerivWithinAt.congr_mono (h : HasDerivWithinAt f f' s x) (ht : ∀ x ∈ t, f₁ x = f x)
    (hx : f₁ x = f x) (h₁ : t ⊆ s) : HasDerivWithinAt f₁ f' t x :=
  HasFderivWithinAt.congrMono h ht hx h₁
#align has_deriv_within_at.congr_mono HasDerivWithinAt.congr_mono

theorem HasDerivWithinAt.congr (h : HasDerivWithinAt f f' s x) (hs : ∀ x ∈ s, f₁ x = f x)
    (hx : f₁ x = f x) : HasDerivWithinAt f₁ f' s x :=
  h.congr_mono hs hx (Subset.refl _)
#align has_deriv_within_at.congr HasDerivWithinAt.congr

theorem HasDerivWithinAt.congr_of_mem (h : HasDerivWithinAt f f' s x) (hs : ∀ x ∈ s, f₁ x = f x)
    (hx : x ∈ s) : HasDerivWithinAt f₁ f' s x :=
  h.congr hs (hs _ hx)
#align has_deriv_within_at.congr_of_mem HasDerivWithinAt.congr_of_mem

theorem HasDerivWithinAt.congr_of_eventually_eq (h : HasDerivWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : HasDerivWithinAt f₁ f' s x :=
  HasDerivAtFilter.congr_of_eventually_eq h h₁ hx
#align has_deriv_within_at.congr_of_eventually_eq HasDerivWithinAt.congr_of_eventually_eq

theorem HasDerivWithinAt.congr_of_eventually_eq_of_mem (h : HasDerivWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) : HasDerivWithinAt f₁ f' s x :=
  h.congr_of_eventually_eq h₁ (h₁.eq_of_nhds_within hx)
#align
  has_deriv_within_at.congr_of_eventually_eq_of_mem HasDerivWithinAt.congr_of_eventually_eq_of_mem

theorem HasDerivAt.congr_of_eventually_eq (h : HasDerivAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) :
    HasDerivAt f₁ f' x :=
  HasDerivAtFilter.congr_of_eventually_eq h h₁ (mem_of_mem_nhds h₁ : _)
#align has_deriv_at.congr_of_eventually_eq HasDerivAt.congr_of_eventually_eq

theorem Filter.EventuallyEq.deriv_within_eq (hs : UniqueDiffWithinAt 𝕜 s x) (hL : f₁ =ᶠ[𝓝[s] x] f)
    (hx : f₁ x = f x) : derivWithin f₁ s x = derivWithin f s x :=
  by
  unfold derivWithin
  rw [hL.fderiv_within_eq hs hx]
#align filter.eventually_eq.deriv_within_eq Filter.EventuallyEq.deriv_within_eq

theorem deriv_within_congr (hs : UniqueDiffWithinAt 𝕜 s x) (hL : ∀ y ∈ s, f₁ y = f y)
    (hx : f₁ x = f x) : derivWithin f₁ s x = derivWithin f s x :=
  by
  unfold derivWithin
  rw [fderiv_within_congr hs hL hx]
#align deriv_within_congr deriv_within_congr

theorem Filter.EventuallyEq.deriv_eq (hL : f₁ =ᶠ[𝓝 x] f) : deriv f₁ x = deriv f x :=
  by
  unfold deriv
  rwa [Filter.EventuallyEq.fderiv_eq]
#align filter.eventually_eq.deriv_eq Filter.EventuallyEq.deriv_eq

protected theorem Filter.EventuallyEq.deriv (h : f₁ =ᶠ[𝓝 x] f) : deriv f₁ =ᶠ[𝓝 x] deriv f :=
  h.eventually_eq_nhds.mono fun x h => h.deriv_eq
#align filter.eventually_eq.deriv Filter.EventuallyEq.deriv

end congr

section id

/-! ### Derivative of the identity -/


variable (s x L)

theorem has_deriv_at_filter_id : HasDerivAtFilter id 1 x L :=
  (hasFderivAtFilterId x L).HasDerivAtFilter
#align has_deriv_at_filter_id has_deriv_at_filter_id

theorem has_deriv_within_at_id : HasDerivWithinAt id 1 s x :=
  has_deriv_at_filter_id _ _
#align has_deriv_within_at_id has_deriv_within_at_id

theorem has_deriv_at_id : HasDerivAt id 1 x :=
  has_deriv_at_filter_id _ _
#align has_deriv_at_id has_deriv_at_id

theorem has_deriv_at_id' : HasDerivAt (fun x : 𝕜 => x) 1 x :=
  has_deriv_at_filter_id _ _
#align has_deriv_at_id' has_deriv_at_id'

theorem has_strict_deriv_at_id : HasStrictDerivAt id 1 x :=
  (hasStrictFderivAtId x).HasStrictDerivAt
#align has_strict_deriv_at_id has_strict_deriv_at_id

theorem deriv_id : deriv id x = 1 :=
  HasDerivAt.deriv (has_deriv_at_id x)
#align deriv_id deriv_id

@[simp]
theorem deriv_id' : deriv (@id 𝕜) = fun _ => 1 :=
  funext deriv_id
#align deriv_id' deriv_id'

@[simp]
theorem deriv_id'' : (deriv fun x : 𝕜 => x) = fun _ => 1 :=
  deriv_id'
#align deriv_id'' deriv_id''

theorem deriv_within_id (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin id s x = 1 :=
  (has_deriv_within_at_id x s).derivWithin hxs
#align deriv_within_id deriv_within_id

end id

section Const

/-! ### Derivative of constant functions -/


variable (c : F) (s x L)

theorem has_deriv_at_filter_const : HasDerivAtFilter (fun x => c) 0 x L :=
  (hasFderivAtFilterConst c x L).HasDerivAtFilter
#align has_deriv_at_filter_const has_deriv_at_filter_const

theorem has_strict_deriv_at_const : HasStrictDerivAt (fun x => c) 0 x :=
  (hasStrictFderivAtConst c x).HasStrictDerivAt
#align has_strict_deriv_at_const has_strict_deriv_at_const

theorem has_deriv_within_at_const : HasDerivWithinAt (fun x => c) 0 s x :=
  has_deriv_at_filter_const _ _ _
#align has_deriv_within_at_const has_deriv_within_at_const

theorem has_deriv_at_const : HasDerivAt (fun x => c) 0 x :=
  has_deriv_at_filter_const _ _ _
#align has_deriv_at_const has_deriv_at_const

theorem deriv_const : deriv (fun x => c) x = 0 :=
  HasDerivAt.deriv (has_deriv_at_const x c)
#align deriv_const deriv_const

@[simp]
theorem deriv_const' : (deriv fun x : 𝕜 => c) = fun x => 0 :=
  funext fun x => deriv_const x c
#align deriv_const' deriv_const'

theorem deriv_within_const (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin (fun x => c) s x = 0 :=
  (has_deriv_within_at_const _ _ _).derivWithin hxs
#align deriv_within_const deriv_within_const

end Const

section ContinuousLinearMap

/-! ### Derivative of continuous linear maps -/


variable (e : 𝕜 →L[𝕜] F)

protected theorem ContinuousLinearMap.has_deriv_at_filter : HasDerivAtFilter e (e 1) x L :=
  e.HasFderivAtFilter.HasDerivAtFilter
#align continuous_linear_map.has_deriv_at_filter ContinuousLinearMap.has_deriv_at_filter

protected theorem ContinuousLinearMap.has_strict_deriv_at : HasStrictDerivAt e (e 1) x :=
  e.HasStrictFderivAt.HasStrictDerivAt
#align continuous_linear_map.has_strict_deriv_at ContinuousLinearMap.has_strict_deriv_at

protected theorem ContinuousLinearMap.has_deriv_at : HasDerivAt e (e 1) x :=
  e.HasDerivAtFilter
#align continuous_linear_map.has_deriv_at ContinuousLinearMap.has_deriv_at

protected theorem ContinuousLinearMap.has_deriv_within_at : HasDerivWithinAt e (e 1) s x :=
  e.HasDerivAtFilter
#align continuous_linear_map.has_deriv_within_at ContinuousLinearMap.has_deriv_within_at

@[simp]
protected theorem ContinuousLinearMap.deriv : deriv e x = e 1 :=
  e.HasDerivAt.deriv
#align continuous_linear_map.deriv ContinuousLinearMap.deriv

protected theorem ContinuousLinearMap.deriv_within (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin e s x = e 1 :=
  e.HasDerivWithinAt.derivWithin hxs
#align continuous_linear_map.deriv_within ContinuousLinearMap.deriv_within

end ContinuousLinearMap

section LinearMap

/-! ### Derivative of bundled linear maps -/


variable (e : 𝕜 →ₗ[𝕜] F)

protected theorem LinearMap.has_deriv_at_filter : HasDerivAtFilter e (e 1) x L :=
  e.toContinuousLinearMap₁.HasDerivAtFilter
#align linear_map.has_deriv_at_filter LinearMap.has_deriv_at_filter

protected theorem LinearMap.has_strict_deriv_at : HasStrictDerivAt e (e 1) x :=
  e.toContinuousLinearMap₁.HasStrictDerivAt
#align linear_map.has_strict_deriv_at LinearMap.has_strict_deriv_at

protected theorem LinearMap.has_deriv_at : HasDerivAt e (e 1) x :=
  e.HasDerivAtFilter
#align linear_map.has_deriv_at LinearMap.has_deriv_at

protected theorem LinearMap.has_deriv_within_at : HasDerivWithinAt e (e 1) s x :=
  e.HasDerivAtFilter
#align linear_map.has_deriv_within_at LinearMap.has_deriv_within_at

@[simp]
protected theorem LinearMap.deriv : deriv e x = e 1 :=
  e.HasDerivAt.deriv
#align linear_map.deriv LinearMap.deriv

protected theorem LinearMap.deriv_within (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin e s x = e 1 :=
  e.HasDerivWithinAt.derivWithin hxs
#align linear_map.deriv_within LinearMap.deriv_within

end LinearMap

section Add

/-! ### Derivative of the sum of two functions -/


theorem HasDerivAtFilter.add (hf : HasDerivAtFilter f f' x L) (hg : HasDerivAtFilter g g' x L) :
    HasDerivAtFilter (fun y => f y + g y) (f' + g') x L := by
  simpa using (hf.add hg).HasDerivAtFilter
#align has_deriv_at_filter.add HasDerivAtFilter.add

theorem HasStrictDerivAt.add (hf : HasStrictDerivAt f f' x) (hg : HasStrictDerivAt g g' x) :
    HasStrictDerivAt (fun y => f y + g y) (f' + g') x := by simpa using (hf.add hg).HasStrictDerivAt
#align has_strict_deriv_at.add HasStrictDerivAt.add

theorem HasDerivWithinAt.add (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithinAt g g' s x) :
    HasDerivWithinAt (fun y => f y + g y) (f' + g') s x :=
  hf.add hg
#align has_deriv_within_at.add HasDerivWithinAt.add

theorem HasDerivAt.add (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun x => f x + g x) (f' + g') x :=
  hf.add hg
#align has_deriv_at.add HasDerivAt.add

theorem deriv_within_add (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    derivWithin (fun y => f y + g y) s x = derivWithin f s x + derivWithin g s x :=
  (hf.HasDerivWithinAt.add hg.HasDerivWithinAt).derivWithin hxs
#align deriv_within_add deriv_within_add

@[simp]
theorem deriv_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    deriv (fun y => f y + g y) x = deriv f x + deriv g x :=
  (hf.HasDerivAt.add hg.HasDerivAt).deriv
#align deriv_add deriv_add

theorem HasDerivAtFilter.add_const (hf : HasDerivAtFilter f f' x L) (c : F) :
    HasDerivAtFilter (fun y => f y + c) f' x L :=
  add_zero f' ▸ hf.add (has_deriv_at_filter_const x L c)
#align has_deriv_at_filter.add_const HasDerivAtFilter.add_const

theorem HasDerivWithinAt.add_const (hf : HasDerivWithinAt f f' s x) (c : F) :
    HasDerivWithinAt (fun y => f y + c) f' s x :=
  hf.AddConst c
#align has_deriv_within_at.add_const HasDerivWithinAt.add_const

theorem HasDerivAt.add_const (hf : HasDerivAt f f' x) (c : F) :
    HasDerivAt (fun x => f x + c) f' x :=
  hf.AddConst c
#align has_deriv_at.add_const HasDerivAt.add_const

theorem deriv_within_add_const (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    derivWithin (fun y => f y + c) s x = derivWithin f s x := by
  simp only [derivWithin, fderiv_within_add_const hxs]
#align deriv_within_add_const deriv_within_add_const

theorem deriv_add_const (c : F) : deriv (fun y => f y + c) x = deriv f x := by
  simp only [deriv, fderiv_add_const]
#align deriv_add_const deriv_add_const

@[simp]
theorem deriv_add_const' (c : F) : (deriv fun y => f y + c) = deriv f :=
  funext fun x => deriv_add_const c
#align deriv_add_const' deriv_add_const'

theorem HasDerivAtFilter.const_add (c : F) (hf : HasDerivAtFilter f f' x L) :
    HasDerivAtFilter (fun y => c + f y) f' x L :=
  zero_add f' ▸ (has_deriv_at_filter_const x L c).add hf
#align has_deriv_at_filter.const_add HasDerivAtFilter.const_add

theorem HasDerivWithinAt.const_add (c : F) (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun y => c + f y) f' s x :=
  hf.const_add c
#align has_deriv_within_at.const_add HasDerivWithinAt.const_add

theorem HasDerivAt.const_add (c : F) (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => c + f x) f' x :=
  hf.const_add c
#align has_deriv_at.const_add HasDerivAt.const_add

theorem deriv_within_const_add (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    derivWithin (fun y => c + f y) s x = derivWithin f s x := by
  simp only [derivWithin, fderiv_within_const_add hxs]
#align deriv_within_const_add deriv_within_const_add

theorem deriv_const_add (c : F) : deriv (fun y => c + f y) x = deriv f x := by
  simp only [deriv, fderiv_const_add]
#align deriv_const_add deriv_const_add

@[simp]
theorem deriv_const_add' (c : F) : (deriv fun y => c + f y) = deriv f :=
  funext fun x => deriv_const_add c
#align deriv_const_add' deriv_const_add'

end Add

section Sum

/-! ### Derivative of a finite sum of functions -/


open BigOperators

variable {ι : Type _} {u : Finset ι} {A : ι → 𝕜 → F} {A' : ι → F}

theorem HasDerivAtFilter.sum (h : ∀ i ∈ u, HasDerivAtFilter (A i) (A' i) x L) :
    HasDerivAtFilter (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x L := by
  simpa [ContinuousLinearMap.sum_apply] using (HasFderivAtFilter.sum h).HasDerivAtFilter
#align has_deriv_at_filter.sum HasDerivAtFilter.sum

theorem HasStrictDerivAt.sum (h : ∀ i ∈ u, HasStrictDerivAt (A i) (A' i) x) :
    HasStrictDerivAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x := by
  simpa [ContinuousLinearMap.sum_apply] using (HasStrictFderivAt.sum h).HasStrictDerivAt
#align has_strict_deriv_at.sum HasStrictDerivAt.sum

theorem HasDerivWithinAt.sum (h : ∀ i ∈ u, HasDerivWithinAt (A i) (A' i) s x) :
    HasDerivWithinAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) s x :=
  HasDerivAtFilter.sum h
#align has_deriv_within_at.sum HasDerivWithinAt.sum

theorem HasDerivAt.sum (h : ∀ i ∈ u, HasDerivAt (A i) (A' i) x) :
    HasDerivAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x :=
  HasDerivAtFilter.sum h
#align has_deriv_at.sum HasDerivAt.sum

theorem deriv_within_sum (hxs : UniqueDiffWithinAt 𝕜 s x)
    (h : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (A i) s x) :
    derivWithin (fun y => ∑ i in u, A i y) s x = ∑ i in u, derivWithin (A i) s x :=
  (HasDerivWithinAt.sum fun i hi => (h i hi).HasDerivWithinAt).derivWithin hxs
#align deriv_within_sum deriv_within_sum

@[simp]
theorem deriv_sum (h : ∀ i ∈ u, DifferentiableAt 𝕜 (A i) x) :
    deriv (fun y => ∑ i in u, A i y) x = ∑ i in u, deriv (A i) x :=
  (HasDerivAt.sum fun i hi => (h i hi).HasDerivAt).deriv
#align deriv_sum deriv_sum

end Sum

section Pi

/-! ### Derivatives of functions `f : 𝕜 → Π i, E i` -/


variable {ι : Type _} [Fintype ι] {E' : ι → Type _} [∀ i, NormedAddCommGroup (E' i)]
  [∀ i, NormedSpace 𝕜 (E' i)] {φ : 𝕜 → ∀ i, E' i} {φ' : ∀ i, E' i}

@[simp]
theorem has_strict_deriv_at_pi :
    HasStrictDerivAt φ φ' x ↔ ∀ i, HasStrictDerivAt (fun x => φ x i) (φ' i) x :=
  has_strict_fderiv_at_pi'
#align has_strict_deriv_at_pi has_strict_deriv_at_pi

@[simp]
theorem has_deriv_at_filter_pi :
    HasDerivAtFilter φ φ' x L ↔ ∀ i, HasDerivAtFilter (fun x => φ x i) (φ' i) x L :=
  has_fderiv_at_filter_pi'
#align has_deriv_at_filter_pi has_deriv_at_filter_pi

theorem has_deriv_at_pi : HasDerivAt φ φ' x ↔ ∀ i, HasDerivAt (fun x => φ x i) (φ' i) x :=
  has_deriv_at_filter_pi
#align has_deriv_at_pi has_deriv_at_pi

theorem has_deriv_within_at_pi :
    HasDerivWithinAt φ φ' s x ↔ ∀ i, HasDerivWithinAt (fun x => φ x i) (φ' i) s x :=
  has_deriv_at_filter_pi
#align has_deriv_within_at_pi has_deriv_within_at_pi

theorem deriv_within_pi (h : ∀ i, DifferentiableWithinAt 𝕜 (fun x => φ x i) s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin φ s x = fun i => derivWithin (fun x => φ x i) s x :=
  (has_deriv_within_at_pi.2 fun i => (h i).HasDerivWithinAt).derivWithin hs
#align deriv_within_pi deriv_within_pi

theorem deriv_pi (h : ∀ i, DifferentiableAt 𝕜 (fun x => φ x i) x) :
    deriv φ x = fun i => deriv (fun x => φ x i) x :=
  (has_deriv_at_pi.2 fun i => (h i).HasDerivAt).deriv
#align deriv_pi deriv_pi

end Pi

section Smul

/-! ### Derivative of the multiplication of a scalar function and a vector function -/


variable {𝕜' : Type _} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F] {c : 𝕜 → 𝕜'} {c' : 𝕜'}

theorem HasDerivWithinAt.smul (hc : HasDerivWithinAt c c' s x) (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun y => c y • f y) (c x • f' + c' • f x) s x := by
  simpa using (HasFderivWithinAt.smul hc hf).HasDerivWithinAt
#align has_deriv_within_at.smul HasDerivWithinAt.smul

theorem HasDerivAt.smul (hc : HasDerivAt c c' x) (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y => c y • f y) (c x • f' + c' • f x) x :=
  by
  rw [← has_deriv_within_at_univ] at *
  exact hc.smul hf
#align has_deriv_at.smul HasDerivAt.smul

theorem HasStrictDerivAt.smul (hc : HasStrictDerivAt c c' x) (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun y => c y • f y) (c x • f' + c' • f x) x := by
  simpa using (hc.smul hf).HasStrictDerivAt
#align has_strict_deriv_at.smul HasStrictDerivAt.smul

theorem deriv_within_smul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hf : DifferentiableWithinAt 𝕜 f s x) :
    derivWithin (fun y => c y • f y) s x = c x • derivWithin f s x + derivWithin c s x • f x :=
  (hc.HasDerivWithinAt.smul hf.HasDerivWithinAt).derivWithin hxs
#align deriv_within_smul deriv_within_smul

theorem deriv_smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x) :
    deriv (fun y => c y • f y) x = c x • deriv f x + deriv c x • f x :=
  (hc.HasDerivAt.smul hf.HasDerivAt).deriv
#align deriv_smul deriv_smul

theorem HasStrictDerivAt.smul_const (hc : HasStrictDerivAt c c' x) (f : F) :
    HasStrictDerivAt (fun y => c y • f) (c' • f) x :=
  by
  have := hc.smul (has_strict_deriv_at_const x f)
  rwa [smul_zero, zero_add] at this
#align has_strict_deriv_at.smul_const HasStrictDerivAt.smul_const

theorem HasDerivWithinAt.smul_const (hc : HasDerivWithinAt c c' s x) (f : F) :
    HasDerivWithinAt (fun y => c y • f) (c' • f) s x :=
  by
  have := hc.smul (has_deriv_within_at_const x s f)
  rwa [smul_zero, zero_add] at this
#align has_deriv_within_at.smul_const HasDerivWithinAt.smul_const

theorem HasDerivAt.smul_const (hc : HasDerivAt c c' x) (f : F) :
    HasDerivAt (fun y => c y • f) (c' • f) x :=
  by
  rw [← has_deriv_within_at_univ] at *
  exact hc.smul_const f
#align has_deriv_at.smul_const HasDerivAt.smul_const

theorem deriv_within_smul_const (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (f : F) :
    derivWithin (fun y => c y • f) s x = derivWithin c s x • f :=
  (hc.HasDerivWithinAt.smul_const f).derivWithin hxs
#align deriv_within_smul_const deriv_within_smul_const

theorem deriv_smul_const (hc : DifferentiableAt 𝕜 c x) (f : F) :
    deriv (fun y => c y • f) x = deriv c x • f :=
  (hc.HasDerivAt.smul_const f).deriv
#align deriv_smul_const deriv_smul_const

end Smul

section ConstSmul

variable {R : Type _} [Semiring R] [Module R F] [SMulCommClass 𝕜 R F] [HasContinuousConstSmul R F]

theorem HasStrictDerivAt.const_smul (c : R) (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun y => c • f y) (c • f') x := by
  simpa using (hf.const_smul c).HasStrictDerivAt
#align has_strict_deriv_at.const_smul HasStrictDerivAt.const_smul

theorem HasDerivAtFilter.const_smul (c : R) (hf : HasDerivAtFilter f f' x L) :
    HasDerivAtFilter (fun y => c • f y) (c • f') x L := by
  simpa using (hf.const_smul c).HasDerivAtFilter
#align has_deriv_at_filter.const_smul HasDerivAtFilter.const_smul

theorem HasDerivWithinAt.const_smul (c : R) (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun y => c • f y) (c • f') s x :=
  hf.const_smul c
#align has_deriv_within_at.const_smul HasDerivWithinAt.const_smul

theorem HasDerivAt.const_smul (c : R) (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y => c • f y) (c • f') x :=
  hf.const_smul c
#align has_deriv_at.const_smul HasDerivAt.const_smul

theorem deriv_within_const_smul (hxs : UniqueDiffWithinAt 𝕜 s x) (c : R)
    (hf : DifferentiableWithinAt 𝕜 f s x) :
    derivWithin (fun y => c • f y) s x = c • derivWithin f s x :=
  (hf.HasDerivWithinAt.const_smul c).derivWithin hxs
#align deriv_within_const_smul deriv_within_const_smul

theorem deriv_const_smul (c : R) (hf : DifferentiableAt 𝕜 f x) :
    deriv (fun y => c • f y) x = c • deriv f x :=
  (hf.HasDerivAt.const_smul c).deriv
#align deriv_const_smul deriv_const_smul

end ConstSmul

section Neg

/-! ### Derivative of the negative of a function -/


theorem HasDerivAtFilter.neg (h : HasDerivAtFilter f f' x L) :
    HasDerivAtFilter (fun x => -f x) (-f') x L := by simpa using h.neg.has_deriv_at_filter
#align has_deriv_at_filter.neg HasDerivAtFilter.neg

theorem HasDerivWithinAt.neg (h : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => -f x) (-f') s x :=
  h.neg
#align has_deriv_within_at.neg HasDerivWithinAt.neg

theorem HasDerivAt.neg (h : HasDerivAt f f' x) : HasDerivAt (fun x => -f x) (-f') x :=
  h.neg
#align has_deriv_at.neg HasDerivAt.neg

theorem HasStrictDerivAt.neg (h : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => -f x) (-f') x := by simpa using h.neg.has_strict_deriv_at
#align has_strict_deriv_at.neg HasStrictDerivAt.neg

theorem derivWithin.neg (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun y => -f y) s x = -derivWithin f s x := by
  simp only [derivWithin, fderiv_within_neg hxs, ContinuousLinearMap.neg_apply]
#align deriv_within.neg derivWithin.neg

theorem deriv.neg : deriv (fun y => -f y) x = -deriv f x := by
  simp only [deriv, fderiv_neg, ContinuousLinearMap.neg_apply]
#align deriv.neg deriv.neg

@[simp]
theorem deriv.neg' : (deriv fun y => -f y) = fun x => -deriv f x :=
  funext fun x => deriv.neg
#align deriv.neg' deriv.neg'

end Neg

section Neg2

/-! ### Derivative of the negation function (i.e `has_neg.neg`) -/


variable (s x L)

theorem has_deriv_at_filter_neg : HasDerivAtFilter Neg.neg (-1) x L :=
  HasDerivAtFilter.neg <| has_deriv_at_filter_id _ _
#align has_deriv_at_filter_neg has_deriv_at_filter_neg

theorem has_deriv_within_at_neg : HasDerivWithinAt Neg.neg (-1) s x :=
  has_deriv_at_filter_neg _ _
#align has_deriv_within_at_neg has_deriv_within_at_neg

theorem has_deriv_at_neg : HasDerivAt Neg.neg (-1) x :=
  has_deriv_at_filter_neg _ _
#align has_deriv_at_neg has_deriv_at_neg

theorem has_deriv_at_neg' : HasDerivAt (fun x => -x) (-1) x :=
  has_deriv_at_filter_neg _ _
#align has_deriv_at_neg' has_deriv_at_neg'

theorem has_strict_deriv_at_neg : HasStrictDerivAt Neg.neg (-1) x :=
  HasStrictDerivAt.neg <| has_strict_deriv_at_id _
#align has_strict_deriv_at_neg has_strict_deriv_at_neg

theorem deriv_neg : deriv Neg.neg x = -1 :=
  HasDerivAt.deriv (has_deriv_at_neg x)
#align deriv_neg deriv_neg

@[simp]
theorem deriv_neg' : deriv (Neg.neg : 𝕜 → 𝕜) = fun _ => -1 :=
  funext deriv_neg
#align deriv_neg' deriv_neg'

@[simp]
theorem deriv_neg'' : deriv (fun x : 𝕜 => -x) x = -1 :=
  deriv_neg x
#align deriv_neg'' deriv_neg''

theorem deriv_within_neg (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin Neg.neg s x = -1 :=
  (has_deriv_within_at_neg x s).derivWithin hxs
#align deriv_within_neg deriv_within_neg

theorem differentiable_neg : Differentiable 𝕜 (Neg.neg : 𝕜 → 𝕜) :=
  Differentiable.neg differentiable_id
#align differentiable_neg differentiable_neg

theorem differentiable_on_neg : DifferentiableOn 𝕜 (Neg.neg : 𝕜 → 𝕜) s :=
  DifferentiableOn.neg differentiable_on_id
#align differentiable_on_neg differentiable_on_neg

end Neg2

section Sub

/-! ### Derivative of the difference of two functions -/


theorem HasDerivAtFilter.sub (hf : HasDerivAtFilter f f' x L) (hg : HasDerivAtFilter g g' x L) :
    HasDerivAtFilter (fun x => f x - g x) (f' - g') x L := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
#align has_deriv_at_filter.sub HasDerivAtFilter.sub

theorem HasDerivWithinAt.sub (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithinAt g g' s x) :
    HasDerivWithinAt (fun x => f x - g x) (f' - g') s x :=
  hf.sub hg
#align has_deriv_within_at.sub HasDerivWithinAt.sub

theorem HasDerivAt.sub (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun x => f x - g x) (f' - g') x :=
  hf.sub hg
#align has_deriv_at.sub HasDerivAt.sub

theorem HasStrictDerivAt.sub (hf : HasStrictDerivAt f f' x) (hg : HasStrictDerivAt g g' x) :
    HasStrictDerivAt (fun x => f x - g x) (f' - g') x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
#align has_strict_deriv_at.sub HasStrictDerivAt.sub

theorem deriv_within_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    derivWithin (fun y => f y - g y) s x = derivWithin f s x - derivWithin g s x :=
  (hf.HasDerivWithinAt.sub hg.HasDerivWithinAt).derivWithin hxs
#align deriv_within_sub deriv_within_sub

@[simp]
theorem deriv_sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    deriv (fun y => f y - g y) x = deriv f x - deriv g x :=
  (hf.HasDerivAt.sub hg.HasDerivAt).deriv
#align deriv_sub deriv_sub

theorem HasDerivAtFilter.is_O_sub (h : HasDerivAtFilter f f' x L) :
    (fun x' => f x' - f x) =O[L] fun x' => x' - x :=
  HasFderivAtFilter.is_O_sub h
#align has_deriv_at_filter.is_O_sub HasDerivAtFilter.is_O_sub

theorem HasDerivAtFilter.is_O_sub_rev (hf : HasDerivAtFilter f f' x L) (hf' : f' ≠ 0) :
    (fun x' => x' - x) =O[L] fun x' => f x' - f x :=
  suffices AntilipschitzWith ‖f'‖₊⁻¹ (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') from hf.is_O_sub_rev this
  AddMonoidHomClass.antilipschitz_of_bound (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') fun x => by
    simp [norm_smul, ← div_eq_inv_mul, mul_div_cancel _ (mt norm_eq_zero.1 hf')]
#align has_deriv_at_filter.is_O_sub_rev HasDerivAtFilter.is_O_sub_rev

theorem HasDerivAtFilter.sub_const (hf : HasDerivAtFilter f f' x L) (c : F) :
    HasDerivAtFilter (fun x => f x - c) f' x L := by
  simpa only [sub_eq_add_neg] using hf.add_const (-c)
#align has_deriv_at_filter.sub_const HasDerivAtFilter.sub_const

theorem HasDerivWithinAt.sub_const (hf : HasDerivWithinAt f f' s x) (c : F) :
    HasDerivWithinAt (fun x => f x - c) f' s x :=
  hf.sub_const c
#align has_deriv_within_at.sub_const HasDerivWithinAt.sub_const

theorem HasDerivAt.sub_const (hf : HasDerivAt f f' x) (c : F) :
    HasDerivAt (fun x => f x - c) f' x :=
  hf.sub_const c
#align has_deriv_at.sub_const HasDerivAt.sub_const

theorem deriv_within_sub_const (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    derivWithin (fun y => f y - c) s x = derivWithin f s x := by
  simp only [derivWithin, fderiv_within_sub_const hxs]
#align deriv_within_sub_const deriv_within_sub_const

theorem deriv_sub_const (c : F) : deriv (fun y => f y - c) x = deriv f x := by
  simp only [deriv, fderiv_sub_const]
#align deriv_sub_const deriv_sub_const

theorem HasDerivAtFilter.const_sub (c : F) (hf : HasDerivAtFilter f f' x L) :
    HasDerivAtFilter (fun x => c - f x) (-f') x L := by
  simpa only [sub_eq_add_neg] using hf.neg.const_add c
#align has_deriv_at_filter.const_sub HasDerivAtFilter.const_sub

theorem HasDerivWithinAt.const_sub (c : F) (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => c - f x) (-f') s x :=
  hf.const_sub c
#align has_deriv_within_at.const_sub HasDerivWithinAt.const_sub

theorem HasStrictDerivAt.const_sub (c : F) (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => c - f x) (-f') x := by
  simpa only [sub_eq_add_neg] using hf.neg.const_add c
#align has_strict_deriv_at.const_sub HasStrictDerivAt.const_sub

theorem HasDerivAt.const_sub (c : F) (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => c - f x) (-f') x :=
  hf.const_sub c
#align has_deriv_at.const_sub HasDerivAt.const_sub

theorem deriv_within_const_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    derivWithin (fun y => c - f y) s x = -derivWithin f s x := by
  simp [derivWithin, fderiv_within_const_sub hxs]
#align deriv_within_const_sub deriv_within_const_sub

theorem deriv_const_sub (c : F) : deriv (fun y => c - f y) x = -deriv f x := by
  simp only [← deriv_within_univ,
    deriv_within_const_sub (uniqueDiffWithinAtUniv : UniqueDiffWithinAt 𝕜 _ _)]
#align deriv_const_sub deriv_const_sub

end Sub

section Continuous

/-! ### Continuity of a function admitting a derivative -/


theorem HasDerivAtFilter.tendsto_nhds (hL : L ≤ 𝓝 x) (h : HasDerivAtFilter f f' x L) :
    Tendsto f L (𝓝 (f x)) :=
  h.tendsto_nhds hL
#align has_deriv_at_filter.tendsto_nhds HasDerivAtFilter.tendsto_nhds

theorem HasDerivWithinAt.continuous_within_at (h : HasDerivWithinAt f f' s x) :
    ContinuousWithinAt f s x :=
  HasDerivAtFilter.tendsto_nhds inf_le_left h
#align has_deriv_within_at.continuous_within_at HasDerivWithinAt.continuous_within_at

theorem HasDerivAt.continuous_at (h : HasDerivAt f f' x) : ContinuousAt f x :=
  HasDerivAtFilter.tendsto_nhds le_rfl h
#align has_deriv_at.continuous_at HasDerivAt.continuous_at

protected theorem HasDerivAt.continuous_on {f f' : 𝕜 → F}
    (hderiv : ∀ x ∈ s, HasDerivAt f (f' x) x) : ContinuousOn f s := fun x hx =>
  (hderiv x hx).ContinuousAt.ContinuousWithinAt
#align has_deriv_at.continuous_on HasDerivAt.continuous_on

end Continuous

section CartesianProduct

/-! ### Derivative of the cartesian product of two functions -/


variable {G : Type w} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable {f₂ : 𝕜 → G} {f₂' : G}

theorem HasDerivAtFilter.prod (hf₁ : HasDerivAtFilter f₁ f₁' x L)
    (hf₂ : HasDerivAtFilter f₂ f₂' x L) : HasDerivAtFilter (fun x => (f₁ x, f₂ x)) (f₁', f₂') x L :=
  hf₁.Prod hf₂
#align has_deriv_at_filter.prod HasDerivAtFilter.prod

theorem HasDerivWithinAt.prod (hf₁ : HasDerivWithinAt f₁ f₁' s x)
    (hf₂ : HasDerivWithinAt f₂ f₂' s x) : HasDerivWithinAt (fun x => (f₁ x, f₂ x)) (f₁', f₂') s x :=
  hf₁.Prod hf₂
#align has_deriv_within_at.prod HasDerivWithinAt.prod

theorem HasDerivAt.prod (hf₁ : HasDerivAt f₁ f₁' x) (hf₂ : HasDerivAt f₂ f₂' x) :
    HasDerivAt (fun x => (f₁ x, f₂ x)) (f₁', f₂') x :=
  hf₁.Prod hf₂
#align has_deriv_at.prod HasDerivAt.prod

theorem HasStrictDerivAt.prod (hf₁ : HasStrictDerivAt f₁ f₁' x) (hf₂ : HasStrictDerivAt f₂ f₂' x) :
    HasStrictDerivAt (fun x => (f₁ x, f₂ x)) (f₁', f₂') x :=
  hf₁.Prod hf₂
#align has_strict_deriv_at.prod HasStrictDerivAt.prod

end CartesianProduct

section Composition

/-!
### Derivative of the composition of a vector function and a scalar function

We use `scomp` in lemmas on composition of vector valued and scalar valued functions, and `comp`
in lemmas on composition of scalar valued functions, in analogy for `smul` and `mul` (and also
because the `comp` version with the shorter name will show up much more often in applications).
The formula for the derivative involves `smul` in `scomp` lemmas, which can be reduced to
usual multiplication in `comp` lemmas.
-/


/- For composition lemmas, we put x explicit to help the elaborator, as otherwise Lean tends to
get confused since there are too many possibilities for composition -/
variable {𝕜' : Type _} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F] {s' t' : Set 𝕜'} {h : 𝕜 → 𝕜'} {h₁ : 𝕜 → 𝕜} {h₂ : 𝕜' → 𝕜'} {h' h₂' : 𝕜'}
  {h₁' : 𝕜} {g₁ : 𝕜' → F} {g₁' : F} {L' : Filter 𝕜'} (x)

theorem HasDerivAtFilter.scomp (hg : HasDerivAtFilter g₁ g₁' (h x) L')
    (hh : HasDerivAtFilter h h' x L) (hL : Tendsto h L L') :
    HasDerivAtFilter (g₁ ∘ h) (h' • g₁') x L := by
  simpa using ((hg.restrict_scalars 𝕜).comp x hh hL).HasDerivAtFilter
#align has_deriv_at_filter.scomp HasDerivAtFilter.scomp

theorem HasDerivWithinAt.scomp_has_deriv_at (hg : HasDerivWithinAt g₁ g₁' s' (h x))
    (hh : HasDerivAt h h' x) (hs : ∀ x, h x ∈ s') : HasDerivAt (g₁ ∘ h) (h' • g₁') x :=
  hg.scomp x hh <| tendsto_inf.2 ⟨hh.ContinuousAt, tendsto_principal.2 <| eventually_of_forall hs⟩
#align has_deriv_within_at.scomp_has_deriv_at HasDerivWithinAt.scomp_has_deriv_at

theorem HasDerivWithinAt.scomp (hg : HasDerivWithinAt g₁ g₁' t' (h x))
    (hh : HasDerivWithinAt h h' s x) (hst : MapsTo h s t') :
    HasDerivWithinAt (g₁ ∘ h) (h' • g₁') s x :=
  hg.scomp x hh <| hh.ContinuousWithinAt.tendsto_nhds_within hst
#align has_deriv_within_at.scomp HasDerivWithinAt.scomp

/-- The chain rule. -/
theorem HasDerivAt.scomp (hg : HasDerivAt g₁ g₁' (h x)) (hh : HasDerivAt h h' x) :
    HasDerivAt (g₁ ∘ h) (h' • g₁') x :=
  hg.scomp x hh hh.ContinuousAt
#align has_deriv_at.scomp HasDerivAt.scomp

theorem HasStrictDerivAt.scomp (hg : HasStrictDerivAt g₁ g₁' (h x)) (hh : HasStrictDerivAt h h' x) :
    HasStrictDerivAt (g₁ ∘ h) (h' • g₁') x := by
  simpa using ((hg.restrict_scalars 𝕜).comp x hh).HasStrictDerivAt
#align has_strict_deriv_at.scomp HasStrictDerivAt.scomp

theorem HasDerivAt.scomp_has_deriv_within_at (hg : HasDerivAt g₁ g₁' (h x))
    (hh : HasDerivWithinAt h h' s x) : HasDerivWithinAt (g₁ ∘ h) (h' • g₁') s x :=
  HasDerivWithinAt.scomp x hg.HasDerivWithinAt hh (mapsTo_univ _ _)
#align has_deriv_at.scomp_has_deriv_within_at HasDerivAt.scomp_has_deriv_within_at

theorem derivWithin.scomp (hg : DifferentiableWithinAt 𝕜' g₁ t' (h x))
    (hh : DifferentiableWithinAt 𝕜 h s x) (hs : MapsTo h s t') (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (g₁ ∘ h) s x = derivWithin h s x • derivWithin g₁ t' (h x) :=
  (HasDerivWithinAt.scomp x hg.HasDerivWithinAt hh.HasDerivWithinAt hs).derivWithin hxs
#align deriv_within.scomp derivWithin.scomp

theorem deriv.scomp (hg : DifferentiableAt 𝕜' g₁ (h x)) (hh : DifferentiableAt 𝕜 h x) :
    deriv (g₁ ∘ h) x = deriv h x • deriv g₁ (h x) :=
  (HasDerivAt.scomp x hg.HasDerivAt hh.HasDerivAt).deriv
#align deriv.scomp deriv.scomp

/-! ### Derivative of the composition of a scalar and vector functions -/


theorem HasDerivAtFilter.compHasFderivAtFilter {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} (x) {L'' : Filter E}
    (hh₂ : HasDerivAtFilter h₂ h₂' (f x) L') (hf : HasFderivAtFilter f f' x L'')
    (hL : Tendsto f L'' L') : HasFderivAtFilter (h₂ ∘ f) (h₂' • f') x L'' :=
  by
  convert (hh₂.restrict_scalars 𝕜).comp x hf hL
  ext x
  simp [mul_comm]
#align has_deriv_at_filter.comp_has_fderiv_at_filter HasDerivAtFilter.compHasFderivAtFilter

theorem HasStrictDerivAt.compHasStrictFderivAt {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} (x)
    (hh : HasStrictDerivAt h₂ h₂' (f x)) (hf : HasStrictFderivAt f f' x) :
    HasStrictFderivAt (h₂ ∘ f) (h₂' • f') x :=
  by
  rw [HasStrictDerivAt] at hh
  convert (hh.restrict_scalars 𝕜).comp x hf
  ext x
  simp [mul_comm]
#align has_strict_deriv_at.comp_has_strict_fderiv_at HasStrictDerivAt.compHasStrictFderivAt

theorem HasDerivAt.compHasFderivAt {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} (x) (hh : HasDerivAt h₂ h₂' (f x))
    (hf : HasFderivAt f f' x) : HasFderivAt (h₂ ∘ f) (h₂' • f') x :=
  hh.compHasFderivAtFilter x hf hf.ContinuousAt
#align has_deriv_at.comp_has_fderiv_at HasDerivAt.compHasFderivAt

theorem HasDerivAt.compHasFderivWithinAt {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} {s} (x)
    (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFderivWithinAt f f' s x) :
    HasFderivWithinAt (h₂ ∘ f) (h₂' • f') s x :=
  hh.compHasFderivAtFilter x hf hf.ContinuousWithinAt
#align has_deriv_at.comp_has_fderiv_within_at HasDerivAt.compHasFderivWithinAt

theorem HasDerivWithinAt.compHasFderivWithinAt {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} {s t} (x)
    (hh : HasDerivWithinAt h₂ h₂' t (f x)) (hf : HasFderivWithinAt f f' s x) (hst : MapsTo f s t) :
    HasFderivWithinAt (h₂ ∘ f) (h₂' • f') s x :=
  hh.compHasFderivAtFilter x hf <| hf.ContinuousWithinAt.tendsto_nhds_within hst
#align has_deriv_within_at.comp_has_fderiv_within_at HasDerivWithinAt.compHasFderivWithinAt

/-! ### Derivative of the composition of two scalar functions -/


theorem HasDerivAtFilter.comp (hh₂ : HasDerivAtFilter h₂ h₂' (h x) L')
    (hh : HasDerivAtFilter h h' x L) (hL : Tendsto h L L') :
    HasDerivAtFilter (h₂ ∘ h) (h₂' * h') x L :=
  by
  rw [mul_comm]
  exact hh₂.scomp x hh hL
#align has_deriv_at_filter.comp HasDerivAtFilter.comp

theorem HasDerivWithinAt.comp (hh₂ : HasDerivWithinAt h₂ h₂' s' (h x))
    (hh : HasDerivWithinAt h h' s x) (hst : MapsTo h s s') :
    HasDerivWithinAt (h₂ ∘ h) (h₂' * h') s x :=
  by
  rw [mul_comm]
  exact hh₂.scomp x hh hst
#align has_deriv_within_at.comp HasDerivWithinAt.comp

/-- The chain rule. -/
theorem HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : HasDerivAt h h' x) :
    HasDerivAt (h₂ ∘ h) (h₂' * h') x :=
  hh₂.comp x hh hh.ContinuousAt
#align has_deriv_at.comp HasDerivAt.comp

theorem HasStrictDerivAt.comp (hh₂ : HasStrictDerivAt h₂ h₂' (h x)) (hh : HasStrictDerivAt h h' x) :
    HasStrictDerivAt (h₂ ∘ h) (h₂' * h') x :=
  by
  rw [mul_comm]
  exact hh₂.scomp x hh
#align has_strict_deriv_at.comp HasStrictDerivAt.comp

theorem HasDerivAt.comp_has_deriv_within_at (hh₂ : HasDerivAt h₂ h₂' (h x))
    (hh : HasDerivWithinAt h h' s x) : HasDerivWithinAt (h₂ ∘ h) (h₂' * h') s x :=
  hh₂.HasDerivWithinAt.comp x hh (mapsTo_univ _ _)
#align has_deriv_at.comp_has_deriv_within_at HasDerivAt.comp_has_deriv_within_at

theorem derivWithin.comp (hh₂ : DifferentiableWithinAt 𝕜' h₂ s' (h x))
    (hh : DifferentiableWithinAt 𝕜 h s x) (hs : MapsTo h s s') (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (h₂ ∘ h) s x = derivWithin h₂ s' (h x) * derivWithin h s x :=
  (hh₂.HasDerivWithinAt.comp x hh.HasDerivWithinAt hs).derivWithin hxs
#align deriv_within.comp derivWithin.comp

theorem deriv.comp (hh₂ : DifferentiableAt 𝕜' h₂ (h x)) (hh : DifferentiableAt 𝕜 h x) :
    deriv (h₂ ∘ h) x = deriv h₂ (h x) * deriv h x :=
  (hh₂.HasDerivAt.comp x hh.HasDerivAt).deriv
#align deriv.comp deriv.comp

protected theorem HasDerivAtFilter.iterate {f : 𝕜 → 𝕜} {f' : 𝕜} (hf : HasDerivAtFilter f f' x L)
    (hL : Tendsto f L L) (hx : f x = x) (n : ℕ) : HasDerivAtFilter (f^[n]) (f' ^ n) x L :=
  by
  have := hf.iterate hL hx n
  rwa [ContinuousLinearMap.smul_right_one_pow] at this
#align has_deriv_at_filter.iterate HasDerivAtFilter.iterate

protected theorem HasDerivAt.iterate {f : 𝕜 → 𝕜} {f' : 𝕜} (hf : HasDerivAt f f' x) (hx : f x = x)
    (n : ℕ) : HasDerivAt (f^[n]) (f' ^ n) x :=
  by
  have := HasFderivAt.iterate hf hx n
  rwa [ContinuousLinearMap.smul_right_one_pow] at this
#align has_deriv_at.iterate HasDerivAt.iterate

protected theorem HasDerivWithinAt.iterate {f : 𝕜 → 𝕜} {f' : 𝕜} (hf : HasDerivWithinAt f f' s x)
    (hx : f x = x) (hs : MapsTo f s s) (n : ℕ) : HasDerivWithinAt (f^[n]) (f' ^ n) s x :=
  by
  have := HasFderivWithinAt.iterate hf hx hs n
  rwa [ContinuousLinearMap.smul_right_one_pow] at this
#align has_deriv_within_at.iterate HasDerivWithinAt.iterate

protected theorem HasStrictDerivAt.iterate {f : 𝕜 → 𝕜} {f' : 𝕜} (hf : HasStrictDerivAt f f' x)
    (hx : f x = x) (n : ℕ) : HasStrictDerivAt (f^[n]) (f' ^ n) x :=
  by
  have := hf.iterate hx n
  rwa [ContinuousLinearMap.smul_right_one_pow] at this
#align has_strict_deriv_at.iterate HasStrictDerivAt.iterate

end Composition

section CompositionVector

/-! ### Derivative of the composition of a function between vector spaces and a function on `𝕜` -/


open ContinuousLinearMap

variable {l : F → E} {l' : F →L[𝕜] E}

variable (x)

/-- The composition `l ∘ f` where `l : F → E` and `f : 𝕜 → F`, has a derivative within a set
equal to the Fréchet derivative of `l` applied to the derivative of `f`. -/
theorem HasFderivWithinAt.comp_has_deriv_within_at {t : Set F} (hl : HasFderivWithinAt l l' t (f x))
    (hf : HasDerivWithinAt f f' s x) (hst : MapsTo f s t) : HasDerivWithinAt (l ∘ f) (l' f') s x :=
  by
  simpa only [one_apply, one_smul, smul_right_apply, coe_comp', (· ∘ ·)] using
    (hl.comp x hf.has_fderiv_within_at hst).HasDerivWithinAt
#align has_fderiv_within_at.comp_has_deriv_within_at HasFderivWithinAt.comp_has_deriv_within_at

theorem HasFderivAt.comp_has_deriv_within_at (hl : HasFderivAt l l' (f x))
    (hf : HasDerivWithinAt f f' s x) : HasDerivWithinAt (l ∘ f) (l' f') s x :=
  hl.HasFderivWithinAt.comp_has_deriv_within_at x hf (mapsTo_univ _ _)
#align has_fderiv_at.comp_has_deriv_within_at HasFderivAt.comp_has_deriv_within_at

/-- The composition `l ∘ f` where `l : F → E` and `f : 𝕜 → F`, has a derivative equal to the
Fréchet derivative of `l` applied to the derivative of `f`. -/
theorem HasFderivAt.comp_has_deriv_at (hl : HasFderivAt l l' (f x)) (hf : HasDerivAt f f' x) :
    HasDerivAt (l ∘ f) (l' f') x :=
  has_deriv_within_at_univ.mp <| hl.comp_has_deriv_within_at x hf.HasDerivWithinAt
#align has_fderiv_at.comp_has_deriv_at HasFderivAt.comp_has_deriv_at

theorem HasStrictFderivAt.comp_has_strict_deriv_at (hl : HasStrictFderivAt l l' (f x))
    (hf : HasStrictDerivAt f f' x) : HasStrictDerivAt (l ∘ f) (l' f') x := by
  simpa only [one_apply, one_smul, smul_right_apply, coe_comp', (· ∘ ·)] using
    (hl.comp x hf.has_strict_fderiv_at).HasStrictDerivAt
#align has_strict_fderiv_at.comp_has_strict_deriv_at HasStrictFderivAt.comp_has_strict_deriv_at

theorem fderivWithin.comp_deriv_within {t : Set F} (hl : DifferentiableWithinAt 𝕜 l t (f x))
    (hf : DifferentiableWithinAt 𝕜 f s x) (hs : MapsTo f s t) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (l ∘ f) s x = (fderivWithin 𝕜 l t (f x) : F → E) (derivWithin f s x) :=
  (hl.HasFderivWithinAt.comp_has_deriv_within_at x hf.HasDerivWithinAt hs).derivWithin hxs
#align fderiv_within.comp_deriv_within fderivWithin.comp_deriv_within

theorem fderiv.comp_deriv (hl : DifferentiableAt 𝕜 l (f x)) (hf : DifferentiableAt 𝕜 f x) :
    deriv (l ∘ f) x = (fderiv 𝕜 l (f x) : F → E) (deriv f x) :=
  (hl.HasFderivAt.comp_has_deriv_at x hf.HasDerivAt).deriv
#align fderiv.comp_deriv fderiv.comp_deriv

end CompositionVector

section Mul

/-! ### Derivative of the multiplication of two functions -/


variable {𝕜' 𝔸 : Type _} [NormedField 𝕜'] [NormedRing 𝔸] [NormedAlgebra 𝕜 𝕜'] [NormedAlgebra 𝕜 𝔸]
  {c d : 𝕜 → 𝔸} {c' d' : 𝔸} {u v : 𝕜 → 𝕜'}

theorem HasDerivWithinAt.mul (hc : HasDerivWithinAt c c' s x) (hd : HasDerivWithinAt d d' s x) :
    HasDerivWithinAt (fun y => c y * d y) (c' * d x + c x * d') s x :=
  by
  have := (HasFderivWithinAt.mul' hc hd).HasDerivWithinAt
  rwa [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_right_apply, ContinuousLinearMap.smul_right_apply,
    ContinuousLinearMap.smul_right_apply, ContinuousLinearMap.one_apply, one_smul, one_smul,
    add_comm] at this
#align has_deriv_within_at.mul HasDerivWithinAt.mul

theorem HasDerivAt.mul (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) :
    HasDerivAt (fun y => c y * d y) (c' * d x + c x * d') x :=
  by
  rw [← has_deriv_within_at_univ] at *
  exact hc.mul hd
#align has_deriv_at.mul HasDerivAt.mul

theorem HasStrictDerivAt.mul (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x) :
    HasStrictDerivAt (fun y => c y * d y) (c' * d x + c x * d') x :=
  by
  have := (HasStrictFderivAt.mul' hc hd).HasStrictDerivAt
  rwa [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_right_apply, ContinuousLinearMap.smul_right_apply,
    ContinuousLinearMap.smul_right_apply, ContinuousLinearMap.one_apply, one_smul, one_smul,
    add_comm] at this
#align has_strict_deriv_at.mul HasStrictDerivAt.mul

theorem deriv_within_mul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    derivWithin (fun y => c y * d y) s x = derivWithin c s x * d x + c x * derivWithin d s x :=
  (hc.HasDerivWithinAt.mul hd.HasDerivWithinAt).derivWithin hxs
#align deriv_within_mul deriv_within_mul

@[simp]
theorem deriv_mul (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    deriv (fun y => c y * d y) x = deriv c x * d x + c x * deriv d x :=
  (hc.HasDerivAt.mul hd.HasDerivAt).deriv
#align deriv_mul deriv_mul

theorem HasDerivWithinAt.mul_const (hc : HasDerivWithinAt c c' s x) (d : 𝔸) :
    HasDerivWithinAt (fun y => c y * d) (c' * d) s x :=
  by
  convert hc.mul (has_deriv_within_at_const x s d)
  rw [mul_zero, add_zero]
#align has_deriv_within_at.mul_const HasDerivWithinAt.mul_const

theorem HasDerivAt.mul_const (hc : HasDerivAt c c' x) (d : 𝔸) :
    HasDerivAt (fun y => c y * d) (c' * d) x :=
  by
  rw [← has_deriv_within_at_univ] at *
  exact hc.mul_const d
#align has_deriv_at.mul_const HasDerivAt.mul_const

theorem has_deriv_at_mul_const (c : 𝕜) : HasDerivAt (fun x => x * c) c x := by
  simpa only [one_mul] using (has_deriv_at_id' x).mul_const c
#align has_deriv_at_mul_const has_deriv_at_mul_const

theorem HasStrictDerivAt.mul_const (hc : HasStrictDerivAt c c' x) (d : 𝔸) :
    HasStrictDerivAt (fun y => c y * d) (c' * d) x :=
  by
  convert hc.mul (has_strict_deriv_at_const x d)
  rw [mul_zero, add_zero]
#align has_strict_deriv_at.mul_const HasStrictDerivAt.mul_const

theorem deriv_within_mul_const (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (d : 𝔸) :
    derivWithin (fun y => c y * d) s x = derivWithin c s x * d :=
  (hc.HasDerivWithinAt.mul_const d).derivWithin hxs
#align deriv_within_mul_const deriv_within_mul_const

theorem deriv_mul_const (hc : DifferentiableAt 𝕜 c x) (d : 𝔸) :
    deriv (fun y => c y * d) x = deriv c x * d :=
  (hc.HasDerivAt.mul_const d).deriv
#align deriv_mul_const deriv_mul_const

theorem deriv_mul_const_field (v : 𝕜') : deriv (fun y => u y * v) x = deriv u x * v :=
  by
  by_cases hu : DifferentiableAt 𝕜 u x
  · exact deriv_mul_const hu v
  · rw [deriv_zero_of_not_differentiable_at hu, zero_mul]
    rcases eq_or_ne v 0 with (rfl | hd)
    · simp only [mul_zero, deriv_const]
    · refine' deriv_zero_of_not_differentiable_at (mt (fun H => _) hu)
      simpa only [mul_inv_cancel_right₀ hd] using H.mul_const v⁻¹
#align deriv_mul_const_field deriv_mul_const_field

@[simp]
theorem deriv_mul_const_field' (v : 𝕜') : (deriv fun x => u x * v) = fun x => deriv u x * v :=
  funext fun _ => deriv_mul_const_field v
#align deriv_mul_const_field' deriv_mul_const_field'

theorem HasDerivWithinAt.const_mul (c : 𝔸) (hd : HasDerivWithinAt d d' s x) :
    HasDerivWithinAt (fun y => c * d y) (c * d') s x :=
  by
  convert (has_deriv_within_at_const x s c).mul hd
  rw [zero_mul, zero_add]
#align has_deriv_within_at.const_mul HasDerivWithinAt.const_mul

theorem HasDerivAt.const_mul (c : 𝔸) (hd : HasDerivAt d d' x) :
    HasDerivAt (fun y => c * d y) (c * d') x :=
  by
  rw [← has_deriv_within_at_univ] at *
  exact hd.const_mul c
#align has_deriv_at.const_mul HasDerivAt.const_mul

theorem HasStrictDerivAt.const_mul (c : 𝔸) (hd : HasStrictDerivAt d d' x) :
    HasStrictDerivAt (fun y => c * d y) (c * d') x :=
  by
  convert (has_strict_deriv_at_const _ _).mul hd
  rw [zero_mul, zero_add]
#align has_strict_deriv_at.const_mul HasStrictDerivAt.const_mul

theorem deriv_within_const_mul (hxs : UniqueDiffWithinAt 𝕜 s x) (c : 𝔸)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    derivWithin (fun y => c * d y) s x = c * derivWithin d s x :=
  (hd.HasDerivWithinAt.const_mul c).derivWithin hxs
#align deriv_within_const_mul deriv_within_const_mul

theorem deriv_const_mul (c : 𝔸) (hd : DifferentiableAt 𝕜 d x) :
    deriv (fun y => c * d y) x = c * deriv d x :=
  (hd.HasDerivAt.const_mul c).deriv
#align deriv_const_mul deriv_const_mul

theorem deriv_const_mul_field (u : 𝕜') : deriv (fun y => u * v y) x = u * deriv v x := by
  simp only [mul_comm u, deriv_mul_const_field]
#align deriv_const_mul_field deriv_const_mul_field

@[simp]
theorem deriv_const_mul_field' (u : 𝕜') : (deriv fun x => u * v x) = fun x => u * deriv v x :=
  funext fun x => deriv_const_mul_field u
#align deriv_const_mul_field' deriv_const_mul_field'

end Mul

section Inverse

/-! ### Derivative of `x ↦ x⁻¹` -/


theorem has_strict_deriv_at_inv (hx : x ≠ 0) : HasStrictDerivAt Inv.inv (-(x ^ 2)⁻¹) x :=
  by
  suffices
    (fun p : 𝕜 × 𝕜 => (p.1 - p.2) * ((x * x)⁻¹ - (p.1 * p.2)⁻¹)) =o[𝓝 (x, x)] fun p =>
      (p.1 - p.2) * 1
    by
    refine' this.congr' _ (eventually_of_forall fun _ => mul_one _)
    refine' eventually.mono (IsOpen.mem_nhds (is_open_ne.prod is_open_ne) ⟨hx, hx⟩) _
    rintro ⟨y, z⟩ ⟨hy, hz⟩
    simp only [mem_set_of_eq] at hy hz
    -- hy : y ≠ 0, hz : z ≠ 0
    field_simp [hx, hy, hz]
    ring
  refine' (is_O_refl (fun p : 𝕜 × 𝕜 => p.1 - p.2) _).mul_is_o ((is_o_one_iff _).2 _)
  rw [← sub_self (x * x)⁻¹]
  exact tendsto_const_nhds.sub ((continuous_mul.tendsto (x, x)).inv₀ <| mul_ne_zero hx hx)
#align has_strict_deriv_at_inv has_strict_deriv_at_inv

theorem has_deriv_at_inv (x_ne_zero : x ≠ 0) : HasDerivAt (fun y => y⁻¹) (-(x ^ 2)⁻¹) x :=
  (has_strict_deriv_at_inv x_ne_zero).HasDerivAt
#align has_deriv_at_inv has_deriv_at_inv

theorem has_deriv_within_at_inv (x_ne_zero : x ≠ 0) (s : Set 𝕜) :
    HasDerivWithinAt (fun x => x⁻¹) (-(x ^ 2)⁻¹) s x :=
  (has_deriv_at_inv x_ne_zero).HasDerivWithinAt
#align has_deriv_within_at_inv has_deriv_within_at_inv

theorem differentiable_at_inv : DifferentiableAt 𝕜 (fun x => x⁻¹) x ↔ x ≠ 0 :=
  ⟨fun H => NormedField.continuous_at_inv.1 H.ContinuousAt, fun H =>
    (has_deriv_at_inv H).DifferentiableAt⟩
#align differentiable_at_inv differentiable_at_inv

theorem differentiable_within_at_inv (x_ne_zero : x ≠ 0) :
    DifferentiableWithinAt 𝕜 (fun x => x⁻¹) s x :=
  (differentiable_at_inv.2 x_ne_zero).DifferentiableWithinAt
#align differentiable_within_at_inv differentiable_within_at_inv

theorem differentiable_on_inv : DifferentiableOn 𝕜 (fun x : 𝕜 => x⁻¹) { x | x ≠ 0 } := fun x hx =>
  differentiable_within_at_inv hx
#align differentiable_on_inv differentiable_on_inv

theorem deriv_inv : deriv (fun x => x⁻¹) x = -(x ^ 2)⁻¹ :=
  by
  rcases eq_or_ne x 0 with (rfl | hne)
  · simp [deriv_zero_of_not_differentiable_at (mt differentiable_at_inv.1 (not_not.2 rfl))]
  · exact (has_deriv_at_inv hne).deriv
#align deriv_inv deriv_inv

@[simp]
theorem deriv_inv' : (deriv fun x : 𝕜 => x⁻¹) = fun x => -(x ^ 2)⁻¹ :=
  funext fun x => deriv_inv
#align deriv_inv' deriv_inv'

theorem deriv_within_inv (x_ne_zero : x ≠ 0) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => x⁻¹) s x = -(x ^ 2)⁻¹ :=
  by
  rw [DifferentiableAt.deriv_within (differentiable_at_inv.2 x_ne_zero) hxs]
  exact deriv_inv
#align deriv_within_inv deriv_within_inv

theorem hasFderivAtInv (x_ne_zero : x ≠ 0) :
    HasFderivAt (fun x => x⁻¹) (smulRight (1 : 𝕜 →L[𝕜] 𝕜) (-(x ^ 2)⁻¹) : 𝕜 →L[𝕜] 𝕜) x :=
  has_deriv_at_inv x_ne_zero
#align has_fderiv_at_inv hasFderivAtInv

theorem hasFderivWithinAtInv (x_ne_zero : x ≠ 0) :
    HasFderivWithinAt (fun x => x⁻¹) (smulRight (1 : 𝕜 →L[𝕜] 𝕜) (-(x ^ 2)⁻¹) : 𝕜 →L[𝕜] 𝕜) s x :=
  (hasFderivAtInv x_ne_zero).HasFderivWithinAt
#align has_fderiv_within_at_inv hasFderivWithinAtInv

theorem fderiv_inv : fderiv 𝕜 (fun x => x⁻¹) x = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (-(x ^ 2)⁻¹) := by
  rw [← deriv_fderiv, deriv_inv]
#align fderiv_inv fderiv_inv

theorem fderiv_within_inv (x_ne_zero : x ≠ 0) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x => x⁻¹) s x = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (-(x ^ 2)⁻¹) :=
  by
  rw [DifferentiableAt.fderiv_within (differentiable_at_inv.2 x_ne_zero) hxs]
  exact fderiv_inv
#align fderiv_within_inv fderiv_within_inv

variable {c : 𝕜 → 𝕜} {h : E → 𝕜} {c' : 𝕜} {z : E} {S : Set E}

theorem HasDerivWithinAt.inv (hc : HasDerivWithinAt c c' s x) (hx : c x ≠ 0) :
    HasDerivWithinAt (fun y => (c y)⁻¹) (-c' / c x ^ 2) s x :=
  by
  convert (has_deriv_at_inv hx).comp_has_deriv_within_at x hc
  field_simp
#align has_deriv_within_at.inv HasDerivWithinAt.inv

theorem HasDerivAt.inv (hc : HasDerivAt c c' x) (hx : c x ≠ 0) :
    HasDerivAt (fun y => (c y)⁻¹) (-c' / c x ^ 2) x :=
  by
  rw [← has_deriv_within_at_univ] at *
  exact hc.inv hx
#align has_deriv_at.inv HasDerivAt.inv

theorem DifferentiableWithinAt.inv (hf : DifferentiableWithinAt 𝕜 h S z) (hz : h z ≠ 0) :
    DifferentiableWithinAt 𝕜 (fun x => (h x)⁻¹) S z :=
  (differentiable_at_inv.mpr hz).comp_differentiable_within_at z hf
#align differentiable_within_at.inv DifferentiableWithinAt.inv

@[simp]
theorem DifferentiableAt.inv (hf : DifferentiableAt 𝕜 h z) (hz : h z ≠ 0) :
    DifferentiableAt 𝕜 (fun x => (h x)⁻¹) z :=
  (differentiable_at_inv.mpr hz).comp z hf
#align differentiable_at.inv DifferentiableAt.inv

theorem DifferentiableOn.inv (hf : DifferentiableOn 𝕜 h S) (hz : ∀ x ∈ S, h x ≠ 0) :
    DifferentiableOn 𝕜 (fun x => (h x)⁻¹) S := fun x h => (hf x h).inv (hz x h)
#align differentiable_on.inv DifferentiableOn.inv

@[simp]
theorem Differentiable.inv (hf : Differentiable 𝕜 h) (hz : ∀ x, h x ≠ 0) :
    Differentiable 𝕜 fun x => (h x)⁻¹ := fun x => (hf x).inv (hz x)
#align differentiable.inv Differentiable.inv

theorem deriv_within_inv' (hc : DifferentiableWithinAt 𝕜 c s x) (hx : c x ≠ 0)
    (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => (c x)⁻¹) s x = -derivWithin c s x / c x ^ 2 :=
  (hc.HasDerivWithinAt.inv hx).derivWithin hxs
#align deriv_within_inv' deriv_within_inv'

@[simp]
theorem deriv_inv'' (hc : DifferentiableAt 𝕜 c x) (hx : c x ≠ 0) :
    deriv (fun x => (c x)⁻¹) x = -deriv c x / c x ^ 2 :=
  (hc.HasDerivAt.inv hx).deriv
#align deriv_inv'' deriv_inv''

end Inverse

section Division

/-! ### Derivative of `x ↦ c x / d x` -/


variable {𝕜' : Type _} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] {c d : 𝕜 → 𝕜'} {c' d' : 𝕜'}

theorem HasDerivWithinAt.div (hc : HasDerivWithinAt c c' s x) (hd : HasDerivWithinAt d d' s x)
    (hx : d x ≠ 0) : HasDerivWithinAt (fun y => c y / d y) ((c' * d x - c x * d') / d x ^ 2) s x :=
  by
  convert hc.mul ((has_deriv_at_inv hx).comp_has_deriv_within_at x hd)
  · simp only [div_eq_mul_inv]
  · field_simp
    ring
#align has_deriv_within_at.div HasDerivWithinAt.div

theorem HasStrictDerivAt.div (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x)
    (hx : d x ≠ 0) : HasStrictDerivAt (fun y => c y / d y) ((c' * d x - c x * d') / d x ^ 2) x :=
  by
  convert hc.mul ((has_strict_deriv_at_inv hx).comp x hd)
  · simp only [div_eq_mul_inv]
  · field_simp
    ring
#align has_strict_deriv_at.div HasStrictDerivAt.div

theorem HasDerivAt.div (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) (hx : d x ≠ 0) :
    HasDerivAt (fun y => c y / d y) ((c' * d x - c x * d') / d x ^ 2) x :=
  by
  rw [← has_deriv_within_at_univ] at *
  exact hc.div hd hx
#align has_deriv_at.div HasDerivAt.div

theorem DifferentiableWithinAt.div (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) (hx : d x ≠ 0) :
    DifferentiableWithinAt 𝕜 (fun x => c x / d x) s x :=
  (hc.HasDerivWithinAt.div hd.HasDerivWithinAt hx).DifferentiableWithinAt
#align differentiable_within_at.div DifferentiableWithinAt.div

@[simp]
theorem DifferentiableAt.div (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x)
    (hx : d x ≠ 0) : DifferentiableAt 𝕜 (fun x => c x / d x) x :=
  (hc.HasDerivAt.div hd.HasDerivAt hx).DifferentiableAt
#align differentiable_at.div DifferentiableAt.div

theorem DifferentiableOn.div (hc : DifferentiableOn 𝕜 c s) (hd : DifferentiableOn 𝕜 d s)
    (hx : ∀ x ∈ s, d x ≠ 0) : DifferentiableOn 𝕜 (fun x => c x / d x) s := fun x h =>
  (hc x h).div (hd x h) (hx x h)
#align differentiable_on.div DifferentiableOn.div

@[simp]
theorem Differentiable.div (hc : Differentiable 𝕜 c) (hd : Differentiable 𝕜 d) (hx : ∀ x, d x ≠ 0) :
    Differentiable 𝕜 fun x => c x / d x := fun x => (hc x).div (hd x) (hx x)
#align differentiable.div Differentiable.div

theorem deriv_within_div (hc : DifferentiableWithinAt 𝕜 c s x) (hd : DifferentiableWithinAt 𝕜 d s x)
    (hx : d x ≠ 0) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => c x / d x) s x =
      (derivWithin c s x * d x - c x * derivWithin d s x) / d x ^ 2 :=
  (hc.HasDerivWithinAt.div hd.HasDerivWithinAt hx).derivWithin hxs
#align deriv_within_div deriv_within_div

@[simp]
theorem deriv_div (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) (hx : d x ≠ 0) :
    deriv (fun x => c x / d x) x = (deriv c x * d x - c x * deriv d x) / d x ^ 2 :=
  (hc.HasDerivAt.div hd.HasDerivAt hx).deriv
#align deriv_div deriv_div

theorem HasDerivAt.div_const (hc : HasDerivAt c c' x) (d : 𝕜') :
    HasDerivAt (fun x => c x / d) (c' / d) x := by
  simpa only [div_eq_mul_inv] using hc.mul_const d⁻¹
#align has_deriv_at.div_const HasDerivAt.div_const

theorem HasDerivWithinAt.div_const (hc : HasDerivWithinAt c c' s x) (d : 𝕜') :
    HasDerivWithinAt (fun x => c x / d) (c' / d) s x := by
  simpa only [div_eq_mul_inv] using hc.mul_const d⁻¹
#align has_deriv_within_at.div_const HasDerivWithinAt.div_const

theorem HasStrictDerivAt.div_const (hc : HasStrictDerivAt c c' x) (d : 𝕜') :
    HasStrictDerivAt (fun x => c x / d) (c' / d) x := by
  simpa only [div_eq_mul_inv] using hc.mul_const d⁻¹
#align has_strict_deriv_at.div_const HasStrictDerivAt.div_const

theorem DifferentiableWithinAt.div_const (hc : DifferentiableWithinAt 𝕜 c s x) {d : 𝕜'} :
    DifferentiableWithinAt 𝕜 (fun x => c x / d) s x :=
  (hc.HasDerivWithinAt.div_const _).DifferentiableWithinAt
#align differentiable_within_at.div_const DifferentiableWithinAt.div_const

@[simp]
theorem DifferentiableAt.div_const (hc : DifferentiableAt 𝕜 c x) {d : 𝕜'} :
    DifferentiableAt 𝕜 (fun x => c x / d) x :=
  (hc.HasDerivAt.div_const _).DifferentiableAt
#align differentiable_at.div_const DifferentiableAt.div_const

theorem DifferentiableOn.div_const (hc : DifferentiableOn 𝕜 c s) {d : 𝕜'} :
    DifferentiableOn 𝕜 (fun x => c x / d) s := fun x hx => (hc x hx).div_const
#align differentiable_on.div_const DifferentiableOn.div_const

@[simp]
theorem Differentiable.div_const (hc : Differentiable 𝕜 c) {d : 𝕜'} :
    Differentiable 𝕜 fun x => c x / d := fun x => (hc x).div_const
#align differentiable.div_const Differentiable.div_const

theorem deriv_within_div_const (hc : DifferentiableWithinAt 𝕜 c s x) {d : 𝕜'}
    (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin (fun x => c x / d) s x = derivWithin c s x / d :=
  by simp [div_eq_inv_mul, deriv_within_const_mul, hc, hxs]
#align deriv_within_div_const deriv_within_div_const

@[simp]
theorem deriv_div_const (d : 𝕜') : deriv (fun x => c x / d) x = deriv c x / d := by
  simp only [div_eq_mul_inv, deriv_mul_const_field]
#align deriv_div_const deriv_div_const

end Division

section ClmCompApply

/-! ### Derivative of the pointwise composition/application of continuous linear maps -/


open ContinuousLinearMap

variable {G : Type _} [NormedAddCommGroup G] [NormedSpace 𝕜 G] {c : 𝕜 → F →L[𝕜] G} {c' : F →L[𝕜] G}
  {d : 𝕜 → E →L[𝕜] F} {d' : E →L[𝕜] F} {u : 𝕜 → F} {u' : F}

theorem HasStrictDerivAt.clm_comp (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x) :
    HasStrictDerivAt (fun y => (c y).comp (d y)) (c'.comp (d x) + (c x).comp d') x :=
  by
  have := (hc.has_strict_fderiv_at.clm_comp hd.has_strict_fderiv_at).HasStrictDerivAt
  rwa [add_apply, comp_apply, comp_apply, smul_right_apply, smul_right_apply, one_apply, one_smul,
    one_smul, add_comm] at this
#align has_strict_deriv_at.clm_comp HasStrictDerivAt.clm_comp

theorem HasDerivWithinAt.clm_comp (hc : HasDerivWithinAt c c' s x)
    (hd : HasDerivWithinAt d d' s x) :
    HasDerivWithinAt (fun y => (c y).comp (d y)) (c'.comp (d x) + (c x).comp d') s x :=
  by
  have := (hc.has_fderiv_within_at.clm_comp hd.has_fderiv_within_at).HasDerivWithinAt
  rwa [add_apply, comp_apply, comp_apply, smul_right_apply, smul_right_apply, one_apply, one_smul,
    one_smul, add_comm] at this
#align has_deriv_within_at.clm_comp HasDerivWithinAt.clm_comp

theorem HasDerivAt.clm_comp (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) :
    HasDerivAt (fun y => (c y).comp (d y)) (c'.comp (d x) + (c x).comp d') x :=
  by
  rw [← has_deriv_within_at_univ] at *
  exact hc.clm_comp hd
#align has_deriv_at.clm_comp HasDerivAt.clm_comp

theorem deriv_within_clm_comp (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun y => (c y).comp (d y)) s x =
      (derivWithin c s x).comp (d x) + (c x).comp (derivWithin d s x) :=
  (hc.HasDerivWithinAt.clm_comp hd.HasDerivWithinAt).derivWithin hxs
#align deriv_within_clm_comp deriv_within_clm_comp

theorem deriv_clm_comp (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    deriv (fun y => (c y).comp (d y)) x = (deriv c x).comp (d x) + (c x).comp (deriv d x) :=
  (hc.HasDerivAt.clm_comp hd.HasDerivAt).deriv
#align deriv_clm_comp deriv_clm_comp

theorem HasStrictDerivAt.clm_apply (hc : HasStrictDerivAt c c' x) (hu : HasStrictDerivAt u u' x) :
    HasStrictDerivAt (fun y => (c y) (u y)) (c' (u x) + c x u') x :=
  by
  have := (hc.has_strict_fderiv_at.clm_apply hu.has_strict_fderiv_at).HasStrictDerivAt
  rwa [add_apply, comp_apply, flip_apply, smul_right_apply, smul_right_apply, one_apply, one_smul,
    one_smul, add_comm] at this
#align has_strict_deriv_at.clm_apply HasStrictDerivAt.clm_apply

theorem HasDerivWithinAt.clm_apply (hc : HasDerivWithinAt c c' s x)
    (hu : HasDerivWithinAt u u' s x) :
    HasDerivWithinAt (fun y => (c y) (u y)) (c' (u x) + c x u') s x :=
  by
  have := (hc.has_fderiv_within_at.clm_apply hu.has_fderiv_within_at).HasDerivWithinAt
  rwa [add_apply, comp_apply, flip_apply, smul_right_apply, smul_right_apply, one_apply, one_smul,
    one_smul, add_comm] at this
#align has_deriv_within_at.clm_apply HasDerivWithinAt.clm_apply

theorem HasDerivAt.clm_apply (hc : HasDerivAt c c' x) (hu : HasDerivAt u u' x) :
    HasDerivAt (fun y => (c y) (u y)) (c' (u x) + c x u') x :=
  by
  have := (hc.has_fderiv_at.clm_apply hu.has_fderiv_at).HasDerivAt
  rwa [add_apply, comp_apply, flip_apply, smul_right_apply, smul_right_apply, one_apply, one_smul,
    one_smul, add_comm] at this
#align has_deriv_at.clm_apply HasDerivAt.clm_apply

theorem deriv_within_clm_apply (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (hu : DifferentiableWithinAt 𝕜 u s x) :
    derivWithin (fun y => (c y) (u y)) s x = derivWithin c s x (u x) + c x (derivWithin u s x) :=
  (hc.HasDerivWithinAt.clmApply hu.HasDerivWithinAt).derivWithin hxs
#align deriv_within_clm_apply deriv_within_clm_apply

theorem deriv_clm_apply (hc : DifferentiableAt 𝕜 c x) (hu : DifferentiableAt 𝕜 u x) :
    deriv (fun y => (c y) (u y)) x = deriv c x (u x) + c x (deriv u x) :=
  (hc.HasDerivAt.clmApply hu.HasDerivAt).deriv
#align deriv_clm_apply deriv_clm_apply

end ClmCompApply

theorem HasStrictDerivAt.hasStrictFderivAtEquiv {f : 𝕜 → 𝕜} {f' x : 𝕜}
    (hf : HasStrictDerivAt f f' x) (hf' : f' ≠ 0) :
    HasStrictFderivAt f (ContinuousLinearEquiv.unitsEquivAut 𝕜 (Units.mk0 f' hf') : 𝕜 →L[𝕜] 𝕜) x :=
  hf
#align has_strict_deriv_at.has_strict_fderiv_at_equiv HasStrictDerivAt.hasStrictFderivAtEquiv

theorem HasDerivAt.hasFderivAtEquiv {f : 𝕜 → 𝕜} {f' x : 𝕜} (hf : HasDerivAt f f' x) (hf' : f' ≠ 0) :
    HasFderivAt f (ContinuousLinearEquiv.unitsEquivAut 𝕜 (Units.mk0 f' hf') : 𝕜 →L[𝕜] 𝕜) x :=
  hf
#align has_deriv_at.has_fderiv_at_equiv HasDerivAt.hasFderivAtEquiv

/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a` in the strict sense, then `g` has the derivative `f'⁻¹` at `a`
in the strict sense.

This is one of the easy parts of the inverse function theorem: it assumes that we already have an
inverse function. -/
theorem HasStrictDerivAt.of_local_left_inverse {f g : 𝕜 → 𝕜} {f' a : 𝕜} (hg : ContinuousAt g a)
    (hf : HasStrictDerivAt f f' (g a)) (hf' : f' ≠ 0) (hfg : ∀ᶠ y in 𝓝 a, f (g y) = y) :
    HasStrictDerivAt g f'⁻¹ a :=
  (hf.hasStrictFderivAtEquiv hf').ofLocalLeftInverse hg hfg
#align has_strict_deriv_at.of_local_left_inverse HasStrictDerivAt.of_local_left_inverse

/-- If `f` is a local homeomorphism defined on a neighbourhood of `f.symm a`, and `f` has a
nonzero derivative `f'` at `f.symm a` in the strict sense, then `f.symm` has the derivative `f'⁻¹`
at `a` in the strict sense.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem LocalHomeomorph.has_strict_deriv_at_symm (f : LocalHomeomorph 𝕜 𝕜) {a f' : 𝕜}
    (ha : a ∈ f.target) (hf' : f' ≠ 0) (htff' : HasStrictDerivAt f f' (f.symm a)) :
    HasStrictDerivAt f.symm f'⁻¹ a :=
  htff'.ofLocalLeftInverse (f.symm.ContinuousAt ha) hf' (f.eventually_right_inverse ha)
#align local_homeomorph.has_strict_deriv_at_symm LocalHomeomorph.has_strict_deriv_at_symm

/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a`, then `g` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem HasDerivAt.of_local_left_inverse {f g : 𝕜 → 𝕜} {f' a : 𝕜} (hg : ContinuousAt g a)
    (hf : HasDerivAt f f' (g a)) (hf' : f' ≠ 0) (hfg : ∀ᶠ y in 𝓝 a, f (g y) = y) :
    HasDerivAt g f'⁻¹ a :=
  (hf.hasFderivAtEquiv hf').ofLocalLeftInverse hg hfg
#align has_deriv_at.of_local_left_inverse HasDerivAt.of_local_left_inverse

/-- If `f` is a local homeomorphism defined on a neighbourhood of `f.symm a`, and `f` has an
nonzero derivative `f'` at `f.symm a`, then `f.symm` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem LocalHomeomorph.has_deriv_at_symm (f : LocalHomeomorph 𝕜 𝕜) {a f' : 𝕜} (ha : a ∈ f.target)
    (hf' : f' ≠ 0) (htff' : HasDerivAt f f' (f.symm a)) : HasDerivAt f.symm f'⁻¹ a :=
  htff'.ofLocalLeftInverse (f.symm.ContinuousAt ha) hf' (f.eventually_right_inverse ha)
#align local_homeomorph.has_deriv_at_symm LocalHomeomorph.has_deriv_at_symm

theorem HasDerivAt.eventually_ne (h : HasDerivAt f f' x) (hf' : f' ≠ 0) :
    ∀ᶠ z in 𝓝[≠] x, f z ≠ f x :=
  (has_deriv_at_iff_has_fderiv_at.1 h).eventually_ne
    ⟨‖f'‖⁻¹, fun z => by field_simp [norm_smul, mt norm_eq_zero.1 hf'] ⟩
#align has_deriv_at.eventually_ne HasDerivAt.eventually_ne

theorem HasDerivAt.tendsto_punctured_nhds (h : HasDerivAt f f' x) (hf' : f' ≠ 0) :
    Tendsto f (𝓝[≠] x) (𝓝[≠] f x) :=
  tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ h.ContinuousAt.ContinuousWithinAt
    (h.eventually_ne hf')
#align has_deriv_at.tendsto_punctured_nhds HasDerivAt.tendsto_punctured_nhds

theorem not_differentiable_within_at_of_local_left_inverse_has_deriv_within_at_zero {f g : 𝕜 → 𝕜}
    {a : 𝕜} {s t : Set 𝕜} (ha : a ∈ s) (hsu : UniqueDiffWithinAt 𝕜 s a)
    (hf : HasDerivWithinAt f 0 t (g a)) (hst : MapsTo g s t) (hfg : f ∘ g =ᶠ[𝓝[s] a] id) :
    ¬DifferentiableWithinAt 𝕜 g s a := by
  intro hg
  have := (hf.comp a hg.has_deriv_within_at hst).congr_of_eventually_eq_of_mem hfg.symm ha
  simpa using hsu.eq_deriv _ this (has_deriv_within_at_id _ _)
#align
  not_differentiable_within_at_of_local_left_inverse_has_deriv_within_at_zero not_differentiable_within_at_of_local_left_inverse_has_deriv_within_at_zero

theorem not_differentiable_at_of_local_left_inverse_has_deriv_at_zero {f g : 𝕜 → 𝕜} {a : 𝕜}
    (hf : HasDerivAt f 0 (g a)) (hfg : f ∘ g =ᶠ[𝓝 a] id) : ¬DifferentiableAt 𝕜 g a :=
  by
  intro hg
  have := (hf.comp a hg.has_deriv_at).congr_of_eventually_eq hfg.symm
  simpa using this.unique (has_deriv_at_id a)
#align
  not_differentiable_at_of_local_left_inverse_has_deriv_at_zero not_differentiable_at_of_local_left_inverse_has_deriv_at_zero

end

namespace Polynomial

/-! ### Derivative of a polynomial -/


variable {x : 𝕜} {s : Set 𝕜}

variable (p : 𝕜[X])

/-- The derivative (in the analysis sense) of a polynomial `p` is given by `p.derivative`. -/
protected theorem has_strict_deriv_at (x : 𝕜) :
    HasStrictDerivAt (fun x => p.eval x) (p.derivative.eval x) x :=
  by
  apply p.induction_on
  · simp [has_strict_deriv_at_const]
  · intro p q hp hq
    convert hp.add hq <;> simp
  · intro n a h
    convert h.mul (has_strict_deriv_at_id x)
    · ext y
      simp [pow_add, mul_assoc]
    · simp only [pow_add, pow_one, derivative_mul, derivative_C, zero_mul, derivative_X_pow,
        derivative_X, mul_one, zero_add, eval_mul, eval_C, eval_add, eval_nat_cast, eval_pow,
        eval_X, id.def]
      ring
#align polynomial.has_strict_deriv_at Polynomial.has_strict_deriv_at

/-- The derivative (in the analysis sense) of a polynomial `p` is given by `p.derivative`. -/
protected theorem has_deriv_at (x : 𝕜) : HasDerivAt (fun x => p.eval x) (p.derivative.eval x) x :=
  (p.HasStrictDerivAt x).HasDerivAt
#align polynomial.has_deriv_at Polynomial.has_deriv_at

protected theorem has_deriv_within_at (x : 𝕜) (s : Set 𝕜) :
    HasDerivWithinAt (fun x => p.eval x) (p.derivative.eval x) s x :=
  (p.HasDerivAt x).HasDerivWithinAt
#align polynomial.has_deriv_within_at Polynomial.has_deriv_within_at

protected theorem differentiable_at : DifferentiableAt 𝕜 (fun x => p.eval x) x :=
  (p.HasDerivAt x).DifferentiableAt
#align polynomial.differentiable_at Polynomial.differentiable_at

protected theorem differentiable_within_at : DifferentiableWithinAt 𝕜 (fun x => p.eval x) s x :=
  p.DifferentiableAt.DifferentiableWithinAt
#align polynomial.differentiable_within_at Polynomial.differentiable_within_at

protected theorem differentiable : Differentiable 𝕜 fun x => p.eval x := fun x => p.DifferentiableAt
#align polynomial.differentiable Polynomial.differentiable

protected theorem differentiable_on : DifferentiableOn 𝕜 (fun x => p.eval x) s :=
  p.Differentiable.DifferentiableOn
#align polynomial.differentiable_on Polynomial.differentiable_on

@[simp]
protected theorem deriv : deriv (fun x => p.eval x) x = p.derivative.eval x :=
  (p.HasDerivAt x).deriv
#align polynomial.deriv Polynomial.deriv

protected theorem deriv_within (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => p.eval x) s x = p.derivative.eval x :=
  by
  rw [DifferentiableAt.deriv_within p.differentiable_at hxs]
  exact p.deriv
#align polynomial.deriv_within Polynomial.deriv_within

protected theorem hasFderivAt (x : 𝕜) :
    HasFderivAt (fun x => p.eval x) (smulRight (1 : 𝕜 →L[𝕜] 𝕜) (p.derivative.eval x)) x :=
  p.HasDerivAt x
#align polynomial.has_fderiv_at Polynomial.hasFderivAt

protected theorem hasFderivWithinAt (x : 𝕜) :
    HasFderivWithinAt (fun x => p.eval x) (smulRight (1 : 𝕜 →L[𝕜] 𝕜) (p.derivative.eval x)) s x :=
  (p.HasFderivAt x).HasFderivWithinAt
#align polynomial.has_fderiv_within_at Polynomial.hasFderivWithinAt

@[simp]
protected theorem fderiv :
    fderiv 𝕜 (fun x => p.eval x) x = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (p.derivative.eval x) :=
  (p.HasFderivAt x).fderiv
#align polynomial.fderiv Polynomial.fderiv

protected theorem fderiv_within (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x => p.eval x) s x = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (p.derivative.eval x) :=
  (p.HasFderivWithinAt x).fderivWithin hxs
#align polynomial.fderiv_within Polynomial.fderiv_within

end Polynomial

section Pow

/-! ### Derivative of `x ↦ x^n` for `n : ℕ` -/


variable {x : 𝕜} {s : Set 𝕜} {c : 𝕜 → 𝕜} {c' : 𝕜}

variable (n : ℕ)

theorem has_strict_deriv_at_pow (n : ℕ) (x : 𝕜) :
    HasStrictDerivAt (fun x => x ^ n) ((n : 𝕜) * x ^ (n - 1)) x :=
  by
  convert (Polynomial.c (1 : 𝕜) * Polynomial.x ^ n).HasStrictDerivAt x
  · simp
  · rw [Polynomial.derivative_C_mul_X_pow]
    simp
#align has_strict_deriv_at_pow has_strict_deriv_at_pow

theorem has_deriv_at_pow (n : ℕ) (x : 𝕜) : HasDerivAt (fun x => x ^ n) ((n : 𝕜) * x ^ (n - 1)) x :=
  (has_strict_deriv_at_pow n x).HasDerivAt
#align has_deriv_at_pow has_deriv_at_pow

theorem has_deriv_within_at_pow (n : ℕ) (x : 𝕜) (s : Set 𝕜) :
    HasDerivWithinAt (fun x => x ^ n) ((n : 𝕜) * x ^ (n - 1)) s x :=
  (has_deriv_at_pow n x).HasDerivWithinAt
#align has_deriv_within_at_pow has_deriv_within_at_pow

theorem differentiable_at_pow : DifferentiableAt 𝕜 (fun x => x ^ n) x :=
  (has_deriv_at_pow n x).DifferentiableAt
#align differentiable_at_pow differentiable_at_pow

theorem differentiable_within_at_pow : DifferentiableWithinAt 𝕜 (fun x => x ^ n) s x :=
  (differentiable_at_pow n).DifferentiableWithinAt
#align differentiable_within_at_pow differentiable_within_at_pow

theorem differentiable_pow : Differentiable 𝕜 fun x : 𝕜 => x ^ n := fun x => differentiable_at_pow n
#align differentiable_pow differentiable_pow

theorem differentiable_on_pow : DifferentiableOn 𝕜 (fun x => x ^ n) s :=
  (differentiable_pow n).DifferentiableOn
#align differentiable_on_pow differentiable_on_pow

theorem deriv_pow : deriv (fun x => x ^ n) x = (n : 𝕜) * x ^ (n - 1) :=
  (has_deriv_at_pow n x).deriv
#align deriv_pow deriv_pow

@[simp]
theorem deriv_pow' : (deriv fun x => x ^ n) = fun x => (n : 𝕜) * x ^ (n - 1) :=
  funext fun x => deriv_pow n
#align deriv_pow' deriv_pow'

theorem deriv_within_pow (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => x ^ n) s x = (n : 𝕜) * x ^ (n - 1) :=
  (has_deriv_within_at_pow n x s).derivWithin hxs
#align deriv_within_pow deriv_within_pow

theorem HasDerivWithinAt.pow (hc : HasDerivWithinAt c c' s x) :
    HasDerivWithinAt (fun y => c y ^ n) ((n : 𝕜) * c x ^ (n - 1) * c') s x :=
  (has_deriv_at_pow n (c x)).comp_has_deriv_within_at x hc
#align has_deriv_within_at.pow HasDerivWithinAt.pow

theorem HasDerivAt.pow (hc : HasDerivAt c c' x) :
    HasDerivAt (fun y => c y ^ n) ((n : 𝕜) * c x ^ (n - 1) * c') x :=
  by
  rw [← has_deriv_within_at_univ] at *
  exact hc.pow n
#align has_deriv_at.pow HasDerivAt.pow

theorem deriv_within_pow' (hc : DifferentiableWithinAt 𝕜 c s x) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => c x ^ n) s x = (n : 𝕜) * c x ^ (n - 1) * derivWithin c s x :=
  (hc.HasDerivWithinAt.pow n).derivWithin hxs
#align deriv_within_pow' deriv_within_pow'

@[simp]
theorem deriv_pow'' (hc : DifferentiableAt 𝕜 c x) :
    deriv (fun x => c x ^ n) x = (n : 𝕜) * c x ^ (n - 1) * deriv c x :=
  (hc.HasDerivAt.pow n).deriv
#align deriv_pow'' deriv_pow''

end Pow

section Zpow

/-! ### Derivative of `x ↦ x^m` for `m : ℤ` -/


variable {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {x : 𝕜} {s : Set 𝕜} {m : ℤ}

theorem has_strict_deriv_at_zpow (m : ℤ) (x : 𝕜) (h : x ≠ 0 ∨ 0 ≤ m) :
    HasStrictDerivAt (fun x => x ^ m) ((m : 𝕜) * x ^ (m - 1)) x :=
  by
  have : ∀ m : ℤ, 0 < m → HasStrictDerivAt (fun x => x ^ m) ((m : 𝕜) * x ^ (m - 1)) x :=
    by
    intro m hm
    lift m to ℕ using le_of_lt hm
    simp only [zpow_ofNat, Int.cast_ofNat]
    convert has_strict_deriv_at_pow _ _ using 2
    rw [← Int.ofNat_one, ← Int.ofNat_sub, zpow_ofNat]
    norm_cast  at hm
    exact Nat.succ_le_of_lt hm
  rcases lt_trichotomy m 0 with (hm | hm | hm)
  · have hx : x ≠ 0 := h.resolve_right hm.not_le
    have := (has_strict_deriv_at_inv _).scomp _ (this (-m) (neg_pos.2 hm)) <;> [skip,
      exact zpow_ne_zero_of_ne_zero hx _]
    simp only [(· ∘ ·), zpow_neg, one_div, inv_inv, smul_eq_mul] at this
    convert this using 1
    rw [sq, mul_inv, inv_inv, Int.cast_neg, neg_mul, neg_mul_neg, ← zpow_add₀ hx, mul_assoc, ←
      zpow_add₀ hx]
    congr
    abel
  · simp only [hm, zpow_zero, Int.cast_zero, zero_mul, has_strict_deriv_at_const]
  · exact this m hm
#align has_strict_deriv_at_zpow has_strict_deriv_at_zpow

theorem has_deriv_at_zpow (m : ℤ) (x : 𝕜) (h : x ≠ 0 ∨ 0 ≤ m) :
    HasDerivAt (fun x => x ^ m) ((m : 𝕜) * x ^ (m - 1)) x :=
  (has_strict_deriv_at_zpow m x h).HasDerivAt
#align has_deriv_at_zpow has_deriv_at_zpow

theorem has_deriv_within_at_zpow (m : ℤ) (x : 𝕜) (h : x ≠ 0 ∨ 0 ≤ m) (s : Set 𝕜) :
    HasDerivWithinAt (fun x => x ^ m) ((m : 𝕜) * x ^ (m - 1)) s x :=
  (has_deriv_at_zpow m x h).HasDerivWithinAt
#align has_deriv_within_at_zpow has_deriv_within_at_zpow

theorem differentiable_at_zpow : DifferentiableAt 𝕜 (fun x => x ^ m) x ↔ x ≠ 0 ∨ 0 ≤ m :=
  ⟨fun H => NormedField.continuous_at_zpow.1 H.ContinuousAt, fun H =>
    (has_deriv_at_zpow m x H).DifferentiableAt⟩
#align differentiable_at_zpow differentiable_at_zpow

theorem differentiable_within_at_zpow (m : ℤ) (x : 𝕜) (h : x ≠ 0 ∨ 0 ≤ m) :
    DifferentiableWithinAt 𝕜 (fun x => x ^ m) s x :=
  (differentiable_at_zpow.mpr h).DifferentiableWithinAt
#align differentiable_within_at_zpow differentiable_within_at_zpow

theorem differentiable_on_zpow (m : ℤ) (s : Set 𝕜) (h : (0 : 𝕜) ∉ s ∨ 0 ≤ m) :
    DifferentiableOn 𝕜 (fun x => x ^ m) s := fun x hxs =>
  differentiable_within_at_zpow m x <| h.imp_left <| ne_of_mem_of_not_mem hxs
#align differentiable_on_zpow differentiable_on_zpow

theorem deriv_zpow (m : ℤ) (x : 𝕜) : deriv (fun x => x ^ m) x = m * x ^ (m - 1) :=
  by
  by_cases H : x ≠ 0 ∨ 0 ≤ m
  · exact (has_deriv_at_zpow m x H).deriv
  · rw [deriv_zero_of_not_differentiable_at (mt differentiable_at_zpow.1 H)]
    push_neg  at H
    rcases H with ⟨rfl, hm⟩
    rw [zero_zpow _ ((sub_one_lt _).trans hm).Ne, mul_zero]
#align deriv_zpow deriv_zpow

@[simp]
theorem deriv_zpow' (m : ℤ) : (deriv fun x : 𝕜 => x ^ m) = fun x => m * x ^ (m - 1) :=
  funext <| deriv_zpow m
#align deriv_zpow' deriv_zpow'

theorem deriv_within_zpow (hxs : UniqueDiffWithinAt 𝕜 s x) (h : x ≠ 0 ∨ 0 ≤ m) :
    derivWithin (fun x => x ^ m) s x = (m : 𝕜) * x ^ (m - 1) :=
  (has_deriv_within_at_zpow m x h s).derivWithin hxs
#align deriv_within_zpow deriv_within_zpow

@[simp]
theorem iter_deriv_zpow' (m : ℤ) (k : ℕ) :
    ((deriv^[k]) fun x : 𝕜 => x ^ m) = fun x => (∏ i in Finset.range k, m - i) * x ^ (m - k) :=
  by
  induction' k with k ihk
  · simp only [one_mul, Int.ofNat_zero, id, sub_zero, Finset.prod_range_zero, Function.iterate_zero]
  ·
    simp only [Function.iterate_succ_apply', ihk, deriv_const_mul_field', deriv_zpow',
      Finset.prod_range_succ, Int.ofNat_succ, ← sub_sub, Int.cast_sub, Int.cast_ofNat, mul_assoc]
#align iter_deriv_zpow' iter_deriv_zpow'

theorem iter_deriv_zpow (m : ℤ) (x : 𝕜) (k : ℕ) :
    (deriv^[k]) (fun y => y ^ m) x = (∏ i in Finset.range k, m - i) * x ^ (m - k) :=
  congr_fun (iter_deriv_zpow' m k) x
#align iter_deriv_zpow iter_deriv_zpow

theorem iter_deriv_pow (n : ℕ) (x : 𝕜) (k : ℕ) :
    (deriv^[k]) (fun x : 𝕜 => x ^ n) x = (∏ i in Finset.range k, n - i) * x ^ (n - k) :=
  by
  simp only [← zpow_ofNat, iter_deriv_zpow, Int.cast_ofNat]
  cases' le_or_lt k n with hkn hnk
  · rw [Int.ofNat_sub hkn]
  · have : (∏ i in Finset.range k, (n - i : 𝕜)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.2 hnk) (sub_self _)
    simp only [this, zero_mul]
#align iter_deriv_pow iter_deriv_pow

@[simp]
theorem iter_deriv_pow' (n k : ℕ) :
    ((deriv^[k]) fun x : 𝕜 => x ^ n) = fun x => (∏ i in Finset.range k, n - i) * x ^ (n - k) :=
  funext fun x => iter_deriv_pow n x k
#align iter_deriv_pow' iter_deriv_pow'

theorem iter_deriv_inv (k : ℕ) (x : 𝕜) :
    (deriv^[k]) Inv.inv x = (∏ i in Finset.range k, -1 - i) * x ^ (-1 - k : ℤ) := by
  simpa only [zpow_neg_one, Int.cast_neg, Int.cast_one] using iter_deriv_zpow (-1) x k
#align iter_deriv_inv iter_deriv_inv

@[simp]
theorem iter_deriv_inv' (k : ℕ) :
    (deriv^[k]) Inv.inv = fun x : 𝕜 => (∏ i in Finset.range k, -1 - i) * x ^ (-1 - k : ℤ) :=
  funext (iter_deriv_inv k)
#align iter_deriv_inv' iter_deriv_inv'

variable {f : E → 𝕜} {t : Set E} {a : E}

theorem DifferentiableWithinAt.zpow (hf : DifferentiableWithinAt 𝕜 f t a) (h : f a ≠ 0 ∨ 0 ≤ m) :
    DifferentiableWithinAt 𝕜 (fun x => f x ^ m) t a :=
  (differentiable_at_zpow.2 h).comp_differentiable_within_at a hf
#align differentiable_within_at.zpow DifferentiableWithinAt.zpow

theorem DifferentiableAt.zpow (hf : DifferentiableAt 𝕜 f a) (h : f a ≠ 0 ∨ 0 ≤ m) :
    DifferentiableAt 𝕜 (fun x => f x ^ m) a :=
  (differentiable_at_zpow.2 h).comp a hf
#align differentiable_at.zpow DifferentiableAt.zpow

theorem DifferentiableOn.zpow (hf : DifferentiableOn 𝕜 f t) (h : (∀ x ∈ t, f x ≠ 0) ∨ 0 ≤ m) :
    DifferentiableOn 𝕜 (fun x => f x ^ m) t := fun x hx =>
  (hf x hx).zpow <| h.imp_left fun h => h x hx
#align differentiable_on.zpow DifferentiableOn.zpow

theorem Differentiable.zpow (hf : Differentiable 𝕜 f) (h : (∀ x, f x ≠ 0) ∨ 0 ≤ m) :
    Differentiable 𝕜 fun x => f x ^ m := fun x => (hf x).zpow <| h.imp_left fun h => h x
#align differentiable.zpow Differentiable.zpow

end Zpow

/-! ### Support of derivatives -/


section Support

open Function

variable {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : 𝕜 → F}

theorem support_deriv_subset : support (deriv f) ⊆ tsupport f :=
  by
  intro x
  rw [← not_imp_not]
  intro h2x
  rw [not_mem_tsupport_iff_eventually_eq] at h2x
  exact nmem_support.mpr (h2x.deriv_eq.trans (deriv_const x 0))
#align support_deriv_subset support_deriv_subset

theorem HasCompactSupport.deriv (hf : HasCompactSupport f) : HasCompactSupport (deriv f) :=
  hf.mono' support_deriv_subset
#align has_compact_support.deriv HasCompactSupport.deriv

end Support

/-! ### Upper estimates on liminf and limsup -/


section Real

variable {f : ℝ → ℝ} {f' : ℝ} {s : Set ℝ} {x : ℝ} {r : ℝ}

theorem HasDerivWithinAt.limsup_slope_le (hf : HasDerivWithinAt f f' s x) (hr : f' < r) :
    ∀ᶠ z in 𝓝[s \ {x}] x, slope f x z < r :=
  has_deriv_within_at_iff_tendsto_slope.1 hf (IsOpen.mem_nhds is_open_Iio hr)
#align has_deriv_within_at.limsup_slope_le HasDerivWithinAt.limsup_slope_le

theorem HasDerivWithinAt.limsup_slope_le' (hf : HasDerivWithinAt f f' s x) (hs : x ∉ s)
    (hr : f' < r) : ∀ᶠ z in 𝓝[s] x, slope f x z < r :=
  (has_deriv_within_at_iff_tendsto_slope' hs).1 hf (IsOpen.mem_nhds is_open_Iio hr)
#align has_deriv_within_at.limsup_slope_le' HasDerivWithinAt.limsup_slope_le'

theorem HasDerivWithinAt.liminf_right_slope_le (hf : HasDerivWithinAt f f' (Ici x) x)
    (hr : f' < r) : ∃ᶠ z in 𝓝[>] x, slope f x z < r :=
  (hf.Ioi_of_Ici.limsup_slope_le' (lt_irrefl x) hr).Frequently
#align has_deriv_within_at.liminf_right_slope_le HasDerivWithinAt.liminf_right_slope_le

end Real

section RealSpace

open Metric

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} {f' : E} {s : Set ℝ}
  {x r : ℝ}

/-- If `f` has derivative `f'` within `s` at `x`, then for any `r > ‖f'‖` the ratio
`‖f z - f x‖ / ‖z - x‖` is less than `r` in some neighborhood of `x` within `s`.
In other words, the limit superior of this ratio as `z` tends to `x` along `s`
is less than or equal to `‖f'‖`. -/
theorem HasDerivWithinAt.limsup_norm_slope_le (hf : HasDerivWithinAt f f' s x) (hr : ‖f'‖ < r) :
    ∀ᶠ z in 𝓝[s] x, ‖z - x‖⁻¹ * ‖f z - f x‖ < r :=
  by
  have hr₀ : 0 < r := lt_of_le_of_lt (norm_nonneg f') hr
  have A : ∀ᶠ z in 𝓝[s \ {x}] x, ‖(z - x)⁻¹ • (f z - f x)‖ ∈ Iio r :=
    (has_deriv_within_at_iff_tendsto_slope.1 hf).norm (IsOpen.mem_nhds is_open_Iio hr)
  have B : ∀ᶠ z in 𝓝[{x}] x, ‖(z - x)⁻¹ • (f z - f x)‖ ∈ Iio r :=
    mem_of_superset self_mem_nhds_within (singleton_subset_iff.2 <| by simp [hr₀])
  have C := mem_sup.2 ⟨A, B⟩
  rw [← nhds_within_union, diff_union_self, nhds_within_union, mem_sup] at C
  filter_upwards [C.1]
  simp only [norm_smul, mem_Iio, norm_inv]
  exact fun _ => id
#align has_deriv_within_at.limsup_norm_slope_le HasDerivWithinAt.limsup_norm_slope_le

/-- If `f` has derivative `f'` within `s` at `x`, then for any `r > ‖f'‖` the ratio
`(‖f z‖ - ‖f x‖) / ‖z - x‖` is less than `r` in some neighborhood of `x` within `s`.
In other words, the limit superior of this ratio as `z` tends to `x` along `s`
is less than or equal to `‖f'‖`.

This lemma is a weaker version of `has_deriv_within_at.limsup_norm_slope_le`
where `‖f z‖ - ‖f x‖` is replaced by `‖f z - f x‖`. -/
theorem HasDerivWithinAt.limsup_slope_norm_le (hf : HasDerivWithinAt f f' s x) (hr : ‖f'‖ < r) :
    ∀ᶠ z in 𝓝[s] x, ‖z - x‖⁻¹ * (‖f z‖ - ‖f x‖) < r :=
  by
  apply (hf.limsup_norm_slope_le hr).mono
  intro z hz
  refine' lt_of_le_of_lt (mul_le_mul_of_nonneg_left (norm_sub_norm_le _ _) _) hz
  exact inv_nonneg.2 (norm_nonneg _)
#align has_deriv_within_at.limsup_slope_norm_le HasDerivWithinAt.limsup_slope_norm_le

/-- If `f` has derivative `f'` within `(x, +∞)` at `x`, then for any `r > ‖f'‖` the ratio
`‖f z - f x‖ / ‖z - x‖` is frequently less than `r` as `z → x+0`.
In other words, the limit inferior of this ratio as `z` tends to `x+0`
is less than or equal to `‖f'‖`. See also `has_deriv_within_at.limsup_norm_slope_le`
for a stronger version using limit superior and any set `s`. -/
theorem HasDerivWithinAt.liminf_right_norm_slope_le (hf : HasDerivWithinAt f f' (Ici x) x)
    (hr : ‖f'‖ < r) : ∃ᶠ z in 𝓝[>] x, ‖z - x‖⁻¹ * ‖f z - f x‖ < r :=
  (hf.Ioi_of_Ici.limsup_norm_slope_le hr).Frequently
#align has_deriv_within_at.liminf_right_norm_slope_le HasDerivWithinAt.liminf_right_norm_slope_le

/-- If `f` has derivative `f'` within `(x, +∞)` at `x`, then for any `r > ‖f'‖` the ratio
`(‖f z‖ - ‖f x‖) / (z - x)` is frequently less than `r` as `z → x+0`.
In other words, the limit inferior of this ratio as `z` tends to `x+0`
is less than or equal to `‖f'‖`.

See also

* `has_deriv_within_at.limsup_norm_slope_le` for a stronger version using
  limit superior and any set `s`;
* `has_deriv_within_at.liminf_right_norm_slope_le` for a stronger version using
  `‖f z - f x‖` instead of `‖f z‖ - ‖f x‖`. -/
theorem HasDerivWithinAt.liminf_right_slope_norm_le (hf : HasDerivWithinAt f f' (Ici x) x)
    (hr : ‖f'‖ < r) : ∃ᶠ z in 𝓝[>] x, (z - x)⁻¹ * (‖f z‖ - ‖f x‖) < r :=
  by
  have := (hf.Ioi_of_Ici.limsup_slope_norm_le hr).Frequently
  refine' this.mp (eventually.mono self_mem_nhds_within _)
  intro z hxz hz
  rwa [Real.norm_eq_abs, abs_of_pos (sub_pos_of_lt hxz)] at hz
#align has_deriv_within_at.liminf_right_slope_norm_le HasDerivWithinAt.liminf_right_slope_norm_le

end RealSpace

