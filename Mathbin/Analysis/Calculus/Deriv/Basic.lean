/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sébastien Gouëzel

! This file was ported from Lean 3 source module analysis.calculus.deriv.basic
! leanprover-community/mathlib commit f60c6087a7275b72d5db3c5a1d0e19e35a429c0a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Calculus.Fderiv.Basic

/-!

# One-dimensional derivatives

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
  - linear maps (in `linear.lean`)
  - addition (in `add.lean`)
  - sum of finitely many functions (in `add.lean`)
  - negation (in `add.lean`)
  - subtraction (in `add.lean`)
  - star  (in `star.lean`)
  - multiplication of two functions in `𝕜 → 𝕜` (in `mul.lean`)
  - multiplication of a function in `𝕜 → 𝕜` and of a function in `𝕜 → E` (in `mul.lean`)
  - powers of a function (in `pow.lean` and `zpow.lean`)
  - inverse `x → x⁻¹` (in `inv.lean`)
  - division (in `inv.lean`)
  - composition of a function in `𝕜 → F` with a function in `𝕜 → 𝕜` (in `comp.lean`)
  - composition of a function in `F → E` with a function in `𝕜 → F` (in `comp.lean`)
  - inverse function (assuming that it exists; the inverse function theorem is in `inverse.lean`)
  - polynomials (in `polynomial.lean`)

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

open scoped Classical Topology BigOperators Filter ENNReal

open Filter Asymptotics Set

open ContinuousLinearMap (smul_right smulRight_one_eq_iff)

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

#print HasDerivAtFilter /-
/-- `f` has the derivative `f'` at the point `x` as `x` goes along the filter `L`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges along the filter `L`.
-/
def HasDerivAtFilter (f : 𝕜 → F) (f' : F) (x : 𝕜) (L : Filter 𝕜) :=
  HasFDerivAtFilter f (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') x L
#align has_deriv_at_filter HasDerivAtFilter
-/

#print HasDerivWithinAt /-
/-- `f` has the derivative `f'` at the point `x` within the subset `s`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges to `x` inside `s`.
-/
def HasDerivWithinAt (f : 𝕜 → F) (f' : F) (s : Set 𝕜) (x : 𝕜) :=
  HasDerivAtFilter f f' x (𝓝[s] x)
#align has_deriv_within_at HasDerivWithinAt
-/

#print HasDerivAt /-
/-- `f` has the derivative `f'` at the point `x`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges to `x`.
-/
def HasDerivAt (f : 𝕜 → F) (f' : F) (x : 𝕜) :=
  HasDerivAtFilter f f' x (𝓝 x)
#align has_deriv_at HasDerivAt
-/

#print HasStrictDerivAt /-
/-- `f` has the derivative `f'` at the point `x` in the sense of strict differentiability.

That is, `f y - f z = (y - z) • f' + o(y - z)` as `y, z → x`. -/
def HasStrictDerivAt (f : 𝕜 → F) (f' : F) (x : 𝕜) :=
  HasStrictFDerivAt f (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') x
#align has_strict_deriv_at HasStrictDerivAt
-/

#print derivWithin /-
/-- Derivative of `f` at the point `x` within the set `s`, if it exists.  Zero otherwise.

If the derivative exists (i.e., `∃ f', has_deriv_within_at f f' s x`), then
`f x' = f x + (x' - x) • deriv_within f s x + o(x' - x)` where `x'` converges to `x` inside `s`.
-/
def derivWithin (f : 𝕜 → F) (s : Set 𝕜) (x : 𝕜) :=
  fderivWithin 𝕜 f s x 1
#align deriv_within derivWithin
-/

#print deriv /-
/-- Derivative of `f` at the point `x`, if it exists.  Zero otherwise.

If the derivative exists (i.e., `∃ f', has_deriv_at f f' x`), then
`f x' = f x + (x' - x) • deriv f x + o(x' - x)` where `x'` converges to `x`.
-/
def deriv (f : 𝕜 → F) (x : 𝕜) :=
  fderiv 𝕜 f x 1
#align deriv deriv
-/

variable {f f₀ f₁ g : 𝕜 → F}

variable {f' f₀' f₁' g' : F}

variable {x : 𝕜}

variable {s t : Set 𝕜}

variable {L L₁ L₂ : Filter 𝕜}

#print hasFDerivAtFilter_iff_hasDerivAtFilter /-
/-- Expressing `has_fderiv_at_filter f f' x L` in terms of `has_deriv_at_filter` -/
theorem hasFDerivAtFilter_iff_hasDerivAtFilter {f' : 𝕜 →L[𝕜] F} :
    HasFDerivAtFilter f f' x L ↔ HasDerivAtFilter f (f' 1) x L := by simp [HasDerivAtFilter]
#align has_fderiv_at_filter_iff_has_deriv_at_filter hasFDerivAtFilter_iff_hasDerivAtFilter
-/

#print HasFDerivAtFilter.hasDerivAtFilter /-
theorem HasFDerivAtFilter.hasDerivAtFilter {f' : 𝕜 →L[𝕜] F} :
    HasFDerivAtFilter f f' x L → HasDerivAtFilter f (f' 1) x L :=
  hasFDerivAtFilter_iff_hasDerivAtFilter.mp
#align has_fderiv_at_filter.has_deriv_at_filter HasFDerivAtFilter.hasDerivAtFilter
-/

#print hasFDerivWithinAt_iff_hasDerivWithinAt /-
/-- Expressing `has_fderiv_within_at f f' s x` in terms of `has_deriv_within_at` -/
theorem hasFDerivWithinAt_iff_hasDerivWithinAt {f' : 𝕜 →L[𝕜] F} :
    HasFDerivWithinAt f f' s x ↔ HasDerivWithinAt f (f' 1) s x :=
  hasFDerivAtFilter_iff_hasDerivAtFilter
#align has_fderiv_within_at_iff_has_deriv_within_at hasFDerivWithinAt_iff_hasDerivWithinAt
-/

#print hasDerivWithinAt_iff_hasFDerivWithinAt /-
/-- Expressing `has_deriv_within_at f f' s x` in terms of `has_fderiv_within_at` -/
theorem hasDerivWithinAt_iff_hasFDerivWithinAt {f' : F} :
    HasDerivWithinAt f f' s x ↔ HasFDerivWithinAt f (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') s x :=
  Iff.rfl
#align has_deriv_within_at_iff_has_fderiv_within_at hasDerivWithinAt_iff_hasFDerivWithinAt
-/

#print HasFDerivWithinAt.hasDerivWithinAt /-
theorem HasFDerivWithinAt.hasDerivWithinAt {f' : 𝕜 →L[𝕜] F} :
    HasFDerivWithinAt f f' s x → HasDerivWithinAt f (f' 1) s x :=
  hasFDerivWithinAt_iff_hasDerivWithinAt.mp
#align has_fderiv_within_at.has_deriv_within_at HasFDerivWithinAt.hasDerivWithinAt
-/

#print HasDerivWithinAt.hasFDerivWithinAt /-
theorem HasDerivWithinAt.hasFDerivWithinAt {f' : F} :
    HasDerivWithinAt f f' s x → HasFDerivWithinAt f (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') s x :=
  hasDerivWithinAt_iff_hasFDerivWithinAt.mp
#align has_deriv_within_at.has_fderiv_within_at HasDerivWithinAt.hasFDerivWithinAt
-/

#print hasFDerivAt_iff_hasDerivAt /-
/-- Expressing `has_fderiv_at f f' x` in terms of `has_deriv_at` -/
theorem hasFDerivAt_iff_hasDerivAt {f' : 𝕜 →L[𝕜] F} : HasFDerivAt f f' x ↔ HasDerivAt f (f' 1) x :=
  hasFDerivAtFilter_iff_hasDerivAtFilter
#align has_fderiv_at_iff_has_deriv_at hasFDerivAt_iff_hasDerivAt
-/

#print HasFDerivAt.hasDerivAt /-
theorem HasFDerivAt.hasDerivAt {f' : 𝕜 →L[𝕜] F} : HasFDerivAt f f' x → HasDerivAt f (f' 1) x :=
  hasFDerivAt_iff_hasDerivAt.mp
#align has_fderiv_at.has_deriv_at HasFDerivAt.hasDerivAt
-/

#print hasStrictFDerivAt_iff_hasStrictDerivAt /-
theorem hasStrictFDerivAt_iff_hasStrictDerivAt {f' : 𝕜 →L[𝕜] F} :
    HasStrictFDerivAt f f' x ↔ HasStrictDerivAt f (f' 1) x := by
  simp [HasStrictDerivAt, HasStrictFDerivAt]
#align has_strict_fderiv_at_iff_has_strict_deriv_at hasStrictFDerivAt_iff_hasStrictDerivAt
-/

#print HasStrictFDerivAt.hasStrictDerivAt /-
protected theorem HasStrictFDerivAt.hasStrictDerivAt {f' : 𝕜 →L[𝕜] F} :
    HasStrictFDerivAt f f' x → HasStrictDerivAt f (f' 1) x :=
  hasStrictFDerivAt_iff_hasStrictDerivAt.mp
#align has_strict_fderiv_at.has_strict_deriv_at HasStrictFDerivAt.hasStrictDerivAt
-/

#print hasStrictDerivAt_iff_hasStrictFDerivAt /-
theorem hasStrictDerivAt_iff_hasStrictFDerivAt :
    HasStrictDerivAt f f' x ↔ HasStrictFDerivAt f (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') x :=
  Iff.rfl
#align has_strict_deriv_at_iff_has_strict_fderiv_at hasStrictDerivAt_iff_hasStrictFDerivAt
-/

alias hasStrictDerivAt_iff_hasStrictFDerivAt ↔ HasStrictDerivAt.hasStrictFDerivAt _
#align has_strict_deriv_at.has_strict_fderiv_at HasStrictDerivAt.hasStrictFDerivAt

#print hasDerivAt_iff_hasFDerivAt /-
/-- Expressing `has_deriv_at f f' x` in terms of `has_fderiv_at` -/
theorem hasDerivAt_iff_hasFDerivAt {f' : F} :
    HasDerivAt f f' x ↔ HasFDerivAt f (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') x :=
  Iff.rfl
#align has_deriv_at_iff_has_fderiv_at hasDerivAt_iff_hasFDerivAt
-/

alias hasDerivAt_iff_hasFDerivAt ↔ HasDerivAt.hasFDerivAt _
#align has_deriv_at.has_fderiv_at HasDerivAt.hasFDerivAt

#print derivWithin_zero_of_not_differentiableWithinAt /-
theorem derivWithin_zero_of_not_differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) :
    derivWithin f s x = 0 := by unfold derivWithin;
  rw [fderivWithin_zero_of_not_differentiableWithinAt]; simp; assumption
#align deriv_within_zero_of_not_differentiable_within_at derivWithin_zero_of_not_differentiableWithinAt
-/

#print differentiableWithinAt_of_derivWithin_ne_zero /-
theorem differentiableWithinAt_of_derivWithin_ne_zero (h : derivWithin f s x ≠ 0) :
    DifferentiableWithinAt 𝕜 f s x :=
  not_imp_comm.1 derivWithin_zero_of_not_differentiableWithinAt h
#align differentiable_within_at_of_deriv_within_ne_zero differentiableWithinAt_of_derivWithin_ne_zero
-/

#print deriv_zero_of_not_differentiableAt /-
theorem deriv_zero_of_not_differentiableAt (h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0 := by
  unfold deriv; rw [fderiv_zero_of_not_differentiableAt]; simp; assumption
#align deriv_zero_of_not_differentiable_at deriv_zero_of_not_differentiableAt
-/

#print differentiableAt_of_deriv_ne_zero /-
theorem differentiableAt_of_deriv_ne_zero (h : deriv f x ≠ 0) : DifferentiableAt 𝕜 f x :=
  not_imp_comm.1 deriv_zero_of_not_differentiableAt h
#align differentiable_at_of_deriv_ne_zero differentiableAt_of_deriv_ne_zero
-/

#print UniqueDiffWithinAt.eq_deriv /-
theorem UniqueDiffWithinAt.eq_deriv (s : Set 𝕜) (H : UniqueDiffWithinAt 𝕜 s x)
    (h : HasDerivWithinAt f f' s x) (h₁ : HasDerivWithinAt f f₁' s x) : f' = f₁' :=
  smulRight_one_eq_iff.mp <| UniqueDiffWithinAt.eq H h h₁
#align unique_diff_within_at.eq_deriv UniqueDiffWithinAt.eq_deriv
-/

#print hasDerivAtFilter_iff_isLittleO /-
theorem hasDerivAtFilter_iff_isLittleO :
    HasDerivAtFilter f f' x L ↔ (fun x' : 𝕜 => f x' - f x - (x' - x) • f') =o[L] fun x' => x' - x :=
  Iff.rfl
#align has_deriv_at_filter_iff_is_o hasDerivAtFilter_iff_isLittleO
-/

#print hasDerivAtFilter_iff_tendsto /-
theorem hasDerivAtFilter_iff_tendsto :
    HasDerivAtFilter f f' x L ↔
      Tendsto (fun x' : 𝕜 => ‖x' - x‖⁻¹ * ‖f x' - f x - (x' - x) • f'‖) L (𝓝 0) :=
  hasFDerivAtFilter_iff_tendsto
#align has_deriv_at_filter_iff_tendsto hasDerivAtFilter_iff_tendsto
-/

#print hasDerivWithinAt_iff_isLittleO /-
theorem hasDerivWithinAt_iff_isLittleO :
    HasDerivWithinAt f f' s x ↔
      (fun x' : 𝕜 => f x' - f x - (x' - x) • f') =o[𝓝[s] x] fun x' => x' - x :=
  Iff.rfl
#align has_deriv_within_at_iff_is_o hasDerivWithinAt_iff_isLittleO
-/

#print hasDerivWithinAt_iff_tendsto /-
theorem hasDerivWithinAt_iff_tendsto :
    HasDerivWithinAt f f' s x ↔
      Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - (x' - x) • f'‖) (𝓝[s] x) (𝓝 0) :=
  hasFDerivAtFilter_iff_tendsto
#align has_deriv_within_at_iff_tendsto hasDerivWithinAt_iff_tendsto
-/

#print hasDerivAt_iff_isLittleO /-
theorem hasDerivAt_iff_isLittleO :
    HasDerivAt f f' x ↔ (fun x' : 𝕜 => f x' - f x - (x' - x) • f') =o[𝓝 x] fun x' => x' - x :=
  Iff.rfl
#align has_deriv_at_iff_is_o hasDerivAt_iff_isLittleO
-/

#print hasDerivAt_iff_tendsto /-
theorem hasDerivAt_iff_tendsto :
    HasDerivAt f f' x ↔ Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - (x' - x) • f'‖) (𝓝 x) (𝓝 0) :=
  hasFDerivAtFilter_iff_tendsto
#align has_deriv_at_iff_tendsto hasDerivAt_iff_tendsto
-/

#print HasDerivAtFilter.isBigO_sub /-
theorem HasDerivAtFilter.isBigO_sub (h : HasDerivAtFilter f f' x L) :
    (fun x' => f x' - f x) =O[L] fun x' => x' - x :=
  HasFDerivAtFilter.isBigO_sub h
#align has_deriv_at_filter.is_O_sub HasDerivAtFilter.isBigO_sub
-/

#print HasDerivAtFilter.isBigO_sub_rev /-
theorem HasDerivAtFilter.isBigO_sub_rev (hf : HasDerivAtFilter f f' x L) (hf' : f' ≠ 0) :
    (fun x' => x' - x) =O[L] fun x' => f x' - f x :=
  suffices AntilipschitzWith ‖f'‖₊⁻¹ (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') from hf.isBigO_sub_rev this
  AddMonoidHomClass.antilipschitz_of_bound (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') fun x => by
    simp [norm_smul, ← div_eq_inv_mul, mul_div_cancel _ (mt norm_eq_zero.1 hf')]
#align has_deriv_at_filter.is_O_sub_rev HasDerivAtFilter.isBigO_sub_rev
-/

#print HasStrictDerivAt.hasDerivAt /-
theorem HasStrictDerivAt.hasDerivAt (h : HasStrictDerivAt f f' x) : HasDerivAt f f' x :=
  h.HasFDerivAt
#align has_strict_deriv_at.has_deriv_at HasStrictDerivAt.hasDerivAt
-/

#print hasDerivWithinAt_congr_set' /-
theorem hasDerivWithinAt_congr_set' {s t : Set 𝕜} (y : 𝕜) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    HasDerivWithinAt f f' s x ↔ HasDerivWithinAt f f' t x :=
  hasFDerivWithinAt_congr_set' y h
#align has_deriv_within_at_congr_set' hasDerivWithinAt_congr_set'
-/

#print hasDerivWithinAt_congr_set /-
theorem hasDerivWithinAt_congr_set {s t : Set 𝕜} (h : s =ᶠ[𝓝 x] t) :
    HasDerivWithinAt f f' s x ↔ HasDerivWithinAt f f' t x :=
  hasFDerivWithinAt_congr_set h
#align has_deriv_within_at_congr_set hasDerivWithinAt_congr_set
-/

alias hasDerivWithinAt_congr_set ↔ HasDerivWithinAt.congr_set _
#align has_deriv_within_at.congr_set HasDerivWithinAt.congr_set

#print hasDerivWithinAt_diff_singleton /-
@[simp]
theorem hasDerivWithinAt_diff_singleton :
    HasDerivWithinAt f f' (s \ {x}) x ↔ HasDerivWithinAt f f' s x :=
  hasFDerivWithinAt_diff_singleton _
#align has_deriv_within_at_diff_singleton hasDerivWithinAt_diff_singleton
-/

#print hasDerivWithinAt_Ioi_iff_Ici /-
@[simp]
theorem hasDerivWithinAt_Ioi_iff_Ici [PartialOrder 𝕜] :
    HasDerivWithinAt f f' (Ioi x) x ↔ HasDerivWithinAt f f' (Ici x) x := by
  rw [← Ici_diff_left, hasDerivWithinAt_diff_singleton]
#align has_deriv_within_at_Ioi_iff_Ici hasDerivWithinAt_Ioi_iff_Ici
-/

alias hasDerivWithinAt_Ioi_iff_Ici ↔ HasDerivWithinAt.Ici_of_Ioi HasDerivWithinAt.Ioi_of_Ici
#align has_deriv_within_at.Ici_of_Ioi HasDerivWithinAt.Ici_of_Ioi
#align has_deriv_within_at.Ioi_of_Ici HasDerivWithinAt.Ioi_of_Ici

#print hasDerivWithinAt_Iio_iff_Iic /-
@[simp]
theorem hasDerivWithinAt_Iio_iff_Iic [PartialOrder 𝕜] :
    HasDerivWithinAt f f' (Iio x) x ↔ HasDerivWithinAt f f' (Iic x) x := by
  rw [← Iic_diff_right, hasDerivWithinAt_diff_singleton]
#align has_deriv_within_at_Iio_iff_Iic hasDerivWithinAt_Iio_iff_Iic
-/

alias hasDerivWithinAt_Iio_iff_Iic ↔ HasDerivWithinAt.Iic_of_Iio HasDerivWithinAt.Iio_of_Iic
#align has_deriv_within_at.Iic_of_Iio HasDerivWithinAt.Iic_of_Iio
#align has_deriv_within_at.Iio_of_Iic HasDerivWithinAt.Iio_of_Iic

#print HasDerivWithinAt.Ioi_iff_Ioo /-
theorem HasDerivWithinAt.Ioi_iff_Ioo [LinearOrder 𝕜] [OrderClosedTopology 𝕜] {x y : 𝕜} (h : x < y) :
    HasDerivWithinAt f f' (Ioo x y) x ↔ HasDerivWithinAt f f' (Ioi x) x :=
  hasFDerivWithinAt_inter <| Iio_mem_nhds h
#align has_deriv_within_at.Ioi_iff_Ioo HasDerivWithinAt.Ioi_iff_Ioo
-/

alias HasDerivWithinAt.Ioi_iff_Ioo ↔ HasDerivWithinAt.Ioi_of_Ioo HasDerivWithinAt.Ioo_of_Ioi
#align has_deriv_within_at.Ioi_of_Ioo HasDerivWithinAt.Ioi_of_Ioo
#align has_deriv_within_at.Ioo_of_Ioi HasDerivWithinAt.Ioo_of_Ioi

#print hasDerivAt_iff_isLittleO_nhds_zero /-
theorem hasDerivAt_iff_isLittleO_nhds_zero :
    HasDerivAt f f' x ↔ (fun h => f (x + h) - f x - h • f') =o[𝓝 0] fun h => h :=
  hasFDerivAt_iff_isLittleO_nhds_zero
#align has_deriv_at_iff_is_o_nhds_zero hasDerivAt_iff_isLittleO_nhds_zero
-/

#print HasDerivAtFilter.mono /-
theorem HasDerivAtFilter.mono (h : HasDerivAtFilter f f' x L₂) (hst : L₁ ≤ L₂) :
    HasDerivAtFilter f f' x L₁ :=
  HasFDerivAtFilter.mono h hst
#align has_deriv_at_filter.mono HasDerivAtFilter.mono
-/

#print HasDerivWithinAt.mono /-
theorem HasDerivWithinAt.mono (h : HasDerivWithinAt f f' t x) (hst : s ⊆ t) :
    HasDerivWithinAt f f' s x :=
  HasFDerivWithinAt.mono h hst
#align has_deriv_within_at.mono HasDerivWithinAt.mono
-/

#print HasDerivWithinAt.mono_of_mem /-
theorem HasDerivWithinAt.mono_of_mem (h : HasDerivWithinAt f f' t x) (hst : t ∈ 𝓝[s] x) :
    HasDerivWithinAt f f' s x :=
  HasFDerivWithinAt.mono_of_mem h hst
#align has_deriv_within_at.mono_of_mem HasDerivWithinAt.mono_of_mem
-/

#print HasDerivAt.hasDerivAtFilter /-
theorem HasDerivAt.hasDerivAtFilter (h : HasDerivAt f f' x) (hL : L ≤ 𝓝 x) :
    HasDerivAtFilter f f' x L :=
  HasFDerivAt.hasFDerivAtFilter h hL
#align has_deriv_at.has_deriv_at_filter HasDerivAt.hasDerivAtFilter
-/

#print HasDerivAt.hasDerivWithinAt /-
theorem HasDerivAt.hasDerivWithinAt (h : HasDerivAt f f' x) : HasDerivWithinAt f f' s x :=
  HasFDerivAt.hasFDerivWithinAt h
#align has_deriv_at.has_deriv_within_at HasDerivAt.hasDerivWithinAt
-/

#print HasDerivWithinAt.differentiableWithinAt /-
theorem HasDerivWithinAt.differentiableWithinAt (h : HasDerivWithinAt f f' s x) :
    DifferentiableWithinAt 𝕜 f s x :=
  HasFDerivWithinAt.differentiableWithinAt h
#align has_deriv_within_at.differentiable_within_at HasDerivWithinAt.differentiableWithinAt
-/

#print HasDerivAt.differentiableAt /-
theorem HasDerivAt.differentiableAt (h : HasDerivAt f f' x) : DifferentiableAt 𝕜 f x :=
  HasFDerivAt.differentiableAt h
#align has_deriv_at.differentiable_at HasDerivAt.differentiableAt
-/

#print hasDerivWithinAt_univ /-
@[simp]
theorem hasDerivWithinAt_univ : HasDerivWithinAt f f' univ x ↔ HasDerivAt f f' x :=
  hasFDerivWithinAt_univ
#align has_deriv_within_at_univ hasDerivWithinAt_univ
-/

#print HasDerivAt.unique /-
theorem HasDerivAt.unique (h₀ : HasDerivAt f f₀' x) (h₁ : HasDerivAt f f₁' x) : f₀' = f₁' :=
  smulRight_one_eq_iff.mp <| h₀.HasFDerivAt.unique h₁
#align has_deriv_at.unique HasDerivAt.unique
-/

#print hasDerivWithinAt_inter' /-
theorem hasDerivWithinAt_inter' (h : t ∈ 𝓝[s] x) :
    HasDerivWithinAt f f' (s ∩ t) x ↔ HasDerivWithinAt f f' s x :=
  hasFDerivWithinAt_inter' h
#align has_deriv_within_at_inter' hasDerivWithinAt_inter'
-/

#print hasDerivWithinAt_inter /-
theorem hasDerivWithinAt_inter (h : t ∈ 𝓝 x) :
    HasDerivWithinAt f f' (s ∩ t) x ↔ HasDerivWithinAt f f' s x :=
  hasFDerivWithinAt_inter h
#align has_deriv_within_at_inter hasDerivWithinAt_inter
-/

#print HasDerivWithinAt.union /-
theorem HasDerivWithinAt.union (hs : HasDerivWithinAt f f' s x) (ht : HasDerivWithinAt f f' t x) :
    HasDerivWithinAt f f' (s ∪ t) x :=
  hs.HasFDerivWithinAt.union ht.HasFDerivWithinAt
#align has_deriv_within_at.union HasDerivWithinAt.union
-/

#print HasDerivWithinAt.nhdsWithin /-
theorem HasDerivWithinAt.nhdsWithin (h : HasDerivWithinAt f f' s x) (ht : s ∈ 𝓝[t] x) :
    HasDerivWithinAt f f' t x :=
  (hasDerivWithinAt_inter' ht).1 (h.mono (inter_subset_right _ _))
#align has_deriv_within_at.nhds_within HasDerivWithinAt.nhdsWithin
-/

#print HasDerivWithinAt.hasDerivAt /-
theorem HasDerivWithinAt.hasDerivAt (h : HasDerivWithinAt f f' s x) (hs : s ∈ 𝓝 x) :
    HasDerivAt f f' x :=
  HasFDerivWithinAt.hasFDerivAt h hs
#align has_deriv_within_at.has_deriv_at HasDerivWithinAt.hasDerivAt
-/

#print DifferentiableWithinAt.hasDerivWithinAt /-
theorem DifferentiableWithinAt.hasDerivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) :
    HasDerivWithinAt f (derivWithin f s x) s x :=
  h.HasFDerivWithinAt.HasDerivWithinAt
#align differentiable_within_at.has_deriv_within_at DifferentiableWithinAt.hasDerivWithinAt
-/

#print DifferentiableAt.hasDerivAt /-
theorem DifferentiableAt.hasDerivAt (h : DifferentiableAt 𝕜 f x) : HasDerivAt f (deriv f x) x :=
  h.HasFDerivAt.HasDerivAt
#align differentiable_at.has_deriv_at DifferentiableAt.hasDerivAt
-/

#print hasDerivAt_deriv_iff /-
@[simp]
theorem hasDerivAt_deriv_iff : HasDerivAt f (deriv f x) x ↔ DifferentiableAt 𝕜 f x :=
  ⟨fun h => h.DifferentiableAt, fun h => h.HasDerivAt⟩
#align has_deriv_at_deriv_iff hasDerivAt_deriv_iff
-/

#print hasDerivWithinAt_derivWithin_iff /-
@[simp]
theorem hasDerivWithinAt_derivWithin_iff :
    HasDerivWithinAt f (derivWithin f s x) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  ⟨fun h => h.DifferentiableWithinAt, fun h => h.HasDerivWithinAt⟩
#align has_deriv_within_at_deriv_within_iff hasDerivWithinAt_derivWithin_iff
-/

#print DifferentiableOn.hasDerivAt /-
theorem DifferentiableOn.hasDerivAt (h : DifferentiableOn 𝕜 f s) (hs : s ∈ 𝓝 x) :
    HasDerivAt f (deriv f x) x :=
  (h.HasFDerivAt hs).HasDerivAt
#align differentiable_on.has_deriv_at DifferentiableOn.hasDerivAt
-/

#print HasDerivAt.deriv /-
theorem HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x = f' :=
  h.DifferentiableAt.HasDerivAt.unique h
#align has_deriv_at.deriv HasDerivAt.deriv
-/

#print deriv_eq /-
theorem deriv_eq {f' : 𝕜 → F} (h : ∀ x, HasDerivAt f (f' x) x) : deriv f = f' :=
  funext fun x => (h x).deriv
#align deriv_eq deriv_eq
-/

#print HasDerivWithinAt.derivWithin /-
theorem HasDerivWithinAt.derivWithin (h : HasDerivWithinAt f f' s x)
    (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f' :=
  hxs.eq_deriv _ h.DifferentiableWithinAt.HasDerivWithinAt h
#align has_deriv_within_at.deriv_within HasDerivWithinAt.derivWithin
-/

#print fderivWithin_derivWithin /-
theorem fderivWithin_derivWithin : (fderivWithin 𝕜 f s x : 𝕜 → F) 1 = derivWithin f s x :=
  rfl
#align fderiv_within_deriv_within fderivWithin_derivWithin
-/

#print derivWithin_fderivWithin /-
theorem derivWithin_fderivWithin :
    smulRight (1 : 𝕜 →L[𝕜] 𝕜) (derivWithin f s x) = fderivWithin 𝕜 f s x := by simp [derivWithin]
#align deriv_within_fderiv_within derivWithin_fderivWithin
-/

#print fderiv_deriv /-
theorem fderiv_deriv : (fderiv 𝕜 f x : 𝕜 → F) 1 = deriv f x :=
  rfl
#align fderiv_deriv fderiv_deriv
-/

#print deriv_fderiv /-
theorem deriv_fderiv : smulRight (1 : 𝕜 →L[𝕜] 𝕜) (deriv f x) = fderiv 𝕜 f x := by simp [deriv]
#align deriv_fderiv deriv_fderiv
-/

#print DifferentiableAt.derivWithin /-
theorem DifferentiableAt.derivWithin (h : DifferentiableAt 𝕜 f x) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin f s x = deriv f x := by unfold derivWithin deriv; rw [h.fderiv_within hxs]
#align differentiable_at.deriv_within DifferentiableAt.derivWithin
-/

#print HasDerivWithinAt.deriv_eq_zero /-
theorem HasDerivWithinAt.deriv_eq_zero (hd : HasDerivWithinAt f 0 s x)
    (H : UniqueDiffWithinAt 𝕜 s x) : deriv f x = 0 :=
  (em' (DifferentiableAt 𝕜 f x)).elim deriv_zero_of_not_differentiableAt fun h =>
    H.eq_deriv _ h.HasDerivAt.HasDerivWithinAt hd
#align has_deriv_within_at.deriv_eq_zero HasDerivWithinAt.deriv_eq_zero
-/

#print derivWithin_of_mem /-
theorem derivWithin_of_mem (st : t ∈ 𝓝[s] x) (ht : UniqueDiffWithinAt 𝕜 s x)
    (h : DifferentiableWithinAt 𝕜 f t x) : derivWithin f s x = derivWithin f t x :=
  ((DifferentiableWithinAt.hasDerivWithinAt h).mono_of_mem st).derivWithin ht
#align deriv_within_of_mem derivWithin_of_mem
-/

#print derivWithin_subset /-
theorem derivWithin_subset (st : s ⊆ t) (ht : UniqueDiffWithinAt 𝕜 s x)
    (h : DifferentiableWithinAt 𝕜 f t x) : derivWithin f s x = derivWithin f t x :=
  ((DifferentiableWithinAt.hasDerivWithinAt h).mono st).derivWithin ht
#align deriv_within_subset derivWithin_subset
-/

#print derivWithin_congr_set' /-
theorem derivWithin_congr_set' (y : 𝕜) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    derivWithin f s x = derivWithin f t x := by simp only [derivWithin, fderivWithin_congr_set' y h]
#align deriv_within_congr_set' derivWithin_congr_set'
-/

#print derivWithin_congr_set /-
theorem derivWithin_congr_set (h : s =ᶠ[𝓝 x] t) : derivWithin f s x = derivWithin f t x := by
  simp only [derivWithin, fderivWithin_congr_set h]
#align deriv_within_congr_set derivWithin_congr_set
-/

#print derivWithin_univ /-
@[simp]
theorem derivWithin_univ : derivWithin f univ = deriv f := by ext; unfold derivWithin deriv;
  rw [fderivWithin_univ]
#align deriv_within_univ derivWithin_univ
-/

#print derivWithin_inter /-
theorem derivWithin_inter (ht : t ∈ 𝓝 x) : derivWithin f (s ∩ t) x = derivWithin f s x := by
  unfold derivWithin; rw [fderivWithin_inter ht]
#align deriv_within_inter derivWithin_inter
-/

#print derivWithin_of_open /-
theorem derivWithin_of_open (hs : IsOpen s) (hx : x ∈ s) : derivWithin f s x = deriv f x := by
  unfold derivWithin; rw [fderivWithin_of_open hs hx]; rfl
#align deriv_within_of_open derivWithin_of_open
-/

#print deriv_mem_iff /-
theorem deriv_mem_iff {f : 𝕜 → F} {s : Set F} {x : 𝕜} :
    deriv f x ∈ s ↔
      DifferentiableAt 𝕜 f x ∧ deriv f x ∈ s ∨ ¬DifferentiableAt 𝕜 f x ∧ (0 : F) ∈ s :=
  by by_cases hx : DifferentiableAt 𝕜 f x <;> simp [deriv_zero_of_not_differentiableAt, *]
#align deriv_mem_iff deriv_mem_iff
-/

#print derivWithin_mem_iff /-
theorem derivWithin_mem_iff {f : 𝕜 → F} {t : Set 𝕜} {s : Set F} {x : 𝕜} :
    derivWithin f t x ∈ s ↔
      DifferentiableWithinAt 𝕜 f t x ∧ derivWithin f t x ∈ s ∨
        ¬DifferentiableWithinAt 𝕜 f t x ∧ (0 : F) ∈ s :=
  by
  by_cases hx : DifferentiableWithinAt 𝕜 f t x <;>
    simp [derivWithin_zero_of_not_differentiableWithinAt, *]
#align deriv_within_mem_iff derivWithin_mem_iff
-/

#print differentiableWithinAt_Ioi_iff_Ici /-
theorem differentiableWithinAt_Ioi_iff_Ici [PartialOrder 𝕜] :
    DifferentiableWithinAt 𝕜 f (Ioi x) x ↔ DifferentiableWithinAt 𝕜 f (Ici x) x :=
  ⟨fun h => h.HasDerivWithinAt.Ici_of_Ioi.DifferentiableWithinAt, fun h =>
    h.HasDerivWithinAt.Ioi_of_Ici.DifferentiableWithinAt⟩
#align differentiable_within_at_Ioi_iff_Ici differentiableWithinAt_Ioi_iff_Ici
-/

#print derivWithin_Ioi_eq_Ici /-
-- Golfed while splitting the file
theorem derivWithin_Ioi_eq_Ici {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E)
    (x : ℝ) : derivWithin f (Ioi x) x = derivWithin f (Ici x) x :=
  by
  by_cases H : DifferentiableWithinAt ℝ f (Ioi x) x
  · have A := H.has_deriv_within_at.Ici_of_Ioi
    have B := (differentiableWithinAt_Ioi_iff_Ici.1 H).HasDerivWithinAt
    simpa using (uniqueDiffOn_Ici x).Eq le_rfl A B
  · rw [derivWithin_zero_of_not_differentiableWithinAt H,
      derivWithin_zero_of_not_differentiableWithinAt]
    rwa [differentiableWithinAt_Ioi_iff_Ici] at H 
#align deriv_within_Ioi_eq_Ici derivWithin_Ioi_eq_Ici
-/

section congr

/-! ### Congruence properties of derivatives -/


#print Filter.EventuallyEq.hasDerivAtFilter_iff /-
theorem Filter.EventuallyEq.hasDerivAtFilter_iff (h₀ : f₀ =ᶠ[L] f₁) (hx : f₀ x = f₁ x)
    (h₁ : f₀' = f₁') : HasDerivAtFilter f₀ f₀' x L ↔ HasDerivAtFilter f₁ f₁' x L :=
  h₀.hasFDerivAtFilter_iff hx (by simp [h₁])
#align filter.eventually_eq.has_deriv_at_filter_iff Filter.EventuallyEq.hasDerivAtFilter_iff
-/

#print HasDerivAtFilter.congr_of_eventuallyEq /-
theorem HasDerivAtFilter.congr_of_eventuallyEq (h : HasDerivAtFilter f f' x L) (hL : f₁ =ᶠ[L] f)
    (hx : f₁ x = f x) : HasDerivAtFilter f₁ f' x L := by rwa [hL.has_deriv_at_filter_iff hx rfl]
#align has_deriv_at_filter.congr_of_eventually_eq HasDerivAtFilter.congr_of_eventuallyEq
-/

#print HasDerivWithinAt.congr_mono /-
theorem HasDerivWithinAt.congr_mono (h : HasDerivWithinAt f f' s x) (ht : ∀ x ∈ t, f₁ x = f x)
    (hx : f₁ x = f x) (h₁ : t ⊆ s) : HasDerivWithinAt f₁ f' t x :=
  HasFDerivWithinAt.congr_mono h ht hx h₁
#align has_deriv_within_at.congr_mono HasDerivWithinAt.congr_mono
-/

#print HasDerivWithinAt.congr /-
theorem HasDerivWithinAt.congr (h : HasDerivWithinAt f f' s x) (hs : ∀ x ∈ s, f₁ x = f x)
    (hx : f₁ x = f x) : HasDerivWithinAt f₁ f' s x :=
  h.congr_mono hs hx (Subset.refl _)
#align has_deriv_within_at.congr HasDerivWithinAt.congr
-/

#print HasDerivWithinAt.congr_of_mem /-
theorem HasDerivWithinAt.congr_of_mem (h : HasDerivWithinAt f f' s x) (hs : ∀ x ∈ s, f₁ x = f x)
    (hx : x ∈ s) : HasDerivWithinAt f₁ f' s x :=
  h.congr hs (hs _ hx)
#align has_deriv_within_at.congr_of_mem HasDerivWithinAt.congr_of_mem
-/

#print HasDerivWithinAt.congr_of_eventuallyEq /-
theorem HasDerivWithinAt.congr_of_eventuallyEq (h : HasDerivWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : HasDerivWithinAt f₁ f' s x :=
  HasDerivAtFilter.congr_of_eventuallyEq h h₁ hx
#align has_deriv_within_at.congr_of_eventually_eq HasDerivWithinAt.congr_of_eventuallyEq
-/

#print HasDerivWithinAt.congr_of_eventuallyEq_of_mem /-
theorem HasDerivWithinAt.congr_of_eventuallyEq_of_mem (h : HasDerivWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) : HasDerivWithinAt f₁ f' s x :=
  h.congr_of_eventuallyEq h₁ (h₁.eq_of_nhdsWithin hx)
#align has_deriv_within_at.congr_of_eventually_eq_of_mem HasDerivWithinAt.congr_of_eventuallyEq_of_mem
-/

#print HasDerivAt.congr_of_eventuallyEq /-
theorem HasDerivAt.congr_of_eventuallyEq (h : HasDerivAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) :
    HasDerivAt f₁ f' x :=
  HasDerivAtFilter.congr_of_eventuallyEq h h₁ (mem_of_mem_nhds h₁ : _)
#align has_deriv_at.congr_of_eventually_eq HasDerivAt.congr_of_eventuallyEq
-/

#print Filter.EventuallyEq.derivWithin_eq /-
theorem Filter.EventuallyEq.derivWithin_eq (hL : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    derivWithin f₁ s x = derivWithin f s x := by unfold derivWithin; rw [hL.fderiv_within_eq hx]
#align filter.eventually_eq.deriv_within_eq Filter.EventuallyEq.derivWithin_eq
-/

#print derivWithin_congr /-
theorem derivWithin_congr (hs : EqOn f₁ f s) (hx : f₁ x = f x) :
    derivWithin f₁ s x = derivWithin f s x := by unfold derivWithin; rw [fderivWithin_congr hs hx]
#align deriv_within_congr derivWithin_congr
-/

#print Filter.EventuallyEq.deriv_eq /-
theorem Filter.EventuallyEq.deriv_eq (hL : f₁ =ᶠ[𝓝 x] f) : deriv f₁ x = deriv f x := by
  unfold deriv; rwa [Filter.EventuallyEq.fderiv_eq]
#align filter.eventually_eq.deriv_eq Filter.EventuallyEq.deriv_eq
-/

#print Filter.EventuallyEq.deriv /-
protected theorem Filter.EventuallyEq.deriv (h : f₁ =ᶠ[𝓝 x] f) : deriv f₁ =ᶠ[𝓝 x] deriv f :=
  h.eventuallyEq_nhds.mono fun x h => h.deriv_eq
#align filter.eventually_eq.deriv Filter.EventuallyEq.deriv
-/

end congr

section id

/-! ### Derivative of the identity -/


variable (s x L)

#print hasDerivAtFilter_id /-
theorem hasDerivAtFilter_id : HasDerivAtFilter id 1 x L :=
  (hasFDerivAtFilter_id x L).HasDerivAtFilter
#align has_deriv_at_filter_id hasDerivAtFilter_id
-/

#print hasDerivWithinAt_id /-
theorem hasDerivWithinAt_id : HasDerivWithinAt id 1 s x :=
  hasDerivAtFilter_id _ _
#align has_deriv_within_at_id hasDerivWithinAt_id
-/

#print hasDerivAt_id /-
theorem hasDerivAt_id : HasDerivAt id 1 x :=
  hasDerivAtFilter_id _ _
#align has_deriv_at_id hasDerivAt_id
-/

#print hasDerivAt_id' /-
theorem hasDerivAt_id' : HasDerivAt (fun x : 𝕜 => x) 1 x :=
  hasDerivAtFilter_id _ _
#align has_deriv_at_id' hasDerivAt_id'
-/

#print hasStrictDerivAt_id /-
theorem hasStrictDerivAt_id : HasStrictDerivAt id 1 x :=
  (hasStrictFDerivAt_id x).HasStrictDerivAt
#align has_strict_deriv_at_id hasStrictDerivAt_id
-/

#print deriv_id /-
theorem deriv_id : deriv id x = 1 :=
  HasDerivAt.deriv (hasDerivAt_id x)
#align deriv_id deriv_id
-/

#print deriv_id' /-
@[simp]
theorem deriv_id' : deriv (@id 𝕜) = fun _ => 1 :=
  funext deriv_id
#align deriv_id' deriv_id'
-/

#print deriv_id'' /-
@[simp]
theorem deriv_id'' : (deriv fun x : 𝕜 => x) = fun _ => 1 :=
  deriv_id'
#align deriv_id'' deriv_id''
-/

#print derivWithin_id /-
theorem derivWithin_id (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin id s x = 1 :=
  (hasDerivWithinAt_id x s).derivWithin hxs
#align deriv_within_id derivWithin_id
-/

end id

section Const

/-! ### Derivative of constant functions -/


variable (c : F) (s x L)

#print hasDerivAtFilter_const /-
theorem hasDerivAtFilter_const : HasDerivAtFilter (fun x => c) 0 x L :=
  (hasFDerivAtFilter_const c x L).HasDerivAtFilter
#align has_deriv_at_filter_const hasDerivAtFilter_const
-/

#print hasStrictDerivAt_const /-
theorem hasStrictDerivAt_const : HasStrictDerivAt (fun x => c) 0 x :=
  (hasStrictFDerivAt_const c x).HasStrictDerivAt
#align has_strict_deriv_at_const hasStrictDerivAt_const
-/

#print hasDerivWithinAt_const /-
theorem hasDerivWithinAt_const : HasDerivWithinAt (fun x => c) 0 s x :=
  hasDerivAtFilter_const _ _ _
#align has_deriv_within_at_const hasDerivWithinAt_const
-/

#print hasDerivAt_const /-
theorem hasDerivAt_const : HasDerivAt (fun x => c) 0 x :=
  hasDerivAtFilter_const _ _ _
#align has_deriv_at_const hasDerivAt_const
-/

#print deriv_const /-
theorem deriv_const : deriv (fun x => c) x = 0 :=
  HasDerivAt.deriv (hasDerivAt_const x c)
#align deriv_const deriv_const
-/

#print deriv_const' /-
@[simp]
theorem deriv_const' : (deriv fun x : 𝕜 => c) = fun x => 0 :=
  funext fun x => deriv_const x c
#align deriv_const' deriv_const'
-/

#print derivWithin_const /-
theorem derivWithin_const (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin (fun x => c) s x = 0 :=
  (hasDerivWithinAt_const _ _ _).derivWithin hxs
#align deriv_within_const derivWithin_const
-/

end Const

section Continuous

/-! ### Continuity of a function admitting a derivative -/


#print HasDerivAtFilter.tendsto_nhds /-
theorem HasDerivAtFilter.tendsto_nhds (hL : L ≤ 𝓝 x) (h : HasDerivAtFilter f f' x L) :
    Tendsto f L (𝓝 (f x)) :=
  h.tendsto_nhds hL
#align has_deriv_at_filter.tendsto_nhds HasDerivAtFilter.tendsto_nhds
-/

#print HasDerivWithinAt.continuousWithinAt /-
theorem HasDerivWithinAt.continuousWithinAt (h : HasDerivWithinAt f f' s x) :
    ContinuousWithinAt f s x :=
  HasDerivAtFilter.tendsto_nhds inf_le_left h
#align has_deriv_within_at.continuous_within_at HasDerivWithinAt.continuousWithinAt
-/

#print HasDerivAt.continuousAt /-
theorem HasDerivAt.continuousAt (h : HasDerivAt f f' x) : ContinuousAt f x :=
  HasDerivAtFilter.tendsto_nhds le_rfl h
#align has_deriv_at.continuous_at HasDerivAt.continuousAt
-/

#print HasDerivAt.continuousOn /-
protected theorem HasDerivAt.continuousOn {f f' : 𝕜 → F} (hderiv : ∀ x ∈ s, HasDerivAt f (f' x) x) :
    ContinuousOn f s := fun x hx => (hderiv x hx).ContinuousAt.ContinuousWithinAt
#align has_deriv_at.continuous_on HasDerivAt.continuousOn
-/

end Continuous

