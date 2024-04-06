/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Yury Kudryashov
-/
import Analysis.Calculus.Deriv.Basic
import Analysis.Calculus.FDeriv.Linear

#align_import analysis.calculus.deriv.linear from "leanprover-community/mathlib"@"f60c6087a7275b72d5db3c5a1d0e19e35a429c0a"

/-!
# Derivatives of continuous linear maps from the base field

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that `f : 𝕜 →L[𝕜] E` (or `f : 𝕜 →ₗ[𝕜] E`) has derivative `f 1`.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`analysis/calculus/deriv/basic`.

## Keywords

derivative, linear map
-/


universe u v w

open scoped Topology Filter

open Filter Asymptotics Set

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {x : 𝕜}

variable {s : Set 𝕜}

variable {L : Filter 𝕜}

section ContinuousLinearMap

/-! ### Derivative of continuous linear maps -/


variable (e : 𝕜 →L[𝕜] F)

#print ContinuousLinearMap.hasDerivAtFilter /-
protected theorem ContinuousLinearMap.hasDerivAtFilter : HasDerivAtFilter e (e 1) x L :=
  e.HasFDerivAtFilter.HasDerivAtFilter
#align continuous_linear_map.has_deriv_at_filter ContinuousLinearMap.hasDerivAtFilter
-/

#print ContinuousLinearMap.hasStrictDerivAt /-
protected theorem ContinuousLinearMap.hasStrictDerivAt : HasStrictDerivAt e (e 1) x :=
  e.HasStrictFDerivAt.HasStrictDerivAt
#align continuous_linear_map.has_strict_deriv_at ContinuousLinearMap.hasStrictDerivAt
-/

#print ContinuousLinearMap.hasDerivAt /-
protected theorem ContinuousLinearMap.hasDerivAt : HasDerivAt e (e 1) x :=
  e.HasDerivAtFilter
#align continuous_linear_map.has_deriv_at ContinuousLinearMap.hasDerivAt
-/

#print ContinuousLinearMap.hasDerivWithinAt /-
protected theorem ContinuousLinearMap.hasDerivWithinAt : HasDerivWithinAt e (e 1) s x :=
  e.HasDerivAtFilter
#align continuous_linear_map.has_deriv_within_at ContinuousLinearMap.hasDerivWithinAt
-/

#print ContinuousLinearMap.deriv /-
@[simp]
protected theorem ContinuousLinearMap.deriv : deriv e x = e 1 :=
  e.HasDerivAt.deriv
#align continuous_linear_map.deriv ContinuousLinearMap.deriv
-/

#print ContinuousLinearMap.derivWithin /-
protected theorem ContinuousLinearMap.derivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin e s x = e 1 :=
  e.HasDerivWithinAt.derivWithin hxs
#align continuous_linear_map.deriv_within ContinuousLinearMap.derivWithin
-/

end ContinuousLinearMap

section LinearMap

/-! ### Derivative of bundled linear maps -/


variable (e : 𝕜 →ₗ[𝕜] F)

#print LinearMap.hasDerivAtFilter /-
protected theorem LinearMap.hasDerivAtFilter : HasDerivAtFilter e (e 1) x L :=
  e.toContinuousLinearMap₁.HasDerivAtFilter
#align linear_map.has_deriv_at_filter LinearMap.hasDerivAtFilter
-/

#print LinearMap.hasStrictDerivAt /-
protected theorem LinearMap.hasStrictDerivAt : HasStrictDerivAt e (e 1) x :=
  e.toContinuousLinearMap₁.HasStrictDerivAt
#align linear_map.has_strict_deriv_at LinearMap.hasStrictDerivAt
-/

#print LinearMap.hasDerivAt /-
protected theorem LinearMap.hasDerivAt : HasDerivAt e (e 1) x :=
  e.HasDerivAtFilter
#align linear_map.has_deriv_at LinearMap.hasDerivAt
-/

#print LinearMap.hasDerivWithinAt /-
protected theorem LinearMap.hasDerivWithinAt : HasDerivWithinAt e (e 1) s x :=
  e.HasDerivAtFilter
#align linear_map.has_deriv_within_at LinearMap.hasDerivWithinAt
-/

#print LinearMap.deriv /-
@[simp]
protected theorem LinearMap.deriv : deriv e x = e 1 :=
  e.HasDerivAt.deriv
#align linear_map.deriv LinearMap.deriv
-/

#print LinearMap.derivWithin /-
protected theorem LinearMap.derivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin e s x = e 1 :=
  e.HasDerivWithinAt.derivWithin hxs
#align linear_map.deriv_within LinearMap.derivWithin
-/

end LinearMap

