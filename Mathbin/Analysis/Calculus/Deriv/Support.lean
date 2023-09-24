/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Analysis.Calculus.Deriv.Basic

#align_import analysis.calculus.deriv.support from "leanprover-community/mathlib"@"f60c6087a7275b72d5db3c5a1d0e19e35a429c0a"

/-!
# Support of the derivative of a function

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that the (topological) support of a function includes the support of its
derivative. As a corollary, we show that the derivative of a function with compact support has
compact support.

## Keywords

derivative, support
-/


universe u v

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {f : 𝕜 → E}

/-! ### Support of derivatives -/


section Support

open Function

#print support_deriv_subset /-
theorem support_deriv_subset : support (deriv f) ⊆ tsupport f :=
  by
  intro x
  rw [← not_imp_not]
  intro h2x
  rw [not_mem_tsupport_iff_eventuallyEq] at h2x 
  exact nmem_support.mpr (h2x.deriv_eq.trans (deriv_const x 0))
#align support_deriv_subset support_deriv_subset
-/

#print HasCompactSupport.deriv /-
theorem HasCompactSupport.deriv (hf : HasCompactSupport f) : HasCompactSupport (deriv f) :=
  hf.mono' support_deriv_subset
#align has_compact_support.deriv HasCompactSupport.deriv
-/

end Support

