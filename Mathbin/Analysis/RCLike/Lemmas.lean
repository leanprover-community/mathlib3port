/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Analysis.NormedSpace.FiniteDimension
import FieldTheory.Tower
import Analysis.RCLike.Basic

#align_import data.is_R_or_C.lemmas from "leanprover-community/mathlib"@"1b0a28e1c93409dbf6d69526863cd9984ef652ce"

/-! # Further lemmas about `is_R_or_C` 

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.-/


variable {K E : Type _} [RCLike K]

namespace Polynomial

open scoped Polynomial

#print Polynomial.ofReal_eval /-
theorem ofReal_eval (p : ℝ[X]) (x : ℝ) : (p.eval x : K) = aeval (↑x) p :=
  (@aeval_algebraMap_apply_eq_algebraMap_eval ℝ K _ _ _ x p).symm
#align polynomial.of_real_eval Polynomial.ofReal_eval
-/

end Polynomial

namespace FiniteDimensional

open scoped Classical

open RCLike

library_note "is_R_or_C instance"/--
This instance generates a type-class problem with a metavariable `?m` that should satisfy
`is_R_or_C ?m`. Since this can only be satisfied by `ℝ` or `ℂ`, this does not cause problems. -/


#print FiniteDimensional.rclike_to_real /-
/-- An `is_R_or_C` field is finite-dimensional over `ℝ`, since it is spanned by `{1, I}`. -/
@[nolint dangerous_instance]
instance rclike_to_real : FiniteDimensional ℝ K :=
  ⟨⟨{1, i}, by
      rw [eq_top_iff]
      intro a _
      rw [Finset.coe_insert, Finset.coe_singleton, Submodule.mem_span_insert]
      refine' ⟨re a, im a • I, _, _⟩
      · rw [Submodule.mem_span_singleton]
        use im a
      simp [re_add_im a, Algebra.smul_def, algebra_map_eq_of_real]⟩⟩
#align finite_dimensional.is_R_or_C_to_real FiniteDimensional.rclike_to_real
-/

variable (K E) [NormedAddCommGroup E] [NormedSpace K E]

#print FiniteDimensional.proper_rclike /-
/-- A finite dimensional vector space over an `is_R_or_C` is a proper metric space.

This is not an instance because it would cause a search for `finite_dimensional ?x E` before
`is_R_or_C ?x`. -/
theorem proper_rclike [FiniteDimensional K E] : ProperSpace E :=
  by
  letI : NormedSpace ℝ E := RestrictScalars.normedSpace ℝ K E
  letI : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ K E
  infer_instance
#align finite_dimensional.proper_is_R_or_C FiniteDimensional.proper_rclike
-/

variable {E}

#print FiniteDimensional.RCLike.properSpace_submodule /-
instance RCLike.properSpace_submodule (S : Submodule K E) [FiniteDimensional K ↥S] :
    ProperSpace S :=
  proper_rclike K S
#align finite_dimensional.is_R_or_C.proper_space_submodule FiniteDimensional.RCLike.properSpace_submodule
-/

end FiniteDimensional

namespace RCLike

#print RCLike.reCLM_norm /-
@[simp, is_R_or_C_simps]
theorem reCLM_norm : ‖(reCLM : K →L[ℝ] ℝ)‖ = 1 :=
  by
  apply le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _)
  convert ContinuousLinearMap.ratio_le_opNorm _ (1 : K)
  · simp
  · infer_instance
#align is_R_or_C.re_clm_norm RCLike.reCLM_norm
-/

#print RCLike.conjCLE_norm /-
@[simp, is_R_or_C_simps]
theorem conjCLE_norm : ‖(@conjCLE K _ : K →L[ℝ] K)‖ = 1 :=
  (@conjLIE K _).toLinearIsometry.norm_toContinuousLinearMap
#align is_R_or_C.conj_cle_norm RCLike.conjCLE_norm
-/

#print RCLike.ofRealCLM_norm /-
@[simp, is_R_or_C_simps]
theorem ofRealCLM_norm : ‖(ofRealCLM : ℝ →L[ℝ] K)‖ = 1 :=
  LinearIsometry.norm_toContinuousLinearMap ofRealLI
#align is_R_or_C.of_real_clm_norm RCLike.ofRealCLM_norm
-/

end RCLike

