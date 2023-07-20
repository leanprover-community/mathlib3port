/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathbin.Analysis.InnerProductSpace.Adjoint

#align_import analysis.inner_product_space.positive from "leanprover-community/mathlib"@"2ebc1d6c2fed9f54c95bbc3998eaa5570527129a"

/-!
# Positive operators

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define positive operators in a Hilbert space. We follow Bourbaki's choice
of requiring self adjointness in the definition.

## Main definitions

* `is_positive` : a continuous linear map is positive if it is self adjoint and
  `∀ x, 0 ≤ re ⟪T x, x⟫`

## Main statements

* `continuous_linear_map.is_positive.conj_adjoint` : if `T : E →L[𝕜] E` is positive,
  then for any `S : E →L[𝕜] F`, `S ∘L T ∘L S†` is also positive.
* `continuous_linear_map.is_positive_iff_complex` : in a ***complex*** hilbert space,
  checking that `⟪T x, x⟫` is a nonnegative real number for all `x` suffices to prove that
  `T` is positive

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

Positive operator
-/


open InnerProductSpace IsROrC ContinuousLinearMap

open scoped InnerProduct ComplexConjugate

namespace ContinuousLinearMap

variable {𝕜 E F : Type _} [IsROrC 𝕜]

variable [NormedAddCommGroup E] [NormedAddCommGroup F]

variable [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]

variable [CompleteSpace E] [CompleteSpace F]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

#print ContinuousLinearMap.IsPositive /-
/-- A continuous linear endomorphism `T` of a Hilbert space is **positive** if it is self adjoint
  and `∀ x, 0 ≤ re ⟪T x, x⟫`. -/
def IsPositive (T : E →L[𝕜] E) : Prop :=
  IsSelfAdjoint T ∧ ∀ x, 0 ≤ T.reApplyInnerSelf x
#align continuous_linear_map.is_positive ContinuousLinearMap.IsPositive
-/

#print ContinuousLinearMap.IsPositive.isSelfAdjoint /-
theorem IsPositive.isSelfAdjoint {T : E →L[𝕜] E} (hT : IsPositive T) : IsSelfAdjoint T :=
  hT.1
#align continuous_linear_map.is_positive.is_self_adjoint ContinuousLinearMap.IsPositive.isSelfAdjoint
-/

#print ContinuousLinearMap.IsPositive.inner_nonneg_left /-
theorem IsPositive.inner_nonneg_left {T : E →L[𝕜] E} (hT : IsPositive T) (x : E) :
    0 ≤ re ⟪T x, x⟫ :=
  hT.2 x
#align continuous_linear_map.is_positive.inner_nonneg_left ContinuousLinearMap.IsPositive.inner_nonneg_left
-/

#print ContinuousLinearMap.IsPositive.inner_nonneg_right /-
theorem IsPositive.inner_nonneg_right {T : E →L[𝕜] E} (hT : IsPositive T) (x : E) :
    0 ≤ re ⟪x, T x⟫ := by rw [inner_re_symm] <;> exact hT.inner_nonneg_left x
#align continuous_linear_map.is_positive.inner_nonneg_right ContinuousLinearMap.IsPositive.inner_nonneg_right
-/

#print ContinuousLinearMap.isPositive_zero /-
theorem isPositive_zero : IsPositive (0 : E →L[𝕜] E) :=
  by
  refine' ⟨isSelfAdjoint_zero _, fun x => _⟩
  change 0 ≤ re ⟪_, _⟫
  rw [zero_apply, inner_zero_left, ZeroHomClass.map_zero]
#align continuous_linear_map.is_positive_zero ContinuousLinearMap.isPositive_zero
-/

#print ContinuousLinearMap.isPositive_one /-
theorem isPositive_one : IsPositive (1 : E →L[𝕜] E) :=
  ⟨isSelfAdjoint_one _, fun x => inner_self_nonneg⟩
#align continuous_linear_map.is_positive_one ContinuousLinearMap.isPositive_one
-/

#print ContinuousLinearMap.IsPositive.add /-
theorem IsPositive.add {T S : E →L[𝕜] E} (hT : T.IsPositive) (hS : S.IsPositive) :
    (T + S).IsPositive :=
  by
  refine' ⟨hT.is_self_adjoint.add hS.is_self_adjoint, fun x => _⟩
  rw [re_apply_inner_self, add_apply, inner_add_left, map_add]
  exact add_nonneg (hT.inner_nonneg_left x) (hS.inner_nonneg_left x)
#align continuous_linear_map.is_positive.add ContinuousLinearMap.IsPositive.add
-/

#print ContinuousLinearMap.IsPositive.conj_adjoint /-
theorem IsPositive.conj_adjoint {T : E →L[𝕜] E} (hT : T.IsPositive) (S : E →L[𝕜] F) :
    (S ∘L T ∘L S†).IsPositive :=
  by
  refine' ⟨hT.is_self_adjoint.conj_adjoint S, fun x => _⟩
  rw [re_apply_inner_self, comp_apply, ← adjoint_inner_right]
  exact hT.inner_nonneg_left _
#align continuous_linear_map.is_positive.conj_adjoint ContinuousLinearMap.IsPositive.conj_adjoint
-/

#print ContinuousLinearMap.IsPositive.adjoint_conj /-
theorem IsPositive.adjoint_conj {T : E →L[𝕜] E} (hT : T.IsPositive) (S : F →L[𝕜] E) :
    (S† ∘L T ∘L S).IsPositive := by
  convert hT.conj_adjoint (S†)
  rw [adjoint_adjoint]
#align continuous_linear_map.is_positive.adjoint_conj ContinuousLinearMap.IsPositive.adjoint_conj
-/

#print ContinuousLinearMap.IsPositive.conj_orthogonalProjection /-
theorem IsPositive.conj_orthogonalProjection (U : Submodule 𝕜 E) {T : E →L[𝕜] E} (hT : T.IsPositive)
    [CompleteSpace U] :
    (U.subtypeL ∘L
        orthogonalProjection U ∘L T ∘L U.subtypeL ∘L orthogonalProjection U).IsPositive :=
  by
  have := hT.conj_adjoint (U.subtypeL ∘L orthogonalProjection U)
  rwa [(orthogonalProjection_isSelfAdjoint U).adjoint_eq] at this 
#align continuous_linear_map.is_positive.conj_orthogonal_projection ContinuousLinearMap.IsPositive.conj_orthogonalProjection
-/

#print ContinuousLinearMap.IsPositive.orthogonalProjection_comp /-
theorem IsPositive.orthogonalProjection_comp {T : E →L[𝕜] E} (hT : T.IsPositive) (U : Submodule 𝕜 E)
    [CompleteSpace U] : (orthogonalProjection U ∘L T ∘L U.subtypeL).IsPositive :=
  by
  have := hT.conj_adjoint (orthogonalProjection U : E →L[𝕜] U)
  rwa [U.adjoint_orthogonal_projection] at this 
#align continuous_linear_map.is_positive.orthogonal_projection_comp ContinuousLinearMap.IsPositive.orthogonalProjection_comp
-/

section Complex

variable {E' : Type _} [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']

#print ContinuousLinearMap.isPositive_iff_complex /-
theorem isPositive_iff_complex (T : E' →L[ℂ] E') :
    IsPositive T ↔ ∀ x, (re ⟪T x, x⟫_ℂ : ℂ) = ⟪T x, x⟫_ℂ ∧ 0 ≤ re ⟪T x, x⟫_ℂ :=
  by
  simp_rw [is_positive, forall_and, is_self_adjoint_iff_is_symmetric,
    LinearMap.isSymmetric_iff_inner_map_self_real, conj_eq_iff_re]
  rfl
#align continuous_linear_map.is_positive_iff_complex ContinuousLinearMap.isPositive_iff_complex
-/

end Complex

end ContinuousLinearMap

