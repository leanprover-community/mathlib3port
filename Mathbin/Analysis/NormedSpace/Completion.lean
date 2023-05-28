/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module analysis.normed_space.completion
! leanprover-community/mathlib commit 33c67ae661dd8988516ff7f247b0be3018cdd952
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Normed.Group.Completion
import Mathbin.Analysis.NormedSpace.OperatorNorm
import Mathbin.Topology.Algebra.UniformRing

/-!
# Normed space structure on the completion of a normed space

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

If `E` is a normed space over `𝕜`, then so is `uniform_space.completion E`. In this file we provide
necessary instances and define `uniform_space.completion.to_complₗᵢ` - coercion
`E → uniform_space.completion E` as a bundled linear isometry.

We also show that if `A` is a normed algebra over `𝕜`, then so is `uniform_space.completion A`.

TODO: Generalise the results here from the concrete `completion` to any `abstract_completion`.
-/


noncomputable section

namespace UniformSpace

namespace Completion

variable (𝕜 E : Type _) [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

#print UniformSpace.Completion.NormedSpace.to_uniformContinuousConstSMul /-
instance (priority := 100) NormedSpace.to_uniformContinuousConstSMul :
    UniformContinuousConstSMul 𝕜 E :=
  ⟨fun c => (lipschitzWith_smul c).UniformContinuous⟩
#align uniform_space.completion.normed_space.to_has_uniform_continuous_const_smul UniformSpace.Completion.NormedSpace.to_uniformContinuousConstSMul
-/

instance : NormedSpace 𝕜 (Completion E) :=
  { Completion.instModule with
    smul := (· • ·)
    norm_smul_le := fun c x =>
      induction_on x
        (isClosed_le (continuous_const_smul _).norm (continuous_const.mul continuous_norm)) fun y =>
        by simp only [← coe_smul, norm_coe, norm_smul] }

variable {𝕜 E}

/- warning: uniform_space.completion.to_complₗᵢ -> UniformSpace.Completion.toComplₗᵢ is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : NormedField.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E _inst_1 (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)], LinearIsometry.{u1, u1, u2, u2} 𝕜 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))) (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))))) E (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.Completion.normedAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))) (NormedSpace.toModule.{u1, u2} 𝕜 E _inst_1 (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (UniformSpace.Completion.instModule.{u1, u2} 𝕜 E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))) (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2) (UniformSpace.Completion.toComplₗᵢ._proof_1.{u2} E _inst_2) (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))) (NormedSpace.toModule.{u1, u2} 𝕜 E _inst_1 (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (UniformSpace.Completion.NormedSpace.to_uniformContinuousConstSMul.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3))
but is expected to have type
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : NormedField.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E _inst_1 (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)], LinearIsometry.{u1, u1, u2, u2} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1)))) (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1)))) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1)))))) E (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))) (NormedSpace.toModule.{u1, u2} 𝕜 E _inst_1 (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (UniformSpace.Completion.instModule.{u1, u2} 𝕜 E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))) (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)) (SeminormedAddCommGroup.to_uniformAddGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)) (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1)))) (NormedSpace.toModule.{u1, u2} 𝕜 E _inst_1 (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (UniformSpace.Completion.NormedSpace.to_uniformContinuousConstSMul.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3))
Case conversion may be inaccurate. Consider using '#align uniform_space.completion.to_complₗᵢ UniformSpace.Completion.toComplₗᵢₓ'. -/
/-- Embedding of a normed space to its completion as a linear isometry. -/
def toComplₗᵢ : E →ₗᵢ[𝕜] Completion E :=
  { toCompl with
    toFun := coe
    map_smul' := coe_smul
    norm_map' := norm_coe }
#align uniform_space.completion.to_complₗᵢ UniformSpace.Completion.toComplₗᵢ

/- warning: uniform_space.completion.coe_to_complₗᵢ -> UniformSpace.Completion.coe_toComplₗᵢ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align uniform_space.completion.coe_to_complₗᵢ UniformSpace.Completion.coe_toComplₗᵢₓ'. -/
@[simp]
theorem coe_toComplₗᵢ : ⇑(toComplₗᵢ : E →ₗᵢ[𝕜] Completion E) = coe :=
  rfl
#align uniform_space.completion.coe_to_complₗᵢ UniformSpace.Completion.coe_toComplₗᵢ

/- warning: uniform_space.completion.to_complL -> UniformSpace.Completion.toComplL is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : NormedField.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E _inst_1 (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)], ContinuousLinearMap.{u1, u1, u2, u2} 𝕜 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))) (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.toTopologicalSpace.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (PseudoMetricSpace.toUniformSpace.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.Completion.normedAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) (AddCommGroup.toAddCommMonoid.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.Completion.addCommGroup.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))) (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2) (UniformSpace.Completion.toComplL._proof_1.{u2} E _inst_2))) (NormedSpace.toModule.{u1, u2} 𝕜 E _inst_1 (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (UniformSpace.Completion.instModule.{u1, u2} 𝕜 E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))) (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2) (UniformSpace.Completion.toComplL._proof_2.{u2} E _inst_2) (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))) (NormedSpace.toModule.{u1, u2} 𝕜 E _inst_1 (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (UniformSpace.Completion.NormedSpace.to_uniformContinuousConstSMul.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3))
but is expected to have type
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : NormedField.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E _inst_1 (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)], ContinuousLinearMap.{u1, u1, u2, u2} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1)))) (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1)))) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1)))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.toTopologicalSpace.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (PseudoMetricSpace.toUniformSpace.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) (AddCommGroup.toAddCommMonoid.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.Completion.instAddCommGroupCompletion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))) (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2) (SeminormedAddCommGroup.to_uniformAddGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (NormedSpace.toModule.{u1, u2} 𝕜 E _inst_1 (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (UniformSpace.Completion.instModule.{u1, u2} 𝕜 E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))) (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2) (SeminormedAddCommGroup.to_uniformAddGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)) (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1)))) (NormedSpace.toModule.{u1, u2} 𝕜 E _inst_1 (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (UniformSpace.Completion.NormedSpace.to_uniformContinuousConstSMul.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3))
Case conversion may be inaccurate. Consider using '#align uniform_space.completion.to_complL UniformSpace.Completion.toComplLₓ'. -/
/-- Embedding of a normed space to its completion as a continuous linear map. -/
def toComplL : E →L[𝕜] Completion E :=
  toComplₗᵢ.toContinuousLinearMap
#align uniform_space.completion.to_complL UniformSpace.Completion.toComplL

/- warning: uniform_space.completion.coe_to_complL -> UniformSpace.Completion.coe_toComplL is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align uniform_space.completion.coe_to_complL UniformSpace.Completion.coe_toComplLₓ'. -/
@[simp]
theorem coe_toComplL : ⇑(toComplL : E →L[𝕜] Completion E) = coe :=
  rfl
#align uniform_space.completion.coe_to_complL UniformSpace.Completion.coe_toComplL

/- warning: uniform_space.completion.norm_to_complL -> UniformSpace.Completion.norm_toComplL is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align uniform_space.completion.norm_to_complL UniformSpace.Completion.norm_toComplLₓ'. -/
@[simp]
theorem norm_toComplL {𝕜 E : Type _} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [Nontrivial E] : ‖(toComplL : E →L[𝕜] Completion E)‖ = 1 :=
  (toComplₗᵢ : E →ₗᵢ[𝕜] Completion E).norm_toContinuousLinearMap
#align uniform_space.completion.norm_to_complL UniformSpace.Completion.norm_toComplL

section Algebra

variable (𝕜) (A : Type _)

instance [SeminormedRing A] : NormedRing (Completion A) :=
  { Completion.ring,
    Completion.instMetricSpace with
    dist_eq := fun x y => by
      apply completion.induction_on₂ x y <;> clear x y
      · refine' isClosed_eq (completion.uniform_continuous_extension₂ _).Continuous _
        exact Continuous.comp completion.continuous_extension continuous_sub
      · intro x y
        rw [← completion.coe_sub, norm_coe, completion.dist_eq, dist_eq_norm]
    norm_mul := fun x y => by
      apply completion.induction_on₂ x y <;> clear x y
      ·
        exact
          isClosed_le (Continuous.comp continuous_norm continuous_mul)
            (Continuous.comp Real.continuous_mul
              (Continuous.prod_map continuous_norm continuous_norm))
      · intro x y
        simp only [← coe_mul, norm_coe]
        exact norm_mul_le x y }

instance [SeminormedCommRing A] [NormedAlgebra 𝕜 A] [UniformContinuousConstSMul 𝕜 A] :
    NormedAlgebra 𝕜 (Completion A) :=
  { Completion.algebra A 𝕜 with
    norm_smul_le := fun r x =>
      by
      apply completion.induction_on x <;> clear x
      ·
        exact
          isClosed_le (Continuous.comp continuous_norm (continuous_const_smul r))
            (Continuous.comp (continuous_mul_left _) continuous_norm)
      · intro x
        simp only [← coe_smul, norm_coe]
        exact norm_smul_le r x }

end Algebra

end Completion

end UniformSpace

