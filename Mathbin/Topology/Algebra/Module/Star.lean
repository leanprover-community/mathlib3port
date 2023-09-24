/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Frédéric Dupuis
-/
import Algebra.Star.Module
import Topology.Algebra.Module.Basic
import Topology.Algebra.Star

#align_import topology.algebra.module.star from "leanprover-community/mathlib"@"ad84a13c884fd19e286fb7abb36f4b9ba7e2f615"

/-!
# The star operation, bundled as a continuous star-linear equiv

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


#print starL /-
/-- If `A` is a topological module over a commutative `R` with compatible actions,
then `star` is a continuous semilinear equivalence. -/
@[simps]
def starL (R : Type _) {A : Type _} [CommSemiring R] [StarRing R] [AddCommMonoid A]
    [StarAddMonoid A] [Module R A] [StarModule R A] [TopologicalSpace A] [ContinuousStar A] :
    A ≃L⋆[R] A where
  toLinearEquiv := starLinearEquiv R
  continuous_toFun := continuous_star
  continuous_invFun := continuous_star
#align starL starL
-/

#print starL' /-
-- TODO: this could be replaced with something like `(starL R).restrict_scalarsₛₗ h` if we
-- implemented the idea in
-- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Star-semilinear.20maps.20are.20semilinear.20when.20star.20is.20trivial/near/359557835
/-- If `A` is a topological module over a commutative `R` with trivial star and compatible actions,
then `star` is a continuous linear equivalence. -/
@[simps]
def starL' (R : Type _) {A : Type _} [CommSemiring R] [StarRing R] [TrivialStar R] [AddCommMonoid A]
    [StarAddMonoid A] [Module R A] [StarModule R A] [TopologicalSpace A] [ContinuousStar A] :
    A ≃L[R] A :=
  (starL R : A ≃L⋆[R] A).trans
    ({ AddEquiv.refl A with
        map_smul' := fun r a => by simp [starRingEnd_apply]
        continuous_toFun := continuous_id
        continuous_invFun := continuous_id } :
      A ≃L⋆[R] A)
#align starL' starL'
-/

variable (R : Type _) (A : Type _) [Semiring R] [StarMul R] [TrivialStar R] [AddCommGroup A]
  [Module R A] [StarAddMonoid A] [StarModule R A] [Invertible (2 : R)] [TopologicalSpace A]

#print continuous_selfAdjointPart /-
theorem continuous_selfAdjointPart [ContinuousAdd A] [ContinuousStar A] [ContinuousConstSMul R A] :
    Continuous (@selfAdjointPart R A _ _ _ _ _ _ _ _) :=
  ((continuous_const_smul _).comp <| continuous_id.add continuous_star).subtype_mk _
#align continuous_self_adjoint_part continuous_selfAdjointPart
-/

#print continuous_skewAdjointPart /-
theorem continuous_skewAdjointPart [ContinuousSub A] [ContinuousStar A] [ContinuousConstSMul R A] :
    Continuous (@skewAdjointPart R A _ _ _ _ _ _ _ _) :=
  ((continuous_const_smul _).comp <| continuous_id.sub continuous_star).subtype_mk _
#align continuous_skew_adjoint_part continuous_skewAdjointPart
-/

#print continuous_decomposeProdAdjoint /-
theorem continuous_decomposeProdAdjoint [TopologicalAddGroup A] [ContinuousStar A]
    [ContinuousConstSMul R A] : Continuous (@StarModule.decomposeProdAdjoint R A _ _ _ _ _ _ _ _) :=
  (continuous_selfAdjointPart R A).prod_mk (continuous_skewAdjointPart R A)
#align continuous_decompose_prod_adjoint continuous_decomposeProdAdjoint
-/

#print continuous_decomposeProdAdjoint_symm /-
theorem continuous_decomposeProdAdjoint_symm [TopologicalAddGroup A] :
    Continuous (@StarModule.decomposeProdAdjoint R A _ _ _ _ _ _ _ _).symm :=
  (continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)
#align continuous_decompose_prod_adjoint_symm continuous_decomposeProdAdjoint_symm
-/

#print selfAdjointPartL /-
/-- The self-adjoint part of an element of a star module, as a continuous linear map. -/
@[simps]
def selfAdjointPartL [ContinuousAdd A] [ContinuousStar A] [ContinuousConstSMul R A] :
    A →L[R] selfAdjoint A where
  toLinearMap := selfAdjointPart R
  cont := continuous_selfAdjointPart _ _
#align self_adjoint_partL selfAdjointPartL
-/

#print skewAdjointPartL /-
/-- The skew-adjoint part of an element of a star module, as a continuous linear map. -/
@[simps]
def skewAdjointPartL [ContinuousSub A] [ContinuousStar A] [ContinuousConstSMul R A] :
    A →L[R] skewAdjoint A where
  toLinearMap := skewAdjointPart R
  cont := continuous_skewAdjointPart _ _
#align skew_adjoint_partL skewAdjointPartL
-/

#print StarModule.decomposeProdAdjointL /-
/-- The decomposition of elements of a star module into their self- and skew-adjoint parts,
as a continuous linear equivalence. -/
@[simps]
def StarModule.decomposeProdAdjointL [TopologicalAddGroup A] [ContinuousStar A]
    [ContinuousConstSMul R A] : A ≃L[R] selfAdjoint A × skewAdjoint A
    where
  toLinearEquiv := StarModule.decomposeProdAdjoint R A
  continuous_toFun := continuous_decomposeProdAdjoint _ _
  continuous_invFun := continuous_decomposeProdAdjoint_symm _ _
#align star_module.decompose_prod_adjointL StarModule.decomposeProdAdjointL
-/

