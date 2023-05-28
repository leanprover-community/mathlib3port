/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang

! This file was ported from Lean 3 source module analysis.normed_space.conformal_linear_map
! leanprover-community/mathlib commit 9d2f0748e6c50d7a2657c564b1ff2c695b39148d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.NormedSpace.Basic
import Mathbin.Analysis.NormedSpace.LinearIsometry

/-!
# Conformal Linear Maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A continuous linear map between `R`-normed spaces `X` and `Y` `is_conformal_map` if it is
a nonzero multiple of a linear isometry.

## Main definitions

* `is_conformal_map`: the main definition of conformal linear maps

## Main results

* The conformality of the composition of two conformal linear maps, the identity map
  and multiplications by nonzero constants as continuous linear maps
* `is_conformal_map_of_subsingleton`: all continuous linear maps on singleton spaces are conformal
* `is_conformal_map.preserves_angle`: if a continuous linear map is conformal, then it
                                      preserves all angles in the normed space

See `analysis.normed_space.conformal_linear_map.inner_product` for
* `is_conformal_map_iff`: a map between inner product spaces is conformal
  iff it preserves inner products up to a fixed scalar factor.


## Tags

conformal

## Warning

The definition of conformality in this file does NOT require the maps to be orientation-preserving.
-/


noncomputable section

open Function LinearIsometry ContinuousLinearMap

#print IsConformalMap /-
/-- A continuous linear map `f'` is said to be conformal if it's
    a nonzero multiple of a linear isometry. -/
def IsConformalMap {R : Type _} {X Y : Type _} [NormedField R] [SeminormedAddCommGroup X]
    [SeminormedAddCommGroup Y] [NormedSpace R X] [NormedSpace R Y] (f' : X →L[R] Y) :=
  ∃ (c : R)(hc : c ≠ 0)(li : X →ₗᵢ[R] Y), f' = c • li.toContinuousLinearMap
#align is_conformal_map IsConformalMap
-/

variable {R M N G M' : Type _} [NormedField R] [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
  [SeminormedAddCommGroup G] [NormedSpace R M] [NormedSpace R N] [NormedSpace R G]
  [NormedAddCommGroup M'] [NormedSpace R M'] {f : M →L[R] N} {g : N →L[R] G} {c : R}

/- warning: is_conformal_map_id -> isConformalMap_id is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : NormedField.{u1} R] [_inst_2 : SeminormedAddCommGroup.{u2} M] [_inst_5 : NormedSpace.{u1, u2} R M _inst_1 _inst_2], IsConformalMap.{u1, u2, u2} R M M _inst_1 _inst_2 _inst_2 _inst_5 _inst_5 (ContinuousLinearMap.id.{u1, u2} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R (NormedCommRing.toNormedRing.{u1} R (NormedField.toNormedCommRing.{u1} R _inst_1)))) M (UniformSpace.toTopologicalSpace.{u2} M (PseudoMetricSpace.toUniformSpace.{u2} M (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} M _inst_2))) (AddCommGroup.toAddCommMonoid.{u2} M (SeminormedAddCommGroup.toAddCommGroup.{u2} M _inst_2)) (NormedSpace.toModule.{u1, u2} R M _inst_1 _inst_2 _inst_5))
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : NormedField.{u2} R] [_inst_2 : SeminormedAddCommGroup.{u1} M] [_inst_5 : NormedSpace.{u2, u1} R M _inst_1 _inst_2], IsConformalMap.{u2, u1, u1} R M M _inst_1 _inst_2 _inst_2 _inst_5 _inst_5 (ContinuousLinearMap.id.{u2, u1} R (DivisionSemiring.toSemiring.{u2} R (Semifield.toDivisionSemiring.{u2} R (Field.toSemifield.{u2} R (NormedField.toField.{u2} R _inst_1)))) M (UniformSpace.toTopologicalSpace.{u1} M (PseudoMetricSpace.toUniformSpace.{u1} M (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} M _inst_2))) (AddCommGroup.toAddCommMonoid.{u1} M (SeminormedAddCommGroup.toAddCommGroup.{u1} M _inst_2)) (NormedSpace.toModule.{u2, u1} R M _inst_1 _inst_2 _inst_5))
Case conversion may be inaccurate. Consider using '#align is_conformal_map_id isConformalMap_idₓ'. -/
theorem isConformalMap_id : IsConformalMap (id R M) :=
  ⟨1, one_ne_zero, id, by simp⟩
#align is_conformal_map_id isConformalMap_id

/- warning: is_conformal_map.smul -> IsConformalMap.smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_conformal_map.smul IsConformalMap.smulₓ'. -/
theorem IsConformalMap.smul (hf : IsConformalMap f) {c : R} (hc : c ≠ 0) : IsConformalMap (c • f) :=
  by
  rcases hf with ⟨c', hc', li, rfl⟩
  exact ⟨c * c', mul_ne_zero hc hc', li, smul_smul _ _ _⟩
#align is_conformal_map.smul IsConformalMap.smul

/- warning: is_conformal_map_const_smul -> isConformalMap_const_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_conformal_map_const_smul isConformalMap_const_smulₓ'. -/
theorem isConformalMap_const_smul (hc : c ≠ 0) : IsConformalMap (c • id R M) :=
  isConformalMap_id.smul hc
#align is_conformal_map_const_smul isConformalMap_const_smul

/- warning: linear_isometry.is_conformal_map -> LinearIsometry.isConformalMap is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : NormedField.{u1} R] [_inst_2 : SeminormedAddCommGroup.{u2} M] [_inst_3 : SeminormedAddCommGroup.{u3} N] [_inst_5 : NormedSpace.{u1, u2} R M _inst_1 _inst_2] [_inst_6 : NormedSpace.{u1, u3} R N _inst_1 _inst_3] (f' : LinearIsometry.{u1, u1, u2, u3} R R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R (NormedCommRing.toNormedRing.{u1} R (NormedField.toNormedCommRing.{u1} R _inst_1)))) (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R (NormedCommRing.toNormedRing.{u1} R (NormedField.toNormedCommRing.{u1} R _inst_1)))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R (NormedCommRing.toNormedRing.{u1} R (NormedField.toNormedCommRing.{u1} R _inst_1)))))) M N _inst_2 _inst_3 (NormedSpace.toModule.{u1, u2} R M _inst_1 _inst_2 _inst_5) (NormedSpace.toModule.{u1, u3} R N _inst_1 _inst_3 _inst_6)), IsConformalMap.{u1, u2, u3} R M N _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 (LinearIsometry.toContinuousLinearMap.{u1, u1, u2, u3} R R M N (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R (NormedCommRing.toNormedRing.{u1} R (NormedField.toNormedCommRing.{u1} R _inst_1)))) (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R (NormedCommRing.toNormedRing.{u1} R (NormedField.toNormedCommRing.{u1} R _inst_1)))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R (NormedCommRing.toNormedRing.{u1} R (NormedField.toNormedCommRing.{u1} R _inst_1)))))) _inst_2 _inst_3 (NormedSpace.toModule.{u1, u2} R M _inst_1 _inst_2 _inst_5) (NormedSpace.toModule.{u1, u3} R N _inst_1 _inst_3 _inst_6) f')
but is expected to have type
  forall {R : Type.{u3}} {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : NormedField.{u3} R] [_inst_2 : SeminormedAddCommGroup.{u2} M] [_inst_3 : SeminormedAddCommGroup.{u1} N] [_inst_5 : NormedSpace.{u3, u2} R M _inst_1 _inst_2] [_inst_6 : NormedSpace.{u3, u1} R N _inst_1 _inst_3] (f' : LinearIsometry.{u3, u3, u2, u1} R R (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (Field.toSemifield.{u3} R (NormedField.toField.{u3} R _inst_1)))) (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (Field.toSemifield.{u3} R (NormedField.toField.{u3} R _inst_1)))) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (Field.toSemifield.{u3} R (NormedField.toField.{u3} R _inst_1)))))) M N _inst_2 _inst_3 (NormedSpace.toModule.{u3, u2} R M _inst_1 _inst_2 _inst_5) (NormedSpace.toModule.{u3, u1} R N _inst_1 _inst_3 _inst_6)), IsConformalMap.{u3, u2, u1} R M N _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 (LinearIsometry.toContinuousLinearMap.{u3, u3, u2, u1} R R M N (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (Field.toSemifield.{u3} R (NormedField.toField.{u3} R _inst_1)))) (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (Field.toSemifield.{u3} R (NormedField.toField.{u3} R _inst_1)))) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (Field.toSemifield.{u3} R (NormedField.toField.{u3} R _inst_1)))))) _inst_2 _inst_3 (NormedSpace.toModule.{u3, u2} R M _inst_1 _inst_2 _inst_5) (NormedSpace.toModule.{u3, u1} R N _inst_1 _inst_3 _inst_6) f')
Case conversion may be inaccurate. Consider using '#align linear_isometry.is_conformal_map LinearIsometry.isConformalMapₓ'. -/
protected theorem LinearIsometry.isConformalMap (f' : M →ₗᵢ[R] N) :
    IsConformalMap f'.toContinuousLinearMap :=
  ⟨1, one_ne_zero, f', (one_smul _ _).symm⟩
#align linear_isometry.is_conformal_map LinearIsometry.isConformalMap

/- warning: is_conformal_map_of_subsingleton -> isConformalMap_of_subsingleton is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : NormedField.{u1} R] [_inst_2 : SeminormedAddCommGroup.{u2} M] [_inst_3 : SeminormedAddCommGroup.{u3} N] [_inst_5 : NormedSpace.{u1, u2} R M _inst_1 _inst_2] [_inst_6 : NormedSpace.{u1, u3} R N _inst_1 _inst_3] [_inst_10 : Subsingleton.{succ u2} M] (f' : ContinuousLinearMap.{u1, u1, u2, u3} R R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R (NormedCommRing.toNormedRing.{u1} R (NormedField.toNormedCommRing.{u1} R _inst_1)))) (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R (NormedCommRing.toNormedRing.{u1} R (NormedField.toNormedCommRing.{u1} R _inst_1)))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R (NormedCommRing.toNormedRing.{u1} R (NormedField.toNormedCommRing.{u1} R _inst_1)))))) M (UniformSpace.toTopologicalSpace.{u2} M (PseudoMetricSpace.toUniformSpace.{u2} M (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} M _inst_2))) (AddCommGroup.toAddCommMonoid.{u2} M (SeminormedAddCommGroup.toAddCommGroup.{u2} M _inst_2)) N (UniformSpace.toTopologicalSpace.{u3} N (PseudoMetricSpace.toUniformSpace.{u3} N (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} N _inst_3))) (AddCommGroup.toAddCommMonoid.{u3} N (SeminormedAddCommGroup.toAddCommGroup.{u3} N _inst_3)) (NormedSpace.toModule.{u1, u2} R M _inst_1 _inst_2 _inst_5) (NormedSpace.toModule.{u1, u3} R N _inst_1 _inst_3 _inst_6)), IsConformalMap.{u1, u2, u3} R M N _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 f'
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u3}} {N : Type.{u1}} [_inst_1 : NormedField.{u2} R] [_inst_2 : SeminormedAddCommGroup.{u3} M] [_inst_3 : SeminormedAddCommGroup.{u1} N] [_inst_5 : NormedSpace.{u2, u3} R M _inst_1 _inst_2] [_inst_6 : NormedSpace.{u2, u1} R N _inst_1 _inst_3] [_inst_10 : Subsingleton.{succ u3} M] (f' : ContinuousLinearMap.{u2, u2, u3, u1} R R (DivisionSemiring.toSemiring.{u2} R (Semifield.toDivisionSemiring.{u2} R (Field.toSemifield.{u2} R (NormedField.toField.{u2} R _inst_1)))) (DivisionSemiring.toSemiring.{u2} R (Semifield.toDivisionSemiring.{u2} R (Field.toSemifield.{u2} R (NormedField.toField.{u2} R _inst_1)))) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (DivisionSemiring.toSemiring.{u2} R (Semifield.toDivisionSemiring.{u2} R (Field.toSemifield.{u2} R (NormedField.toField.{u2} R _inst_1)))))) M (UniformSpace.toTopologicalSpace.{u3} M (PseudoMetricSpace.toUniformSpace.{u3} M (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} M _inst_2))) (AddCommGroup.toAddCommMonoid.{u3} M (SeminormedAddCommGroup.toAddCommGroup.{u3} M _inst_2)) N (UniformSpace.toTopologicalSpace.{u1} N (PseudoMetricSpace.toUniformSpace.{u1} N (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} N _inst_3))) (AddCommGroup.toAddCommMonoid.{u1} N (SeminormedAddCommGroup.toAddCommGroup.{u1} N _inst_3)) (NormedSpace.toModule.{u2, u3} R M _inst_1 _inst_2 _inst_5) (NormedSpace.toModule.{u2, u1} R N _inst_1 _inst_3 _inst_6)), IsConformalMap.{u2, u3, u1} R M N _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 f'
Case conversion may be inaccurate. Consider using '#align is_conformal_map_of_subsingleton isConformalMap_of_subsingletonₓ'. -/
@[nontriviality]
theorem isConformalMap_of_subsingleton [Subsingleton M] (f' : M →L[R] N) : IsConformalMap f' :=
  ⟨1, one_ne_zero, ⟨0, fun x => by simp [Subsingleton.elim x 0]⟩, Subsingleton.elim _ _⟩
#align is_conformal_map_of_subsingleton isConformalMap_of_subsingleton

namespace IsConformalMap

/- warning: is_conformal_map.comp -> IsConformalMap.comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_conformal_map.comp IsConformalMap.compₓ'. -/
theorem comp (hg : IsConformalMap g) (hf : IsConformalMap f) : IsConformalMap (g.comp f) :=
  by
  rcases hf with ⟨cf, hcf, lif, rfl⟩
  rcases hg with ⟨cg, hcg, lig, rfl⟩
  refine' ⟨cg * cf, mul_ne_zero hcg hcf, lig.comp lif, _⟩
  rw [smul_comp, comp_smul, mul_smul]
  rfl
#align is_conformal_map.comp IsConformalMap.comp

/- warning: is_conformal_map.injective -> IsConformalMap.injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_conformal_map.injective IsConformalMap.injectiveₓ'. -/
protected theorem injective {f : M' →L[R] N} (h : IsConformalMap f) : Function.Injective f :=
  by
  rcases h with ⟨c, hc, li, rfl⟩
  exact (smul_right_injective _ hc).comp li.injective
#align is_conformal_map.injective IsConformalMap.injective

/- warning: is_conformal_map.ne_zero -> IsConformalMap.ne_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_conformal_map.ne_zero IsConformalMap.ne_zeroₓ'. -/
theorem ne_zero [Nontrivial M'] {f' : M' →L[R] N} (hf' : IsConformalMap f') : f' ≠ 0 :=
  by
  rintro rfl
  rcases exists_ne (0 : M') with ⟨a, ha⟩
  exact ha (hf'.injective rfl)
#align is_conformal_map.ne_zero IsConformalMap.ne_zero

end IsConformalMap

