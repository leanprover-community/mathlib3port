/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash

! This file was ported from Lean 3 source module topology.continuous_function.locally_constant
! leanprover-community/mathlib commit f0339374016bccf700da0b2e0129d107c4346521
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.LocallyConstant.Algebra
import Mathbin.Topology.ContinuousFunction.Basic
import Mathbin.Topology.ContinuousFunction.Algebra

/-!
# The algebra morphism from locally constant functions to continuous functions.

-/


namespace LocallyConstant

variable {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y] (f : LocallyConstant X Y)

/- warning: locally_constant.to_continuous_map_monoid_hom -> LocallyConstant.toContinuousMapMonoidHom is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] [_inst_3 : Monoid.{u2} Y] [_inst_4 : ContinuousMul.{u2} Y _inst_2 (MulOneClass.toHasMul.{u2} Y (Monoid.toMulOneClass.{u2} Y _inst_3))], MonoidHom.{max u1 u2, max u1 u2} (LocallyConstant.{u1, u2} X Y _inst_1) (ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) (LocallyConstant.mulOneClass.{u1, u2} X Y _inst_1 (Monoid.toMulOneClass.{u2} Y _inst_3)) (ContinuousMap.mulOneClass.{u1, u2} X Y _inst_1 _inst_2 (Monoid.toMulOneClass.{u2} Y _inst_3) _inst_4)
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] [_inst_3 : Monoid.{u2} Y] [_inst_4 : ContinuousMul.{u2} Y _inst_2 (MulOneClass.toMul.{u2} Y (Monoid.toMulOneClass.{u2} Y _inst_3))], MonoidHom.{max u2 u1, max u2 u1} (LocallyConstant.{u1, u2} X Y _inst_1) (ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) (LocallyConstant.instMulOneClassLocallyConstant.{u1, u2} X Y _inst_1 (Monoid.toMulOneClass.{u2} Y _inst_3)) (ContinuousMap.instMulOneClassContinuousMap.{u1, u2} X Y _inst_1 _inst_2 (Monoid.toMulOneClass.{u2} Y _inst_3) _inst_4)
Case conversion may be inaccurate. Consider using '#align locally_constant.to_continuous_map_monoid_hom LocallyConstant.toContinuousMapMonoidHomₓ'. -/
/-- The inclusion of locally-constant functions into continuous functions as a multiplicative
monoid hom. -/
@[to_additive
      "The inclusion of locally-constant functions into continuous functions as an\nadditive monoid hom.",
  simps]
def toContinuousMapMonoidHom [Monoid Y] [ContinuousMul Y] : LocallyConstant X Y →* C(X, Y)
    where
  toFun := coe
  map_one' := by
    ext
    simp
  map_mul' x y := by
    ext
    simp
#align locally_constant.to_continuous_map_monoid_hom LocallyConstant.toContinuousMapMonoidHom
#align locally_constant.to_continuous_map_add_monoid_hom LocallyConstant.toContinuousMapAddMonoidHom

/- warning: locally_constant.to_continuous_map_linear_map -> LocallyConstant.toContinuousMapLinearMap is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] (R : Type.{u3}) [_inst_3 : Semiring.{u3} R] [_inst_4 : AddCommMonoid.{u2} Y] [_inst_5 : Module.{u3, u2} R Y _inst_3 _inst_4] [_inst_6 : ContinuousAdd.{u2} Y _inst_2 (AddZeroClass.toHasAdd.{u2} Y (AddMonoid.toAddZeroClass.{u2} Y (AddCommMonoid.toAddMonoid.{u2} Y _inst_4)))] [_inst_7 : ContinuousConstSMul.{u3, u2} R Y _inst_2 (SMulZeroClass.toHasSmul.{u3, u2} R Y (AddZeroClass.toHasZero.{u2} Y (AddMonoid.toAddZeroClass.{u2} Y (AddCommMonoid.toAddMonoid.{u2} Y _inst_4))) (SMulWithZero.toSmulZeroClass.{u3, u2} R Y (MulZeroClass.toHasZero.{u3} R (MulZeroOneClass.toMulZeroClass.{u3} R (MonoidWithZero.toMulZeroOneClass.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_3)))) (AddZeroClass.toHasZero.{u2} Y (AddMonoid.toAddZeroClass.{u2} Y (AddCommMonoid.toAddMonoid.{u2} Y _inst_4))) (MulActionWithZero.toSMulWithZero.{u3, u2} R Y (Semiring.toMonoidWithZero.{u3} R _inst_3) (AddZeroClass.toHasZero.{u2} Y (AddMonoid.toAddZeroClass.{u2} Y (AddCommMonoid.toAddMonoid.{u2} Y _inst_4))) (Module.toMulActionWithZero.{u3, u2} R Y _inst_3 _inst_4 _inst_5))))], LinearMap.{u3, u3, max u1 u2, max u1 u2} R R _inst_3 _inst_3 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_3)) (LocallyConstant.{u1, u2} X Y _inst_1) (ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) (LocallyConstant.addCommMonoid.{u1, u2} X Y _inst_1 _inst_4) (ContinuousMap.addCommMonoid.{u1, u2} X Y _inst_1 _inst_2 _inst_4 _inst_6) (LocallyConstant.module.{u1, u2, u3} X Y _inst_1 R _inst_3 _inst_4 _inst_5) (ContinuousMap.module.{u1, u3, u2} X _inst_1 R Y _inst_2 _inst_3 _inst_4 _inst_6 _inst_5 _inst_7)
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] (R : Type.{u3}) [_inst_3 : Semiring.{u3} R] [_inst_4 : AddCommMonoid.{u2} Y] [_inst_5 : Module.{u3, u2} R Y _inst_3 _inst_4] [_inst_6 : ContinuousAdd.{u2} Y _inst_2 (AddZeroClass.toAdd.{u2} Y (AddMonoid.toAddZeroClass.{u2} Y (AddCommMonoid.toAddMonoid.{u2} Y _inst_4)))] [_inst_7 : ContinuousConstSMul.{u3, u2} R Y _inst_2 (SMulZeroClass.toSMul.{u3, u2} R Y (AddMonoid.toZero.{u2} Y (AddCommMonoid.toAddMonoid.{u2} Y _inst_4)) (SMulWithZero.toSMulZeroClass.{u3, u2} R Y (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_3)) (AddMonoid.toZero.{u2} Y (AddCommMonoid.toAddMonoid.{u2} Y _inst_4)) (MulActionWithZero.toSMulWithZero.{u3, u2} R Y (Semiring.toMonoidWithZero.{u3} R _inst_3) (AddMonoid.toZero.{u2} Y (AddCommMonoid.toAddMonoid.{u2} Y _inst_4)) (Module.toMulActionWithZero.{u3, u2} R Y _inst_3 _inst_4 _inst_5))))], LinearMap.{u3, u3, max u2 u1, max u2 u1} R R _inst_3 _inst_3 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_3)) (LocallyConstant.{u1, u2} X Y _inst_1) (ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) (LocallyConstant.instAddCommMonoidLocallyConstant.{u1, u2} X Y _inst_1 _inst_4) (ContinuousMap.instAddCommMonoidContinuousMap.{u1, u2} X Y _inst_1 _inst_2 _inst_4 _inst_6) (LocallyConstant.instModuleLocallyConstantInstAddCommMonoidLocallyConstant.{u1, u2, u3} X Y _inst_1 R _inst_3 _inst_4 _inst_5) (ContinuousMap.module.{u1, u3, u2} X _inst_1 R Y _inst_2 _inst_3 _inst_4 _inst_6 _inst_5 _inst_7)
Case conversion may be inaccurate. Consider using '#align locally_constant.to_continuous_map_linear_map LocallyConstant.toContinuousMapLinearMapₓ'. -/
/-- The inclusion of locally-constant functions into continuous functions as a linear map. -/
@[simps]
def toContinuousMapLinearMap (R : Type _) [Semiring R] [AddCommMonoid Y] [Module R Y]
    [ContinuousAdd Y] [ContinuousConstSMul R Y] : LocallyConstant X Y →ₗ[R] C(X, Y)
    where
  toFun := coe
  map_add' x y := by
    ext
    simp
  map_smul' x y := by
    ext
    simp
#align locally_constant.to_continuous_map_linear_map LocallyConstant.toContinuousMapLinearMap

/- warning: locally_constant.to_continuous_map_alg_hom -> LocallyConstant.toContinuousMapAlgHom is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] (R : Type.{u3}) [_inst_3 : CommSemiring.{u3} R] [_inst_4 : Semiring.{u2} Y] [_inst_5 : Algebra.{u3, u2} R Y _inst_3 _inst_4] [_inst_6 : TopologicalSemiring.{u2} Y _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} Y (Semiring.toNonAssocSemiring.{u2} Y _inst_4))], AlgHom.{u3, max u1 u2, max u1 u2} R (LocallyConstant.{u1, u2} X Y _inst_1) (ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) _inst_3 (LocallyConstant.semiring.{u1, u2} X Y _inst_1 _inst_4) (ContinuousMap.semiring.{u1, u2} X Y _inst_1 _inst_2 _inst_4 _inst_6) (LocallyConstant.algebra.{u1, u2, u3} X Y _inst_1 R _inst_3 _inst_4 _inst_5) (ContinuousMap.algebra.{u1, u3, u2} X _inst_1 R _inst_3 Y _inst_2 _inst_4 _inst_5 _inst_6)
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] (R : Type.{u3}) [_inst_3 : CommSemiring.{u3} R] [_inst_4 : Semiring.{u2} Y] [_inst_5 : Algebra.{u3, u2} R Y _inst_3 _inst_4] [_inst_6 : TopologicalSemiring.{u2} Y _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} Y (Semiring.toNonAssocSemiring.{u2} Y _inst_4))], AlgHom.{u3, max u2 u1, max u2 u1} R (LocallyConstant.{u1, u2} X Y _inst_1) (ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) _inst_3 (LocallyConstant.instSemiringLocallyConstant.{u1, u2} X Y _inst_1 _inst_4) (ContinuousMap.instSemiringContinuousMap.{u1, u2} X Y _inst_1 _inst_2 _inst_4 _inst_6) (LocallyConstant.instAlgebraLocallyConstantInstSemiringLocallyConstant.{u1, u2, u3} X Y _inst_1 R _inst_3 _inst_4 _inst_5) (ContinuousMap.algebra.{u1, u3, u2} X _inst_1 R _inst_3 Y _inst_2 _inst_4 _inst_5 _inst_6)
Case conversion may be inaccurate. Consider using '#align locally_constant.to_continuous_map_alg_hom LocallyConstant.toContinuousMapAlgHomₓ'. -/
/-- The inclusion of locally-constant functions into continuous functions as an algebra map. -/
@[simps]
def toContinuousMapAlgHom (R : Type _) [CommSemiring R] [Semiring Y] [Algebra R Y]
    [TopologicalSemiring Y] : LocallyConstant X Y →ₐ[R] C(X, Y)
    where
  toFun := coe
  map_one' := by
    ext
    simp
  map_mul' x y := by
    ext
    simp
  map_zero' := by
    ext
    simp
  map_add' x y := by
    ext
    simp
  commutes' r := by
    ext x
    simp [Algebra.smul_def]
#align locally_constant.to_continuous_map_alg_hom LocallyConstant.toContinuousMapAlgHom

end LocallyConstant

