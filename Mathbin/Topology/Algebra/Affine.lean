/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis

! This file was ported from Lean 3 source module topology.algebra.affine
! leanprover-community/mathlib commit 69c6a5a12d8a2b159f20933e60115a4f2de62b58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.AffineSpace.AffineMap
import Mathbin.Topology.Algebra.Group.Basic
import Mathbin.Topology.Algebra.MulAction

/-!
# Topological properties of affine spaces and maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

For now, this contains only a few facts regarding the continuity of affine maps in the special
case when the point space and vector space are the same.

TODO: Deal with the case where the point spaces are different from the vector spaces. Note that
we do have some results in this direction under the assumption that the topologies are induced by
(semi)norms.
-/


namespace AffineMap

variable {R E F : Type _}

variable [AddCommGroup E] [TopologicalSpace E]

variable [AddCommGroup F] [TopologicalSpace F] [TopologicalAddGroup F]

section Ring

variable [Ring R] [Module R E] [Module R F]

/- warning: affine_map.continuous_iff -> AffineMap.continuous_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : AddCommGroup.{u2} E] [_inst_2 : TopologicalSpace.{u2} E] [_inst_3 : AddCommGroup.{u3} F] [_inst_4 : TopologicalSpace.{u3} F] [_inst_5 : TopologicalAddGroup.{u3} F _inst_4 (AddCommGroup.toAddGroup.{u3} F _inst_3)] [_inst_6 : Ring.{u1} R] [_inst_7 : Module.{u1, u2} R E (Ring.toSemiring.{u1} R _inst_6) (AddCommGroup.toAddCommMonoid.{u2} E _inst_1)] [_inst_8 : Module.{u1, u3} R F (Ring.toSemiring.{u1} R _inst_6) (AddCommGroup.toAddCommMonoid.{u3} F _inst_3)] {f : AffineMap.{u1, u2, u2, u3, u3} R E E F F _inst_6 _inst_1 _inst_7 (addGroupIsAddTorsor.{u2} E (AddCommGroup.toAddGroup.{u2} E _inst_1)) _inst_3 _inst_8 (addGroupIsAddTorsor.{u3} F (AddCommGroup.toAddGroup.{u3} F _inst_3))}, Iff (Continuous.{u2, u3} E F _inst_2 _inst_4 (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (AffineMap.{u1, u2, u2, u3, u3} R E E F F _inst_6 _inst_1 _inst_7 (addGroupIsAddTorsor.{u2} E (AddCommGroup.toAddGroup.{u2} E _inst_1)) _inst_3 _inst_8 (addGroupIsAddTorsor.{u3} F (AddCommGroup.toAddGroup.{u3} F _inst_3))) (fun (_x : AffineMap.{u1, u2, u2, u3, u3} R E E F F _inst_6 _inst_1 _inst_7 (addGroupIsAddTorsor.{u2} E (AddCommGroup.toAddGroup.{u2} E _inst_1)) _inst_3 _inst_8 (addGroupIsAddTorsor.{u3} F (AddCommGroup.toAddGroup.{u3} F _inst_3))) => E -> F) (AffineMap.hasCoeToFun.{u1, u2, u2, u3, u3} R E E F F _inst_6 _inst_1 _inst_7 (addGroupIsAddTorsor.{u2} E (AddCommGroup.toAddGroup.{u2} E _inst_1)) _inst_3 _inst_8 (addGroupIsAddTorsor.{u3} F (AddCommGroup.toAddGroup.{u3} F _inst_3))) f)) (Continuous.{u2, u3} E F _inst_2 _inst_4 (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LinearMap.{u1, u1, u2, u3} R R (Ring.toSemiring.{u1} R _inst_6) (Ring.toSemiring.{u1} R _inst_6) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_6))) E F (AddCommGroup.toAddCommMonoid.{u2} E _inst_1) (AddCommGroup.toAddCommMonoid.{u3} F _inst_3) _inst_7 _inst_8) (fun (_x : LinearMap.{u1, u1, u2, u3} R R (Ring.toSemiring.{u1} R _inst_6) (Ring.toSemiring.{u1} R _inst_6) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_6))) E F (AddCommGroup.toAddCommMonoid.{u2} E _inst_1) (AddCommGroup.toAddCommMonoid.{u3} F _inst_3) _inst_7 _inst_8) => E -> F) (LinearMap.hasCoeToFun.{u1, u1, u2, u3} R R E F (Ring.toSemiring.{u1} R _inst_6) (Ring.toSemiring.{u1} R _inst_6) (AddCommGroup.toAddCommMonoid.{u2} E _inst_1) (AddCommGroup.toAddCommMonoid.{u3} F _inst_3) _inst_7 _inst_8 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_6)))) (AffineMap.linear.{u1, u2, u2, u3, u3} R E E F F _inst_6 _inst_1 _inst_7 (addGroupIsAddTorsor.{u2} E (AddCommGroup.toAddGroup.{u2} E _inst_1)) _inst_3 _inst_8 (addGroupIsAddTorsor.{u3} F (AddCommGroup.toAddGroup.{u3} F _inst_3)) f)))
but is expected to have type
  forall {R : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : AddCommGroup.{u2} E] [_inst_2 : TopologicalSpace.{u2} E] [_inst_3 : AddCommGroup.{u1} F] [_inst_4 : TopologicalSpace.{u1} F] [_inst_5 : TopologicalAddGroup.{u1} F _inst_4 (AddCommGroup.toAddGroup.{u1} F _inst_3)] [_inst_6 : Ring.{u3} R] [_inst_7 : Module.{u3, u2} R E (Ring.toSemiring.{u3} R _inst_6) (AddCommGroup.toAddCommMonoid.{u2} E _inst_1)] [_inst_8 : Module.{u3, u1} R F (Ring.toSemiring.{u3} R _inst_6) (AddCommGroup.toAddCommMonoid.{u1} F _inst_3)] {f : AffineMap.{u3, u2, u2, u1, u1} R E E F F _inst_6 _inst_1 _inst_7 (addGroupIsAddTorsor.{u2} E (AddCommGroup.toAddGroup.{u2} E _inst_1)) _inst_3 _inst_8 (addGroupIsAddTorsor.{u1} F (AddCommGroup.toAddGroup.{u1} F _inst_3))}, Iff (Continuous.{u2, u1} E F _inst_2 _inst_4 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (AffineMap.{u3, u2, u2, u1, u1} R E E F F _inst_6 _inst_1 _inst_7 (addGroupIsAddTorsor.{u2} E (AddCommGroup.toAddGroup.{u2} E _inst_1)) _inst_3 _inst_8 (addGroupIsAddTorsor.{u1} F (AddCommGroup.toAddGroup.{u1} F _inst_3))) E (fun (_x : E) => (fun (a._@.Mathlib.LinearAlgebra.AffineSpace.AffineMap._hyg.1004 : E) => F) _x) (AffineMap.funLike.{u3, u2, u2, u1, u1} R E E F F _inst_6 _inst_1 _inst_7 (addGroupIsAddTorsor.{u2} E (AddCommGroup.toAddGroup.{u2} E _inst_1)) _inst_3 _inst_8 (addGroupIsAddTorsor.{u1} F (AddCommGroup.toAddGroup.{u1} F _inst_3))) f)) (Continuous.{u2, u1} E F _inst_2 _inst_4 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LinearMap.{u3, u3, u2, u1} R R (Ring.toSemiring.{u3} R _inst_6) (Ring.toSemiring.{u3} R _inst_6) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R (Ring.toSemiring.{u3} R _inst_6))) E F (AddCommGroup.toAddCommMonoid.{u2} E _inst_1) (AddCommGroup.toAddCommMonoid.{u1} F _inst_3) _inst_7 _inst_8) E (fun (_x : E) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6190 : E) => F) _x) (LinearMap.instFunLikeLinearMap.{u3, u3, u2, u1} R R E F (Ring.toSemiring.{u3} R _inst_6) (Ring.toSemiring.{u3} R _inst_6) (AddCommGroup.toAddCommMonoid.{u2} E _inst_1) (AddCommGroup.toAddCommMonoid.{u1} F _inst_3) _inst_7 _inst_8 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R (Ring.toSemiring.{u3} R _inst_6)))) (AffineMap.linear.{u3, u2, u2, u1, u1} R E E F F _inst_6 _inst_1 _inst_7 (addGroupIsAddTorsor.{u2} E (AddCommGroup.toAddGroup.{u2} E _inst_1)) _inst_3 _inst_8 (addGroupIsAddTorsor.{u1} F (AddCommGroup.toAddGroup.{u1} F _inst_3)) f)))
Case conversion may be inaccurate. Consider using '#align affine_map.continuous_iff AffineMap.continuous_iffₓ'. -/
/-- An affine map is continuous iff its underlying linear map is continuous. See also
`affine_map.continuous_linear_iff`. -/
theorem continuous_iff {f : E →ᵃ[R] F} : Continuous f ↔ Continuous f.linear :=
  by
  constructor
  · intro hc
    rw [decomp' f]
    have := hc.sub continuous_const
    exact this
  · intro hc
    rw [decomp f]
    have := hc.add continuous_const
    exact this
#align affine_map.continuous_iff AffineMap.continuous_iff

/- warning: affine_map.line_map_continuous -> AffineMap.lineMap_continuous is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {F : Type.{u2}} [_inst_3 : AddCommGroup.{u2} F] [_inst_4 : TopologicalSpace.{u2} F] [_inst_5 : TopologicalAddGroup.{u2} F _inst_4 (AddCommGroup.toAddGroup.{u2} F _inst_3)] [_inst_6 : Ring.{u1} R] [_inst_8 : Module.{u1, u2} R F (Ring.toSemiring.{u1} R _inst_6) (AddCommGroup.toAddCommMonoid.{u2} F _inst_3)] [_inst_9 : TopologicalSpace.{u1} R] [_inst_10 : ContinuousSMul.{u1, u2} R F (SMulZeroClass.toHasSmul.{u1, u2} R F (AddZeroClass.toHasZero.{u2} F (AddMonoid.toAddZeroClass.{u2} F (AddCommMonoid.toAddMonoid.{u2} F (AddCommGroup.toAddCommMonoid.{u2} F _inst_3)))) (SMulWithZero.toSmulZeroClass.{u1, u2} R F (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_6))))) (AddZeroClass.toHasZero.{u2} F (AddMonoid.toAddZeroClass.{u2} F (AddCommMonoid.toAddMonoid.{u2} F (AddCommGroup.toAddCommMonoid.{u2} F _inst_3)))) (MulActionWithZero.toSMulWithZero.{u1, u2} R F (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_6)) (AddZeroClass.toHasZero.{u2} F (AddMonoid.toAddZeroClass.{u2} F (AddCommMonoid.toAddMonoid.{u2} F (AddCommGroup.toAddCommMonoid.{u2} F _inst_3)))) (Module.toMulActionWithZero.{u1, u2} R F (Ring.toSemiring.{u1} R _inst_6) (AddCommGroup.toAddCommMonoid.{u2} F _inst_3) _inst_8)))) _inst_9 _inst_4] {p : F} {v : F}, Continuous.{u1, u2} R F _inst_9 _inst_4 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (AffineMap.{u1, u1, u1, u2, u2} R R R F F _inst_6 (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_6))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R _inst_6)) (addGroupIsAddTorsor.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_6)))) _inst_3 _inst_8 (addGroupIsAddTorsor.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_3))) (fun (_x : AffineMap.{u1, u1, u1, u2, u2} R R R F F _inst_6 (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_6))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R _inst_6)) (addGroupIsAddTorsor.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_6)))) _inst_3 _inst_8 (addGroupIsAddTorsor.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_3))) => R -> F) (AffineMap.hasCoeToFun.{u1, u1, u1, u2, u2} R R R F F _inst_6 (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_6))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R _inst_6)) (addGroupIsAddTorsor.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_6)))) _inst_3 _inst_8 (addGroupIsAddTorsor.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_3))) (AffineMap.lineMap.{u1, u2, u2} R F F _inst_6 _inst_3 _inst_8 (addGroupIsAddTorsor.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_3)) p v))
but is expected to have type
  forall {R : Type.{u2}} {F : Type.{u1}} [_inst_3 : AddCommGroup.{u1} F] [_inst_4 : TopologicalSpace.{u1} F] [_inst_5 : TopologicalAddGroup.{u1} F _inst_4 (AddCommGroup.toAddGroup.{u1} F _inst_3)] [_inst_6 : Ring.{u2} R] [_inst_8 : Module.{u2, u1} R F (Ring.toSemiring.{u2} R _inst_6) (AddCommGroup.toAddCommMonoid.{u1} F _inst_3)] [_inst_9 : TopologicalSpace.{u2} R] [_inst_10 : ContinuousSMul.{u2, u1} R F (SMulZeroClass.toSMul.{u2, u1} R F (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F _inst_3))))) (SMulWithZero.toSMulZeroClass.{u2, u1} R F (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_6))) (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F _inst_3))))) (MulActionWithZero.toSMulWithZero.{u2, u1} R F (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_6)) (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F _inst_3))))) (Module.toMulActionWithZero.{u2, u1} R F (Ring.toSemiring.{u2} R _inst_6) (AddCommGroup.toAddCommMonoid.{u1} F _inst_3) _inst_8)))) _inst_9 _inst_4] {p : F} {v : F}, Continuous.{u2, u1} R F _inst_9 _inst_4 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (AffineMap.{u2, u2, u2, u1, u1} R R R F F _inst_6 (Ring.toAddCommGroup.{u2} R _inst_6) (AffineMap.instModuleToSemiringToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonUnitalRing.{u2} R _inst_6) (addGroupIsAddTorsor.{u2} R (AddGroupWithOne.toAddGroup.{u2} R (Ring.toAddGroupWithOne.{u2} R _inst_6))) _inst_3 _inst_8 (addGroupIsAddTorsor.{u1} F (AddCommGroup.toAddGroup.{u1} F _inst_3))) R (fun (_x : R) => (fun (a._@.Mathlib.LinearAlgebra.AffineSpace.AffineMap._hyg.1004 : R) => F) _x) (AffineMap.funLike.{u2, u2, u2, u1, u1} R R R F F _inst_6 (Ring.toAddCommGroup.{u2} R _inst_6) (AffineMap.instModuleToSemiringToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonUnitalRing.{u2} R _inst_6) (addGroupIsAddTorsor.{u2} R (AddGroupWithOne.toAddGroup.{u2} R (Ring.toAddGroupWithOne.{u2} R _inst_6))) _inst_3 _inst_8 (addGroupIsAddTorsor.{u1} F (AddCommGroup.toAddGroup.{u1} F _inst_3))) (AffineMap.lineMap.{u2, u1, u1} R F F _inst_6 _inst_3 _inst_8 (addGroupIsAddTorsor.{u1} F (AddCommGroup.toAddGroup.{u1} F _inst_3)) p v))
Case conversion may be inaccurate. Consider using '#align affine_map.line_map_continuous AffineMap.lineMap_continuousₓ'. -/
/-- The line map is continuous. -/
@[continuity]
theorem lineMap_continuous [TopologicalSpace R] [ContinuousSMul R F] {p v : F} :
    Continuous ⇑(lineMap p v : R →ᵃ[R] F) :=
  continuous_iff.mpr <|
    (continuous_id.smul continuous_const).add <| @continuous_const _ _ _ _ (0 : F)
#align affine_map.line_map_continuous AffineMap.lineMap_continuous

end Ring

section CommRing

variable [CommRing R] [Module R F] [ContinuousConstSMul R F]

#print AffineMap.homothety_continuous /-
@[continuity]
theorem homothety_continuous (x : F) (t : R) : Continuous <| homothety x t :=
  by
  suffices ⇑(homothety x t) = fun y => t • (y - x) + x
    by
    rw [this]
    continuity
  ext y
  simp [homothety_apply]
#align affine_map.homothety_continuous AffineMap.homothety_continuous
-/

end CommRing

section Field

variable [Field R] [Module R F] [ContinuousConstSMul R F]

/- warning: affine_map.homothety_is_open_map -> AffineMap.homothety_isOpenMap is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {F : Type.{u2}} [_inst_3 : AddCommGroup.{u2} F] [_inst_4 : TopologicalSpace.{u2} F] [_inst_5 : TopologicalAddGroup.{u2} F _inst_4 (AddCommGroup.toAddGroup.{u2} F _inst_3)] [_inst_6 : Field.{u1} R] [_inst_7 : Module.{u1, u2} R F (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R _inst_6))) (AddCommGroup.toAddCommMonoid.{u2} F _inst_3)] [_inst_8 : ContinuousConstSMul.{u1, u2} R F _inst_4 (SMulZeroClass.toHasSmul.{u1, u2} R F (AddZeroClass.toHasZero.{u2} F (AddMonoid.toAddZeroClass.{u2} F (AddCommMonoid.toAddMonoid.{u2} F (AddCommGroup.toAddCommMonoid.{u2} F _inst_3)))) (SMulWithZero.toSmulZeroClass.{u1, u2} R F (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R _inst_6))))))) (AddZeroClass.toHasZero.{u2} F (AddMonoid.toAddZeroClass.{u2} F (AddCommMonoid.toAddMonoid.{u2} F (AddCommGroup.toAddCommMonoid.{u2} F _inst_3)))) (MulActionWithZero.toSMulWithZero.{u1, u2} R F (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R _inst_6)))) (AddZeroClass.toHasZero.{u2} F (AddMonoid.toAddZeroClass.{u2} F (AddCommMonoid.toAddMonoid.{u2} F (AddCommGroup.toAddCommMonoid.{u2} F _inst_3)))) (Module.toMulActionWithZero.{u1, u2} R F (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R _inst_6))) (AddCommGroup.toAddCommMonoid.{u2} F _inst_3) _inst_7))))] (x : F) (t : R), (Ne.{succ u1} R t (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R _inst_6))))))))))) -> (IsOpenMap.{u2, u2} F F _inst_4 _inst_4 (coeFn.{succ u2, succ u2} (AffineMap.{u1, u2, u2, u2, u2} R F F F F (CommRing.toRing.{u1} R (Field.toCommRing.{u1} R _inst_6)) _inst_3 _inst_7 (addGroupIsAddTorsor.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_3)) _inst_3 _inst_7 (addGroupIsAddTorsor.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_3))) (fun (_x : AffineMap.{u1, u2, u2, u2, u2} R F F F F (CommRing.toRing.{u1} R (Field.toCommRing.{u1} R _inst_6)) _inst_3 _inst_7 (addGroupIsAddTorsor.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_3)) _inst_3 _inst_7 (addGroupIsAddTorsor.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_3))) => F -> F) (AffineMap.hasCoeToFun.{u1, u2, u2, u2, u2} R F F F F (CommRing.toRing.{u1} R (Field.toCommRing.{u1} R _inst_6)) _inst_3 _inst_7 (addGroupIsAddTorsor.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_3)) _inst_3 _inst_7 (addGroupIsAddTorsor.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_3))) (AffineMap.homothety.{u1, u2, u2} R F F (Field.toCommRing.{u1} R _inst_6) _inst_3 (addGroupIsAddTorsor.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_3)) _inst_7 x t)))
but is expected to have type
  forall {R : Type.{u2}} {F : Type.{u1}} [_inst_3 : AddCommGroup.{u1} F] [_inst_4 : TopologicalSpace.{u1} F] [_inst_5 : TopologicalAddGroup.{u1} F _inst_4 (AddCommGroup.toAddGroup.{u1} F _inst_3)] [_inst_6 : Field.{u2} R] [_inst_7 : Module.{u2, u1} R F (DivisionSemiring.toSemiring.{u2} R (Semifield.toDivisionSemiring.{u2} R (Field.toSemifield.{u2} R _inst_6))) (AddCommGroup.toAddCommMonoid.{u1} F _inst_3)] [_inst_8 : ContinuousConstSMul.{u2, u1} R F _inst_4 (SMulZeroClass.toSMul.{u2, u1} R F (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F _inst_3))))) (SMulWithZero.toSMulZeroClass.{u2, u1} R F (CommMonoidWithZero.toZero.{u2} R (CommGroupWithZero.toCommMonoidWithZero.{u2} R (Semifield.toCommGroupWithZero.{u2} R (Field.toSemifield.{u2} R _inst_6)))) (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F _inst_3))))) (MulActionWithZero.toSMulWithZero.{u2, u1} R F (Semiring.toMonoidWithZero.{u2} R (DivisionSemiring.toSemiring.{u2} R (Semifield.toDivisionSemiring.{u2} R (Field.toSemifield.{u2} R _inst_6)))) (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F _inst_3))))) (Module.toMulActionWithZero.{u2, u1} R F (DivisionSemiring.toSemiring.{u2} R (Semifield.toDivisionSemiring.{u2} R (Field.toSemifield.{u2} R _inst_6))) (AddCommGroup.toAddCommMonoid.{u1} F _inst_3) _inst_7))))] (x : F) (t : R), (Ne.{succ u2} R t (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (CommMonoidWithZero.toZero.{u2} R (CommGroupWithZero.toCommMonoidWithZero.{u2} R (Semifield.toCommGroupWithZero.{u2} R (Field.toSemifield.{u2} R _inst_6))))))) -> (IsOpenMap.{u1, u1} F F _inst_4 _inst_4 (FunLike.coe.{succ u1, succ u1, succ u1} (AffineMap.{u2, u1, u1, u1, u1} R F F F F (CommRing.toRing.{u2} R (Field.toCommRing.{u2} R _inst_6)) _inst_3 _inst_7 (addGroupIsAddTorsor.{u1} F (AddCommGroup.toAddGroup.{u1} F _inst_3)) _inst_3 _inst_7 (addGroupIsAddTorsor.{u1} F (AddCommGroup.toAddGroup.{u1} F _inst_3))) F (fun (_x : F) => (fun (a._@.Mathlib.LinearAlgebra.AffineSpace.AffineMap._hyg.1004 : F) => F) _x) (AffineMap.funLike.{u2, u1, u1, u1, u1} R F F F F (CommRing.toRing.{u2} R (Field.toCommRing.{u2} R _inst_6)) _inst_3 _inst_7 (addGroupIsAddTorsor.{u1} F (AddCommGroup.toAddGroup.{u1} F _inst_3)) _inst_3 _inst_7 (addGroupIsAddTorsor.{u1} F (AddCommGroup.toAddGroup.{u1} F _inst_3))) (AffineMap.homothety.{u2, u1, u1} R F F (Field.toCommRing.{u2} R _inst_6) _inst_3 (addGroupIsAddTorsor.{u1} F (AddCommGroup.toAddGroup.{u1} F _inst_3)) _inst_7 x t)))
Case conversion may be inaccurate. Consider using '#align affine_map.homothety_is_open_map AffineMap.homothety_isOpenMapₓ'. -/
theorem homothety_isOpenMap (x : F) (t : R) (ht : t ≠ 0) : IsOpenMap <| homothety x t := by
  apply IsOpenMap.of_inverse (homothety_continuous x t⁻¹) <;> intro e <;>
    simp [← AffineMap.comp_apply, ← homothety_mul, ht]
#align affine_map.homothety_is_open_map AffineMap.homothety_isOpenMap

end Field

end AffineMap

