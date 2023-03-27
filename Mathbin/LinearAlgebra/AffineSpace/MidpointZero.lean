/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module linear_algebra.affine_space.midpoint_zero
! leanprover-community/mathlib commit 78261225eb5cedc61c5c74ecb44e5b385d13b733
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.CharP.Invertible
import Mathbin.LinearAlgebra.AffineSpace.Midpoint

/-!
# Midpoint of a segment for characteristic zero

We collect lemmas that require that the underlying ring has characteristic zero.

## Tags

midpoint
-/


open AffineMap AffineEquiv

/- warning: line_map_inv_two -> lineMap_inv_two is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : DivisionRing.{u1} R] [_inst_2 : CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R _inst_1))))] [_inst_3 : AddCommGroup.{u2} V] [_inst_4 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_3)] [_inst_5 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_3)] (a : P) (b : P), Eq.{succ u3} P (coeFn.{max (succ u1) (succ u2) (succ u3), max (succ u1) (succ u3)} (AffineMap.{u1, u1, u1, u2, u3} R R R V P (DivisionRing.toRing.{u1} R _inst_1) (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R _inst_1))) (addGroupIsAddTorsor.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R _inst_1))))) _inst_3 _inst_4 _inst_5) (fun (_x : AffineMap.{u1, u1, u1, u2, u3} R R R V P (DivisionRing.toRing.{u1} R _inst_1) (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R _inst_1))) (addGroupIsAddTorsor.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R _inst_1))))) _inst_3 _inst_4 _inst_5) => R -> P) (AffineMap.hasCoeToFun.{u1, u1, u1, u2, u3} R R R V P (DivisionRing.toRing.{u1} R _inst_1) (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R _inst_1))) (addGroupIsAddTorsor.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R _inst_1))))) _inst_3 _inst_4 _inst_5) (AffineMap.lineMap.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R _inst_1) _inst_3 _inst_4 _inst_5 a b) (Inv.inv.{u1} R (DivInvMonoid.toHasInv.{u1} R (DivisionRing.toDivInvMonoid.{u1} R _inst_1)) (OfNat.ofNat.{u1} R 2 (OfNat.mk.{u1} R 2 (bit0.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (DivisionRing.toRing.{u1} R _inst_1))) (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R _inst_1))))))))))) (midpoint.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R _inst_1) (invertibleTwo.{u1} R _inst_1 _inst_2) _inst_3 _inst_4 _inst_5 a b)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : DivisionRing.{u3} R] [_inst_2 : CharZero.{u3} R (AddGroupWithOne.toAddMonoidWithOne.{u3} R (Ring.toAddGroupWithOne.{u3} R (DivisionRing.toRing.{u3} R _inst_1)))] [_inst_3 : AddCommGroup.{u2} V] [_inst_4 : Module.{u3, u2} R V (DivisionSemiring.toSemiring.{u3} R (DivisionRing.toDivisionSemiring.{u3} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_3)] [_inst_5 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_3)] (a : P) (b : P), Eq.{succ u1} ((fun (a._@.Mathlib.LinearAlgebra.AffineSpace.AffineMap._hyg.1004 : R) => P) (Inv.inv.{u3} R (DivisionRing.toInv.{u3} R _inst_1) (OfNat.ofNat.{u3} R 2 (instOfNat.{u3} R 2 (NonAssocRing.toNatCast.{u3} R (Ring.toNonAssocRing.{u3} R (DivisionRing.toRing.{u3} R _inst_1))) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (FunLike.coe.{max (max (succ u3) (succ u2)) (succ u1), succ u3, succ u1} (AffineMap.{u3, u3, u3, u2, u1} R R R V P (DivisionRing.toRing.{u3} R _inst_1) (Ring.toAddCommGroup.{u3} R (DivisionRing.toRing.{u3} R _inst_1)) (AffineMap.instModuleToSemiringToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonUnitalRing.{u3} R (DivisionRing.toRing.{u3} R _inst_1)) (addGroupIsAddTorsor.{u3} R (AddGroupWithOne.toAddGroup.{u3} R (Ring.toAddGroupWithOne.{u3} R (DivisionRing.toRing.{u3} R _inst_1)))) _inst_3 _inst_4 _inst_5) R (fun (_x : R) => (fun (a._@.Mathlib.LinearAlgebra.AffineSpace.AffineMap._hyg.1004 : R) => P) _x) (AffineMap.funLike.{u3, u3, u3, u2, u1} R R R V P (DivisionRing.toRing.{u3} R _inst_1) (Ring.toAddCommGroup.{u3} R (DivisionRing.toRing.{u3} R _inst_1)) (AffineMap.instModuleToSemiringToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonUnitalRing.{u3} R (DivisionRing.toRing.{u3} R _inst_1)) (addGroupIsAddTorsor.{u3} R (AddGroupWithOne.toAddGroup.{u3} R (Ring.toAddGroupWithOne.{u3} R (DivisionRing.toRing.{u3} R _inst_1)))) _inst_3 _inst_4 _inst_5) (AffineMap.lineMap.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R _inst_1) _inst_3 _inst_4 _inst_5 a b) (Inv.inv.{u3} R (DivisionRing.toInv.{u3} R _inst_1) (OfNat.ofNat.{u3} R 2 (instOfNat.{u3} R 2 (NonAssocRing.toNatCast.{u3} R (Ring.toNonAssocRing.{u3} R (DivisionRing.toRing.{u3} R _inst_1))) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (midpoint.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R _inst_1) (invertibleTwo.{u3} R _inst_1 _inst_2) _inst_3 _inst_4 _inst_5 a b)
Case conversion may be inaccurate. Consider using '#align line_map_inv_two lineMap_inv_twoₓ'. -/
theorem lineMap_inv_two {R : Type _} {V P : Type _} [DivisionRing R] [CharZero R] [AddCommGroup V]
    [Module R V] [AddTorsor V P] (a b : P) : lineMap a b (2⁻¹ : R) = midpoint R a b :=
  rfl
#align line_map_inv_two lineMap_inv_two

/- warning: line_map_one_half -> lineMap_one_half is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : DivisionRing.{u1} R] [_inst_2 : CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R _inst_1))))] [_inst_3 : AddCommGroup.{u2} V] [_inst_4 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_3)] [_inst_5 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_3)] (a : P) (b : P), Eq.{succ u3} P (coeFn.{max (succ u1) (succ u2) (succ u3), max (succ u1) (succ u3)} (AffineMap.{u1, u1, u1, u2, u3} R R R V P (DivisionRing.toRing.{u1} R _inst_1) (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R _inst_1))) (addGroupIsAddTorsor.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R _inst_1))))) _inst_3 _inst_4 _inst_5) (fun (_x : AffineMap.{u1, u1, u1, u2, u3} R R R V P (DivisionRing.toRing.{u1} R _inst_1) (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R _inst_1))) (addGroupIsAddTorsor.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R _inst_1))))) _inst_3 _inst_4 _inst_5) => R -> P) (AffineMap.hasCoeToFun.{u1, u1, u1, u2, u3} R R R V P (DivisionRing.toRing.{u1} R _inst_1) (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R _inst_1))) (addGroupIsAddTorsor.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R _inst_1))))) _inst_3 _inst_4 _inst_5) (AffineMap.lineMap.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R _inst_1) _inst_3 _inst_4 _inst_5 a b) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (DivInvMonoid.toHasDiv.{u1} R (DivisionRing.toDivInvMonoid.{u1} R _inst_1))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R _inst_1)))))))) (OfNat.ofNat.{u1} R 2 (OfNat.mk.{u1} R 2 (bit0.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (DivisionRing.toRing.{u1} R _inst_1))) (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R _inst_1))))))))))) (midpoint.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R _inst_1) (invertibleTwo.{u1} R _inst_1 _inst_2) _inst_3 _inst_4 _inst_5 a b)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : DivisionRing.{u3} R] [_inst_2 : CharZero.{u3} R (AddGroupWithOne.toAddMonoidWithOne.{u3} R (Ring.toAddGroupWithOne.{u3} R (DivisionRing.toRing.{u3} R _inst_1)))] [_inst_3 : AddCommGroup.{u2} V] [_inst_4 : Module.{u3, u2} R V (DivisionSemiring.toSemiring.{u3} R (DivisionRing.toDivisionSemiring.{u3} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_3)] [_inst_5 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_3)] (a : P) (b : P), Eq.{succ u1} ((fun (a._@.Mathlib.LinearAlgebra.AffineSpace.AffineMap._hyg.1004 : R) => P) (HDiv.hDiv.{u3, u3, u3} R R R (instHDiv.{u3} R (DivisionRing.toDiv.{u3} R _inst_1)) (OfNat.ofNat.{u3} R 1 (One.toOfNat1.{u3} R (NonAssocRing.toOne.{u3} R (Ring.toNonAssocRing.{u3} R (DivisionRing.toRing.{u3} R _inst_1))))) (OfNat.ofNat.{u3} R 2 (instOfNat.{u3} R 2 (NonAssocRing.toNatCast.{u3} R (Ring.toNonAssocRing.{u3} R (DivisionRing.toRing.{u3} R _inst_1))) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (FunLike.coe.{max (max (succ u3) (succ u2)) (succ u1), succ u3, succ u1} (AffineMap.{u3, u3, u3, u2, u1} R R R V P (DivisionRing.toRing.{u3} R _inst_1) (Ring.toAddCommGroup.{u3} R (DivisionRing.toRing.{u3} R _inst_1)) (AffineMap.instModuleToSemiringToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonUnitalRing.{u3} R (DivisionRing.toRing.{u3} R _inst_1)) (addGroupIsAddTorsor.{u3} R (AddGroupWithOne.toAddGroup.{u3} R (Ring.toAddGroupWithOne.{u3} R (DivisionRing.toRing.{u3} R _inst_1)))) _inst_3 _inst_4 _inst_5) R (fun (_x : R) => (fun (a._@.Mathlib.LinearAlgebra.AffineSpace.AffineMap._hyg.1004 : R) => P) _x) (AffineMap.funLike.{u3, u3, u3, u2, u1} R R R V P (DivisionRing.toRing.{u3} R _inst_1) (Ring.toAddCommGroup.{u3} R (DivisionRing.toRing.{u3} R _inst_1)) (AffineMap.instModuleToSemiringToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonUnitalRing.{u3} R (DivisionRing.toRing.{u3} R _inst_1)) (addGroupIsAddTorsor.{u3} R (AddGroupWithOne.toAddGroup.{u3} R (Ring.toAddGroupWithOne.{u3} R (DivisionRing.toRing.{u3} R _inst_1)))) _inst_3 _inst_4 _inst_5) (AffineMap.lineMap.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R _inst_1) _inst_3 _inst_4 _inst_5 a b) (HDiv.hDiv.{u3, u3, u3} R R R (instHDiv.{u3} R (DivisionRing.toDiv.{u3} R _inst_1)) (OfNat.ofNat.{u3} R 1 (One.toOfNat1.{u3} R (NonAssocRing.toOne.{u3} R (Ring.toNonAssocRing.{u3} R (DivisionRing.toRing.{u3} R _inst_1))))) (OfNat.ofNat.{u3} R 2 (instOfNat.{u3} R 2 (NonAssocRing.toNatCast.{u3} R (Ring.toNonAssocRing.{u3} R (DivisionRing.toRing.{u3} R _inst_1))) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (midpoint.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R _inst_1) (invertibleTwo.{u3} R _inst_1 _inst_2) _inst_3 _inst_4 _inst_5 a b)
Case conversion may be inaccurate. Consider using '#align line_map_one_half lineMap_one_halfₓ'. -/
theorem lineMap_one_half {R : Type _} {V P : Type _} [DivisionRing R] [CharZero R] [AddCommGroup V]
    [Module R V] [AddTorsor V P] (a b : P) : lineMap a b (1 / 2 : R) = midpoint R a b := by
  rw [one_div, lineMap_inv_two]
#align line_map_one_half lineMap_one_half

/- warning: homothety_inv_of_two -> homothety_invOf_two is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Invertible.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1))) (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (OfNat.ofNat.{u1} R 2 (OfNat.mk.{u1} R 2 (bit0.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1))) (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1)))))))))] [_inst_3 : AddCommGroup.{u2} V] [_inst_4 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_3)] [_inst_5 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_3)] (a : P) (b : P), Eq.{succ u3} P (coeFn.{max (succ u2) (succ u3), succ u3} (AffineMap.{u1, u2, u3, u2, u3} R V P V P (CommRing.toRing.{u1} R _inst_1) _inst_3 _inst_4 _inst_5 _inst_3 _inst_4 _inst_5) (fun (_x : AffineMap.{u1, u2, u3, u2, u3} R V P V P (CommRing.toRing.{u1} R _inst_1) _inst_3 _inst_4 _inst_5 _inst_3 _inst_4 _inst_5) => P -> P) (AffineMap.hasCoeToFun.{u1, u2, u3, u2, u3} R V P V P (CommRing.toRing.{u1} R _inst_1) _inst_3 _inst_4 _inst_5 _inst_3 _inst_4 _inst_5) (AffineMap.homothety.{u1, u2, u3} R V P _inst_1 _inst_3 _inst_5 _inst_4 a (Invertible.invOf.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1))) (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (OfNat.ofNat.{u1} R 2 (OfNat.mk.{u1} R 2 (bit0.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1))) (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1))))))))) _inst_2)) b) (midpoint.{u1, u2, u3} R V P (CommRing.toRing.{u1} R _inst_1) _inst_2 _inst_3 _inst_4 _inst_5 a b)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : CommRing.{u3} R] [_inst_2 : Invertible.{u3} R (NonUnitalNonAssocRing.toMul.{u3} R (NonAssocRing.toNonUnitalNonAssocRing.{u3} R (Ring.toNonAssocRing.{u3} R (CommRing.toRing.{u3} R _inst_1)))) (NonAssocRing.toOne.{u3} R (Ring.toNonAssocRing.{u3} R (CommRing.toRing.{u3} R _inst_1))) (OfNat.ofNat.{u3} R 2 (instOfNat.{u3} R 2 (NonAssocRing.toNatCast.{u3} R (Ring.toNonAssocRing.{u3} R (CommRing.toRing.{u3} R _inst_1))) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))] [_inst_3 : AddCommGroup.{u2} V] [_inst_4 : Module.{u3, u2} R V (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_3)] [_inst_5 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_3)] (a : P) (b : P), Eq.{succ u1} ((fun (a._@.Mathlib.LinearAlgebra.AffineSpace.AffineMap._hyg.1004 : P) => P) b) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u1} (AffineMap.{u3, u2, u1, u2, u1} R V P V P (CommRing.toRing.{u3} R _inst_1) _inst_3 _inst_4 _inst_5 _inst_3 _inst_4 _inst_5) P (fun (_x : P) => (fun (a._@.Mathlib.LinearAlgebra.AffineSpace.AffineMap._hyg.1004 : P) => P) _x) (AffineMap.funLike.{u3, u2, u1, u2, u1} R V P V P (CommRing.toRing.{u3} R _inst_1) _inst_3 _inst_4 _inst_5 _inst_3 _inst_4 _inst_5) (AffineMap.homothety.{u3, u2, u1} R V P _inst_1 _inst_3 _inst_5 _inst_4 a (Invertible.invOf.{u3} R (NonUnitalNonAssocRing.toMul.{u3} R (NonAssocRing.toNonUnitalNonAssocRing.{u3} R (Ring.toNonAssocRing.{u3} R (CommRing.toRing.{u3} R _inst_1)))) (NonAssocRing.toOne.{u3} R (Ring.toNonAssocRing.{u3} R (CommRing.toRing.{u3} R _inst_1))) (OfNat.ofNat.{u3} R 2 (instOfNat.{u3} R 2 (NonAssocRing.toNatCast.{u3} R (Ring.toNonAssocRing.{u3} R (CommRing.toRing.{u3} R _inst_1))) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) _inst_2)) b) (midpoint.{u3, u2, u1} R V P (CommRing.toRing.{u3} R _inst_1) _inst_2 _inst_3 _inst_4 _inst_5 a b)
Case conversion may be inaccurate. Consider using '#align homothety_inv_of_two homothety_invOf_twoₓ'. -/
theorem homothety_invOf_two {R : Type _} {V P : Type _} [CommRing R] [Invertible (2 : R)]
    [AddCommGroup V] [Module R V] [AddTorsor V P] (a b : P) :
    homothety a (⅟ 2 : R) b = midpoint R a b :=
  rfl
#align homothety_inv_of_two homothety_invOf_two

/- warning: homothety_inv_two -> homothety_inv_two is a dubious translation:
lean 3 declaration is
  forall {k : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : Field.{u1} k] [_inst_2 : CharZero.{u1} k (AddGroupWithOne.toAddMonoidWithOne.{u1} k (AddCommGroupWithOne.toAddGroupWithOne.{u1} k (Ring.toAddCommGroupWithOne.{u1} k (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_1)))))] [_inst_3 : AddCommGroup.{u2} V] [_inst_4 : Module.{u1, u2} k V (Ring.toSemiring.{u1} k (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_3)] [_inst_5 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_3)] (a : P) (b : P), Eq.{succ u3} P (coeFn.{max (succ u2) (succ u3), succ u3} (AffineMap.{u1, u2, u3, u2, u3} k V P V P (CommRing.toRing.{u1} k (Field.toCommRing.{u1} k _inst_1)) _inst_3 _inst_4 _inst_5 _inst_3 _inst_4 _inst_5) (fun (_x : AffineMap.{u1, u2, u3, u2, u3} k V P V P (CommRing.toRing.{u1} k (Field.toCommRing.{u1} k _inst_1)) _inst_3 _inst_4 _inst_5 _inst_3 _inst_4 _inst_5) => P -> P) (AffineMap.hasCoeToFun.{u1, u2, u3, u2, u3} k V P V P (CommRing.toRing.{u1} k (Field.toCommRing.{u1} k _inst_1)) _inst_3 _inst_4 _inst_5 _inst_3 _inst_4 _inst_5) (AffineMap.homothety.{u1, u2, u3} k V P (Field.toCommRing.{u1} k _inst_1) _inst_3 _inst_5 _inst_4 a (Inv.inv.{u1} k (DivInvMonoid.toHasInv.{u1} k (DivisionRing.toDivInvMonoid.{u1} k (Field.toDivisionRing.{u1} k _inst_1))) (OfNat.ofNat.{u1} k 2 (OfNat.mk.{u1} k 2 (bit0.{u1} k (Distrib.toHasAdd.{u1} k (Ring.toDistrib.{u1} k (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_1)))) (One.one.{u1} k (AddMonoidWithOne.toOne.{u1} k (AddGroupWithOne.toAddMonoidWithOne.{u1} k (AddCommGroupWithOne.toAddGroupWithOne.{u1} k (Ring.toAddCommGroupWithOne.{u1} k (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_1)))))))))))) b) (midpoint.{u1, u2, u3} k V P (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_1)) (invertibleTwo.{u1} k (Field.toDivisionRing.{u1} k _inst_1) _inst_2) _inst_3 _inst_4 _inst_5 a b)
but is expected to have type
  forall {k : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : Field.{u3} k] [_inst_2 : CharZero.{u3} k (AddGroupWithOne.toAddMonoidWithOne.{u3} k (Ring.toAddGroupWithOne.{u3} k (DivisionRing.toRing.{u3} k (Field.toDivisionRing.{u3} k _inst_1))))] [_inst_3 : AddCommGroup.{u2} V] [_inst_4 : Module.{u3, u2} k V (DivisionSemiring.toSemiring.{u3} k (Semifield.toDivisionSemiring.{u3} k (Field.toSemifield.{u3} k _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_3)] [_inst_5 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_3)] (a : P) (b : P), Eq.{succ u1} ((fun (a._@.Mathlib.LinearAlgebra.AffineSpace.AffineMap._hyg.1004 : P) => P) b) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u1} (AffineMap.{u3, u2, u1, u2, u1} k V P V P (CommRing.toRing.{u3} k (Field.toCommRing.{u3} k _inst_1)) _inst_3 _inst_4 _inst_5 _inst_3 _inst_4 _inst_5) P (fun (_x : P) => (fun (a._@.Mathlib.LinearAlgebra.AffineSpace.AffineMap._hyg.1004 : P) => P) _x) (AffineMap.funLike.{u3, u2, u1, u2, u1} k V P V P (CommRing.toRing.{u3} k (Field.toCommRing.{u3} k _inst_1)) _inst_3 _inst_4 _inst_5 _inst_3 _inst_4 _inst_5) (AffineMap.homothety.{u3, u2, u1} k V P (Field.toCommRing.{u3} k _inst_1) _inst_3 _inst_5 _inst_4 a (Inv.inv.{u3} k (Field.toInv.{u3} k _inst_1) (OfNat.ofNat.{u3} k 2 (instOfNat.{u3} k 2 (NonAssocRing.toNatCast.{u3} k (Ring.toNonAssocRing.{u3} k (DivisionRing.toRing.{u3} k (Field.toDivisionRing.{u3} k _inst_1)))) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) b) (midpoint.{u3, u2, u1} k V P (DivisionRing.toRing.{u3} k (Field.toDivisionRing.{u3} k _inst_1)) (invertibleTwo.{u3} k (Field.toDivisionRing.{u3} k _inst_1) _inst_2) _inst_3 _inst_4 _inst_5 a b)
Case conversion may be inaccurate. Consider using '#align homothety_inv_two homothety_inv_twoₓ'. -/
theorem homothety_inv_two {k : Type _} {V P : Type _} [Field k] [CharZero k] [AddCommGroup V]
    [Module k V] [AddTorsor V P] (a b : P) : homothety a (2⁻¹ : k) b = midpoint k a b :=
  rfl
#align homothety_inv_two homothety_inv_two

/- warning: homothety_one_half -> homothety_one_half is a dubious translation:
lean 3 declaration is
  forall {k : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : Field.{u1} k] [_inst_2 : CharZero.{u1} k (AddGroupWithOne.toAddMonoidWithOne.{u1} k (AddCommGroupWithOne.toAddGroupWithOne.{u1} k (Ring.toAddCommGroupWithOne.{u1} k (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_1)))))] [_inst_3 : AddCommGroup.{u2} V] [_inst_4 : Module.{u1, u2} k V (Ring.toSemiring.{u1} k (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_3)] [_inst_5 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_3)] (a : P) (b : P), Eq.{succ u3} P (coeFn.{max (succ u2) (succ u3), succ u3} (AffineMap.{u1, u2, u3, u2, u3} k V P V P (CommRing.toRing.{u1} k (Field.toCommRing.{u1} k _inst_1)) _inst_3 _inst_4 _inst_5 _inst_3 _inst_4 _inst_5) (fun (_x : AffineMap.{u1, u2, u3, u2, u3} k V P V P (CommRing.toRing.{u1} k (Field.toCommRing.{u1} k _inst_1)) _inst_3 _inst_4 _inst_5 _inst_3 _inst_4 _inst_5) => P -> P) (AffineMap.hasCoeToFun.{u1, u2, u3, u2, u3} k V P V P (CommRing.toRing.{u1} k (Field.toCommRing.{u1} k _inst_1)) _inst_3 _inst_4 _inst_5 _inst_3 _inst_4 _inst_5) (AffineMap.homothety.{u1, u2, u3} k V P (Field.toCommRing.{u1} k _inst_1) _inst_3 _inst_5 _inst_4 a (HDiv.hDiv.{u1, u1, u1} k k k (instHDiv.{u1} k (DivInvMonoid.toHasDiv.{u1} k (DivisionRing.toDivInvMonoid.{u1} k (Field.toDivisionRing.{u1} k _inst_1)))) (OfNat.ofNat.{u1} k 1 (OfNat.mk.{u1} k 1 (One.one.{u1} k (AddMonoidWithOne.toOne.{u1} k (AddGroupWithOne.toAddMonoidWithOne.{u1} k (AddCommGroupWithOne.toAddGroupWithOne.{u1} k (Ring.toAddCommGroupWithOne.{u1} k (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_1))))))))) (OfNat.ofNat.{u1} k 2 (OfNat.mk.{u1} k 2 (bit0.{u1} k (Distrib.toHasAdd.{u1} k (Ring.toDistrib.{u1} k (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_1)))) (One.one.{u1} k (AddMonoidWithOne.toOne.{u1} k (AddGroupWithOne.toAddMonoidWithOne.{u1} k (AddCommGroupWithOne.toAddGroupWithOne.{u1} k (Ring.toAddCommGroupWithOne.{u1} k (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_1)))))))))))) b) (midpoint.{u1, u2, u3} k V P (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_1)) (invertibleTwo.{u1} k (Field.toDivisionRing.{u1} k _inst_1) _inst_2) _inst_3 _inst_4 _inst_5 a b)
but is expected to have type
  forall {k : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : Field.{u3} k] [_inst_2 : CharZero.{u3} k (AddGroupWithOne.toAddMonoidWithOne.{u3} k (Ring.toAddGroupWithOne.{u3} k (DivisionRing.toRing.{u3} k (Field.toDivisionRing.{u3} k _inst_1))))] [_inst_3 : AddCommGroup.{u2} V] [_inst_4 : Module.{u3, u2} k V (DivisionSemiring.toSemiring.{u3} k (Semifield.toDivisionSemiring.{u3} k (Field.toSemifield.{u3} k _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_3)] [_inst_5 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_3)] (a : P) (b : P), Eq.{succ u1} ((fun (a._@.Mathlib.LinearAlgebra.AffineSpace.AffineMap._hyg.1004 : P) => P) b) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u1} (AffineMap.{u3, u2, u1, u2, u1} k V P V P (CommRing.toRing.{u3} k (Field.toCommRing.{u3} k _inst_1)) _inst_3 _inst_4 _inst_5 _inst_3 _inst_4 _inst_5) P (fun (_x : P) => (fun (a._@.Mathlib.LinearAlgebra.AffineSpace.AffineMap._hyg.1004 : P) => P) _x) (AffineMap.funLike.{u3, u2, u1, u2, u1} k V P V P (CommRing.toRing.{u3} k (Field.toCommRing.{u3} k _inst_1)) _inst_3 _inst_4 _inst_5 _inst_3 _inst_4 _inst_5) (AffineMap.homothety.{u3, u2, u1} k V P (Field.toCommRing.{u3} k _inst_1) _inst_3 _inst_5 _inst_4 a (HDiv.hDiv.{u3, u3, u3} k k k (instHDiv.{u3} k (Field.toDiv.{u3} k _inst_1)) (OfNat.ofNat.{u3} k 1 (One.toOfNat1.{u3} k (NonAssocRing.toOne.{u3} k (Ring.toNonAssocRing.{u3} k (DivisionRing.toRing.{u3} k (Field.toDivisionRing.{u3} k _inst_1)))))) (OfNat.ofNat.{u3} k 2 (instOfNat.{u3} k 2 (NonAssocRing.toNatCast.{u3} k (Ring.toNonAssocRing.{u3} k (DivisionRing.toRing.{u3} k (Field.toDivisionRing.{u3} k _inst_1)))) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) b) (midpoint.{u3, u2, u1} k V P (DivisionRing.toRing.{u3} k (Field.toDivisionRing.{u3} k _inst_1)) (invertibleTwo.{u3} k (Field.toDivisionRing.{u3} k _inst_1) _inst_2) _inst_3 _inst_4 _inst_5 a b)
Case conversion may be inaccurate. Consider using '#align homothety_one_half homothety_one_halfₓ'. -/
theorem homothety_one_half {k : Type _} {V P : Type _} [Field k] [CharZero k] [AddCommGroup V]
    [Module k V] [AddTorsor V P] (a b : P) : homothety a (1 / 2 : k) b = midpoint k a b := by
  rw [one_div, homothety_inv_two]
#align homothety_one_half homothety_one_half

/- warning: pi_midpoint_apply -> pi_midpoint_apply is a dubious translation:
lean 3 declaration is
  forall {k : Type.{u1}} {ι : Type.{u2}} {V : ι -> Type.{u3}} {P : ι -> Type.{u4}} [_inst_1 : Field.{u1} k] [_inst_2 : Invertible.{u1} k (Distrib.toHasMul.{u1} k (Ring.toDistrib.{u1} k (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_1)))) (AddMonoidWithOne.toOne.{u1} k (AddGroupWithOne.toAddMonoidWithOne.{u1} k (AddCommGroupWithOne.toAddGroupWithOne.{u1} k (Ring.toAddCommGroupWithOne.{u1} k (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_1)))))) (OfNat.ofNat.{u1} k 2 (OfNat.mk.{u1} k 2 (bit0.{u1} k (Distrib.toHasAdd.{u1} k (Ring.toDistrib.{u1} k (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_1)))) (One.one.{u1} k (AddMonoidWithOne.toOne.{u1} k (AddGroupWithOne.toAddMonoidWithOne.{u1} k (AddCommGroupWithOne.toAddGroupWithOne.{u1} k (Ring.toAddCommGroupWithOne.{u1} k (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_1))))))))))] [_inst_3 : forall (i : ι), AddCommGroup.{u3} (V i)] [_inst_4 : forall (i : ι), Module.{u1, u3} k (V i) (Ring.toSemiring.{u1} k (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_1))) (AddCommGroup.toAddCommMonoid.{u3} (V i) (_inst_3 i))] [_inst_5 : forall (i : ι), AddTorsor.{u3, u4} (V i) (P i) (AddCommGroup.toAddGroup.{u3} (V i) (_inst_3 i))] (f : forall (i : ι), P i) (g : forall (i : ι), P i) (i : ι), Eq.{succ u4} (P i) (midpoint.{u1, max u2 u3, max u2 u4} k (forall (i : ι), V i) (forall (i : ι), P i) (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_1)) _inst_2 (Pi.addCommGroup.{u2, u3} ι (fun (i : ι) => V i) (fun (i : ι) => _inst_3 i)) (Pi.module.{u2, u3, u1} ι (fun (i : ι) => V i) k (Ring.toSemiring.{u1} k (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_1))) (fun (i : ι) => AddCommGroup.toAddCommMonoid.{u3} (V i) (_inst_3 i)) (fun (i : ι) => _inst_4 i)) (Pi.addTorsor.{u2, u3, u4} ι (fun (i : ι) => V i) (fun (i : ι) => AddCommGroup.toAddGroup.{u3} (V i) (_inst_3 i)) (fun (i : ι) => P i) (fun (i : ι) => _inst_5 i)) f g i) (midpoint.{u1, u3, u4} k (V i) (P i) (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_1)) _inst_2 (_inst_3 i) (_inst_4 i) (_inst_5 i) (f i) (g i))
but is expected to have type
  forall {k : Type.{u4}} {ι : Type.{u3}} {V : ι -> Type.{u2}} {P : ι -> Type.{u1}} [_inst_1 : Field.{u4} k] [_inst_2 : Invertible.{u4} k (NonUnitalNonAssocRing.toMul.{u4} k (NonAssocRing.toNonUnitalNonAssocRing.{u4} k (Ring.toNonAssocRing.{u4} k (DivisionRing.toRing.{u4} k (Field.toDivisionRing.{u4} k _inst_1))))) (NonAssocRing.toOne.{u4} k (Ring.toNonAssocRing.{u4} k (DivisionRing.toRing.{u4} k (Field.toDivisionRing.{u4} k _inst_1)))) (OfNat.ofNat.{u4} k 2 (instOfNat.{u4} k 2 (NonAssocRing.toNatCast.{u4} k (Ring.toNonAssocRing.{u4} k (DivisionRing.toRing.{u4} k (Field.toDivisionRing.{u4} k _inst_1)))) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))] [_inst_3 : forall (i : ι), AddCommGroup.{u2} (V i)] [_inst_4 : forall (i : ι), Module.{u4, u2} k (V i) (DivisionSemiring.toSemiring.{u4} k (Semifield.toDivisionSemiring.{u4} k (Field.toSemifield.{u4} k _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} (V i) (_inst_3 i))] [_inst_5 : forall (i : ι), AddTorsor.{u2, u1} (V i) (P i) (AddCommGroup.toAddGroup.{u2} (V i) (_inst_3 i))] (f : forall (i : ι), P i) (g : forall (i : ι), P i) (i : ι), Eq.{succ u1} (P i) (midpoint.{u4, max u3 u2, max u3 u1} k (forall (i : ι), V i) (forall (i : ι), P i) (DivisionRing.toRing.{u4} k (Field.toDivisionRing.{u4} k _inst_1)) _inst_2 (Pi.addCommGroup.{u3, u2} ι (fun (i : ι) => V i) (fun (i : ι) => _inst_3 i)) (Pi.module.{u3, u2, u4} ι (fun (i : ι) => V i) k (Ring.toSemiring.{u4} k (DivisionRing.toRing.{u4} k (Field.toDivisionRing.{u4} k _inst_1))) (fun (i : ι) => AddCommGroup.toAddCommMonoid.{u2} (V i) (_inst_3 i)) (fun (i : ι) => _inst_4 i)) (AffineMap.instAddTorsorForAllForAllAddGroupToAddGroup.{u3, u2, u1} ι (fun (i : ι) => V i) (fun (i : ι) => P i) (fun (i : ι) => _inst_3 i) (fun (i : ι) => _inst_5 i)) f g i) (midpoint.{u4, u2, u1} k (V i) (P i) (DivisionRing.toRing.{u4} k (Field.toDivisionRing.{u4} k _inst_1)) _inst_2 (_inst_3 i) (_inst_4 i) (_inst_5 i) (f i) (g i))
Case conversion may be inaccurate. Consider using '#align pi_midpoint_apply pi_midpoint_applyₓ'. -/
@[simp]
theorem pi_midpoint_apply {k ι : Type _} {V : ∀ i : ι, Type _} {P : ∀ i : ι, Type _} [Field k]
    [Invertible (2 : k)] [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, AddTorsor (V i) (P i)] (f g : ∀ i, P i) (i : ι) :
    midpoint k f g i = midpoint k (f i) (g i) :=
  rfl
#align pi_midpoint_apply pi_midpoint_apply

