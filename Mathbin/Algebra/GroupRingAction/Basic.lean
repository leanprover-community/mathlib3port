/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

! This file was ported from Lean 3 source module algebra.group_ring_action.basic
! leanprover-community/mathlib commit 8631e2d5ea77f6c13054d9151d82b83069680cb1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Ring.Equiv
import Mathbin.Algebra.Field.Defs
import Mathbin.GroupTheory.GroupAction.Group

/-!
# Group action on rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the typeclass of monoid acting on semirings `mul_semiring_action M R`,
and the corresponding typeclass of invariant subrings.

Note that `algebra` does not satisfy the axioms of `mul_semiring_action`.

## Implementation notes

There is no separate typeclass for group acting on rings, group acting on fields, etc.
They are all grouped under `mul_semiring_action`.

## Tags

group action, invariant subring

-/


universe u v

#print MulSemiringAction /-
/-- Typeclass for multiplicative actions by monoids on semirings.

This combines `distrib_mul_action` with `mul_distrib_mul_action`. -/
class MulSemiringAction (M : Type u) (R : Type v) [Monoid M] [Semiring R] extends
  DistribMulAction M R where
  smul_one : ∀ g : M, (g • 1 : R) = 1
  smul_mul : ∀ (g : M) (x y : R), g • (x * y) = g • x * g • y
#align mul_semiring_action MulSemiringAction
-/

section Semiring

variable (M N G : Type _) [Monoid M] [Monoid N] [Group G]

variable (A R S F : Type v) [AddMonoid A] [Semiring R] [CommSemiring S] [DivisionRing F]

#print MulSemiringAction.toMulDistribMulAction /-
-- note we could not use `extends` since these typeclasses are made with `old_structure_cmd`
instance (priority := 100) MulSemiringAction.toMulDistribMulAction [h : MulSemiringAction M R] :
    MulDistribMulAction M R :=
  { h with }
#align mul_semiring_action.to_mul_distrib_mul_action MulSemiringAction.toMulDistribMulAction
-/

#print MulSemiringAction.toRingHom /-
/-- Each element of the monoid defines a semiring homomorphism. -/
@[simps]
def MulSemiringAction.toRingHom [MulSemiringAction M R] (x : M) : R →+* R :=
  { MulDistribMulAction.toMonoidHom R x, DistribMulAction.toAddMonoidHom R x with }
#align mul_semiring_action.to_ring_hom MulSemiringAction.toRingHom
-/

/- warning: to_ring_hom_injective -> toRingHom_injective is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u2}) [_inst_1 : Monoid.{u2} M] (R : Type.{u1}) [_inst_5 : Semiring.{u1} R] [_inst_8 : MulSemiringAction.{u2, u1} M R _inst_1 _inst_5] [_inst_9 : FaithfulSMul.{u2, u1} M R (SMulZeroClass.toHasSmul.{u2, u1} M R (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_5)))))) (DistribSMul.toSmulZeroClass.{u2, u1} M R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_5))))) (DistribMulAction.toDistribSMul.{u2, u1} M R _inst_1 (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_5)))) (MulSemiringAction.toDistribMulAction.{u2, u1} M R _inst_1 _inst_5 _inst_8))))], Function.Injective.{succ u2, succ u1} M (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R _inst_5) (Semiring.toNonAssocSemiring.{u1} R _inst_5)) (MulSemiringAction.toRingHom.{u1, u2} M _inst_1 R _inst_5 _inst_8)
but is expected to have type
  forall (M : Type.{u1}) [_inst_1 : Monoid.{u1} M] (R : Type.{u2}) [_inst_5 : Semiring.{u2} R] [_inst_8 : MulSemiringAction.{u1, u2} M R _inst_1 _inst_5] [_inst_9 : FaithfulSMul.{u1, u2} M R (SMulZeroClass.toSMul.{u1, u2} M R (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_5)) (DistribSMul.toSMulZeroClass.{u1, u2} M R (AddMonoid.toAddZeroClass.{u2} R (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_5))))) (DistribMulAction.toDistribSMul.{u1, u2} M R _inst_1 (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_5)))) (MulSemiringAction.toDistribMulAction.{u1, u2} M R _inst_1 _inst_5 _inst_8))))], Function.Injective.{succ u1, succ u2} M (RingHom.{u2, u2} R R (Semiring.toNonAssocSemiring.{u2} R _inst_5) (Semiring.toNonAssocSemiring.{u2} R _inst_5)) (MulSemiringAction.toRingHom.{u2, u1} M _inst_1 R _inst_5 _inst_8)
Case conversion may be inaccurate. Consider using '#align to_ring_hom_injective toRingHom_injectiveₓ'. -/
theorem toRingHom_injective [MulSemiringAction M R] [FaithfulSMul M R] :
    Function.Injective (MulSemiringAction.toRingHom M R) := fun m₁ m₂ h =>
  eq_of_smul_eq_smul fun r => RingHom.ext_iff.1 h r
#align to_ring_hom_injective toRingHom_injective

/- warning: mul_semiring_action.to_ring_equiv -> MulSemiringAction.toRingEquiv is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u2}) [_inst_3 : Group.{u2} G] (R : Type.{u1}) [_inst_5 : Semiring.{u1} R] [_inst_8 : MulSemiringAction.{u2, u1} G R (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3)) _inst_5], G -> (RingEquiv.{u1, u1} R R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_5)))) (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_5)))) (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_5)))) (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_5)))))
but is expected to have type
  forall (G : Type.{u2}) [_inst_3 : Group.{u2} G] (R : Type.{u1}) [_inst_5 : Semiring.{u1} R] [_inst_8 : MulSemiringAction.{u2, u1} G R (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3)) _inst_5], G -> (RingEquiv.{u1, u1} R R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_5))) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_5))) (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_5)))) (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_5)))))
Case conversion may be inaccurate. Consider using '#align mul_semiring_action.to_ring_equiv MulSemiringAction.toRingEquivₓ'. -/
/-- Each element of the group defines a semiring isomorphism. -/
@[simps]
def MulSemiringAction.toRingEquiv [MulSemiringAction G R] (x : G) : R ≃+* R :=
  { DistribMulAction.toAddEquiv R x, MulSemiringAction.toRingHom G R x with }
#align mul_semiring_action.to_ring_equiv MulSemiringAction.toRingEquiv

section

variable {M N}

#print MulSemiringAction.compHom /-
/-- Compose a `mul_semiring_action` with a `monoid_hom`, with action `f r' • m`.
See note [reducible non-instances]. -/
@[reducible]
def MulSemiringAction.compHom (f : N →* M) [MulSemiringAction M R] : MulSemiringAction N R :=
  { DistribMulAction.compHom R f, MulDistribMulAction.compHom R f with smul := SMul.comp.smul f }
#align mul_semiring_action.comp_hom MulSemiringAction.compHom
-/

end

section SimpLemmas

variable {M G A R F}

attribute [simp] smul_one smul_mul' smul_zero smul_add

/- warning: smul_inv'' -> smul_inv'' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u2}} [_inst_1 : Monoid.{u2} M] {F : Type.{u1}} [_inst_7 : DivisionRing.{u1} F] [_inst_8 : MulSemiringAction.{u2, u1} M F _inst_1 (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F _inst_7))] (x : M) (m : F), Eq.{succ u1} F (SMul.smul.{u2, u1} M F (SMulZeroClass.toHasSmul.{u2, u1} M F (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddMonoidWithOne.toAddMonoid.{u1} F (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} F (NonAssocSemiring.toAddCommMonoidWithOne.{u1} F (Semiring.toNonAssocSemiring.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F _inst_7)))))))) (DistribSMul.toSmulZeroClass.{u2, u1} M F (AddMonoid.toAddZeroClass.{u1} F (AddMonoidWithOne.toAddMonoid.{u1} F (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} F (NonAssocSemiring.toAddCommMonoidWithOne.{u1} F (Semiring.toNonAssocSemiring.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F _inst_7))))))) (DistribMulAction.toDistribSMul.{u2, u1} M F _inst_1 (AddMonoidWithOne.toAddMonoid.{u1} F (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} F (NonAssocSemiring.toAddCommMonoidWithOne.{u1} F (Semiring.toNonAssocSemiring.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F _inst_7)))))) (MulSemiringAction.toDistribMulAction.{u2, u1} M F _inst_1 (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F _inst_7)) _inst_8)))) x (Inv.inv.{u1} F (DivInvMonoid.toHasInv.{u1} F (DivisionRing.toDivInvMonoid.{u1} F _inst_7)) m)) (Inv.inv.{u1} F (DivInvMonoid.toHasInv.{u1} F (DivisionRing.toDivInvMonoid.{u1} F _inst_7)) (SMul.smul.{u2, u1} M F (SMulZeroClass.toHasSmul.{u2, u1} M F (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddMonoidWithOne.toAddMonoid.{u1} F (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} F (NonAssocSemiring.toAddCommMonoidWithOne.{u1} F (Semiring.toNonAssocSemiring.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F _inst_7)))))))) (DistribSMul.toSmulZeroClass.{u2, u1} M F (AddMonoid.toAddZeroClass.{u1} F (AddMonoidWithOne.toAddMonoid.{u1} F (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} F (NonAssocSemiring.toAddCommMonoidWithOne.{u1} F (Semiring.toNonAssocSemiring.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F _inst_7))))))) (DistribMulAction.toDistribSMul.{u2, u1} M F _inst_1 (AddMonoidWithOne.toAddMonoid.{u1} F (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} F (NonAssocSemiring.toAddCommMonoidWithOne.{u1} F (Semiring.toNonAssocSemiring.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F _inst_7)))))) (MulSemiringAction.toDistribMulAction.{u2, u1} M F _inst_1 (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F _inst_7)) _inst_8)))) x m))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {F : Type.{u2}} [_inst_7 : DivisionRing.{u2} F] [_inst_8 : MulSemiringAction.{u1, u2} M F _inst_1 (DivisionSemiring.toSemiring.{u2} F (DivisionRing.toDivisionSemiring.{u2} F _inst_7))] (x : M) (m : F), Eq.{succ u2} F (HSMul.hSMul.{u1, u2, u2} M F F (instHSMul.{u1, u2} M F (SMulZeroClass.toSMul.{u1, u2} M F (MonoidWithZero.toZero.{u2} F (Semiring.toMonoidWithZero.{u2} F (DivisionSemiring.toSemiring.{u2} F (DivisionRing.toDivisionSemiring.{u2} F _inst_7)))) (DistribSMul.toSMulZeroClass.{u1, u2} M F (AddMonoid.toAddZeroClass.{u2} F (AddMonoidWithOne.toAddMonoid.{u2} F (AddGroupWithOne.toAddMonoidWithOne.{u2} F (Ring.toAddGroupWithOne.{u2} F (DivisionRing.toRing.{u2} F _inst_7))))) (DistribMulAction.toDistribSMul.{u1, u2} M F _inst_1 (AddMonoidWithOne.toAddMonoid.{u2} F (AddGroupWithOne.toAddMonoidWithOne.{u2} F (Ring.toAddGroupWithOne.{u2} F (DivisionRing.toRing.{u2} F _inst_7)))) (MulSemiringAction.toDistribMulAction.{u1, u2} M F _inst_1 (Ring.toSemiring.{u2} F (DivisionRing.toRing.{u2} F _inst_7)) _inst_8))))) x (Inv.inv.{u2} F (DivisionRing.toInv.{u2} F _inst_7) m)) (Inv.inv.{u2} F (DivisionRing.toInv.{u2} F _inst_7) (HSMul.hSMul.{u1, u2, u2} M F F (instHSMul.{u1, u2} M F (SMulZeroClass.toSMul.{u1, u2} M F (MonoidWithZero.toZero.{u2} F (Semiring.toMonoidWithZero.{u2} F (DivisionSemiring.toSemiring.{u2} F (DivisionRing.toDivisionSemiring.{u2} F _inst_7)))) (DistribSMul.toSMulZeroClass.{u1, u2} M F (AddMonoid.toAddZeroClass.{u2} F (AddMonoidWithOne.toAddMonoid.{u2} F (AddGroupWithOne.toAddMonoidWithOne.{u2} F (Ring.toAddGroupWithOne.{u2} F (DivisionRing.toRing.{u2} F _inst_7))))) (DistribMulAction.toDistribSMul.{u1, u2} M F _inst_1 (AddMonoidWithOne.toAddMonoid.{u2} F (AddGroupWithOne.toAddMonoidWithOne.{u2} F (Ring.toAddGroupWithOne.{u2} F (DivisionRing.toRing.{u2} F _inst_7)))) (MulSemiringAction.toDistribMulAction.{u1, u2} M F _inst_1 (Ring.toSemiring.{u2} F (DivisionRing.toRing.{u2} F _inst_7)) _inst_8))))) x m))
Case conversion may be inaccurate. Consider using '#align smul_inv'' smul_inv''ₓ'. -/
/-- Note that `smul_inv'` refers to the group case, and `smul_inv` has an additional inverse
on `x`. -/
@[simp]
theorem smul_inv'' [MulSemiringAction M F] (x : M) (m : F) : x • m⁻¹ = (x • m)⁻¹ :=
  map_inv₀ (MulSemiringAction.toRingHom M F x) _
#align smul_inv'' smul_inv''

end SimpLemmas

end Semiring

