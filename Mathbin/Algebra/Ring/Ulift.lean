/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.ring.ulift
! leanprover-community/mathlib commit dd71334db81d0bd444af1ee339a29298bef40734
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Ulift
import Mathbin.Algebra.Field.Defs
import Mathbin.Algebra.Ring.Equiv

/-!
# `ulift` instances for ring

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines instances for ring, semiring and related structures on `ulift` types.

(Recall `ulift α` is just a "copy" of a type `α` in a higher universe.)

We also provide `ulift.ring_equiv : ulift R ≃+* R`.
-/


universe u v

variable {α : Type u} {x y : ULift.{v} α}

namespace ULift

#print ULift.mulZeroClass /-
instance mulZeroClass [MulZeroClass α] : MulZeroClass (ULift α) := by
  refine_struct
      { zero := (0 : ULift α)
        mul := (· * ·).. } <;>
    pi_instance_derive_field
#align ulift.mul_zero_class ULift.mulZeroClass
-/

#print ULift.distrib /-
instance distrib [Distrib α] : Distrib (ULift α) := by
  refine_struct
      { add := (· + ·)
        mul := (· * ·).. } <;>
    pi_instance_derive_field
#align ulift.distrib ULift.distrib
-/

#print ULift.nonUnitalNonAssocSemiring /-
instance nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring α] :
    NonUnitalNonAssocSemiring (ULift α) := by
  refine_struct
      { zero := (0 : ULift α)
        add := (· + ·)
        mul := (· * ·)
        nsmul := AddMonoid.nsmul } <;>
    pi_instance_derive_field
#align ulift.non_unital_non_assoc_semiring ULift.nonUnitalNonAssocSemiring
-/

#print ULift.nonAssocSemiring /-
instance nonAssocSemiring [NonAssocSemiring α] : NonAssocSemiring (ULift α) := by
  refine_struct
      { ULift.addMonoidWithOne with
        zero := (0 : ULift α)
        one := 1
        add := (· + ·)
        mul := (· * ·)
        nsmul := AddMonoid.nsmul } <;>
    pi_instance_derive_field
#align ulift.non_assoc_semiring ULift.nonAssocSemiring
-/

#print ULift.nonUnitalSemiring /-
instance nonUnitalSemiring [NonUnitalSemiring α] : NonUnitalSemiring (ULift α) := by
  refine_struct
      { zero := (0 : ULift α)
        add := (· + ·)
        mul := (· * ·)
        nsmul := AddMonoid.nsmul } <;>
    pi_instance_derive_field
#align ulift.non_unital_semiring ULift.nonUnitalSemiring
-/

#print ULift.semiring /-
instance semiring [Semiring α] : Semiring (ULift α) := by
  refine_struct
      { ULift.addMonoidWithOne with
        zero := (0 : ULift α)
        one := 1
        add := (· + ·)
        mul := (· * ·)
        nsmul := AddMonoid.nsmul
        npow := Monoid.npow } <;>
    pi_instance_derive_field
#align ulift.semiring ULift.semiring
-/

/- warning: ulift.ring_equiv -> ULift.ringEquiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α], RingEquiv.{max u1 u2, u1} (ULift.{u2, u1} α) α (ULift.mul.{u1, u2} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1))) (ULift.add.{u1, u2} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1))) (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)) (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α], RingEquiv.{max u1 u2, u1} (ULift.{u2, u1} α) α (ULift.mul.{u1, u2} α (NonUnitalNonAssocSemiring.toMul.{u1} α _inst_1)) (NonUnitalNonAssocSemiring.toMul.{u1} α _inst_1) (ULift.add.{u1, u2} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1))) (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align ulift.ring_equiv ULift.ringEquivₓ'. -/
/-- The ring equivalence between `ulift α` and `α`.
-/
def ringEquiv [NonUnitalNonAssocSemiring α] : ULift α ≃+* α
    where
  toFun := ULift.down
  invFun := ULift.up
  map_mul' x y := rfl
  map_add' x y := rfl
  left_inv := by tidy
  right_inv := by tidy
#align ulift.ring_equiv ULift.ringEquiv

#print ULift.nonUnitalCommSemiring /-
instance nonUnitalCommSemiring [NonUnitalCommSemiring α] : NonUnitalCommSemiring (ULift α) := by
  refine_struct
      { zero := (0 : ULift α)
        add := (· + ·)
        mul := (· * ·)
        nsmul := AddMonoid.nsmul } <;>
    pi_instance_derive_field
#align ulift.non_unital_comm_semiring ULift.nonUnitalCommSemiring
-/

#print ULift.commSemiring /-
instance commSemiring [CommSemiring α] : CommSemiring (ULift α) := by
  refine_struct
      { ULift.semiring with
        zero := (0 : ULift α)
        one := 1
        add := (· + ·)
        mul := (· * ·)
        nsmul := AddMonoid.nsmul
        npow := Monoid.npow } <;>
    pi_instance_derive_field
#align ulift.comm_semiring ULift.commSemiring
-/

#print ULift.nonUnitalNonAssocRing /-
instance nonUnitalNonAssocRing [NonUnitalNonAssocRing α] : NonUnitalNonAssocRing (ULift α) := by
  refine_struct
      { zero := (0 : ULift α)
        add := (· + ·)
        mul := (· * ·)
        sub := Sub.sub
        neg := Neg.neg
        nsmul := AddMonoid.nsmul
        zsmul := SubNegMonoid.zsmul } <;>
    pi_instance_derive_field
#align ulift.non_unital_non_assoc_ring ULift.nonUnitalNonAssocRing
-/

#print ULift.nonUnitalRing /-
instance nonUnitalRing [NonUnitalRing α] : NonUnitalRing (ULift α) := by
  refine_struct
      { zero := (0 : ULift α)
        add := (· + ·)
        mul := (· * ·)
        sub := Sub.sub
        neg := Neg.neg
        nsmul := AddMonoid.nsmul
        zsmul := SubNegMonoid.zsmul } <;>
    pi_instance_derive_field
#align ulift.non_unital_ring ULift.nonUnitalRing
-/

#print ULift.nonAssocRing /-
instance nonAssocRing [NonAssocRing α] : NonAssocRing (ULift α) := by
  refine_struct
      { ULift.addGroupWithOne with
        zero := (0 : ULift α)
        one := 1
        add := (· + ·)
        mul := (· * ·)
        sub := Sub.sub
        neg := Neg.neg
        nsmul := AddMonoid.nsmul
        zsmul := SubNegMonoid.zsmul } <;>
    pi_instance_derive_field
#align ulift.non_assoc_ring ULift.nonAssocRing
-/

#print ULift.ring /-
instance ring [Ring α] : Ring (ULift α) := by
  refine_struct
      { ULift.semiring,
        ULift.addGroupWithOne with
        zero := (0 : ULift α)
        one := 1
        add := (· + ·)
        mul := (· * ·)
        sub := Sub.sub
        neg := Neg.neg
        nsmul := AddMonoid.nsmul
        npow := Monoid.npow
        zsmul := SubNegMonoid.zsmul } <;>
    pi_instance_derive_field
#align ulift.ring ULift.ring
-/

#print ULift.nonUnitalCommRing /-
instance nonUnitalCommRing [NonUnitalCommRing α] : NonUnitalCommRing (ULift α) := by
  refine_struct
      { zero := (0 : ULift α)
        add := (· + ·)
        mul := (· * ·)
        sub := Sub.sub
        neg := Neg.neg
        nsmul := AddMonoid.nsmul
        zsmul := SubNegMonoid.zsmul } <;>
    pi_instance_derive_field
#align ulift.non_unital_comm_ring ULift.nonUnitalCommRing
-/

#print ULift.commRing /-
instance commRing [CommRing α] : CommRing (ULift α) := by
  refine_struct { ULift.ring with } <;> pi_instance_derive_field
#align ulift.comm_ring ULift.commRing
-/

instance [RatCast α] : RatCast (ULift α) :=
  ⟨fun a => ULift.up (coe a)⟩

/- warning: ulift.rat_cast_down -> ULift.rat_cast_down is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : RatCast.{u1} α] (n : Rat), Eq.{succ u1} α (ULift.down.{u2, u1} α ((fun (a : Type) (b : Type.{max u1 u2}) [self : HasLiftT.{1, succ (max u1 u2)} a b] => self.0) Rat (ULift.{u2, u1} α) (HasLiftT.mk.{1, succ (max u1 u2)} Rat (ULift.{u2, u1} α) (CoeTCₓ.coe.{1, succ (max u1 u2)} Rat (ULift.{u2, u1} α) (Rat.castCoe.{max u1 u2} (ULift.{u2, u1} α) (ULift.hasRatCast.{u1, u2} α _inst_1)))) n)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α _inst_1))) n)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : RatCast.{u2} α] (n : Rat), Eq.{succ u2} α (ULift.down.{u1, u2} α (RatCast.ratCast.{max u2 u1} (ULift.{u1, u2} α) (ULift.instRatCastULift.{u2, u1} α _inst_1) n)) (RatCast.ratCast.{u2} α _inst_1 n)
Case conversion may be inaccurate. Consider using '#align ulift.rat_cast_down ULift.rat_cast_downₓ'. -/
@[simp]
theorem rat_cast_down [RatCast α] (n : ℚ) : ULift.down (n : ULift α) = n :=
  rfl
#align ulift.rat_cast_down ULift.rat_cast_down

#print ULift.field /-
instance field [Field α] : Field (ULift α) :=
  by
  have of_rat_mk : ∀ a b h1 h2, ((⟨a, b, h1, h2⟩ : ℚ) : ULift α) = ↑a * (↑b)⁻¹ :=
    by
    intro a b h1 h2
    ext
    rw [rat_cast_down, mul_down, inv_down, nat_cast_down, int_cast_down]
    exact Field.rat_cast_mk a b h1 h2
  refine_struct
      { @ULift.nontrivial α _,
        ULift.commRing with
        zero := (0 : ULift α)
        inv := Inv.inv
        div := Div.div
        zpow := fun n a => ULift.up (a.down ^ n)
        ratCast := coe
        rat_cast_mk := of_rat_mk
        qsmul := (· • ·) } <;>
    pi_instance_derive_field
  -- `mul_inv_cancel` requires special attention: it leaves the goal `∀ {a}, a ≠ 0 → a * a⁻¹ = 1`.
  cases a
  tauto
#align ulift.field ULift.field
-/

end ULift

