/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Algebra.Group.ULift
import Algebra.Ring.Equiv

#align_import algebra.ring.ulift from "leanprover-community/mathlib"@"13e18cfa070ea337ea960176414f5ae3a1534aae"

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
        mul := (· * ·) .. } <;>
    pi_instance_derive_field
#align ulift.mul_zero_class ULift.mulZeroClass
-/

#print ULift.distrib /-
instance distrib [Distrib α] : Distrib (ULift α) := by
  refine_struct
      { add := (· + ·)
        mul := (· * ·) .. } <;>
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

#print ULift.ringEquiv /-
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
-/

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

end ULift

