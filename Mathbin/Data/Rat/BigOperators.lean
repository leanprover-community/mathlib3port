/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module data.rat.big_operators
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Rat.Cast
import Mathbin.Algebra.BigOperators.Basic

/-! # Casting lemmas for rational numbers involving sums and products

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open BigOperators

variable {ι α : Type _}

namespace Rat

section WithDivRing

variable [DivisionRing α] [CharZero α]

/- warning: rat.cast_list_sum -> Rat.cast_list_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))] (s : List.{0} Rat), Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) (List.sum.{0} Rat Rat.hasAdd Rat.hasZero s)) (List.sum.{u1} α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α (DivisionRing.toRing.{u1} α _inst_1))) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))) (List.map.{0, u1} Rat α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1))))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (Ring.toAddGroupWithOne.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))] (s : List.{0} Rat), Eq.{succ u1} α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) (List.sum.{0} Rat Rat.instAddRat (CommMonoidWithZero.toZero.{0} Rat (CommGroupWithZero.toCommMonoidWithZero.{0} Rat Rat.commGroupWithZero)) s)) (List.sum.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))) (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α _inst_1)))) (List.map.{0, u1} Rat α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1)) s))
Case conversion may be inaccurate. Consider using '#align rat.cast_list_sum Rat.cast_list_sumₓ'. -/
@[simp, norm_cast]
theorem cast_list_sum (s : List ℚ) : (↑s.Sum : α) = (s.map coe).Sum :=
  map_list_sum (Rat.castHom α) _
#align rat.cast_list_sum Rat.cast_list_sum

/- warning: rat.cast_multiset_sum -> Rat.cast_multiset_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))] (s : Multiset.{0} Rat), Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) (Multiset.sum.{0} Rat Rat.addCommMonoid s)) (Multiset.sum.{u1} α (AddCommGroup.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))) (Multiset.map.{0, u1} Rat α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1))))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (Ring.toAddGroupWithOne.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))] (s : Multiset.{0} Rat), Eq.{succ u1} α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) (Multiset.sum.{0} Rat Rat.addCommMonoid s)) (Multiset.sum.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))) (Multiset.map.{0, u1} Rat α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1)) s))
Case conversion may be inaccurate. Consider using '#align rat.cast_multiset_sum Rat.cast_multiset_sumₓ'. -/
@[simp, norm_cast]
theorem cast_multiset_sum (s : Multiset ℚ) : (↑s.Sum : α) = (s.map coe).Sum :=
  map_multiset_sum (Rat.castHom α) _
#align rat.cast_multiset_sum Rat.cast_multiset_sum

/- warning: rat.cast_sum -> Rat.cast_sum is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : DivisionRing.{u2} α] [_inst_2 : CharZero.{u2} α (AddGroupWithOne.toAddMonoidWithOne.{u2} α (NonAssocRing.toAddGroupWithOne.{u2} α (Ring.toNonAssocRing.{u2} α (DivisionRing.toRing.{u2} α _inst_1))))] (s : Finset.{u1} ι) (f : ι -> Rat), Eq.{succ u2} α ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u2} Rat α (CoeTCₓ.coe.{1, succ u2} Rat α (Rat.castCoe.{u2} α (DivisionRing.toHasRatCast.{u2} α _inst_1)))) (Finset.sum.{0, u1} Rat ι Rat.addCommMonoid s (fun (i : ι) => f i))) (Finset.sum.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (NonUnitalNonAssocRing.toAddCommGroup.{u2} α (NonAssocRing.toNonUnitalNonAssocRing.{u2} α (Ring.toNonAssocRing.{u2} α (DivisionRing.toRing.{u2} α _inst_1))))) s (fun (i : ι) => (fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u2} Rat α (CoeTCₓ.coe.{1, succ u2} Rat α (Rat.castCoe.{u2} α (DivisionRing.toHasRatCast.{u2} α _inst_1)))) (f i)))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (Ring.toAddGroupWithOne.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))] (s : Finset.{u2} ι) (f : ι -> Rat), Eq.{succ u1} α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) (Finset.sum.{0, u2} Rat ι Rat.addCommMonoid s (fun (i : ι) => f i))) (Finset.sum.{u1, u2} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))) s (fun (i : ι) => RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) (f i)))
Case conversion may be inaccurate. Consider using '#align rat.cast_sum Rat.cast_sumₓ'. -/
@[simp, norm_cast]
theorem cast_sum (s : Finset ι) (f : ι → ℚ) : (↑(∑ i in s, f i) : α) = ∑ i in s, f i :=
  map_sum (Rat.castHom α) _ _
#align rat.cast_sum Rat.cast_sum

/- warning: rat.cast_list_prod -> Rat.cast_list_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))] (s : List.{0} Rat), Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) (List.prod.{0} Rat Rat.hasMul Rat.hasOne s)) (List.prod.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (DivisionRing.toRing.{u1} α _inst_1))) (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))) (List.map.{0, u1} Rat α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1))))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (Ring.toAddGroupWithOne.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))] (s : List.{0} Rat), Eq.{succ u1} α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) (List.prod.{0} Rat Rat.instMulRat (NonAssocRing.toOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))) s)) (List.prod.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))) (NonAssocRing.toOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))) (List.map.{0, u1} Rat α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1)) s))
Case conversion may be inaccurate. Consider using '#align rat.cast_list_prod Rat.cast_list_prodₓ'. -/
@[simp, norm_cast]
theorem cast_list_prod (s : List ℚ) : (↑s.Prod : α) = (s.map coe).Prod :=
  map_list_prod (Rat.castHom α) _
#align rat.cast_list_prod Rat.cast_list_prod

end WithDivRing

section Field

variable [Field α] [CharZero α]

/- warning: rat.cast_multiset_prod -> Rat.cast_multiset_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Field.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α (Field.toDivisionRing.{u1} α _inst_1)))))] (s : Multiset.{0} Rat), Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α (Field.toDivisionRing.{u1} α _inst_1))))) (Multiset.prod.{0} Rat Rat.commMonoid s)) (Multiset.prod.{u1} α (CommRing.toCommMonoid.{u1} α (Field.toCommRing.{u1} α _inst_1)) (Multiset.map.{0, u1} Rat α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α (Field.toDivisionRing.{u1} α _inst_1)))))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Field.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (Ring.toAddGroupWithOne.{u1} α (DivisionRing.toRing.{u1} α (Field.toDivisionRing.{u1} α _inst_1))))] (s : Multiset.{0} Rat), Eq.{succ u1} α (RatCast.ratCast.{u1} α (Field.toRatCast.{u1} α _inst_1) (Multiset.prod.{0} Rat Rat.commMonoid s)) (Multiset.prod.{u1} α (CommRing.toCommMonoid.{u1} α (Field.toCommRing.{u1} α _inst_1)) (Multiset.map.{0, u1} Rat α (RatCast.ratCast.{u1} α (Field.toRatCast.{u1} α _inst_1)) s))
Case conversion may be inaccurate. Consider using '#align rat.cast_multiset_prod Rat.cast_multiset_prodₓ'. -/
@[simp, norm_cast]
theorem cast_multiset_prod (s : Multiset ℚ) : (↑s.Prod : α) = (s.map coe).Prod :=
  map_multiset_prod (Rat.castHom α) _
#align rat.cast_multiset_prod Rat.cast_multiset_prod

/- warning: rat.cast_prod -> Rat.cast_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Field.{u2} α] [_inst_2 : CharZero.{u2} α (AddGroupWithOne.toAddMonoidWithOne.{u2} α (NonAssocRing.toAddGroupWithOne.{u2} α (Ring.toNonAssocRing.{u2} α (DivisionRing.toRing.{u2} α (Field.toDivisionRing.{u2} α _inst_1)))))] (s : Finset.{u1} ι) (f : ι -> Rat), Eq.{succ u2} α ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u2} Rat α (CoeTCₓ.coe.{1, succ u2} Rat α (Rat.castCoe.{u2} α (DivisionRing.toHasRatCast.{u2} α (Field.toDivisionRing.{u2} α _inst_1))))) (Finset.prod.{0, u1} Rat ι Rat.commMonoid s (fun (i : ι) => f i))) (Finset.prod.{u2, u1} α ι (CommRing.toCommMonoid.{u2} α (Field.toCommRing.{u2} α _inst_1)) s (fun (i : ι) => (fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u2} Rat α (CoeTCₓ.coe.{1, succ u2} Rat α (Rat.castCoe.{u2} α (DivisionRing.toHasRatCast.{u2} α (Field.toDivisionRing.{u2} α _inst_1))))) (f i)))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : Field.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (Ring.toAddGroupWithOne.{u1} α (DivisionRing.toRing.{u1} α (Field.toDivisionRing.{u1} α _inst_1))))] (s : Finset.{u2} ι) (f : ι -> Rat), Eq.{succ u1} α (RatCast.ratCast.{u1} α (Field.toRatCast.{u1} α _inst_1) (Finset.prod.{0, u2} Rat ι Rat.commMonoid s (fun (i : ι) => f i))) (Finset.prod.{u1, u2} α ι (CommRing.toCommMonoid.{u1} α (Field.toCommRing.{u1} α _inst_1)) s (fun (i : ι) => RatCast.ratCast.{u1} α (Field.toRatCast.{u1} α _inst_1) (f i)))
Case conversion may be inaccurate. Consider using '#align rat.cast_prod Rat.cast_prodₓ'. -/
@[simp, norm_cast]
theorem cast_prod (s : Finset ι) (f : ι → ℚ) : (↑(∏ i in s, f i) : α) = ∏ i in s, f i :=
  map_prod (Rat.castHom α) _ _
#align rat.cast_prod Rat.cast_prod

end Field

end Rat

