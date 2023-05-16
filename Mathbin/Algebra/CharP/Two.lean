/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module algebra.char_p.two
! leanprover-community/mathlib commit 10bf4f825ad729c5653adc039dafa3622e7f93c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.CharP.Basic

/-!
# Lemmas about rings of characteristic two

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains results about `char_p R 2`, in the `char_two` namespace.

The lemmas in this file with a `_sq` suffix are just special cases of the `_pow_char` lemmas
elsewhere, with a shorter name for ease of discovery, and no need for a `[fact (prime 2)]` argument.
-/


variable {R ι : Type _}

namespace CharTwo

section Semiring

variable [Semiring R] [CharP R 2]

/- warning: char_two.two_eq_zero -> CharTwo.two_eq_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] [_inst_2 : CharP.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))], Eq.{succ u1} R (OfNat.ofNat.{u1} R 2 (OfNat.mk.{u1} R 2 (bit0.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] [_inst_2 : CharP.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))], Eq.{succ u1} R (OfNat.ofNat.{u1} R 2 (instOfNat.{u1} R 2 (Semiring.toNatCast.{u1} R _inst_1) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align char_two.two_eq_zero CharTwo.two_eq_zeroₓ'. -/
theorem two_eq_zero : (2 : R) = 0 := by rw [← Nat.cast_two, CharP.cast_eq_zero]
#align char_two.two_eq_zero CharTwo.two_eq_zero

/- warning: char_two.add_self_eq_zero -> CharTwo.add_self_eq_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] [_inst_2 : CharP.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))] (x : R), Eq.{succ u1} R (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) x x) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] [_inst_2 : CharP.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))] (x : R), Eq.{succ u1} R (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) x x) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align char_two.add_self_eq_zero CharTwo.add_self_eq_zeroₓ'. -/
@[simp]
theorem add_self_eq_zero (x : R) : x + x = 0 := by rw [← two_smul R x, two_eq_zero, zero_smul]
#align char_two.add_self_eq_zero CharTwo.add_self_eq_zero

/- warning: char_two.bit0_eq_zero -> CharTwo.bit0_eq_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] [_inst_2 : CharP.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))], Eq.{succ u1} (R -> R) (bit0.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (OfNat.ofNat.{u1} (R -> R) 0 (OfNat.mk.{u1} (R -> R) 0 (Zero.zero.{u1} (R -> R) (Pi.instZero.{u1, u1} R (fun (a : R) => R) (fun (i : R) => MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] [_inst_2 : CharP.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))], Eq.{succ u1} (R -> R) (bit0.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (OfNat.ofNat.{u1} (R -> R) 0 (Zero.toOfNat0.{u1} (R -> R) (Pi.instZero.{u1, u1} R (fun (a : R) => R) (fun (i : R) => MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align char_two.bit0_eq_zero CharTwo.bit0_eq_zeroₓ'. -/
@[simp]
theorem bit0_eq_zero : (bit0 : R → R) = 0 := by
  funext
  exact add_self_eq_zero _
#align char_two.bit0_eq_zero CharTwo.bit0_eq_zero

/- warning: char_two.bit0_apply_eq_zero -> CharTwo.bit0_apply_eq_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] [_inst_2 : CharP.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))] (x : R), Eq.{succ u1} R (bit0.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) x) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] [_inst_2 : CharP.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))] (x : R), Eq.{succ u1} R (bit0.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) x) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align char_two.bit0_apply_eq_zero CharTwo.bit0_apply_eq_zeroₓ'. -/
theorem bit0_apply_eq_zero (x : R) : (bit0 x : R) = 0 := by simp
#align char_two.bit0_apply_eq_zero CharTwo.bit0_apply_eq_zero

/- warning: char_two.bit1_eq_one -> CharTwo.bit1_eq_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] [_inst_2 : CharP.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))], Eq.{succ u1} (R -> R) (bit1.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (OfNat.ofNat.{u1} (R -> R) 1 (OfNat.mk.{u1} (R -> R) 1 (One.one.{u1} (R -> R) (Pi.instOne.{u1, u1} R (fun (a : R) => R) (fun (i : R) => AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] [_inst_2 : CharP.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))], Eq.{succ u1} (R -> R) (bit1.{u1} R (Semiring.toOne.{u1} R _inst_1) (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (OfNat.ofNat.{u1} (R -> R) 1 (One.toOfNat1.{u1} (R -> R) (Pi.instOne.{u1, u1} R (fun (a : R) => R) (fun (i : R) => Semiring.toOne.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align char_two.bit1_eq_one CharTwo.bit1_eq_oneₓ'. -/
@[simp]
theorem bit1_eq_one : (bit1 : R → R) = 1 := by
  funext
  simp [bit1]
#align char_two.bit1_eq_one CharTwo.bit1_eq_one

/- warning: char_two.bit1_apply_eq_one -> CharTwo.bit1_apply_eq_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] [_inst_2 : CharP.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))] (x : R), Eq.{succ u1} R (bit1.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) x) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] [_inst_2 : CharP.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))] (x : R), Eq.{succ u1} R (bit1.{u1} R (Semiring.toOne.{u1} R _inst_1) (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) x) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R _inst_1)))
Case conversion may be inaccurate. Consider using '#align char_two.bit1_apply_eq_one CharTwo.bit1_apply_eq_oneₓ'. -/
theorem bit1_apply_eq_one (x : R) : (bit1 x : R) = 1 := by simp
#align char_two.bit1_apply_eq_one CharTwo.bit1_apply_eq_one

end Semiring

section Ring

variable [Ring R] [CharP R 2]

/- warning: char_two.neg_eq -> CharTwo.neg_eq is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] [_inst_2 : CharP.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))] (x : R), Eq.{succ u1} R (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))))) x) x
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] [_inst_2 : CharP.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))] (x : R), Eq.{succ u1} R (Neg.neg.{u1} R (Ring.toNeg.{u1} R _inst_1) x) x
Case conversion may be inaccurate. Consider using '#align char_two.neg_eq CharTwo.neg_eqₓ'. -/
@[simp]
theorem neg_eq (x : R) : -x = x := by
  rw [neg_eq_iff_add_eq_zero, ← two_smul R x, two_eq_zero, zero_smul]
#align char_two.neg_eq CharTwo.neg_eq

/- warning: char_two.neg_eq' -> CharTwo.neg_eq' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] [_inst_2 : CharP.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))], Eq.{succ u1} (R -> R) (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))))) (id.{succ u1} R)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] [_inst_2 : CharP.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))], Eq.{succ u1} (R -> R) (Neg.neg.{u1} R (Ring.toNeg.{u1} R _inst_1)) (id.{succ u1} R)
Case conversion may be inaccurate. Consider using '#align char_two.neg_eq' CharTwo.neg_eq'ₓ'. -/
theorem neg_eq' : Neg.neg = (id : R → R) :=
  funext neg_eq
#align char_two.neg_eq' CharTwo.neg_eq'

/- warning: char_two.sub_eq_add -> CharTwo.sub_eq_add is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] [_inst_2 : CharP.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))] (x : R) (y : R), Eq.{succ u1} R (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))))) x y) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R _inst_1))) x y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] [_inst_2 : CharP.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))] (x : R) (y : R), Eq.{succ u1} R (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R _inst_1)) x y) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))) x y)
Case conversion may be inaccurate. Consider using '#align char_two.sub_eq_add CharTwo.sub_eq_addₓ'. -/
@[simp]
theorem sub_eq_add (x y : R) : x - y = x + y := by rw [sub_eq_add_neg, neg_eq]
#align char_two.sub_eq_add CharTwo.sub_eq_add

/- warning: char_two.sub_eq_add' -> CharTwo.sub_eq_add' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] [_inst_2 : CharP.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))], Eq.{succ u1} (R -> R -> R) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R _inst_1))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] [_inst_2 : CharP.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))], Eq.{succ u1} (R -> R -> R) (Sub.sub.{u1} R (Ring.toSub.{u1} R _inst_1)) (fun (x._@.Mathlib.Algebra.CharP.Two._hyg.477 : R) (x._@.Mathlib.Algebra.CharP.Two._hyg.479 : R) => HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))) x._@.Mathlib.Algebra.CharP.Two._hyg.477 x._@.Mathlib.Algebra.CharP.Two._hyg.479)
Case conversion may be inaccurate. Consider using '#align char_two.sub_eq_add' CharTwo.sub_eq_add'ₓ'. -/
theorem sub_eq_add' : Sub.sub = ((· + ·) : R → R → R) :=
  funext fun x => funext fun y => sub_eq_add x y
#align char_two.sub_eq_add' CharTwo.sub_eq_add'

end Ring

section CommSemiring

variable [CommSemiring R] [CharP R 2]

/- warning: char_two.add_sq -> CharTwo.add_sq is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : CharP.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))] (x : R) (y : R), Eq.{succ u1} R (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x y) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) x (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) y (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : CharP.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))] (x : R) (y : R), Eq.{succ u1} R (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x y) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) x (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) y (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
Case conversion may be inaccurate. Consider using '#align char_two.add_sq CharTwo.add_sqₓ'. -/
theorem add_sq (x y : R) : (x + y) ^ 2 = x ^ 2 + y ^ 2 :=
  add_pow_char _ _ _
#align char_two.add_sq CharTwo.add_sq

/- warning: char_two.add_mul_self -> CharTwo.add_mul_self is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : CharP.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))] (x : R) (y : R), Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x y) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x y)) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x x) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) y y))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : CharP.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))] (x : R) (y : R), Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x y) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x y)) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) x x) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) y y))
Case conversion may be inaccurate. Consider using '#align char_two.add_mul_self CharTwo.add_mul_selfₓ'. -/
theorem add_mul_self (x y : R) : (x + y) * (x + y) = x * x + y * y := by
  rw [← pow_two, ← pow_two, ← pow_two, add_sq]
#align char_two.add_mul_self CharTwo.add_mul_self

open BigOperators

/- warning: char_two.list_sum_sq -> CharTwo.list_sum_sq is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : CharP.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))] (l : List.{u1} R), Eq.{succ u1} R (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (List.sum.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) l) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (List.sum.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (List.map.{u1, u1} R R (fun (_x : R) => HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) _x (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) l))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : CharP.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))] (l : List.{u1} R), Eq.{succ u1} R (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (List.sum.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R _inst_1)) l) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (List.sum.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R _inst_1)) (List.map.{u1, u1} R R (fun (_x : R) => HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) _x (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) l))
Case conversion may be inaccurate. Consider using '#align char_two.list_sum_sq CharTwo.list_sum_sqₓ'. -/
theorem list_sum_sq (l : List R) : l.Sum ^ 2 = (l.map (· ^ 2)).Sum :=
  list_sum_pow_char _ _
#align char_two.list_sum_sq CharTwo.list_sum_sq

/- warning: char_two.list_sum_mul_self -> CharTwo.list_sum_mul_self is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : CharP.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))] (l : List.{u1} R), Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (List.sum.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) l) (List.sum.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) l)) (List.sum.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (List.map.{u1, u1} R R (fun (x : R) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x x) l))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : CharP.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))] (l : List.{u1} R), Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (List.sum.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R _inst_1)) l) (List.sum.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R _inst_1)) l)) (List.sum.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R _inst_1)) (List.map.{u1, u1} R R (fun (x : R) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) x x) l))
Case conversion may be inaccurate. Consider using '#align char_two.list_sum_mul_self CharTwo.list_sum_mul_selfₓ'. -/
theorem list_sum_mul_self (l : List R) : l.Sum * l.Sum = (List.map (fun x => x * x) l).Sum := by
  simp_rw [← pow_two, list_sum_sq]
#align char_two.list_sum_mul_self CharTwo.list_sum_mul_self

#print CharTwo.multiset_sum_sq /-
theorem multiset_sum_sq (l : Multiset R) : l.Sum ^ 2 = (l.map (· ^ 2)).Sum :=
  multiset_sum_pow_char _ _
#align char_two.multiset_sum_sq CharTwo.multiset_sum_sq
-/

/- warning: char_two.multiset_sum_mul_self -> CharTwo.multiset_sum_mul_self is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : CharP.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))] (l : Multiset.{u1} R), Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (Multiset.sum.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) l) (Multiset.sum.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) l)) (Multiset.sum.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Multiset.map.{u1, u1} R R (fun (x : R) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x x) l))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : CharP.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))] (l : Multiset.{u1} R), Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Multiset.sum.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) l) (Multiset.sum.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) l)) (Multiset.sum.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Multiset.map.{u1, u1} R R (fun (x : R) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) x x) l))
Case conversion may be inaccurate. Consider using '#align char_two.multiset_sum_mul_self CharTwo.multiset_sum_mul_selfₓ'. -/
theorem multiset_sum_mul_self (l : Multiset R) :
    l.Sum * l.Sum = (Multiset.map (fun x => x * x) l).Sum := by simp_rw [← pow_two, multiset_sum_sq]
#align char_two.multiset_sum_mul_self CharTwo.multiset_sum_mul_self

#print CharTwo.sum_sq /-
theorem sum_sq (s : Finset ι) (f : ι → R) : (∑ i in s, f i) ^ 2 = ∑ i in s, f i ^ 2 :=
  sum_pow_char _ _ _
#align char_two.sum_sq CharTwo.sum_sq
-/

/- warning: char_two.sum_mul_self -> CharTwo.sum_mul_self is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {ι : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : CharP.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))] (s : Finset.{u2} ι) (f : ι -> R), Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (Finset.sum.{u1, u2} R ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) s (fun (i : ι) => f i)) (Finset.sum.{u1, u2} R ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) s (fun (i : ι) => f i))) (Finset.sum.{u1, u2} R ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) s (fun (i : ι) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (f i) (f i)))
but is expected to have type
  forall {R : Type.{u1}} {ι : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : CharP.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))] (s : Finset.{u2} ι) (f : ι -> R), Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Finset.sum.{u1, u2} R ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) s (fun (i : ι) => f i)) (Finset.sum.{u1, u2} R ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) s (fun (i : ι) => f i))) (Finset.sum.{u1, u2} R ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) s (fun (i : ι) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (f i) (f i)))
Case conversion may be inaccurate. Consider using '#align char_two.sum_mul_self CharTwo.sum_mul_selfₓ'. -/
theorem sum_mul_self (s : Finset ι) (f : ι → R) :
    ((∑ i in s, f i) * ∑ i in s, f i) = ∑ i in s, f i * f i := by simp_rw [← pow_two, sum_sq]
#align char_two.sum_mul_self CharTwo.sum_mul_self

end CommSemiring

end CharTwo

section ringChar

variable [Ring R]

/- warning: neg_one_eq_one_iff -> neg_one_eq_one_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] [_inst_2 : Nontrivial.{u1} R], Iff (Eq.{succ u1} R (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))))))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))))))) (Eq.{1} Nat (ringChar.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] [_inst_2 : Nontrivial.{u1} R], Iff (Eq.{succ u1} R (Neg.neg.{u1} R (Ring.toNeg.{u1} R _inst_1) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) (Eq.{1} Nat (ringChar.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
Case conversion may be inaccurate. Consider using '#align neg_one_eq_one_iff neg_one_eq_one_iffₓ'. -/
theorem neg_one_eq_one_iff [Nontrivial R] : (-1 : R) = 1 ↔ ringChar R = 2 :=
  by
  refine' ⟨fun h => _, fun h => @CharTwo.neg_eq _ (ringChar.of_eq h) 1⟩
  rw [eq_comm, ← sub_eq_zero, sub_neg_eq_add, ← Nat.cast_one, ← Nat.cast_add] at h
  exact ((Nat.dvd_prime Nat.prime_two).mp (ringChar.dvd h)).resolve_left CharP.ringChar_ne_one
#align neg_one_eq_one_iff neg_one_eq_one_iff

/- warning: order_of_neg_one -> orderOf_neg_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] [_inst_2 : Nontrivial.{u1} R], Eq.{1} Nat (orderOf.{u1} R (Ring.toMonoid.{u1} R _inst_1) (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))))))))) (ite.{1} Nat (Eq.{1} Nat (ringChar.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Nat.decidableEq (ringChar.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] [_inst_2 : Nontrivial.{u1} R], Eq.{1} Nat (orderOf.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (Neg.neg.{u1} R (Ring.toNeg.{u1} R _inst_1) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (Ring.toSemiring.{u1} R _inst_1)))))) (ite.{1} Nat (Eq.{1} Nat (ringChar.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (instDecidableEqNat (ringChar.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
Case conversion may be inaccurate. Consider using '#align order_of_neg_one orderOf_neg_oneₓ'. -/
@[simp]
theorem orderOf_neg_one [Nontrivial R] : orderOf (-1 : R) = if ringChar R = 2 then 1 else 2 :=
  by
  split_ifs
  · rw [neg_one_eq_one_iff.2 h, orderOf_one]
  apply orderOf_eq_prime
  · simp
  simpa [neg_one_eq_one_iff] using h
#align order_of_neg_one orderOf_neg_one

end ringChar

