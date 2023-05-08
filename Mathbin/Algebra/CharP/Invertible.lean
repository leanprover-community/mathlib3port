/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module algebra.char_p.invertible
! leanprover-community/mathlib commit 10bf4f825ad729c5653adc039dafa3622e7f93c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Invertible
import Mathbin.Algebra.CharP.Basic

/-!
# Invertibility of elements given a characteristic

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file includes some instances of `invertible` for specific numbers in
characteristic zero. Some more cases are given as a `def`, to be included only
when needed. To construct instances for concrete numbers,
`invertible_of_nonzero` is a useful definition.
-/


variable {K : Type _}

section Field

variable [Field K]

/- warning: invertible_of_ring_char_not_dvd -> invertibleOfRingCharNotDvd is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : Field.{u1} K] {t : Nat}, (Not (Dvd.Dvd.{0} Nat Nat.hasDvd (ringChar.{u1} K (NonAssocRing.toNonAssocSemiring.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))))) t)) -> (Invertible.{u1} K (MulZeroClass.toHasMul.{u1} K (MulZeroOneClass.toMulZeroClass.{u1} K (MonoidWithZero.toMulZeroOneClass.{u1} K (GroupWithZero.toMonoidWithZero.{u1} K (DivisionSemiring.toGroupWithZero.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1))))))) (MulOneClass.toHasOne.{u1} K (MulZeroOneClass.toMulOneClass.{u1} K (MonoidWithZero.toMulZeroOneClass.{u1} K (GroupWithZero.toMonoidWithZero.{u1} K (DivisionSemiring.toGroupWithZero.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat K (HasLiftT.mk.{1, succ u1} Nat K (CoeTCₓ.coe.{1, succ u1} Nat K (Nat.castCoe.{u1} K (AddMonoidWithOne.toNatCast.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))))))))) t))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : Field.{u1} K] {t : Nat}, (Not (Dvd.dvd.{0} Nat Nat.instDvdNat (ringChar.{u1} K (Semiring.toNonAssocSemiring.{u1} K (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1))))) t)) -> (Invertible.{u1} K (NonUnitalNonAssocRing.toMul.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))))) (Semiring.toOne.{u1} K (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1)))) (Nat.cast.{u1} K (Semiring.toNatCast.{u1} K (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1)))) t))
Case conversion may be inaccurate. Consider using '#align invertible_of_ring_char_not_dvd invertibleOfRingCharNotDvdₓ'. -/
/-- A natural number `t` is invertible in a field `K` if the charactistic of `K` does not divide
`t`. -/
def invertibleOfRingCharNotDvd {t : ℕ} (not_dvd : ¬ringChar K ∣ t) : Invertible (t : K) :=
  invertibleOfNonzero fun h => not_dvd ((ringChar.spec K t).mp h)
#align invertible_of_ring_char_not_dvd invertibleOfRingCharNotDvd

/- warning: not_ring_char_dvd_of_invertible -> not_ringChar_dvd_of_invertible is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : Field.{u1} K] {t : Nat} [_inst_2 : Invertible.{u1} K (Distrib.toHasMul.{u1} K (Ring.toDistrib.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1)))) (AddMonoidWithOne.toOne.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1)))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat K (HasLiftT.mk.{1, succ u1} Nat K (CoeTCₓ.coe.{1, succ u1} Nat K (Nat.castCoe.{u1} K (AddMonoidWithOne.toNatCast.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))))))))) t)], Not (Dvd.Dvd.{0} Nat Nat.hasDvd (ringChar.{u1} K (NonAssocRing.toNonAssocSemiring.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))))) t)
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : Field.{u1} K] {t : Nat} [_inst_2 : Invertible.{u1} K (NonUnitalNonAssocRing.toMul.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))))) (Semiring.toOne.{u1} K (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1)))) (Nat.cast.{u1} K (Semiring.toNatCast.{u1} K (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1)))) t)], Not (Dvd.dvd.{0} Nat Nat.instDvdNat (ringChar.{u1} K (Semiring.toNonAssocSemiring.{u1} K (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1))))) t)
Case conversion may be inaccurate. Consider using '#align not_ring_char_dvd_of_invertible not_ringChar_dvd_of_invertibleₓ'. -/
theorem not_ringChar_dvd_of_invertible {t : ℕ} [Invertible (t : K)] : ¬ringChar K ∣ t :=
  by
  rw [← ringChar.spec, ← Ne.def]
  exact nonzero_of_invertible (t : K)
#align not_ring_char_dvd_of_invertible not_ringChar_dvd_of_invertible

/- warning: invertible_of_char_p_not_dvd -> invertibleOfCharPNotDvd is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : Field.{u1} K] {p : Nat} [_inst_2 : CharP.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))))) p] {t : Nat}, (Not (Dvd.Dvd.{0} Nat Nat.hasDvd p t)) -> (Invertible.{u1} K (MulZeroClass.toHasMul.{u1} K (MulZeroOneClass.toMulZeroClass.{u1} K (MonoidWithZero.toMulZeroOneClass.{u1} K (GroupWithZero.toMonoidWithZero.{u1} K (DivisionSemiring.toGroupWithZero.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1))))))) (MulOneClass.toHasOne.{u1} K (MulZeroOneClass.toMulOneClass.{u1} K (MonoidWithZero.toMulZeroOneClass.{u1} K (GroupWithZero.toMonoidWithZero.{u1} K (DivisionSemiring.toGroupWithZero.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat K (HasLiftT.mk.{1, succ u1} Nat K (CoeTCₓ.coe.{1, succ u1} Nat K (Nat.castCoe.{u1} K (AddMonoidWithOne.toNatCast.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))))))))) t))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : Field.{u1} K] {p : Nat} [_inst_2 : CharP.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (Ring.toAddGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1)))) p] {t : Nat}, (Not (Dvd.dvd.{0} Nat Nat.instDvdNat p t)) -> (Invertible.{u1} K (NonUnitalNonAssocRing.toMul.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))))) (Semiring.toOne.{u1} K (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1)))) (Nat.cast.{u1} K (Semiring.toNatCast.{u1} K (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1)))) t))
Case conversion may be inaccurate. Consider using '#align invertible_of_char_p_not_dvd invertibleOfCharPNotDvdₓ'. -/
/-- A natural number `t` is invertible in a field `K` of charactistic `p` if `p` does not divide
`t`. -/
def invertibleOfCharPNotDvd {p : ℕ} [CharP K p] {t : ℕ} (not_dvd : ¬p ∣ t) : Invertible (t : K) :=
  invertibleOfNonzero fun h => not_dvd ((CharP.cast_eq_zero_iff K p t).mp h)
#align invertible_of_char_p_not_dvd invertibleOfCharPNotDvd

/- warning: invertible_of_pos -> invertibleOfPos is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : Field.{u1} K] [_inst_2 : CharZero.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1)))))] (n : Nat) [_inst_3 : NeZero.{0} Nat Nat.hasZero n], Invertible.{u1} K (MulZeroClass.toHasMul.{u1} K (MulZeroOneClass.toMulZeroClass.{u1} K (MonoidWithZero.toMulZeroOneClass.{u1} K (GroupWithZero.toMonoidWithZero.{u1} K (DivisionSemiring.toGroupWithZero.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1))))))) (MulOneClass.toHasOne.{u1} K (MulZeroOneClass.toMulOneClass.{u1} K (MonoidWithZero.toMulZeroOneClass.{u1} K (GroupWithZero.toMonoidWithZero.{u1} K (DivisionSemiring.toGroupWithZero.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat K (HasLiftT.mk.{1, succ u1} Nat K (CoeTCₓ.coe.{1, succ u1} Nat K (Nat.castCoe.{u1} K (AddMonoidWithOne.toNatCast.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))))))))) n)
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : Field.{u1} K] [_inst_2 : CharZero.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (Ring.toAddGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))))] (n : Nat) [_inst_3 : NeZero.{0} Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) n], Invertible.{u1} K (NonUnitalNonAssocRing.toMul.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))))) (Semiring.toOne.{u1} K (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1)))) (Nat.cast.{u1} K (Semiring.toNatCast.{u1} K (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1)))) n)
Case conversion may be inaccurate. Consider using '#align invertible_of_pos invertibleOfPosₓ'. -/
-- warning: this could potentially loop with `ne_zero.invertible` - if there is weird type-class
-- loops, watch out for that.
instance invertibleOfPos [CharZero K] (n : ℕ) [NeZero n] : Invertible (n : K) :=
  invertibleOfNonzero <| NeZero.out
#align invertible_of_pos invertibleOfPos

end Field

section DivisionRing

variable [DivisionRing K] [CharZero K]

/- warning: invertible_succ -> invertibleSucc is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : CharZero.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K _inst_1))))] (n : Nat), Invertible.{u1} K (MulZeroClass.toHasMul.{u1} K (MulZeroOneClass.toMulZeroClass.{u1} K (MonoidWithZero.toMulZeroOneClass.{u1} K (GroupWithZero.toMonoidWithZero.{u1} K (DivisionSemiring.toGroupWithZero.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)))))) (MulOneClass.toHasOne.{u1} K (MulZeroOneClass.toMulOneClass.{u1} K (MonoidWithZero.toMulZeroOneClass.{u1} K (GroupWithZero.toMonoidWithZero.{u1} K (DivisionSemiring.toGroupWithZero.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat K (HasLiftT.mk.{1, succ u1} Nat K (CoeTCₓ.coe.{1, succ u1} Nat K (Nat.castCoe.{u1} K (AddMonoidWithOne.toNatCast.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))))))) (Nat.succ n))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : CharZero.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (Ring.toAddGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))] (n : Nat), Invertible.{u1} K (NonUnitalNonAssocRing.toMul.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))) (Semiring.toOne.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1))) (Nat.cast.{u1} K (Semiring.toNatCast.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1))) (Nat.succ n))
Case conversion may be inaccurate. Consider using '#align invertible_succ invertibleSuccₓ'. -/
instance invertibleSucc (n : ℕ) : Invertible (n.succ : K) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _))
#align invertible_succ invertibleSucc

/-!
A few `invertible n` instances for small numerals `n`. Feel free to add your own
number when you need its inverse.
-/


/- warning: invertible_two -> invertibleTwo is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : CharZero.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K _inst_1))))], Invertible.{u1} K (MulZeroClass.toHasMul.{u1} K (MulZeroOneClass.toMulZeroClass.{u1} K (MonoidWithZero.toMulZeroOneClass.{u1} K (GroupWithZero.toMonoidWithZero.{u1} K (DivisionSemiring.toGroupWithZero.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)))))) (MulOneClass.toHasOne.{u1} K (MulZeroOneClass.toMulOneClass.{u1} K (MonoidWithZero.toMulZeroOneClass.{u1} K (GroupWithZero.toMonoidWithZero.{u1} K (DivisionSemiring.toGroupWithZero.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)))))) (OfNat.ofNat.{u1} K 2 (OfNat.mk.{u1} K 2 (bit0.{u1} K (Distrib.toHasAdd.{u1} K (Ring.toDistrib.{u1} K (DivisionRing.toRing.{u1} K _inst_1))) (One.one.{u1} K (AddMonoidWithOne.toOne.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))))))))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : CharZero.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (Ring.toAddGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))], Invertible.{u1} K (NonUnitalNonAssocRing.toMul.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))) (Semiring.toOne.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1))) (OfNat.ofNat.{u1} K 2 (instOfNat.{u1} K 2 (Semiring.toNatCast.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1))) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))
Case conversion may be inaccurate. Consider using '#align invertible_two invertibleTwoₓ'. -/
instance invertibleTwo : Invertible (2 : K) :=
  invertibleOfNonzero (by exact_mod_cast (by decide : 2 ≠ 0))
#align invertible_two invertibleTwo

/- warning: invertible_three -> invertibleThree is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : CharZero.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K _inst_1))))], Invertible.{u1} K (MulZeroClass.toHasMul.{u1} K (MulZeroOneClass.toMulZeroClass.{u1} K (MonoidWithZero.toMulZeroOneClass.{u1} K (GroupWithZero.toMonoidWithZero.{u1} K (DivisionSemiring.toGroupWithZero.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)))))) (MulOneClass.toHasOne.{u1} K (MulZeroOneClass.toMulOneClass.{u1} K (MonoidWithZero.toMulZeroOneClass.{u1} K (GroupWithZero.toMonoidWithZero.{u1} K (DivisionSemiring.toGroupWithZero.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)))))) (OfNat.ofNat.{u1} K 3 (OfNat.mk.{u1} K 3 (bit1.{u1} K (AddMonoidWithOne.toOne.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K _inst_1))))) (Distrib.toHasAdd.{u1} K (Ring.toDistrib.{u1} K (DivisionRing.toRing.{u1} K _inst_1))) (One.one.{u1} K (AddMonoidWithOne.toOne.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))))))))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : CharZero.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (Ring.toAddGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))], Invertible.{u1} K (NonUnitalNonAssocRing.toMul.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))) (Semiring.toOne.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1))) (OfNat.ofNat.{u1} K 3 (instOfNat.{u1} K 3 (Semiring.toNatCast.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1))) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))
Case conversion may be inaccurate. Consider using '#align invertible_three invertibleThreeₓ'. -/
instance invertibleThree : Invertible (3 : K) :=
  invertibleOfNonzero (by exact_mod_cast (by decide : 3 ≠ 0))
#align invertible_three invertibleThree

end DivisionRing

