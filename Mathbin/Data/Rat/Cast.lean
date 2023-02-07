/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module data.rat.cast
! leanprover-community/mathlib commit 0a0ec35061ed9960bf0e7ffb0335f44447b58977
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Rat.Order
import Mathbin.Data.Rat.Lemmas
import Mathbin.Data.Int.CharZero
import Mathbin.Algebra.GroupWithZero.Power
import Mathbin.Algebra.Field.Opposite
import Mathbin.Algebra.Order.Field.Basic

/-!
# Casts for Rational Numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Summary

We define the canonical injection from ℚ into an arbitrary division ring and prove various
casting lemmas showing the well-behavedness of this injection.

## Notations

- `/.` is infix notation for `rat.mk`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, cast, coercion, casting
-/


variable {F ι α β : Type _}

namespace Rat

open Rat

section WithDivRing

variable [DivisionRing α]

/- warning: rat.cast_coe_int -> Rat.cast_coe_int is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] (n : Int), Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Rat (HasLiftT.mk.{1, 1} Int Rat (CoeTCₓ.coe.{1, 1} Int Rat (Int.castCoe.{0} Rat Rat.hasIntCast))) n)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))))) n)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] (n : Int), Eq.{succ u1} α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) (Int.cast.{0} Rat Rat.instIntCastRat n)) (Int.cast.{u1} α (Ring.toIntCast.{u1} α (DivisionRing.toRing.{u1} α _inst_1)) n)
Case conversion may be inaccurate. Consider using '#align rat.cast_coe_int Rat.cast_coe_intₓ'. -/
@[simp, norm_cast]
theorem cast_coe_int (n : ℤ) : ((n : ℚ) : α) = n :=
  (cast_def _).trans <| show (n / (1 : ℕ) : α) = n by rw [Nat.cast_one, div_one]
#align rat.cast_coe_int Rat.cast_coe_int

/- warning: rat.cast_coe_nat -> Rat.cast_coe_nat is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] (n : Nat), Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))))))) n)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))))) n)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] (n : Nat), Eq.{succ u1} α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))) n)) (Nat.cast.{u1} α (NonAssocRing.toNatCast.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))) n)
Case conversion may be inaccurate. Consider using '#align rat.cast_coe_nat Rat.cast_coe_natₓ'. -/
@[simp, norm_cast]
theorem cast_coe_nat (n : ℕ) : ((n : ℚ) : α) = n := by
  rw [← Int.cast_ofNat, cast_coe_int, Int.cast_ofNat]
#align rat.cast_coe_nat Rat.cast_coe_nat

/- warning: rat.cast_zero -> Rat.cast_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α], Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero)))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α], Eq.{succ u1} α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align rat.cast_zero Rat.cast_zeroₓ'. -/
@[simp, norm_cast]
theorem cast_zero : ((0 : ℚ) : α) = 0 :=
  (cast_coe_int _).trans Int.cast_zero
#align rat.cast_zero Rat.cast_zero

/- warning: rat.cast_one -> Rat.cast_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α], Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) (OfNat.ofNat.{0} Rat 1 (OfNat.mk.{0} Rat 1 (One.one.{0} Rat Rat.hasOne)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α], Eq.{succ u1} α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) (OfNat.ofNat.{0} Rat 1 (Rat.instOfNatRat 1))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (NonAssocRing.toOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align rat.cast_one Rat.cast_oneₓ'. -/
@[simp, norm_cast]
theorem cast_one : ((1 : ℚ) : α) = 1 :=
  (cast_coe_int _).trans Int.cast_one
#align rat.cast_one Rat.cast_one

/- warning: rat.cast_commute -> Rat.cast_commute is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] (r : Rat) (a : α), Commute.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (DivisionRing.toRing.{u1} α _inst_1))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) r) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] (r : Rat) (a : α), Commute.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))) (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) r) a
Case conversion may be inaccurate. Consider using '#align rat.cast_commute Rat.cast_commuteₓ'. -/
theorem cast_commute (r : ℚ) (a : α) : Commute (↑r) a := by
  simpa only [cast_def] using (r.1.cast_commute a).divLeft (r.2.cast_commute a)
#align rat.cast_commute Rat.cast_commute

/- warning: rat.cast_comm -> Rat.cast_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] (r : Rat) (a : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) r) a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))) a ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) r))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] (r : Rat) (a : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))) (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) r) a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))) a (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) r))
Case conversion may be inaccurate. Consider using '#align rat.cast_comm Rat.cast_commₓ'. -/
theorem cast_comm (r : ℚ) (a : α) : (r : α) * a = a * r :=
  (cast_commute r a).Eq
#align rat.cast_comm Rat.cast_comm

/- warning: rat.commute_cast -> Rat.commute_cast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] (a : α) (r : Rat), Commute.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (DivisionRing.toRing.{u1} α _inst_1))) a ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) r)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] (a : α) (r : Rat), Commute.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))) a (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) r)
Case conversion may be inaccurate. Consider using '#align rat.commute_cast Rat.commute_castₓ'. -/
theorem commute_cast (a : α) (r : ℚ) : Commute a r :=
  (r.cast_commute a).symm
#align rat.commute_cast Rat.commute_cast

/- warning: rat.cast_mk_of_ne_zero -> Rat.cast_mk_of_ne_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] (a : Int) (b : Int), (Ne.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))))) b) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))))))) -> (Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) (Rat.mk a b)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionRing.toDivInvMonoid.{u1} α _inst_1))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))))) a) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))))) b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] (a : Int) (b : Int), (Ne.{succ u1} α (Int.cast.{u1} α (Ring.toIntCast.{u1} α (DivisionRing.toRing.{u1} α _inst_1)) b) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α _inst_1))))))) -> (Eq.{succ u1} α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) (Rat.divInt a b)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivisionRing.toDiv.{u1} α _inst_1)) (Int.cast.{u1} α (Ring.toIntCast.{u1} α (DivisionRing.toRing.{u1} α _inst_1)) a) (Int.cast.{u1} α (Ring.toIntCast.{u1} α (DivisionRing.toRing.{u1} α _inst_1)) b)))
Case conversion may be inaccurate. Consider using '#align rat.cast_mk_of_ne_zero Rat.cast_mk_of_ne_zeroₓ'. -/
@[norm_cast]
theorem cast_mk_of_ne_zero (a b : ℤ) (b0 : (b : α) ≠ 0) : (a /. b : α) = a / b :=
  by
  have b0' : b ≠ 0 := by
    refine' mt _ b0
    simp (config := { contextual := true })
  cases' e : a /. b with n d h c
  have d0 : (d : α) ≠ 0 := by
    intro d0
    have dd := denom_dvd a b
    cases' show (d : ℤ) ∣ b by rwa [e] at dd with k ke
    have : (b : α) = (d : α) * (k : α) := by rw [ke, Int.cast_mul, Int.cast_ofNat]
    rw [d0, zero_mul] at this
    contradiction
  rw [num_denom'] at e
  have := congr_arg (coe : ℤ → α) ((mk_eq b0' <| ne_of_gt <| Int.coe_nat_pos.2 h).1 e)
  rw [Int.cast_mul, Int.cast_mul, Int.cast_ofNat] at this
  symm
  rw [cast_def, div_eq_mul_inv, eq_div_iff_mul_eq d0, mul_assoc, (d.commute_cast _).Eq, ← mul_assoc,
    this, mul_assoc, mul_inv_cancel b0, mul_one]
#align rat.cast_mk_of_ne_zero Rat.cast_mk_of_ne_zero

/- warning: rat.cast_add_of_ne_zero -> Rat.cast_add_of_ne_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] {m : Rat} {n : Rat}, (Ne.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))))) (Rat.den m)) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))))))) -> (Ne.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))))) (Rat.den n)) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))))))) -> (Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) (HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.hasAdd) m n)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) m) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) n)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] {m : Rat} {n : Rat}, (Ne.{succ u1} α (Nat.cast.{u1} α (NonAssocRing.toNatCast.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))) (Rat.den m)) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α _inst_1))))))) -> (Ne.{succ u1} α (Nat.cast.{u1} α (NonAssocRing.toNatCast.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))) (Rat.den n)) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α _inst_1))))))) -> (Eq.{succ u1} α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) (HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.instAddRat) m n)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))))) (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) m) (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) n)))
Case conversion may be inaccurate. Consider using '#align rat.cast_add_of_ne_zero Rat.cast_add_of_ne_zeroₓ'. -/
@[norm_cast]
theorem cast_add_of_ne_zero :
    ∀ {m n : ℚ}, (m.den : α) ≠ 0 → (n.den : α) ≠ 0 → ((m + n : ℚ) : α) = m + n
  | ⟨n₁, d₁, h₁, c₁⟩, ⟨n₂, d₂, h₂, c₂⟩ => fun (d₁0 : (d₁ : α) ≠ 0) (d₂0 : (d₂ : α) ≠ 0) =>
    by
    have d₁0' : (d₁ : ℤ) ≠ 0 :=
      Int.coe_nat_ne_zero.2 fun e => by rw [e] at d₁0 <;> exact d₁0 Nat.cast_zero
    have d₂0' : (d₂ : ℤ) ≠ 0 :=
      Int.coe_nat_ne_zero.2 fun e => by rw [e] at d₂0 <;> exact d₂0 Nat.cast_zero
    rw [num_denom', num_denom', add_def d₁0' d₂0']
    suffices (n₁ * (d₂ * (d₂⁻¹ * d₁⁻¹)) + n₂ * (d₁ * d₂⁻¹) * d₁⁻¹ : α) = n₁ * d₁⁻¹ + n₂ * d₂⁻¹
      by
      rw [cast_mk_of_ne_zero, cast_mk_of_ne_zero, cast_mk_of_ne_zero]
      · simpa [division_def, left_distrib, right_distrib, mul_inv_rev, d₁0, d₂0, mul_assoc]
      all_goals simp [d₁0, d₂0]
    rw [← mul_assoc (d₂ : α), mul_inv_cancel d₂0, one_mul, (Nat.cast_commute _ _).Eq]
    simp [d₁0, mul_assoc]
#align rat.cast_add_of_ne_zero Rat.cast_add_of_ne_zero

/- warning: rat.cast_neg -> Rat.cast_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] (n : Rat), Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) (Neg.neg.{0} Rat Rat.hasNeg n)) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] (n : Rat), Eq.{succ u1} α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) (Neg.neg.{0} Rat Rat.instNegRat n)) (Neg.neg.{u1} α (Ring.toNeg.{u1} α (DivisionRing.toRing.{u1} α _inst_1)) (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) n))
Case conversion may be inaccurate. Consider using '#align rat.cast_neg Rat.cast_negₓ'. -/
@[simp, norm_cast]
theorem cast_neg : ∀ n, ((-n : ℚ) : α) = -n
  | ⟨n, d, h, c⟩ => by
    simpa only [cast_def] using
      show (↑(-n) / d : α) = -(n / d) by
        rw [div_eq_mul_inv, div_eq_mul_inv, Int.cast_neg, neg_mul_eq_neg_mul]
#align rat.cast_neg Rat.cast_neg

/- warning: rat.cast_sub_of_ne_zero -> Rat.cast_sub_of_ne_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] {m : Rat} {n : Rat}, (Ne.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))))) (Rat.den m)) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))))))) -> (Ne.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))))) (Rat.den n)) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))))))) -> (Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) (HSub.hSub.{0, 0, 0} Rat Rat Rat (instHSub.{0} Rat (SubNegMonoid.toHasSub.{0} Rat (AddGroup.toSubNegMonoid.{0} Rat Rat.addGroup))) m n)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) m) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) n)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] {m : Rat} {n : Rat}, (Ne.{succ u1} α (Nat.cast.{u1} α (NonAssocRing.toNatCast.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))) (Rat.den m)) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α _inst_1))))))) -> (Ne.{succ u1} α (Nat.cast.{u1} α (NonAssocRing.toNatCast.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))) (Rat.den n)) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α _inst_1))))))) -> (Eq.{succ u1} α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) (HSub.hSub.{0, 0, 0} Rat Rat Rat (instHSub.{0} Rat Rat.instSubRat) m n)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (Ring.toSub.{u1} α (DivisionRing.toRing.{u1} α _inst_1))) (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) m) (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) n)))
Case conversion may be inaccurate. Consider using '#align rat.cast_sub_of_ne_zero Rat.cast_sub_of_ne_zeroₓ'. -/
@[norm_cast]
theorem cast_sub_of_ne_zero {m n : ℚ} (m0 : (m.den : α) ≠ 0) (n0 : (n.den : α) ≠ 0) :
    ((m - n : ℚ) : α) = m - n :=
  by
  have : ((-n).den : α) ≠ 0 := by cases n <;> exact n0
  simp [sub_eq_add_neg, cast_add_of_ne_zero m0 this]
#align rat.cast_sub_of_ne_zero Rat.cast_sub_of_ne_zero

/- warning: rat.cast_mul_of_ne_zero -> Rat.cast_mul_of_ne_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] {m : Rat} {n : Rat}, (Ne.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))))) (Rat.den m)) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))))))) -> (Ne.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))))) (Rat.den n)) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))))))) -> (Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) (HMul.hMul.{0, 0, 0} Rat Rat Rat (instHMul.{0} Rat Rat.hasMul) m n)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) m) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) n)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] {m : Rat} {n : Rat}, (Ne.{succ u1} α (Nat.cast.{u1} α (NonAssocRing.toNatCast.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))) (Rat.den m)) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α _inst_1))))))) -> (Ne.{succ u1} α (Nat.cast.{u1} α (NonAssocRing.toNatCast.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))) (Rat.den n)) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α _inst_1))))))) -> (Eq.{succ u1} α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) (HMul.hMul.{0, 0, 0} Rat Rat Rat (instHMul.{0} Rat Rat.instMulRat) m n)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))) (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) m) (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) n)))
Case conversion may be inaccurate. Consider using '#align rat.cast_mul_of_ne_zero Rat.cast_mul_of_ne_zeroₓ'. -/
@[norm_cast]
theorem cast_mul_of_ne_zero :
    ∀ {m n : ℚ}, (m.den : α) ≠ 0 → (n.den : α) ≠ 0 → ((m * n : ℚ) : α) = m * n
  | ⟨n₁, d₁, h₁, c₁⟩, ⟨n₂, d₂, h₂, c₂⟩ => fun (d₁0 : (d₁ : α) ≠ 0) (d₂0 : (d₂ : α) ≠ 0) =>
    by
    have d₁0' : (d₁ : ℤ) ≠ 0 :=
      Int.coe_nat_ne_zero.2 fun e => by rw [e] at d₁0 <;> exact d₁0 Nat.cast_zero
    have d₂0' : (d₂ : ℤ) ≠ 0 :=
      Int.coe_nat_ne_zero.2 fun e => by rw [e] at d₂0 <;> exact d₂0 Nat.cast_zero
    rw [num_denom', num_denom', mul_def d₁0' d₂0']
    suffices (n₁ * (n₂ * d₂⁻¹ * d₁⁻¹) : α) = n₁ * (d₁⁻¹ * (n₂ * d₂⁻¹))
      by
      rw [cast_mk_of_ne_zero, cast_mk_of_ne_zero, cast_mk_of_ne_zero]
      · simpa [division_def, mul_inv_rev, d₁0, d₂0, mul_assoc]
      all_goals simp [d₁0, d₂0]
    rw [(d₁.commute_cast (_ : α)).inv_right₀.Eq]
#align rat.cast_mul_of_ne_zero Rat.cast_mul_of_ne_zero

/- warning: rat.cast_inv_nat -> Rat.cast_inv_nat is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] (n : Nat), Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) (Inv.inv.{0} Rat Rat.hasInv ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))))))) n))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionRing.toDivInvMonoid.{u1} α _inst_1)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))))) n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] (n : Nat), Eq.{succ u1} α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) (Inv.inv.{0} Rat Rat.instInvRat (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))) n))) (Inv.inv.{u1} α (DivisionRing.toInv.{u1} α _inst_1) (Nat.cast.{u1} α (NonAssocRing.toNatCast.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))) n))
Case conversion may be inaccurate. Consider using '#align rat.cast_inv_nat Rat.cast_inv_natₓ'. -/
@[simp]
theorem cast_inv_nat (n : ℕ) : ((n⁻¹ : ℚ) : α) = n⁻¹ :=
  by
  cases n; · simp
  simp_rw [coe_nat_eq_mk, inv_def, mk, mk_nat, dif_neg n.succ_ne_zero, mk_pnat]
  simp [cast_def]
#align rat.cast_inv_nat Rat.cast_inv_nat

/- warning: rat.cast_inv_int -> Rat.cast_inv_int is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] (n : Int), Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) (Inv.inv.{0} Rat Rat.hasInv ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Rat (HasLiftT.mk.{1, 1} Int Rat (CoeTCₓ.coe.{1, 1} Int Rat (Int.castCoe.{0} Rat Rat.hasIntCast))) n))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionRing.toDivInvMonoid.{u1} α _inst_1)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))))) n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] (n : Int), Eq.{succ u1} α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) (Inv.inv.{0} Rat Rat.instInvRat (Int.cast.{0} Rat Rat.instIntCastRat n))) (Inv.inv.{u1} α (DivisionRing.toInv.{u1} α _inst_1) (Int.cast.{u1} α (Ring.toIntCast.{u1} α (DivisionRing.toRing.{u1} α _inst_1)) n))
Case conversion may be inaccurate. Consider using '#align rat.cast_inv_int Rat.cast_inv_intₓ'. -/
@[simp]
theorem cast_inv_int (n : ℤ) : ((n⁻¹ : ℚ) : α) = n⁻¹ :=
  by
  cases n
  · simp [cast_inv_nat]
  · simp only [Int.cast_negSucc, ← Nat.cast_succ, cast_neg, inv_neg, cast_inv_nat]
#align rat.cast_inv_int Rat.cast_inv_int

/- warning: rat.cast_inv_of_ne_zero -> Rat.cast_inv_of_ne_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] {n : Rat}, (Ne.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))))) (Rat.num n)) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))))))) -> (Ne.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))))) (Rat.den n)) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))))))) -> (Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) (Inv.inv.{0} Rat Rat.hasInv n)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionRing.toDivInvMonoid.{u1} α _inst_1)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) n)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] {n : Rat}, (Ne.{succ u1} α (Int.cast.{u1} α (Ring.toIntCast.{u1} α (DivisionRing.toRing.{u1} α _inst_1)) (Rat.num n)) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α _inst_1))))))) -> (Ne.{succ u1} α (Nat.cast.{u1} α (NonAssocRing.toNatCast.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))) (Rat.den n)) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α _inst_1))))))) -> (Eq.{succ u1} α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) (Inv.inv.{0} Rat Rat.instInvRat n)) (Inv.inv.{u1} α (DivisionRing.toInv.{u1} α _inst_1) (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) n)))
Case conversion may be inaccurate. Consider using '#align rat.cast_inv_of_ne_zero Rat.cast_inv_of_ne_zeroₓ'. -/
@[norm_cast]
theorem cast_inv_of_ne_zero : ∀ {n : ℚ}, (n.num : α) ≠ 0 → (n.den : α) ≠ 0 → ((n⁻¹ : ℚ) : α) = n⁻¹
  | ⟨n, d, h, c⟩ => fun (n0 : (n : α) ≠ 0) (d0 : (d : α) ≠ 0) =>
    by
    have n0' : (n : ℤ) ≠ 0 := fun e => by rw [e] at n0 <;> exact n0 Int.cast_zero
    have d0' : (d : ℤ) ≠ 0 :=
      Int.coe_nat_ne_zero.2 fun e => by rw [e] at d0 <;> exact d0 Nat.cast_zero
    rw [num_denom', inv_def]
    rw [cast_mk_of_ne_zero, cast_mk_of_ne_zero, inv_div] <;> simp [n0, d0]
#align rat.cast_inv_of_ne_zero Rat.cast_inv_of_ne_zero

/- warning: rat.cast_div_of_ne_zero -> Rat.cast_div_of_ne_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] {m : Rat} {n : Rat}, (Ne.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))))) (Rat.den m)) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))))))) -> (Ne.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))))) (Rat.num n)) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))))))) -> (Ne.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))))) (Rat.den n)) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))))))) -> (Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.hasDiv) m n)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionRing.toDivInvMonoid.{u1} α _inst_1))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) m) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) n)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] {m : Rat} {n : Rat}, (Ne.{succ u1} α (Nat.cast.{u1} α (NonAssocRing.toNatCast.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))) (Rat.den m)) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α _inst_1))))))) -> (Ne.{succ u1} α (Int.cast.{u1} α (Ring.toIntCast.{u1} α (DivisionRing.toRing.{u1} α _inst_1)) (Rat.num n)) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α _inst_1))))))) -> (Ne.{succ u1} α (Nat.cast.{u1} α (NonAssocRing.toNatCast.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))) (Rat.den n)) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α _inst_1))))))) -> (Eq.{succ u1} α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.instDivRat) m n)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivisionRing.toDiv.{u1} α _inst_1)) (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) m) (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) n)))
Case conversion may be inaccurate. Consider using '#align rat.cast_div_of_ne_zero Rat.cast_div_of_ne_zeroₓ'. -/
@[norm_cast]
theorem cast_div_of_ne_zero {m n : ℚ} (md : (m.den : α) ≠ 0) (nn : (n.num : α) ≠ 0)
    (nd : (n.den : α) ≠ 0) : ((m / n : ℚ) : α) = m / n :=
  by
  have : (n⁻¹.den : ℤ) ∣ n.num := by
    conv in n⁻¹.den => rw [← @num_denom n, inv_def] <;> apply denom_dvd
  have : (n⁻¹.den : α) = 0 → (n.num : α) = 0 := fun h =>
    by
    let ⟨k, e⟩ := this
    have := congr_arg (coe : ℤ → α) e <;> rwa [Int.cast_mul, Int.cast_ofNat, h, zero_mul] at this
  rw [division_def, cast_mul_of_ne_zero md (mt this nn), cast_inv_of_ne_zero nn nd, division_def]
#align rat.cast_div_of_ne_zero Rat.cast_div_of_ne_zero

/- warning: rat.cast_inj -> Rat.cast_inj is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))] {m : Rat} {n : Rat}, Iff (Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) m) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) n)) (Eq.{1} Rat m n)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (Ring.toAddGroupWithOne.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))] {m : Rat} {n : Rat}, Iff (Eq.{succ u1} α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) m) (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) n)) (Eq.{1} Rat m n)
Case conversion may be inaccurate. Consider using '#align rat.cast_inj Rat.cast_injₓ'. -/
@[simp, norm_cast]
theorem cast_inj [CharZero α] : ∀ {m n : ℚ}, (m : α) = n ↔ m = n
  | ⟨n₁, d₁, h₁, c₁⟩, ⟨n₂, d₂, h₂, c₂⟩ =>
    by
    refine' ⟨fun h => _, congr_arg _⟩
    have d₁0 : d₁ ≠ 0 := ne_of_gt h₁
    have d₂0 : d₂ ≠ 0 := ne_of_gt h₂
    have d₁a : (d₁ : α) ≠ 0 := Nat.cast_ne_zero.2 d₁0
    have d₂a : (d₂ : α) ≠ 0 := Nat.cast_ne_zero.2 d₂0
    rw [num_denom', num_denom'] at h⊢
    rw [cast_mk_of_ne_zero, cast_mk_of_ne_zero] at h <;> simp [d₁0, d₂0] at h⊢
    rwa [eq_div_iff_mul_eq d₂a, division_def, mul_assoc, (d₁.cast_commute (d₂ : α)).inv_left₀.Eq, ←
      mul_assoc, ← division_def, eq_comm, eq_div_iff_mul_eq d₁a, eq_comm, ← Int.cast_ofNat d₁, ←
      Int.cast_mul, ← Int.cast_ofNat d₂, ← Int.cast_mul, Int.cast_inj, ←
      mk_eq (Int.coe_nat_ne_zero.2 d₁0) (Int.coe_nat_ne_zero.2 d₂0)] at h
#align rat.cast_inj Rat.cast_inj

/- warning: rat.cast_injective -> Rat.cast_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))], Function.Injective.{1, succ u1} Rat α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (Ring.toAddGroupWithOne.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))], Function.Injective.{1, succ u1} Rat α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align rat.cast_injective Rat.cast_injectiveₓ'. -/
theorem cast_injective [CharZero α] : Function.Injective (coe : ℚ → α)
  | m, n => cast_inj.1
#align rat.cast_injective Rat.cast_injective

/- warning: rat.cast_eq_zero -> Rat.cast_eq_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))] {n : Rat}, Iff (Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) n) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))))))) (Eq.{1} Rat n (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (Ring.toAddGroupWithOne.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))] {n : Rat}, Iff (Eq.{succ u1} α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) n) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α _inst_1))))))) (Eq.{1} Rat n (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)))
Case conversion may be inaccurate. Consider using '#align rat.cast_eq_zero Rat.cast_eq_zeroₓ'. -/
@[simp]
theorem cast_eq_zero [CharZero α] {n : ℚ} : (n : α) = 0 ↔ n = 0 := by rw [← cast_zero, cast_inj]
#align rat.cast_eq_zero Rat.cast_eq_zero

/- warning: rat.cast_ne_zero -> Rat.cast_ne_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))] {n : Rat}, Iff (Ne.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) n) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))))))) (Ne.{1} Rat n (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (Ring.toAddGroupWithOne.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))] {n : Rat}, Iff (Ne.{succ u1} α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) n) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α _inst_1))))))) (Ne.{1} Rat n (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)))
Case conversion may be inaccurate. Consider using '#align rat.cast_ne_zero Rat.cast_ne_zeroₓ'. -/
theorem cast_ne_zero [CharZero α] {n : ℚ} : (n : α) ≠ 0 ↔ n ≠ 0 :=
  not_congr cast_eq_zero
#align rat.cast_ne_zero Rat.cast_ne_zero

/- warning: rat.cast_add -> Rat.cast_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))] (m : Rat) (n : Rat), Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) (HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.hasAdd) m n)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) m) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (Ring.toAddGroupWithOne.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))] (m : Rat) (n : Rat), Eq.{succ u1} α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) (HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.instAddRat) m n)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))))) (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) m) (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) n))
Case conversion may be inaccurate. Consider using '#align rat.cast_add Rat.cast_addₓ'. -/
@[simp, norm_cast]
theorem cast_add [CharZero α] (m n) : ((m + n : ℚ) : α) = m + n :=
  cast_add_of_ne_zero (Nat.cast_ne_zero.2 <| ne_of_gt m.Pos) (Nat.cast_ne_zero.2 <| ne_of_gt n.Pos)
#align rat.cast_add Rat.cast_add

/- warning: rat.cast_sub -> Rat.cast_sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))] (m : Rat) (n : Rat), Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) (HSub.hSub.{0, 0, 0} Rat Rat Rat (instHSub.{0} Rat (SubNegMonoid.toHasSub.{0} Rat (AddGroup.toSubNegMonoid.{0} Rat Rat.addGroup))) m n)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) m) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (Ring.toAddGroupWithOne.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))] (m : Rat) (n : Rat), Eq.{succ u1} α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) (HSub.hSub.{0, 0, 0} Rat Rat Rat (instHSub.{0} Rat Rat.instSubRat) m n)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (Ring.toSub.{u1} α (DivisionRing.toRing.{u1} α _inst_1))) (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) m) (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) n))
Case conversion may be inaccurate. Consider using '#align rat.cast_sub Rat.cast_subₓ'. -/
@[simp, norm_cast]
theorem cast_sub [CharZero α] (m n) : ((m - n : ℚ) : α) = m - n :=
  cast_sub_of_ne_zero (Nat.cast_ne_zero.2 <| ne_of_gt m.Pos) (Nat.cast_ne_zero.2 <| ne_of_gt n.Pos)
#align rat.cast_sub Rat.cast_sub

/- warning: rat.cast_mul -> Rat.cast_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))] (m : Rat) (n : Rat), Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) (HMul.hMul.{0, 0, 0} Rat Rat Rat (instHMul.{0} Rat Rat.hasMul) m n)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) m) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (Ring.toAddGroupWithOne.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))] (m : Rat) (n : Rat), Eq.{succ u1} α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) (HMul.hMul.{0, 0, 0} Rat Rat Rat (instHMul.{0} Rat Rat.instMulRat) m n)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))) (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) m) (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) n))
Case conversion may be inaccurate. Consider using '#align rat.cast_mul Rat.cast_mulₓ'. -/
@[simp, norm_cast]
theorem cast_mul [CharZero α] (m n) : ((m * n : ℚ) : α) = m * n :=
  cast_mul_of_ne_zero (Nat.cast_ne_zero.2 <| ne_of_gt m.Pos) (Nat.cast_ne_zero.2 <| ne_of_gt n.Pos)
#align rat.cast_mul Rat.cast_mul

/- warning: rat.cast_bit0 -> Rat.cast_bit0 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))] (n : Rat), Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) (bit0.{0} Rat Rat.hasAdd n)) (bit0.{u1} α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α (DivisionRing.toRing.{u1} α _inst_1))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (Ring.toAddGroupWithOne.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))] (n : Rat), Eq.{succ u1} α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) (bit0.{0} Rat Rat.instAddRat n)) (bit0.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))) (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) n))
Case conversion may be inaccurate. Consider using '#align rat.cast_bit0 Rat.cast_bit0ₓ'. -/
@[simp, norm_cast]
theorem cast_bit0 [CharZero α] (n : ℚ) : ((bit0 n : ℚ) : α) = bit0 n :=
  cast_add _ _
#align rat.cast_bit0 Rat.cast_bit0

/- warning: rat.cast_bit1 -> Rat.cast_bit1 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))] (n : Rat), Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) (bit1.{0} Rat Rat.hasOne Rat.hasAdd n)) (bit1.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))) (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α (DivisionRing.toRing.{u1} α _inst_1))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (Ring.toAddGroupWithOne.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))] (n : Rat), Eq.{succ u1} α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) (bit1.{0} Rat (NonAssocRing.toOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))) Rat.instAddRat n)) (bit1.{u1} α (NonAssocRing.toOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))) (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))) (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) n))
Case conversion may be inaccurate. Consider using '#align rat.cast_bit1 Rat.cast_bit1ₓ'. -/
@[simp, norm_cast]
theorem cast_bit1 [CharZero α] (n : ℚ) : ((bit1 n : ℚ) : α) = bit1 n := by
  rw [bit1, cast_add, cast_one, cast_bit0] <;> rfl
#align rat.cast_bit1 Rat.cast_bit1

variable (α) [CharZero α]

/- warning: rat.cast_hom -> Rat.castHom is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))], RingHom.{0, u1} Rat α (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing)))) (NonAssocRing.toNonAssocSemiring.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (Ring.toAddGroupWithOne.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))], RingHom.{0, u1} Rat α (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))) (NonAssocRing.toNonAssocSemiring.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align rat.cast_hom Rat.castHomₓ'. -/
/-- Coercion `ℚ → α` as a `ring_hom`. -/
def castHom : ℚ →+* α :=
  ⟨coe, cast_one, cast_mul, cast_zero, cast_add⟩
#align rat.cast_hom Rat.castHom

variable {α}

/- warning: rat.coe_cast_hom -> Rat.coe_cast_hom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))], Eq.{succ u1} (Rat -> α) (coeFn.{succ u1, succ u1} (RingHom.{0, u1} Rat α (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing)))) (NonAssocRing.toNonAssocSemiring.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))) (fun (_x : RingHom.{0, u1} Rat α (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing)))) (NonAssocRing.toNonAssocSemiring.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))) => Rat -> α) (RingHom.hasCoeToFun.{0, u1} Rat α (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing)))) (NonAssocRing.toNonAssocSemiring.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))) (Rat.castHom.{u1} α _inst_1 _inst_2)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (Ring.toAddGroupWithOne.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))], Eq.{succ u1} (forall (ᾰ : Rat), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Rat) => α) ᾰ) (FunLike.coe.{succ u1, 1, succ u1} (RingHom.{0, u1} Rat α (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))) (NonAssocRing.toNonAssocSemiring.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))) Rat (fun (_x : Rat) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Rat) => α) _x) (MulHomClass.toFunLike.{u1, 0, u1} (RingHom.{0, u1} Rat α (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))) (NonAssocRing.toNonAssocSemiring.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))) Rat α (NonUnitalNonAssocSemiring.toMul.{0} Rat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))))) (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonAssocSemiring.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))) (NonUnitalRingHomClass.toMulHomClass.{u1, 0, u1} (RingHom.{0, u1} Rat α (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))) (NonAssocRing.toNonAssocSemiring.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))) Rat α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonAssocSemiring.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))) (RingHomClass.toNonUnitalRingHomClass.{u1, 0, u1} (RingHom.{0, u1} Rat α (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))) (NonAssocRing.toNonAssocSemiring.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))) Rat α (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))) (NonAssocRing.toNonAssocSemiring.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))) (RingHom.instRingHomClassRingHom.{0, u1} Rat α (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))) (NonAssocRing.toNonAssocSemiring.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))))) (Rat.castHom.{u1} α _inst_1 _inst_2)) (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align rat.coe_cast_hom Rat.coe_cast_homₓ'. -/
@[simp]
theorem coe_cast_hom : ⇑(castHom α) = coe :=
  rfl
#align rat.coe_cast_hom Rat.coe_cast_hom

/- warning: rat.cast_inv -> Rat.cast_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))] (n : Rat), Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) (Inv.inv.{0} Rat Rat.hasInv n)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionRing.toDivInvMonoid.{u1} α _inst_1)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (Ring.toAddGroupWithOne.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))] (n : Rat), Eq.{succ u1} α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) (Inv.inv.{0} Rat Rat.instInvRat n)) (Inv.inv.{u1} α (DivisionRing.toInv.{u1} α _inst_1) (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) n))
Case conversion may be inaccurate. Consider using '#align rat.cast_inv Rat.cast_invₓ'. -/
@[simp, norm_cast]
theorem cast_inv (n) : ((n⁻¹ : ℚ) : α) = n⁻¹ :=
  map_inv₀ (castHom α) _
#align rat.cast_inv Rat.cast_inv

/- warning: rat.cast_div -> Rat.cast_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))] (m : Rat) (n : Rat), Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.hasDiv) m n)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionRing.toDivInvMonoid.{u1} α _inst_1))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) m) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (Ring.toAddGroupWithOne.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))] (m : Rat) (n : Rat), Eq.{succ u1} α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.instDivRat) m n)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivisionRing.toDiv.{u1} α _inst_1)) (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) m) (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) n))
Case conversion may be inaccurate. Consider using '#align rat.cast_div Rat.cast_divₓ'. -/
@[simp, norm_cast]
theorem cast_div (m n) : ((m / n : ℚ) : α) = m / n :=
  map_div₀ (castHom α) _ _
#align rat.cast_div Rat.cast_div

/- warning: rat.cast_zpow -> Rat.cast_zpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))] (q : Rat) (n : Int), Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) (HPow.hPow.{0, 0, 0} Rat Int Rat (instHPow.{0, 0} Rat Int (DivInvMonoid.Pow.{0} Rat (DivisionRing.toDivInvMonoid.{0} Rat Rat.divisionRing))) q n)) (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (DivisionRing.toDivInvMonoid.{u1} α _inst_1))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) q) n)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (Ring.toAddGroupWithOne.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))] (q : Rat) (n : Int), Eq.{succ u1} α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) (HPow.hPow.{0, 0, 0} Rat Int Rat (instHPow.{0, 0} Rat Int (DivInvMonoid.Pow.{0} Rat (DivisionRing.toDivInvMonoid.{0} Rat Rat.divisionRing))) q n)) (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (DivisionRing.toDivInvMonoid.{u1} α _inst_1))) (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) q) n)
Case conversion may be inaccurate. Consider using '#align rat.cast_zpow Rat.cast_zpowₓ'. -/
@[simp, norm_cast]
theorem cast_zpow (q : ℚ) (n : ℤ) : ((q ^ n : ℚ) : α) = q ^ n :=
  map_zpow₀ (castHom α) q n
#align rat.cast_zpow Rat.cast_zpow

/- warning: rat.cast_mk -> Rat.cast_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))] (a : Int) (b : Int), Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) (Rat.mk a b)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionRing.toDivInvMonoid.{u1} α _inst_1))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))))) a) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))))) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (Ring.toAddGroupWithOne.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))] (a : Int) (b : Int), Eq.{succ u1} α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) (Rat.divInt a b)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivisionRing.toDiv.{u1} α _inst_1)) (Int.cast.{u1} α (Ring.toIntCast.{u1} α (DivisionRing.toRing.{u1} α _inst_1)) a) (Int.cast.{u1} α (Ring.toIntCast.{u1} α (DivisionRing.toRing.{u1} α _inst_1)) b))
Case conversion may be inaccurate. Consider using '#align rat.cast_mk Rat.cast_mkₓ'. -/
@[norm_cast]
theorem cast_mk (a b : ℤ) : (a /. b : α) = a / b := by simp only [mk_eq_div, cast_div, cast_coe_int]
#align rat.cast_mk Rat.cast_mk

/- warning: rat.cast_pow -> Rat.cast_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))] (q : Rat) (k : Nat), Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) (HPow.hPow.{0, 0, 0} Rat Nat Rat (instHPow.{0, 0} Rat Nat (Monoid.Pow.{0} Rat Rat.monoid)) q k)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (Ring.toMonoid.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) q) k)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (Ring.toAddGroupWithOne.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))] (q : Rat) (k : Nat), Eq.{succ u1} α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) (HPow.hPow.{0, 0, 0} Rat Nat Rat (instHPow.{0, 0} Rat Nat (Monoid.Pow.{0} Rat Rat.monoid)) q k)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α _inst_1)))))) (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) q) k)
Case conversion may be inaccurate. Consider using '#align rat.cast_pow Rat.cast_powₓ'. -/
@[simp, norm_cast]
theorem cast_pow (q) (k : ℕ) : ((q ^ k : ℚ) : α) = q ^ k :=
  (castHom α).map_pow q k
#align rat.cast_pow Rat.cast_pow

end WithDivRing

section LinearOrderedField

variable {K : Type _} [LinearOrderedField K]

/- warning: rat.cast_pos_of_pos -> Rat.cast_pos_of_pos is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] {r : Rat}, (LT.lt.{0} Rat Rat.hasLt (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) r) -> (LT.lt.{u1} K (Preorder.toLT.{u1} K (PartialOrder.toPreorder.{u1} K (OrderedAddCommGroup.toPartialOrder.{u1} K (StrictOrderedRing.toOrderedAddCommGroup.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))))) (OfNat.ofNat.{u1} K 0 (OfNat.mk.{u1} K 0 (Zero.zero.{u1} K (MulZeroClass.toHasZero.{u1} K (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (StrictOrderedRing.toRing.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)))))))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))) r))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] {r : Rat}, (LT.lt.{0} Rat Rat.instLTRat_1 (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) r) -> (LT.lt.{u1} K (Preorder.toLT.{u1} K (PartialOrder.toPreorder.{u1} K (StrictOrderedRing.toPartialOrder.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)))))) (OfNat.ofNat.{u1} K 0 (Zero.toOfNat0.{u1} K (CommMonoidWithZero.toZero.{u1} K (CommGroupWithZero.toCommMonoidWithZero.{u1} K (Semifield.toCommGroupWithZero.{u1} K (LinearOrderedSemifield.toSemifield.{u1} K (LinearOrderedField.toLinearOrderedSemifield.{u1} K _inst_1))))))) (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1) r))
Case conversion may be inaccurate. Consider using '#align rat.cast_pos_of_pos Rat.cast_pos_of_posₓ'. -/
theorem cast_pos_of_pos {r : ℚ} (hr : 0 < r) : (0 : K) < r :=
  by
  rw [Rat.cast_def]
  exact div_pos (Int.cast_pos.2 <| num_pos_iff_pos.2 hr) (Nat.cast_pos.2 r.pos)
#align rat.cast_pos_of_pos Rat.cast_pos_of_pos

/- warning: rat.cast_strict_mono -> Rat.cast_strictMono is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K], StrictMono.{0, u1} Rat K Rat.preorder (PartialOrder.toPreorder.{u1} K (OrderedAddCommGroup.toPartialOrder.{u1} K (StrictOrderedRing.toOrderedAddCommGroup.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K], StrictMono.{0, u1} Rat K Rat.instPreorderRat (PartialOrder.toPreorder.{u1} K (StrictOrderedRing.toPartialOrder.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))) (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1))
Case conversion may be inaccurate. Consider using '#align rat.cast_strict_mono Rat.cast_strictMonoₓ'. -/
@[mono]
theorem cast_strictMono : StrictMono (coe : ℚ → K) := fun m n => by
  simpa only [sub_pos, cast_sub] using @cast_pos_of_pos K _ (n - m)
#align rat.cast_strict_mono Rat.cast_strictMono

/- warning: rat.cast_mono -> Rat.cast_mono is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K], Monotone.{0, u1} Rat K Rat.preorder (PartialOrder.toPreorder.{u1} K (OrderedAddCommGroup.toPartialOrder.{u1} K (StrictOrderedRing.toOrderedAddCommGroup.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K], Monotone.{0, u1} Rat K Rat.instPreorderRat (PartialOrder.toPreorder.{u1} K (StrictOrderedRing.toPartialOrder.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))) (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1))
Case conversion may be inaccurate. Consider using '#align rat.cast_mono Rat.cast_monoₓ'. -/
@[mono]
theorem cast_mono : Monotone (coe : ℚ → K) :=
  cast_strictMono.Monotone
#align rat.cast_mono Rat.cast_mono

/- warning: rat.cast_order_embedding -> Rat.castOrderEmbedding is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K], OrderEmbedding.{0, u1} Rat K Rat.hasLe (Preorder.toLE.{u1} K (PartialOrder.toPreorder.{u1} K (OrderedAddCommGroup.toPartialOrder.{u1} K (StrictOrderedRing.toOrderedAddCommGroup.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)))))))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K], OrderEmbedding.{0, u1} Rat K Rat.instLERat (Preorder.toLE.{u1} K (PartialOrder.toPreorder.{u1} K (StrictOrderedRing.toPartialOrder.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))))
Case conversion may be inaccurate. Consider using '#align rat.cast_order_embedding Rat.castOrderEmbeddingₓ'. -/
/-- Coercion from `ℚ` as an order embedding. -/
@[simps]
def castOrderEmbedding : ℚ ↪o K :=
  OrderEmbedding.ofStrictMono coe cast_strictMono
#align rat.cast_order_embedding Rat.castOrderEmbedding

/- warning: rat.cast_le -> Rat.cast_le is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] {m : Rat} {n : Rat}, Iff (LE.le.{u1} K (Preorder.toLE.{u1} K (PartialOrder.toPreorder.{u1} K (OrderedAddCommGroup.toPartialOrder.{u1} K (StrictOrderedRing.toOrderedAddCommGroup.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))) m) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))) n)) (LE.le.{0} Rat Rat.hasLe m n)
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] {m : Rat} {n : Rat}, Iff (LE.le.{u1} K (Preorder.toLE.{u1} K (PartialOrder.toPreorder.{u1} K (StrictOrderedRing.toPartialOrder.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)))))) (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1) m) (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1) n)) (LE.le.{0} Rat Rat.instLERat m n)
Case conversion may be inaccurate. Consider using '#align rat.cast_le Rat.cast_leₓ'. -/
@[simp, norm_cast]
theorem cast_le {m n : ℚ} : (m : K) ≤ n ↔ m ≤ n :=
  castOrderEmbedding.le_iff_le
#align rat.cast_le Rat.cast_le

/- warning: rat.cast_lt -> Rat.cast_lt is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] {m : Rat} {n : Rat}, Iff (LT.lt.{u1} K (Preorder.toLT.{u1} K (PartialOrder.toPreorder.{u1} K (OrderedAddCommGroup.toPartialOrder.{u1} K (StrictOrderedRing.toOrderedAddCommGroup.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))) m) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))) n)) (LT.lt.{0} Rat Rat.hasLt m n)
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] {m : Rat} {n : Rat}, Iff (LT.lt.{u1} K (Preorder.toLT.{u1} K (PartialOrder.toPreorder.{u1} K (StrictOrderedRing.toPartialOrder.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)))))) (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1) m) (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1) n)) (LT.lt.{0} Rat Rat.instLTRat_1 m n)
Case conversion may be inaccurate. Consider using '#align rat.cast_lt Rat.cast_ltₓ'. -/
@[simp, norm_cast]
theorem cast_lt {m n : ℚ} : (m : K) < n ↔ m < n :=
  cast_strictMono.lt_iff_lt
#align rat.cast_lt Rat.cast_lt

/- warning: rat.cast_nonneg -> Rat.cast_nonneg is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] {n : Rat}, Iff (LE.le.{u1} K (Preorder.toLE.{u1} K (PartialOrder.toPreorder.{u1} K (OrderedAddCommGroup.toPartialOrder.{u1} K (StrictOrderedRing.toOrderedAddCommGroup.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))))) (OfNat.ofNat.{u1} K 0 (OfNat.mk.{u1} K 0 (Zero.zero.{u1} K (MulZeroClass.toHasZero.{u1} K (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (StrictOrderedRing.toRing.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)))))))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))) n)) (LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) n)
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] {n : Rat}, Iff (LE.le.{u1} K (Preorder.toLE.{u1} K (PartialOrder.toPreorder.{u1} K (StrictOrderedRing.toPartialOrder.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)))))) (OfNat.ofNat.{u1} K 0 (Zero.toOfNat0.{u1} K (CommMonoidWithZero.toZero.{u1} K (CommGroupWithZero.toCommMonoidWithZero.{u1} K (Semifield.toCommGroupWithZero.{u1} K (LinearOrderedSemifield.toSemifield.{u1} K (LinearOrderedField.toLinearOrderedSemifield.{u1} K _inst_1))))))) (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1) n)) (LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) n)
Case conversion may be inaccurate. Consider using '#align rat.cast_nonneg Rat.cast_nonnegₓ'. -/
@[simp]
theorem cast_nonneg {n : ℚ} : 0 ≤ (n : K) ↔ 0 ≤ n := by norm_cast
#align rat.cast_nonneg Rat.cast_nonneg

/- warning: rat.cast_nonpos -> Rat.cast_nonpos is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] {n : Rat}, Iff (LE.le.{u1} K (Preorder.toLE.{u1} K (PartialOrder.toPreorder.{u1} K (OrderedAddCommGroup.toPartialOrder.{u1} K (StrictOrderedRing.toOrderedAddCommGroup.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))) n) (OfNat.ofNat.{u1} K 0 (OfNat.mk.{u1} K 0 (Zero.zero.{u1} K (MulZeroClass.toHasZero.{u1} K (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (StrictOrderedRing.toRing.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))))))))))) (LE.le.{0} Rat Rat.hasLe n (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] {n : Rat}, Iff (LE.le.{u1} K (Preorder.toLE.{u1} K (PartialOrder.toPreorder.{u1} K (StrictOrderedRing.toPartialOrder.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)))))) (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1) n) (OfNat.ofNat.{u1} K 0 (Zero.toOfNat0.{u1} K (CommMonoidWithZero.toZero.{u1} K (CommGroupWithZero.toCommMonoidWithZero.{u1} K (Semifield.toCommGroupWithZero.{u1} K (LinearOrderedSemifield.toSemifield.{u1} K (LinearOrderedField.toLinearOrderedSemifield.{u1} K _inst_1)))))))) (LE.le.{0} Rat Rat.instLERat n (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)))
Case conversion may be inaccurate. Consider using '#align rat.cast_nonpos Rat.cast_nonposₓ'. -/
@[simp]
theorem cast_nonpos {n : ℚ} : (n : K) ≤ 0 ↔ n ≤ 0 := by norm_cast
#align rat.cast_nonpos Rat.cast_nonpos

/- warning: rat.cast_pos -> Rat.cast_pos is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] {n : Rat}, Iff (LT.lt.{u1} K (Preorder.toLT.{u1} K (PartialOrder.toPreorder.{u1} K (OrderedAddCommGroup.toPartialOrder.{u1} K (StrictOrderedRing.toOrderedAddCommGroup.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))))) (OfNat.ofNat.{u1} K 0 (OfNat.mk.{u1} K 0 (Zero.zero.{u1} K (MulZeroClass.toHasZero.{u1} K (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (StrictOrderedRing.toRing.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)))))))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))) n)) (LT.lt.{0} Rat Rat.hasLt (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) n)
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] {n : Rat}, Iff (LT.lt.{u1} K (Preorder.toLT.{u1} K (PartialOrder.toPreorder.{u1} K (StrictOrderedRing.toPartialOrder.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)))))) (OfNat.ofNat.{u1} K 0 (Zero.toOfNat0.{u1} K (CommMonoidWithZero.toZero.{u1} K (CommGroupWithZero.toCommMonoidWithZero.{u1} K (Semifield.toCommGroupWithZero.{u1} K (LinearOrderedSemifield.toSemifield.{u1} K (LinearOrderedField.toLinearOrderedSemifield.{u1} K _inst_1))))))) (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1) n)) (LT.lt.{0} Rat Rat.instLTRat_1 (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) n)
Case conversion may be inaccurate. Consider using '#align rat.cast_pos Rat.cast_posₓ'. -/
@[simp]
theorem cast_pos {n : ℚ} : (0 : K) < n ↔ 0 < n := by norm_cast
#align rat.cast_pos Rat.cast_pos

/- warning: rat.cast_lt_zero -> Rat.cast_lt_zero is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] {n : Rat}, Iff (LT.lt.{u1} K (Preorder.toLT.{u1} K (PartialOrder.toPreorder.{u1} K (OrderedAddCommGroup.toPartialOrder.{u1} K (StrictOrderedRing.toOrderedAddCommGroup.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))) n) (OfNat.ofNat.{u1} K 0 (OfNat.mk.{u1} K 0 (Zero.zero.{u1} K (MulZeroClass.toHasZero.{u1} K (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (StrictOrderedRing.toRing.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))))))))))) (LT.lt.{0} Rat Rat.hasLt n (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] {n : Rat}, Iff (LT.lt.{u1} K (Preorder.toLT.{u1} K (PartialOrder.toPreorder.{u1} K (StrictOrderedRing.toPartialOrder.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)))))) (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1) n) (OfNat.ofNat.{u1} K 0 (Zero.toOfNat0.{u1} K (CommMonoidWithZero.toZero.{u1} K (CommGroupWithZero.toCommMonoidWithZero.{u1} K (Semifield.toCommGroupWithZero.{u1} K (LinearOrderedSemifield.toSemifield.{u1} K (LinearOrderedField.toLinearOrderedSemifield.{u1} K _inst_1)))))))) (LT.lt.{0} Rat Rat.instLTRat_1 n (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)))
Case conversion may be inaccurate. Consider using '#align rat.cast_lt_zero Rat.cast_lt_zeroₓ'. -/
@[simp]
theorem cast_lt_zero {n : ℚ} : (n : K) < 0 ↔ n < 0 := by norm_cast
#align rat.cast_lt_zero Rat.cast_lt_zero

/- warning: rat.cast_min -> Rat.cast_min is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] {a : Rat} {b : Rat}, Eq.{succ u1} K ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))) (LinearOrder.min.{0} Rat Rat.linearOrder a b)) (LinearOrder.min.{u1} K (LinearOrderedRing.toLinearOrder.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))) a) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))) b))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] {a : Rat} {b : Rat}, Eq.{succ u1} K (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1) (Min.min.{0} Rat (LinearOrderedRing.toMin.{0} Rat Rat.instLinearOrderedRingRat) a b)) (Min.min.{u1} K (LinearOrderedRing.toMin.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))) (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1) a) (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1) b))
Case conversion may be inaccurate. Consider using '#align rat.cast_min Rat.cast_minₓ'. -/
@[simp, norm_cast]
theorem cast_min {a b : ℚ} : (↑(min a b) : K) = min a b :=
  (@cast_mono K _).map_min
#align rat.cast_min Rat.cast_min

/- warning: rat.cast_max -> Rat.cast_max is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] {a : Rat} {b : Rat}, Eq.{succ u1} K ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))) (LinearOrder.max.{0} Rat Rat.linearOrder a b)) (LinearOrder.max.{u1} K (LinearOrderedRing.toLinearOrder.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))) a) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))) b))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] {a : Rat} {b : Rat}, Eq.{succ u1} K (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1) (Max.max.{0} Rat (LinearOrderedRing.toMax.{0} Rat Rat.instLinearOrderedRingRat) a b)) (Max.max.{u1} K (LinearOrderedRing.toMax.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))) (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1) a) (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1) b))
Case conversion may be inaccurate. Consider using '#align rat.cast_max Rat.cast_maxₓ'. -/
@[simp, norm_cast]
theorem cast_max {a b : ℚ} : (↑(max a b) : K) = max a b :=
  (@cast_mono K _).map_max
#align rat.cast_max Rat.cast_max

/- warning: rat.cast_abs -> Rat.cast_abs is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] {q : Rat}, Eq.{succ u1} K ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup) q)) (Abs.abs.{u1} K (Neg.toHasAbs.{u1} K (SubNegMonoid.toHasNeg.{u1} K (AddGroup.toSubNegMonoid.{u1} K (AddGroupWithOne.toAddGroup.{u1} K (NonAssocRing.toAddGroupWithOne.{u1} K (Ring.toNonAssocRing.{u1} K (StrictOrderedRing.toRing.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))))))) (SemilatticeSup.toHasSup.{u1} K (Lattice.toSemilatticeSup.{u1} K (LinearOrder.toLattice.{u1} K (LinearOrderedRing.toLinearOrder.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))) q))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] {q : Rat}, Eq.{succ u1} K (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat) q)) (Abs.abs.{u1} K (Neg.toHasAbs.{u1} K (Ring.toNeg.{u1} K (StrictOrderedRing.toRing.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))) (SemilatticeSup.toHasSup.{u1} K (Lattice.toSemilatticeSup.{u1} K (DistribLattice.toLattice.{u1} K (instDistribLattice.{u1} K (LinearOrderedRing.toLinearOrder.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)))))))) (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1) q))
Case conversion may be inaccurate. Consider using '#align rat.cast_abs Rat.cast_absₓ'. -/
@[simp, norm_cast]
theorem cast_abs {q : ℚ} : ((|q| : ℚ) : K) = |q| := by simp [abs_eq_max_neg]
#align rat.cast_abs Rat.cast_abs

open Set

/- warning: rat.preimage_cast_Icc -> Rat.preimage_cast_Icc is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] (a : Rat) (b : Rat), Eq.{1} (Set.{0} Rat) (Set.preimage.{0, u1} Rat K ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1))))))) (Set.Icc.{u1} K (PartialOrder.toPreorder.{u1} K (OrderedAddCommGroup.toPartialOrder.{u1} K (StrictOrderedRing.toOrderedAddCommGroup.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))) a) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))) b))) (Set.Icc.{0} Rat Rat.preorder a b)
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] (a : Rat) (b : Rat), Eq.{1} (Set.{0} Rat) (Set.preimage.{0, u1} Rat K (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1)) (Set.Icc.{u1} K (PartialOrder.toPreorder.{u1} K (StrictOrderedRing.toPartialOrder.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))) (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1) a) (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1) b))) (Set.Icc.{0} Rat Rat.instPreorderRat a b)
Case conversion may be inaccurate. Consider using '#align rat.preimage_cast_Icc Rat.preimage_cast_Iccₓ'. -/
@[simp]
theorem preimage_cast_Icc (a b : ℚ) : coe ⁻¹' Icc (a : K) b = Icc a b :=
  by
  ext x
  simp
#align rat.preimage_cast_Icc Rat.preimage_cast_Icc

/- warning: rat.preimage_cast_Ico -> Rat.preimage_cast_Ico is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] (a : Rat) (b : Rat), Eq.{1} (Set.{0} Rat) (Set.preimage.{0, u1} Rat K ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1))))))) (Set.Ico.{u1} K (PartialOrder.toPreorder.{u1} K (OrderedAddCommGroup.toPartialOrder.{u1} K (StrictOrderedRing.toOrderedAddCommGroup.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))) a) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))) b))) (Set.Ico.{0} Rat Rat.preorder a b)
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] (a : Rat) (b : Rat), Eq.{1} (Set.{0} Rat) (Set.preimage.{0, u1} Rat K (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1)) (Set.Ico.{u1} K (PartialOrder.toPreorder.{u1} K (StrictOrderedRing.toPartialOrder.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))) (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1) a) (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1) b))) (Set.Ico.{0} Rat Rat.instPreorderRat a b)
Case conversion may be inaccurate. Consider using '#align rat.preimage_cast_Ico Rat.preimage_cast_Icoₓ'. -/
@[simp]
theorem preimage_cast_Ico (a b : ℚ) : coe ⁻¹' Ico (a : K) b = Ico a b :=
  by
  ext x
  simp
#align rat.preimage_cast_Ico Rat.preimage_cast_Ico

/- warning: rat.preimage_cast_Ioc -> Rat.preimage_cast_Ioc is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] (a : Rat) (b : Rat), Eq.{1} (Set.{0} Rat) (Set.preimage.{0, u1} Rat K ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1))))))) (Set.Ioc.{u1} K (PartialOrder.toPreorder.{u1} K (OrderedAddCommGroup.toPartialOrder.{u1} K (StrictOrderedRing.toOrderedAddCommGroup.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))) a) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))) b))) (Set.Ioc.{0} Rat Rat.preorder a b)
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] (a : Rat) (b : Rat), Eq.{1} (Set.{0} Rat) (Set.preimage.{0, u1} Rat K (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1)) (Set.Ioc.{u1} K (PartialOrder.toPreorder.{u1} K (StrictOrderedRing.toPartialOrder.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))) (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1) a) (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1) b))) (Set.Ioc.{0} Rat Rat.instPreorderRat a b)
Case conversion may be inaccurate. Consider using '#align rat.preimage_cast_Ioc Rat.preimage_cast_Iocₓ'. -/
@[simp]
theorem preimage_cast_Ioc (a b : ℚ) : coe ⁻¹' Ioc (a : K) b = Ioc a b :=
  by
  ext x
  simp
#align rat.preimage_cast_Ioc Rat.preimage_cast_Ioc

/- warning: rat.preimage_cast_Ioo -> Rat.preimage_cast_Ioo is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] (a : Rat) (b : Rat), Eq.{1} (Set.{0} Rat) (Set.preimage.{0, u1} Rat K ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1))))))) (Set.Ioo.{u1} K (PartialOrder.toPreorder.{u1} K (OrderedAddCommGroup.toPartialOrder.{u1} K (StrictOrderedRing.toOrderedAddCommGroup.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))) a) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))) b))) (Set.Ioo.{0} Rat Rat.preorder a b)
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] (a : Rat) (b : Rat), Eq.{1} (Set.{0} Rat) (Set.preimage.{0, u1} Rat K (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1)) (Set.Ioo.{u1} K (PartialOrder.toPreorder.{u1} K (StrictOrderedRing.toPartialOrder.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))) (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1) a) (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1) b))) (Set.Ioo.{0} Rat Rat.instPreorderRat a b)
Case conversion may be inaccurate. Consider using '#align rat.preimage_cast_Ioo Rat.preimage_cast_Iooₓ'. -/
@[simp]
theorem preimage_cast_Ioo (a b : ℚ) : coe ⁻¹' Ioo (a : K) b = Ioo a b :=
  by
  ext x
  simp
#align rat.preimage_cast_Ioo Rat.preimage_cast_Ioo

/- warning: rat.preimage_cast_Ici -> Rat.preimage_cast_Ici is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] (a : Rat), Eq.{1} (Set.{0} Rat) (Set.preimage.{0, u1} Rat K ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1))))))) (Set.Ici.{u1} K (PartialOrder.toPreorder.{u1} K (OrderedAddCommGroup.toPartialOrder.{u1} K (StrictOrderedRing.toOrderedAddCommGroup.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))) a))) (Set.Ici.{0} Rat Rat.preorder a)
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] (a : Rat), Eq.{1} (Set.{0} Rat) (Set.preimage.{0, u1} Rat K (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1)) (Set.Ici.{u1} K (PartialOrder.toPreorder.{u1} K (StrictOrderedRing.toPartialOrder.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))) (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1) a))) (Set.Ici.{0} Rat Rat.instPreorderRat a)
Case conversion may be inaccurate. Consider using '#align rat.preimage_cast_Ici Rat.preimage_cast_Iciₓ'. -/
@[simp]
theorem preimage_cast_Ici (a : ℚ) : coe ⁻¹' Ici (a : K) = Ici a :=
  by
  ext x
  simp
#align rat.preimage_cast_Ici Rat.preimage_cast_Ici

/- warning: rat.preimage_cast_Iic -> Rat.preimage_cast_Iic is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] (a : Rat), Eq.{1} (Set.{0} Rat) (Set.preimage.{0, u1} Rat K ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1))))))) (Set.Iic.{u1} K (PartialOrder.toPreorder.{u1} K (OrderedAddCommGroup.toPartialOrder.{u1} K (StrictOrderedRing.toOrderedAddCommGroup.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))) a))) (Set.Iic.{0} Rat Rat.preorder a)
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] (a : Rat), Eq.{1} (Set.{0} Rat) (Set.preimage.{0, u1} Rat K (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1)) (Set.Iic.{u1} K (PartialOrder.toPreorder.{u1} K (StrictOrderedRing.toPartialOrder.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))) (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1) a))) (Set.Iic.{0} Rat Rat.instPreorderRat a)
Case conversion may be inaccurate. Consider using '#align rat.preimage_cast_Iic Rat.preimage_cast_Iicₓ'. -/
@[simp]
theorem preimage_cast_Iic (a : ℚ) : coe ⁻¹' Iic (a : K) = Iic a :=
  by
  ext x
  simp
#align rat.preimage_cast_Iic Rat.preimage_cast_Iic

/- warning: rat.preimage_cast_Ioi -> Rat.preimage_cast_Ioi is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] (a : Rat), Eq.{1} (Set.{0} Rat) (Set.preimage.{0, u1} Rat K ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1))))))) (Set.Ioi.{u1} K (PartialOrder.toPreorder.{u1} K (OrderedAddCommGroup.toPartialOrder.{u1} K (StrictOrderedRing.toOrderedAddCommGroup.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))) a))) (Set.Ioi.{0} Rat Rat.preorder a)
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] (a : Rat), Eq.{1} (Set.{0} Rat) (Set.preimage.{0, u1} Rat K (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1)) (Set.Ioi.{u1} K (PartialOrder.toPreorder.{u1} K (StrictOrderedRing.toPartialOrder.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))) (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1) a))) (Set.Ioi.{0} Rat Rat.instPreorderRat a)
Case conversion may be inaccurate. Consider using '#align rat.preimage_cast_Ioi Rat.preimage_cast_Ioiₓ'. -/
@[simp]
theorem preimage_cast_Ioi (a : ℚ) : coe ⁻¹' Ioi (a : K) = Ioi a :=
  by
  ext x
  simp
#align rat.preimage_cast_Ioi Rat.preimage_cast_Ioi

/- warning: rat.preimage_cast_Iio -> Rat.preimage_cast_Iio is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] (a : Rat), Eq.{1} (Set.{0} Rat) (Set.preimage.{0, u1} Rat K ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1))))))) (Set.Iio.{u1} K (PartialOrder.toPreorder.{u1} K (OrderedAddCommGroup.toPartialOrder.{u1} K (StrictOrderedRing.toOrderedAddCommGroup.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))) a))) (Set.Iio.{0} Rat Rat.preorder a)
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] (a : Rat), Eq.{1} (Set.{0} Rat) (Set.preimage.{0, u1} Rat K (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1)) (Set.Iio.{u1} K (PartialOrder.toPreorder.{u1} K (StrictOrderedRing.toPartialOrder.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))) (RatCast.ratCast.{u1} K (LinearOrderedField.toRatCast.{u1} K _inst_1) a))) (Set.Iio.{0} Rat Rat.instPreorderRat a)
Case conversion may be inaccurate. Consider using '#align rat.preimage_cast_Iio Rat.preimage_cast_Iioₓ'. -/
@[simp]
theorem preimage_cast_Iio (a : ℚ) : coe ⁻¹' Iio (a : K) = Iio a :=
  by
  ext x
  simp
#align rat.preimage_cast_Iio Rat.preimage_cast_Iio

end LinearOrderedField

/- warning: rat.cast_id -> Rat.cast_id is a dubious translation:
lean 3 declaration is
  forall (n : Rat), Eq.{1} Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Rat (HasLiftT.mk.{1, 1} Rat Rat (CoeTCₓ.coe.{1, 1} Rat Rat (Rat.castCoe.{0} Rat (DivisionRing.toHasRatCast.{0} Rat Rat.divisionRing)))) n) n
but is expected to have type
  forall (n : Rat), Eq.{1} Rat (RatCast.ratCast.{0} Rat (LinearOrderedField.toRatCast.{0} Rat Rat.instLinearOrderedFieldRat) n) n
Case conversion may be inaccurate. Consider using '#align rat.cast_id Rat.cast_idₓ'. -/
@[norm_cast]
theorem cast_id (n : ℚ) : (↑n : ℚ) = n := by rw [cast_def, num_div_denom]
#align rat.cast_id Rat.cast_id

/- warning: rat.cast_eq_id -> Rat.cast_eq_id is a dubious translation:
lean 3 declaration is
  Eq.{1} (Rat -> Rat) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Rat (HasLiftT.mk.{1, 1} Rat Rat (CoeTCₓ.coe.{1, 1} Rat Rat (Rat.castCoe.{0} Rat (DivisionRing.toHasRatCast.{0} Rat Rat.divisionRing))))) (id.{1} Rat)
but is expected to have type
  Eq.{1} (Rat -> Rat) (fun (x : Rat) => x) (id.{1} Rat)
Case conversion may be inaccurate. Consider using '#align rat.cast_eq_id Rat.cast_eq_idₓ'. -/
@[simp]
theorem cast_eq_id : (coe : ℚ → ℚ) = id :=
  funext cast_id
#align rat.cast_eq_id Rat.cast_eq_id

/- warning: rat.cast_hom_rat -> Rat.cast_hom_rat is a dubious translation:
lean 3 declaration is
  Eq.{1} (RingHom.{0, 0} Rat Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing)))) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))) (Rat.castHom.{0} Rat Rat.divisionRing (StrictOrderedSemiring.to_charZero.{0} Rat (StrictOrderedRing.toStrictOrderedSemiring.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing)))) (RingHom.id.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing)))))
but is expected to have type
  Eq.{1} (RingHom.{0, 0} Rat Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))) (Rat.castHom.{0} Rat Rat.divisionRing (StrictOrderedSemiring.to_charZero.{0} Rat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} Rat Rat.instLinearOrderedSemiringRat))) (RingHom.id.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))))
Case conversion may be inaccurate. Consider using '#align rat.cast_hom_rat Rat.cast_hom_ratₓ'. -/
@[simp]
theorem cast_hom_rat : castHom ℚ = RingHom.id ℚ :=
  RingHom.ext cast_id
#align rat.cast_hom_rat Rat.cast_hom_rat

end Rat

open Rat

/- warning: map_rat_cast -> map_ratCast is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : DivisionRing.{u2} α] [_inst_2 : DivisionRing.{u3} β] [_inst_3 : RingHomClass.{u1, u2, u3} F α β (NonAssocRing.toNonAssocSemiring.{u2} α (Ring.toNonAssocRing.{u2} α (DivisionRing.toRing.{u2} α _inst_1))) (NonAssocRing.toNonAssocSemiring.{u3} β (Ring.toNonAssocRing.{u3} β (DivisionRing.toRing.{u3} β _inst_2)))] (f : F) (q : Rat), Eq.{succ u3} β (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u1, u2, u3} F α β (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (NonAssocRing.toNonAssocSemiring.{u2} α (Ring.toNonAssocRing.{u2} α (DivisionRing.toRing.{u2} α _inst_1)))))) (Distrib.toHasMul.{u3} β (NonUnitalNonAssocSemiring.toDistrib.{u3} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} β (NonAssocRing.toNonAssocSemiring.{u3} β (Ring.toNonAssocRing.{u3} β (DivisionRing.toRing.{u3} β _inst_2)))))) (NonUnitalRingHomClass.toMulHomClass.{u1, u2, u3} F α β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (NonAssocRing.toNonAssocSemiring.{u2} α (Ring.toNonAssocRing.{u2} α (DivisionRing.toRing.{u2} α _inst_1)))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} β (NonAssocRing.toNonAssocSemiring.{u3} β (Ring.toNonAssocRing.{u3} β (DivisionRing.toRing.{u3} β _inst_2)))) (RingHomClass.toNonUnitalRingHomClass.{u1, u2, u3} F α β (NonAssocRing.toNonAssocSemiring.{u2} α (Ring.toNonAssocRing.{u2} α (DivisionRing.toRing.{u2} α _inst_1))) (NonAssocRing.toNonAssocSemiring.{u3} β (Ring.toNonAssocRing.{u3} β (DivisionRing.toRing.{u3} β _inst_2))) _inst_3)))) f ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u2} Rat α (CoeTCₓ.coe.{1, succ u2} Rat α (Rat.castCoe.{u2} α (DivisionRing.toHasRatCast.{u2} α _inst_1)))) q)) ((fun (a : Type) (b : Type.{u3}) [self : HasLiftT.{1, succ u3} a b] => self.0) Rat β (HasLiftT.mk.{1, succ u3} Rat β (CoeTCₓ.coe.{1, succ u3} Rat β (Rat.castCoe.{u3} β (DivisionRing.toHasRatCast.{u3} β _inst_2)))) q)
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : DivisionRing.{u3} α] [_inst_2 : DivisionRing.{u2} β] [_inst_3 : RingHomClass.{u1, u3, u2} F α β (NonAssocRing.toNonAssocSemiring.{u3} α (Ring.toNonAssocRing.{u3} α (DivisionRing.toRing.{u3} α _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} β (Ring.toNonAssocRing.{u2} β (DivisionRing.toRing.{u2} β _inst_2)))] (f : F) (q : Rat), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) (RatCast.ratCast.{u3} α (DivisionRing.toRatCast.{u3} α _inst_1) q)) (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) _x) (MulHomClass.toFunLike.{u1, u3, u2} F α β (NonUnitalNonAssocSemiring.toMul.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (NonAssocRing.toNonAssocSemiring.{u3} α (Ring.toNonAssocRing.{u3} α (DivisionRing.toRing.{u3} α _inst_1))))) (NonUnitalNonAssocSemiring.toMul.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (NonAssocRing.toNonAssocSemiring.{u2} β (Ring.toNonAssocRing.{u2} β (DivisionRing.toRing.{u2} β _inst_2))))) (NonUnitalRingHomClass.toMulHomClass.{u1, u3, u2} F α β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (NonAssocRing.toNonAssocSemiring.{u3} α (Ring.toNonAssocRing.{u3} α (DivisionRing.toRing.{u3} α _inst_1)))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (NonAssocRing.toNonAssocSemiring.{u2} β (Ring.toNonAssocRing.{u2} β (DivisionRing.toRing.{u2} β _inst_2)))) (RingHomClass.toNonUnitalRingHomClass.{u1, u3, u2} F α β (NonAssocRing.toNonAssocSemiring.{u3} α (Ring.toNonAssocRing.{u3} α (DivisionRing.toRing.{u3} α _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} β (Ring.toNonAssocRing.{u2} β (DivisionRing.toRing.{u2} β _inst_2))) _inst_3))) f (RatCast.ratCast.{u3} α (DivisionRing.toRatCast.{u3} α _inst_1) q)) (RatCast.ratCast.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) (RatCast.ratCast.{u3} α (DivisionRing.toRatCast.{u3} α _inst_1) q)) (DivisionRing.toRatCast.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) (RatCast.ratCast.{u3} α (DivisionRing.toRatCast.{u3} α _inst_1) q)) _inst_2) q)
Case conversion may be inaccurate. Consider using '#align map_rat_cast map_ratCastₓ'. -/
@[simp]
theorem map_ratCast [DivisionRing α] [DivisionRing β] [RingHomClass F α β] (f : F) (q : ℚ) :
    f q = q := by rw [cast_def, map_div₀, map_intCast, map_natCast, cast_def]
#align map_rat_cast map_ratCast

/- warning: eq_rat_cast -> eq_ratCast is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {k : Type.{u2}} [_inst_1 : DivisionRing.{u2} k] [_inst_2 : RingHomClass.{u1, 0, u2} F Rat k (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing)))) (NonAssocRing.toNonAssocSemiring.{u2} k (Ring.toNonAssocRing.{u2} k (DivisionRing.toRing.{u2} k _inst_1)))] (f : F) (r : Rat), Eq.{succ u2} k (coeFn.{succ u1, succ u2} F (fun (_x : F) => Rat -> k) (FunLike.hasCoeToFun.{succ u1, 1, succ u2} F Rat (fun (_x : Rat) => k) (MulHomClass.toFunLike.{u1, 0, u2} F Rat k (Distrib.toHasMul.{0} Rat (NonUnitalNonAssocSemiring.toDistrib.{0} Rat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))))) (Distrib.toHasMul.{u2} k (NonUnitalNonAssocSemiring.toDistrib.{u2} k (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} k (NonAssocRing.toNonAssocSemiring.{u2} k (Ring.toNonAssocRing.{u2} k (DivisionRing.toRing.{u2} k _inst_1)))))) (NonUnitalRingHomClass.toMulHomClass.{u1, 0, u2} F Rat k (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} k (NonAssocRing.toNonAssocSemiring.{u2} k (Ring.toNonAssocRing.{u2} k (DivisionRing.toRing.{u2} k _inst_1)))) (RingHomClass.toNonUnitalRingHomClass.{u1, 0, u2} F Rat k (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing)))) (NonAssocRing.toNonAssocSemiring.{u2} k (Ring.toNonAssocRing.{u2} k (DivisionRing.toRing.{u2} k _inst_1))) _inst_2)))) f r) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Rat k (HasLiftT.mk.{1, succ u2} Rat k (CoeTCₓ.coe.{1, succ u2} Rat k (Rat.castCoe.{u2} k (DivisionRing.toHasRatCast.{u2} k _inst_1)))) r)
but is expected to have type
  forall {F : Type.{u1}} {k : Type.{u2}} [_inst_1 : DivisionRing.{u2} k] [_inst_2 : RingHomClass.{u1, 0, u2} F Rat k (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))) (NonAssocRing.toNonAssocSemiring.{u2} k (Ring.toNonAssocRing.{u2} k (DivisionRing.toRing.{u2} k _inst_1)))] (f : F) (r : Rat), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Rat) => k) r) (FunLike.coe.{succ u1, 1, succ u2} F Rat (fun (_x : Rat) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Rat) => k) _x) (MulHomClass.toFunLike.{u1, 0, u2} F Rat k (NonUnitalNonAssocSemiring.toMul.{0} Rat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))))) (NonUnitalNonAssocSemiring.toMul.{u2} k (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} k (NonAssocRing.toNonAssocSemiring.{u2} k (Ring.toNonAssocRing.{u2} k (DivisionRing.toRing.{u2} k _inst_1))))) (NonUnitalRingHomClass.toMulHomClass.{u1, 0, u2} F Rat k (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} k (NonAssocRing.toNonAssocSemiring.{u2} k (Ring.toNonAssocRing.{u2} k (DivisionRing.toRing.{u2} k _inst_1)))) (RingHomClass.toNonUnitalRingHomClass.{u1, 0, u2} F Rat k (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))) (NonAssocRing.toNonAssocSemiring.{u2} k (Ring.toNonAssocRing.{u2} k (DivisionRing.toRing.{u2} k _inst_1))) _inst_2))) f r) (RatCast.ratCast.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Rat) => k) r) (DivisionRing.toRatCast.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Rat) => k) r) _inst_1) r)
Case conversion may be inaccurate. Consider using '#align eq_rat_cast eq_ratCastₓ'. -/
@[simp]
theorem eq_ratCast {k} [DivisionRing k] [RingHomClass F ℚ k] (f : F) (r : ℚ) : f r = r := by
  rw [← map_ratCast f, Rat.cast_id]
#align eq_rat_cast eq_ratCast

namespace MonoidWithZeroHom

variable {M₀ : Type _} [MonoidWithZero M₀] [MonoidWithZeroHomClass F ℚ M₀] {f g : F}

include M₀

/- warning: monoid_with_zero_hom.ext_rat' -> MonoidWithZeroHom.ext_rat' is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {M₀ : Type.{u2}} [_inst_1 : MonoidWithZero.{u2} M₀] [_inst_2 : MonoidWithZeroHomClass.{u1, 0, u2} F Rat M₀ (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))) (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1)] {f : F} {g : F}, (forall (m : Int), Eq.{succ u2} M₀ (coeFn.{succ u1, succ u2} F (fun (_x : F) => Rat -> M₀) (FunLike.hasCoeToFun.{succ u1, 1, succ u2} F Rat (fun (_x : Rat) => M₀) (MulHomClass.toFunLike.{u1, 0, u2} F Rat M₀ (MulOneClass.toHasMul.{0} Rat (MulZeroOneClass.toMulOneClass.{0} Rat (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))))) (MulOneClass.toHasMul.{u2} M₀ (MulZeroOneClass.toMulOneClass.{u2} M₀ (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1))) (MonoidHomClass.toMulHomClass.{u1, 0, u2} F Rat M₀ (MulZeroOneClass.toMulOneClass.{0} Rat (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing)))))) (MulZeroOneClass.toMulOneClass.{u2} M₀ (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1)) (MonoidWithZeroHomClass.toMonoidHomClass.{u1, 0, u2} F Rat M₀ (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))) (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1) _inst_2)))) f ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Rat (HasLiftT.mk.{1, 1} Int Rat (CoeTCₓ.coe.{1, 1} Int Rat (Int.castCoe.{0} Rat Rat.hasIntCast))) m)) (coeFn.{succ u1, succ u2} F (fun (_x : F) => Rat -> M₀) (FunLike.hasCoeToFun.{succ u1, 1, succ u2} F Rat (fun (_x : Rat) => M₀) (MulHomClass.toFunLike.{u1, 0, u2} F Rat M₀ (MulOneClass.toHasMul.{0} Rat (MulZeroOneClass.toMulOneClass.{0} Rat (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))))) (MulOneClass.toHasMul.{u2} M₀ (MulZeroOneClass.toMulOneClass.{u2} M₀ (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1))) (MonoidHomClass.toMulHomClass.{u1, 0, u2} F Rat M₀ (MulZeroOneClass.toMulOneClass.{0} Rat (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing)))))) (MulZeroOneClass.toMulOneClass.{u2} M₀ (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1)) (MonoidWithZeroHomClass.toMonoidHomClass.{u1, 0, u2} F Rat M₀ (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))) (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1) _inst_2)))) g ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Rat (HasLiftT.mk.{1, 1} Int Rat (CoeTCₓ.coe.{1, 1} Int Rat (Int.castCoe.{0} Rat Rat.hasIntCast))) m))) -> (Eq.{succ u1} F f g)
but is expected to have type
  forall {F : Type.{u1}} {M₀ : Type.{u2}} [_inst_1 : MonoidWithZero.{u2} M₀] [_inst_2 : MonoidWithZeroHomClass.{u1, 0, u2} F Rat M₀ (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))) (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1)] {f : F} {g : F}, (forall (m : Int), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Rat) => M₀) (Int.cast.{0} Rat Rat.instIntCastRat m)) (FunLike.coe.{succ u1, 1, succ u2} F Rat (fun (_x : Rat) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Rat) => M₀) _x) (MulHomClass.toFunLike.{u1, 0, u2} F Rat M₀ (MulOneClass.toMul.{0} Rat (MulZeroOneClass.toMulOneClass.{0} Rat (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))))) (MulOneClass.toMul.{u2} M₀ (MulZeroOneClass.toMulOneClass.{u2} M₀ (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1))) (MonoidHomClass.toMulHomClass.{u1, 0, u2} F Rat M₀ (MulZeroOneClass.toMulOneClass.{0} Rat (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))))) (MulZeroOneClass.toMulOneClass.{u2} M₀ (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1)) (MonoidWithZeroHomClass.toMonoidHomClass.{u1, 0, u2} F Rat M₀ (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))) (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1) _inst_2))) f (Int.cast.{0} Rat Rat.instIntCastRat m)) (FunLike.coe.{succ u1, 1, succ u2} F Rat (fun (_x : Rat) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Rat) => M₀) _x) (MulHomClass.toFunLike.{u1, 0, u2} F Rat M₀ (MulOneClass.toMul.{0} Rat (MulZeroOneClass.toMulOneClass.{0} Rat (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))))) (MulOneClass.toMul.{u2} M₀ (MulZeroOneClass.toMulOneClass.{u2} M₀ (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1))) (MonoidHomClass.toMulHomClass.{u1, 0, u2} F Rat M₀ (MulZeroOneClass.toMulOneClass.{0} Rat (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))))) (MulZeroOneClass.toMulOneClass.{u2} M₀ (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1)) (MonoidWithZeroHomClass.toMonoidHomClass.{u1, 0, u2} F Rat M₀ (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))) (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1) _inst_2))) g (Int.cast.{0} Rat Rat.instIntCastRat m))) -> (Eq.{succ u1} F f g)
Case conversion may be inaccurate. Consider using '#align monoid_with_zero_hom.ext_rat' MonoidWithZeroHom.ext_rat'ₓ'. -/
/-- If `f` and `g` agree on the integers then they are equal `φ`. -/
theorem ext_rat' (h : ∀ m : ℤ, f m = g m) : f = g :=
  FunLike.ext f g fun r => by
    rw [← r.num_div_denom, div_eq_mul_inv, map_mul, map_mul, h, ← Int.cast_ofNat,
      eq_on_inv₀ f g (h _)]
#align monoid_with_zero_hom.ext_rat' MonoidWithZeroHom.ext_rat'

/- warning: monoid_with_zero_hom.ext_rat -> MonoidWithZeroHom.ext_rat is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] {f : MonoidWithZeroHom.{0, u1} Rat M₀ (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))) (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)} {g : MonoidWithZeroHom.{0, u1} Rat M₀ (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))) (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)}, (Eq.{succ u1} (MonoidWithZeroHom.{0, u1} Int M₀ (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)) (MonoidWithZeroHom.comp.{0, 0, u1} Int Rat M₀ (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))) (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1) f ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (RingHom.{0, 0} Int Rat (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))) (MonoidWithZeroHom.{0, 0} Int Rat (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing)))))) (HasLiftT.mk.{1, 1} (RingHom.{0, 0} Int Rat (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))) (MonoidWithZeroHom.{0, 0} Int Rat (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing)))))) (CoeTCₓ.coe.{1, 1} (RingHom.{0, 0} Int Rat (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))) (MonoidWithZeroHom.{0, 0} Int Rat (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing)))))) (MonoidWithZeroHom.hasCoeT.{0, 0, 0} Int Rat (RingHom.{0, 0} Int Rat (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))) (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))) (RingHomClass.toMonoidWithZeroHomClass.{0, 0, 0} (RingHom.{0, 0} Int Rat (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))) Int Rat (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing)))) (RingHom.ringHomClass.{0, 0} Int Rat (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))))))) (Int.castRingHom.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing)))))) (MonoidWithZeroHom.comp.{0, 0, u1} Int Rat M₀ (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))) (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1) g ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (RingHom.{0, 0} Int Rat (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))) (MonoidWithZeroHom.{0, 0} Int Rat (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing)))))) (HasLiftT.mk.{1, 1} (RingHom.{0, 0} Int Rat (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))) (MonoidWithZeroHom.{0, 0} Int Rat (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing)))))) (CoeTCₓ.coe.{1, 1} (RingHom.{0, 0} Int Rat (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))) (MonoidWithZeroHom.{0, 0} Int Rat (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing)))))) (MonoidWithZeroHom.hasCoeT.{0, 0, 0} Int Rat (RingHom.{0, 0} Int Rat (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))) (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))) (RingHomClass.toMonoidWithZeroHomClass.{0, 0, 0} (RingHom.{0, 0} Int Rat (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))) Int Rat (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing)))) (RingHom.ringHomClass.{0, 0} Int Rat (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))))))) (Int.castRingHom.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))))) -> (Eq.{succ u1} (MonoidWithZeroHom.{0, u1} Rat M₀ (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))) (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)) f g)
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] {f : MonoidWithZeroHom.{0, u1} Rat M₀ (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))) (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)} {g : MonoidWithZeroHom.{0, u1} Rat M₀ (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))) (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)}, (Eq.{succ u1} (MonoidWithZeroHom.{0, u1} Int M₀ (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))) (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)) (MonoidWithZeroHom.comp.{0, 0, u1} Int Rat M₀ (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))) (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))) (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1) f (MonoidWithZeroHomClass.toMonoidWithZeroHom.{0, 0, 0} Int Rat (RingHom.{0, 0} Int Rat (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))) (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))) (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))) (RingHomClass.toMonoidWithZeroHomClass.{0, 0, 0} (RingHom.{0, 0} Int Rat (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))) Int Rat (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))) (RingHom.instRingHomClassRingHom.{0, 0} Int Rat (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))))) (Int.castRingHom.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))))) (MonoidWithZeroHom.comp.{0, 0, u1} Int Rat M₀ (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))) (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))) (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1) g (MonoidWithZeroHomClass.toMonoidWithZeroHom.{0, 0, 0} Int Rat (RingHom.{0, 0} Int Rat (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))) (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))) (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))) (RingHomClass.toMonoidWithZeroHomClass.{0, 0, 0} (RingHom.{0, 0} Int Rat (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))) Int Rat (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))) (RingHom.instRingHomClassRingHom.{0, 0} Int Rat (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))))) (Int.castRingHom.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))))) -> (Eq.{succ u1} (MonoidWithZeroHom.{0, u1} Rat M₀ (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))) (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)) f g)
Case conversion may be inaccurate. Consider using '#align monoid_with_zero_hom.ext_rat MonoidWithZeroHom.ext_ratₓ'. -/
/-- If `f` and `g` agree on the integers then they are equal `φ`.

See note [partially-applied ext lemmas] for why `comp` is used here. -/
@[ext]
theorem ext_rat {f g : ℚ →*₀ M₀}
    (h : f.comp (Int.castRingHom ℚ : ℤ →*₀ ℚ) = g.comp (Int.castRingHom ℚ)) : f = g :=
  ext_rat' <| congr_fun h
#align monoid_with_zero_hom.ext_rat MonoidWithZeroHom.ext_rat

/- warning: monoid_with_zero_hom.ext_rat_on_pnat -> MonoidWithZeroHom.ext_rat_on_pnat is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {M₀ : Type.{u2}} [_inst_1 : MonoidWithZero.{u2} M₀] [_inst_2 : MonoidWithZeroHomClass.{u1, 0, u2} F Rat M₀ (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))) (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1)] {f : F} {g : F}, (Eq.{succ u2} M₀ (coeFn.{succ u1, succ u2} F (fun (_x : F) => Rat -> M₀) (FunLike.hasCoeToFun.{succ u1, 1, succ u2} F Rat (fun (_x : Rat) => M₀) (MulHomClass.toFunLike.{u1, 0, u2} F Rat M₀ (MulOneClass.toHasMul.{0} Rat (MulZeroOneClass.toMulOneClass.{0} Rat (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))))) (MulOneClass.toHasMul.{u2} M₀ (MulZeroOneClass.toMulOneClass.{u2} M₀ (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1))) (MonoidHomClass.toMulHomClass.{u1, 0, u2} F Rat M₀ (MulZeroOneClass.toMulOneClass.{0} Rat (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing)))))) (MulZeroOneClass.toMulOneClass.{u2} M₀ (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1)) (MonoidWithZeroHomClass.toMonoidHomClass.{u1, 0, u2} F Rat M₀ (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))) (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1) _inst_2)))) f (Neg.neg.{0} Rat Rat.hasNeg (OfNat.ofNat.{0} Rat 1 (OfNat.mk.{0} Rat 1 (One.one.{0} Rat Rat.hasOne))))) (coeFn.{succ u1, succ u2} F (fun (_x : F) => Rat -> M₀) (FunLike.hasCoeToFun.{succ u1, 1, succ u2} F Rat (fun (_x : Rat) => M₀) (MulHomClass.toFunLike.{u1, 0, u2} F Rat M₀ (MulOneClass.toHasMul.{0} Rat (MulZeroOneClass.toMulOneClass.{0} Rat (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))))) (MulOneClass.toHasMul.{u2} M₀ (MulZeroOneClass.toMulOneClass.{u2} M₀ (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1))) (MonoidHomClass.toMulHomClass.{u1, 0, u2} F Rat M₀ (MulZeroOneClass.toMulOneClass.{0} Rat (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing)))))) (MulZeroOneClass.toMulOneClass.{u2} M₀ (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1)) (MonoidWithZeroHomClass.toMonoidHomClass.{u1, 0, u2} F Rat M₀ (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))) (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1) _inst_2)))) g (Neg.neg.{0} Rat Rat.hasNeg (OfNat.ofNat.{0} Rat 1 (OfNat.mk.{0} Rat 1 (One.one.{0} Rat Rat.hasOne)))))) -> (forall (n : Nat), (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) -> (Eq.{succ u2} M₀ (coeFn.{succ u1, succ u2} F (fun (_x : F) => Rat -> M₀) (FunLike.hasCoeToFun.{succ u1, 1, succ u2} F Rat (fun (_x : Rat) => M₀) (MulHomClass.toFunLike.{u1, 0, u2} F Rat M₀ (MulOneClass.toHasMul.{0} Rat (MulZeroOneClass.toMulOneClass.{0} Rat (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))))) (MulOneClass.toHasMul.{u2} M₀ (MulZeroOneClass.toMulOneClass.{u2} M₀ (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1))) (MonoidHomClass.toMulHomClass.{u1, 0, u2} F Rat M₀ (MulZeroOneClass.toMulOneClass.{0} Rat (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing)))))) (MulZeroOneClass.toMulOneClass.{u2} M₀ (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1)) (MonoidWithZeroHomClass.toMonoidHomClass.{u1, 0, u2} F Rat M₀ (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))) (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1) _inst_2)))) f ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))))))) n)) (coeFn.{succ u1, succ u2} F (fun (_x : F) => Rat -> M₀) (FunLike.hasCoeToFun.{succ u1, 1, succ u2} F Rat (fun (_x : Rat) => M₀) (MulHomClass.toFunLike.{u1, 0, u2} F Rat M₀ (MulOneClass.toHasMul.{0} Rat (MulZeroOneClass.toMulOneClass.{0} Rat (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))))) (MulOneClass.toHasMul.{u2} M₀ (MulZeroOneClass.toMulOneClass.{u2} M₀ (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1))) (MonoidHomClass.toMulHomClass.{u1, 0, u2} F Rat M₀ (MulZeroOneClass.toMulOneClass.{0} Rat (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing)))))) (MulZeroOneClass.toMulOneClass.{u2} M₀ (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1)) (MonoidWithZeroHomClass.toMonoidHomClass.{u1, 0, u2} F Rat M₀ (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))) (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1) _inst_2)))) g ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))))))) n)))) -> (Eq.{succ u1} F f g)
but is expected to have type
  forall {F : Type.{u1}} {M₀ : Type.{u2}} [_inst_1 : MonoidWithZero.{u2} M₀] [_inst_2 : MonoidWithZeroHomClass.{u1, 0, u2} F Rat M₀ (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))) (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1)] {f : F} {g : F}, (Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Rat) => M₀) (Neg.neg.{0} Rat Rat.instNegRat (OfNat.ofNat.{0} Rat 1 (Rat.instOfNatRat 1)))) (FunLike.coe.{succ u1, 1, succ u2} F Rat (fun (_x : Rat) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Rat) => M₀) _x) (MulHomClass.toFunLike.{u1, 0, u2} F Rat M₀ (MulOneClass.toMul.{0} Rat (MulZeroOneClass.toMulOneClass.{0} Rat (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))))) (MulOneClass.toMul.{u2} M₀ (MulZeroOneClass.toMulOneClass.{u2} M₀ (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1))) (MonoidHomClass.toMulHomClass.{u1, 0, u2} F Rat M₀ (MulZeroOneClass.toMulOneClass.{0} Rat (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))))) (MulZeroOneClass.toMulOneClass.{u2} M₀ (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1)) (MonoidWithZeroHomClass.toMonoidHomClass.{u1, 0, u2} F Rat M₀ (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))) (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1) _inst_2))) f (Neg.neg.{0} Rat Rat.instNegRat (OfNat.ofNat.{0} Rat 1 (Rat.instOfNatRat 1)))) (FunLike.coe.{succ u1, 1, succ u2} F Rat (fun (_x : Rat) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Rat) => M₀) _x) (MulHomClass.toFunLike.{u1, 0, u2} F Rat M₀ (MulOneClass.toMul.{0} Rat (MulZeroOneClass.toMulOneClass.{0} Rat (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))))) (MulOneClass.toMul.{u2} M₀ (MulZeroOneClass.toMulOneClass.{u2} M₀ (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1))) (MonoidHomClass.toMulHomClass.{u1, 0, u2} F Rat M₀ (MulZeroOneClass.toMulOneClass.{0} Rat (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))))) (MulZeroOneClass.toMulOneClass.{u2} M₀ (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1)) (MonoidWithZeroHomClass.toMonoidHomClass.{u1, 0, u2} F Rat M₀ (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))) (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1) _inst_2))) g (Neg.neg.{0} Rat Rat.instNegRat (OfNat.ofNat.{0} Rat 1 (Rat.instOfNatRat 1))))) -> (forall (n : Nat), (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) -> (Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Rat) => M₀) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))) n)) (FunLike.coe.{succ u1, 1, succ u2} F Rat (fun (_x : Rat) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Rat) => M₀) _x) (MulHomClass.toFunLike.{u1, 0, u2} F Rat M₀ (MulOneClass.toMul.{0} Rat (MulZeroOneClass.toMulOneClass.{0} Rat (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))))) (MulOneClass.toMul.{u2} M₀ (MulZeroOneClass.toMulOneClass.{u2} M₀ (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1))) (MonoidHomClass.toMulHomClass.{u1, 0, u2} F Rat M₀ (MulZeroOneClass.toMulOneClass.{0} Rat (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))))) (MulZeroOneClass.toMulOneClass.{u2} M₀ (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1)) (MonoidWithZeroHomClass.toMonoidHomClass.{u1, 0, u2} F Rat M₀ (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))) (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1) _inst_2))) f (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))) n)) (FunLike.coe.{succ u1, 1, succ u2} F Rat (fun (_x : Rat) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Rat) => M₀) _x) (MulHomClass.toFunLike.{u1, 0, u2} F Rat M₀ (MulOneClass.toMul.{0} Rat (MulZeroOneClass.toMulOneClass.{0} Rat (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))))) (MulOneClass.toMul.{u2} M₀ (MulZeroOneClass.toMulOneClass.{u2} M₀ (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1))) (MonoidHomClass.toMulHomClass.{u1, 0, u2} F Rat M₀ (MulZeroOneClass.toMulOneClass.{0} Rat (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))))) (MulZeroOneClass.toMulOneClass.{u2} M₀ (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1)) (MonoidWithZeroHomClass.toMonoidHomClass.{u1, 0, u2} F Rat M₀ (NonAssocSemiring.toMulZeroOneClass.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))) (MonoidWithZero.toMulZeroOneClass.{u2} M₀ _inst_1) _inst_2))) g (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))) n)))) -> (Eq.{succ u1} F f g)
Case conversion may be inaccurate. Consider using '#align monoid_with_zero_hom.ext_rat_on_pnat MonoidWithZeroHom.ext_rat_on_pnatₓ'. -/
/-- Positive integer values of a morphism `φ` and its value on `-1` completely determine `φ`. -/
theorem ext_rat_on_pnat (same_on_neg_one : f (-1) = g (-1))
    (same_on_pnat : ∀ n : ℕ, 0 < n → f n = g n) : f = g :=
  ext_rat' <|
    FunLike.congr_fun <|
      show
        (f : ℚ →*₀ M₀).comp (Int.castRingHom ℚ : ℤ →*₀ ℚ) =
          (g : ℚ →*₀ M₀).comp (Int.castRingHom ℚ : ℤ →*₀ ℚ)
        from ext_int' (by simpa) (by simpa)
#align monoid_with_zero_hom.ext_rat_on_pnat MonoidWithZeroHom.ext_rat_on_pnat

end MonoidWithZeroHom

/- warning: ring_hom.ext_rat -> RingHom.ext_rat is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {R : Type.{u2}} [_inst_1 : Semiring.{u2} R] [_inst_2 : RingHomClass.{u1, 0, u2} F Rat R (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing)))) (Semiring.toNonAssocSemiring.{u2} R _inst_1)] (f : F) (g : F), Eq.{succ u1} F f g
but is expected to have type
  forall {F : Type.{u1}} {R : Type.{u2}} [_inst_1 : Semiring.{u2} R] [_inst_2 : RingHomClass.{u1, 0, u2} F Rat R (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))) (Semiring.toNonAssocSemiring.{u2} R _inst_1)] (f : F) (g : F), Eq.{succ u1} F f g
Case conversion may be inaccurate. Consider using '#align ring_hom.ext_rat RingHom.ext_ratₓ'. -/
/-- Any two ring homomorphisms from `ℚ` to a semiring are equal. If the codomain is a division ring,
then this lemma follows from `eq_rat_cast`. -/
theorem RingHom.ext_rat {R : Type _} [Semiring R] [RingHomClass F ℚ R] (f g : F) : f = g :=
  MonoidWithZeroHom.ext_rat' <|
    RingHom.congr_fun <|
      ((f : ℚ →+* R).comp (Int.castRingHom ℚ)).ext_int ((g : ℚ →+* R).comp (Int.castRingHom ℚ))
#align ring_hom.ext_rat RingHom.ext_rat

/- warning: rat.subsingleton_ring_hom -> Rat.subsingleton_ringHom is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R], Subsingleton.{succ u1} (RingHom.{0, u1} Rat R (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing)))) (Semiring.toNonAssocSemiring.{u1} R _inst_1))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R], Subsingleton.{succ u1} (RingHom.{0, u1} Rat R (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))) (Semiring.toNonAssocSemiring.{u1} R _inst_1))
Case conversion may be inaccurate. Consider using '#align rat.subsingleton_ring_hom Rat.subsingleton_ringHomₓ'. -/
instance Rat.subsingleton_ringHom {R : Type _} [Semiring R] : Subsingleton (ℚ →+* R) :=
  ⟨RingHom.ext_rat⟩
#align rat.subsingleton_ring_hom Rat.subsingleton_ringHom

namespace MulOpposite

variable [DivisionRing α]

/- warning: mul_opposite.op_rat_cast -> MulOpposite.op_ratCast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] (r : Rat), Eq.{succ u1} (MulOpposite.{u1} α) (MulOpposite.op.{u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) r)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat (MulOpposite.{u1} α) (HasLiftT.mk.{1, succ u1} Rat (MulOpposite.{u1} α) (CoeTCₓ.coe.{1, succ u1} Rat (MulOpposite.{u1} α) (Rat.castCoe.{u1} (MulOpposite.{u1} α) (DivisionRing.toHasRatCast.{u1} (MulOpposite.{u1} α) (MulOpposite.divisionRing.{u1} α _inst_1))))) r)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] (r : Rat), Eq.{succ u1} (MulOpposite.{u1} α) (MulOpposite.op.{u1} α (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) r)) (RatCast.ratCast.{u1} (MulOpposite.{u1} α) (DivisionRing.toRatCast.{u1} (MulOpposite.{u1} α) (MulOpposite.instDivisionRingMulOpposite.{u1} α _inst_1)) r)
Case conversion may be inaccurate. Consider using '#align mul_opposite.op_rat_cast MulOpposite.op_ratCastₓ'. -/
@[simp, norm_cast]
theorem op_ratCast (r : ℚ) : op (r : α) = (↑r : αᵐᵒᵖ) := by
  rw [cast_def, div_eq_mul_inv, op_mul, op_inv, op_nat_cast, op_int_cast,
    (Commute.cast_int_right _ r.num).Eq, cast_def, div_eq_mul_inv]
#align mul_opposite.op_rat_cast MulOpposite.op_ratCast

/- warning: mul_opposite.unop_rat_cast -> MulOpposite.unop_ratCast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] (r : Rat), Eq.{succ u1} α (MulOpposite.unop.{u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat (MulOpposite.{u1} α) (HasLiftT.mk.{1, succ u1} Rat (MulOpposite.{u1} α) (CoeTCₓ.coe.{1, succ u1} Rat (MulOpposite.{u1} α) (Rat.castCoe.{u1} (MulOpposite.{u1} α) (DivisionRing.toHasRatCast.{u1} (MulOpposite.{u1} α) (MulOpposite.divisionRing.{u1} α _inst_1))))) r)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α _inst_1)))) r)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] (r : Rat), Eq.{succ u1} α (MulOpposite.unop.{u1} α (RatCast.ratCast.{u1} (MulOpposite.{u1} α) (DivisionRing.toRatCast.{u1} (MulOpposite.{u1} α) (MulOpposite.instDivisionRingMulOpposite.{u1} α _inst_1)) r)) (RatCast.ratCast.{u1} α (DivisionRing.toRatCast.{u1} α _inst_1) r)
Case conversion may be inaccurate. Consider using '#align mul_opposite.unop_rat_cast MulOpposite.unop_ratCastₓ'. -/
@[simp, norm_cast]
theorem unop_ratCast (r : ℚ) : unop (r : αᵐᵒᵖ) = r := by
  rw [cast_def, div_eq_mul_inv, unop_mul, unop_inv, unop_nat_cast, unop_int_cast,
    (Commute.cast_int_right _ r.num).Eq, cast_def, div_eq_mul_inv]
#align mul_opposite.unop_rat_cast MulOpposite.unop_ratCast

end MulOpposite

section Smul

namespace Rat

variable {K : Type _} [DivisionRing K]

#print Rat.distribSMul /-
instance (priority := 100) distribSMul : DistribSMul ℚ K
    where
  smul := (· • ·)
  smul_zero a := by rw [smul_def, mul_zero]
  smul_add a x y := by simp only [smul_def, mul_add, cast_add]
#align rat.distrib_smul Rat.distribSMul
-/

/- warning: rat.is_scalar_tower_right -> Rat.isScalarTower_right is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : DivisionRing.{u1} K], IsScalarTower.{0, u1, u1} Rat K K (SMulZeroClass.toHasSmul.{0, u1} Rat K (AddZeroClass.toHasZero.{u1} K (AddMonoid.toAddZeroClass.{u1} K (AddMonoidWithOne.toAddMonoid.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (NonAssocRing.toAddGroupWithOne.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1))))))) (DistribSMul.toSmulZeroClass.{0, u1} Rat K (AddMonoid.toAddZeroClass.{u1} K (AddMonoidWithOne.toAddMonoid.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (NonAssocRing.toAddGroupWithOne.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))))) (Rat.distribSMul.{u1} K _inst_1))) (Mul.toSMul.{u1} K (Distrib.toHasMul.{u1} K (Ring.toDistrib.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))) (SMulZeroClass.toHasSmul.{0, u1} Rat K (AddZeroClass.toHasZero.{u1} K (AddMonoid.toAddZeroClass.{u1} K (AddMonoidWithOne.toAddMonoid.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (NonAssocRing.toAddGroupWithOne.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1))))))) (DistribSMul.toSmulZeroClass.{0, u1} Rat K (AddMonoid.toAddZeroClass.{u1} K (AddMonoidWithOne.toAddMonoid.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (NonAssocRing.toAddGroupWithOne.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))))) (Rat.distribSMul.{u1} K _inst_1)))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : DivisionRing.{u1} K], IsScalarTower.{0, u1, u1} Rat K K (SMulZeroClass.toSMul.{0, u1} Rat K (MonoidWithZero.toZero.{u1} K (Semiring.toMonoidWithZero.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)))) (DistribSMul.toSMulZeroClass.{0, u1} Rat K (AddMonoid.toAddZeroClass.{u1} K (AddMonoidWithOne.toAddMonoid.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (Ring.toAddGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K _inst_1))))) (Rat.distribSMul.{u1} K _inst_1))) (MulAction.toSMul.{u1, u1} K K (MonoidWithZero.toMonoid.{u1} K (Semiring.toMonoidWithZero.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)))) (Monoid.toMulAction.{u1} K (MonoidWithZero.toMonoid.{u1} K (Semiring.toMonoidWithZero.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)))))) (SMulZeroClass.toSMul.{0, u1} Rat K (MonoidWithZero.toZero.{u1} K (Semiring.toMonoidWithZero.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)))) (DistribSMul.toSMulZeroClass.{0, u1} Rat K (AddMonoid.toAddZeroClass.{u1} K (AddMonoidWithOne.toAddMonoid.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (Ring.toAddGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K _inst_1))))) (Rat.distribSMul.{u1} K _inst_1)))
Case conversion may be inaccurate. Consider using '#align rat.is_scalar_tower_right Rat.isScalarTower_rightₓ'. -/
instance isScalarTower_right : IsScalarTower ℚ K K :=
  ⟨fun a x y => by simp only [smul_def, smul_eq_mul, mul_assoc]⟩
#align rat.is_scalar_tower_right Rat.isScalarTower_right

end Rat

end Smul

