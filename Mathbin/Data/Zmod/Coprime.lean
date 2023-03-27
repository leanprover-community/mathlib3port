/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll

! This file was ported from Lean 3 source module data.zmod.coprime
! leanprover-community/mathlib commit c085f3044fe585c575e322bfab45b3633c48d820
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Zmod.Basic
import Mathbin.RingTheory.Int.Basic

/-!
# Coprimality and vanishing

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We show that for prime `p`, the image of an integer `a` in `zmod p` vanishes if and only if
`a` and `p` are not coprime.
-/


namespace ZMod

/- warning: zmod.eq_zero_iff_gcd_ne_one -> ZMod.eq_zero_iff_gcd_ne_one is a dubious translation:
lean 3 declaration is
  forall {a : Int} {p : Nat} [pp : Fact (Nat.Prime p)], Iff (Eq.{1} (ZMod p) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (ZMod p) (HasLiftT.mk.{1, 1} Int (ZMod p) (CoeTCₓ.coe.{1, 1} Int (ZMod p) (Int.castCoe.{0} (ZMod p) (AddGroupWithOne.toHasIntCast.{0} (ZMod p) (AddCommGroupWithOne.toAddGroupWithOne.{0} (ZMod p) (Ring.toAddCommGroupWithOne.{0} (ZMod p) (DivisionRing.toRing.{0} (ZMod p) (Field.toDivisionRing.{0} (ZMod p) (ZMod.field p pp))))))))) a) (OfNat.ofNat.{0} (ZMod p) 0 (OfNat.mk.{0} (ZMod p) 0 (Zero.zero.{0} (ZMod p) (MulZeroClass.toHasZero.{0} (ZMod p) (NonUnitalNonAssocSemiring.toMulZeroClass.{0} (ZMod p) (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} (ZMod p) (NonAssocRing.toNonUnitalNonAssocRing.{0} (ZMod p) (Ring.toNonAssocRing.{0} (ZMod p) (DivisionRing.toRing.{0} (ZMod p) (Field.toDivisionRing.{0} (ZMod p) (ZMod.field p pp)))))))))))) (Ne.{1} Nat (Int.gcd a ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) p)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall {a : Int} {p : Nat} [pp : Fact (Nat.Prime p)], Iff (Eq.{1} (ZMod p) (Int.cast.{0} (ZMod p) (Ring.toIntCast.{0} (ZMod p) (DivisionRing.toRing.{0} (ZMod p) (Field.toDivisionRing.{0} (ZMod p) (ZMod.instFieldZMod p pp)))) a) (OfNat.ofNat.{0} (ZMod p) 0 (Zero.toOfNat0.{0} (ZMod p) (CommMonoidWithZero.toZero.{0} (ZMod p) (CommGroupWithZero.toCommMonoidWithZero.{0} (ZMod p) (Semifield.toCommGroupWithZero.{0} (ZMod p) (Field.toSemifield.{0} (ZMod p) (ZMod.instFieldZMod p pp)))))))) (Ne.{1} Nat (Int.gcd a (Nat.cast.{0} Int instNatCastInt p)) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align zmod.eq_zero_iff_gcd_ne_one ZMod.eq_zero_iff_gcd_ne_oneₓ'. -/
/-- If `p` is a prime and `a` is an integer, then `a : zmod p` is zero if and only if
`gcd a p ≠ 1`. -/
theorem eq_zero_iff_gcd_ne_one {a : ℤ} {p : ℕ} [pp : Fact p.Prime] :
    (a : ZMod p) = 0 ↔ a.gcd p ≠ 1 := by
  rw [Ne, Int.gcd_comm, Int.gcd_eq_one_iff_coprime,
    (Nat.prime_iff_prime_int.1 pp.1).coprime_iff_not_dvd, Classical.not_not,
    int_coe_zmod_eq_zero_iff_dvd]
#align zmod.eq_zero_iff_gcd_ne_one ZMod.eq_zero_iff_gcd_ne_one

/- warning: zmod.ne_zero_of_gcd_eq_one -> ZMod.ne_zero_of_gcd_eq_one is a dubious translation:
lean 3 declaration is
  forall {a : Int} {p : Nat}, (Nat.Prime p) -> (Eq.{1} Nat (Int.gcd a ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) p)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) -> (Ne.{1} (ZMod p) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (ZMod p) (HasLiftT.mk.{1, 1} Int (ZMod p) (CoeTCₓ.coe.{1, 1} Int (ZMod p) (Int.castCoe.{0} (ZMod p) (AddGroupWithOne.toHasIntCast.{0} (ZMod p) (AddCommGroupWithOne.toAddGroupWithOne.{0} (ZMod p) (Ring.toAddCommGroupWithOne.{0} (ZMod p) (CommRing.toRing.{0} (ZMod p) (ZMod.commRing p)))))))) a) (OfNat.ofNat.{0} (ZMod p) 0 (OfNat.mk.{0} (ZMod p) 0 (Zero.zero.{0} (ZMod p) (MulZeroClass.toHasZero.{0} (ZMod p) (NonUnitalNonAssocSemiring.toMulZeroClass.{0} (ZMod p) (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} (ZMod p) (NonAssocRing.toNonUnitalNonAssocRing.{0} (ZMod p) (Ring.toNonAssocRing.{0} (ZMod p) (CommRing.toRing.{0} (ZMod p) (ZMod.commRing p)))))))))))
but is expected to have type
  forall {a : Int} {p : Nat}, (Nat.Prime p) -> (Eq.{1} Nat (Int.gcd a (Nat.cast.{0} Int instNatCastInt p)) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) -> (Ne.{1} (ZMod p) (Int.cast.{0} (ZMod p) (Ring.toIntCast.{0} (ZMod p) (CommRing.toRing.{0} (ZMod p) (ZMod.commRing p))) a) (OfNat.ofNat.{0} (ZMod p) 0 (Zero.toOfNat0.{0} (ZMod p) (CommMonoidWithZero.toZero.{0} (ZMod p) (CommSemiring.toCommMonoidWithZero.{0} (ZMod p) (CommRing.toCommSemiring.{0} (ZMod p) (ZMod.commRing p)))))))
Case conversion may be inaccurate. Consider using '#align zmod.ne_zero_of_gcd_eq_one ZMod.ne_zero_of_gcd_eq_oneₓ'. -/
/-- If an integer `a` and a prime `p` satisfy `gcd a p = 1`, then `a : zmod p` is nonzero. -/
theorem ne_zero_of_gcd_eq_one {a : ℤ} {p : ℕ} (pp : p.Prime) (h : a.gcd p = 1) : (a : ZMod p) ≠ 0 :=
  mt (@eq_zero_iff_gcd_ne_one a p ⟨pp⟩).mp (Classical.not_not.mpr h)
#align zmod.ne_zero_of_gcd_eq_one ZMod.ne_zero_of_gcd_eq_one

/- warning: zmod.eq_zero_of_gcd_ne_one -> ZMod.eq_zero_of_gcd_ne_one is a dubious translation:
lean 3 declaration is
  forall {a : Int} {p : Nat}, (Nat.Prime p) -> (Ne.{1} Nat (Int.gcd a ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) p)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) -> (Eq.{1} (ZMod p) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (ZMod p) (HasLiftT.mk.{1, 1} Int (ZMod p) (CoeTCₓ.coe.{1, 1} Int (ZMod p) (Int.castCoe.{0} (ZMod p) (AddGroupWithOne.toHasIntCast.{0} (ZMod p) (AddCommGroupWithOne.toAddGroupWithOne.{0} (ZMod p) (Ring.toAddCommGroupWithOne.{0} (ZMod p) (CommRing.toRing.{0} (ZMod p) (ZMod.commRing p)))))))) a) (OfNat.ofNat.{0} (ZMod p) 0 (OfNat.mk.{0} (ZMod p) 0 (Zero.zero.{0} (ZMod p) (MulZeroClass.toHasZero.{0} (ZMod p) (NonUnitalNonAssocSemiring.toMulZeroClass.{0} (ZMod p) (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} (ZMod p) (NonAssocRing.toNonUnitalNonAssocRing.{0} (ZMod p) (Ring.toNonAssocRing.{0} (ZMod p) (CommRing.toRing.{0} (ZMod p) (ZMod.commRing p)))))))))))
but is expected to have type
  forall {a : Int} {p : Nat}, (Nat.Prime p) -> (Ne.{1} Nat (Int.gcd a (Nat.cast.{0} Int instNatCastInt p)) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) -> (Eq.{1} (ZMod p) (Int.cast.{0} (ZMod p) (Ring.toIntCast.{0} (ZMod p) (CommRing.toRing.{0} (ZMod p) (ZMod.commRing p))) a) (OfNat.ofNat.{0} (ZMod p) 0 (Zero.toOfNat0.{0} (ZMod p) (CommMonoidWithZero.toZero.{0} (ZMod p) (CommSemiring.toCommMonoidWithZero.{0} (ZMod p) (CommRing.toCommSemiring.{0} (ZMod p) (ZMod.commRing p)))))))
Case conversion may be inaccurate. Consider using '#align zmod.eq_zero_of_gcd_ne_one ZMod.eq_zero_of_gcd_ne_oneₓ'. -/
/-- If an integer `a` and a prime `p` satisfy `gcd a p ≠ 1`, then `a : zmod p` is zero. -/
theorem eq_zero_of_gcd_ne_one {a : ℤ} {p : ℕ} (pp : p.Prime) (h : a.gcd p ≠ 1) : (a : ZMod p) = 0 :=
  (@eq_zero_iff_gcd_ne_one a p ⟨pp⟩).mpr h
#align zmod.eq_zero_of_gcd_ne_one ZMod.eq_zero_of_gcd_ne_one

end ZMod

