/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module algebra.char_zero.lemmas
! leanprover-community/mathlib commit dd71334db81d0bd444af1ee339a29298bef40734
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Cast.Field
import Mathbin.Algebra.GroupPower.Lemmas

/-!
# Characteristic zero (additional theorems)

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A ring `R` is called of characteristic zero if every natural number `n` is non-zero when considered
as an element of `R`. Since this definition doesn't mention the multiplicative structure of `R`
except for the existence of `1` in this file characteristic zero is defined for additive monoids
with `1`.

## Main statements

* Characteristic zero implies that the additive monoid is infinite.
-/


namespace Nat

variable {R : Type _} [AddMonoidWithOne R] [CharZero R]

#print Nat.castEmbedding /-
/-- `nat.cast` as an embedding into monoids of characteristic `0`. -/
@[simps]
def castEmbedding : ℕ ↪ R :=
  ⟨coe, cast_injective⟩
#align nat.cast_embedding Nat.castEmbedding
-/

#print Nat.cast_pow_eq_one /-
@[simp]
theorem cast_pow_eq_one {R : Type _} [Semiring R] [CharZero R] (q : ℕ) (n : ℕ) (hn : n ≠ 0) :
    (q : R) ^ n = 1 ↔ q = 1 := by
  rw [← cast_pow, cast_eq_one]
  exact pow_eq_one_iff hn
#align nat.cast_pow_eq_one Nat.cast_pow_eq_one
-/

/- warning: nat.cast_div_char_zero -> Nat.cast_div_charZero is a dubious translation:
lean 3 declaration is
  forall {k : Type.{u1}} [_inst_3 : Field.{u1} k] [_inst_4 : CharZero.{u1} k (AddGroupWithOne.toAddMonoidWithOne.{u1} k (NonAssocRing.toAddGroupWithOne.{u1} k (Ring.toNonAssocRing.{u1} k (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_3)))))] {m : Nat} {n : Nat}, (Dvd.Dvd.{0} Nat Nat.hasDvd n m) -> (Eq.{succ u1} k ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat k (HasLiftT.mk.{1, succ u1} Nat k (CoeTCₓ.coe.{1, succ u1} Nat k (Nat.castCoe.{u1} k (AddMonoidWithOne.toNatCast.{u1} k (AddGroupWithOne.toAddMonoidWithOne.{u1} k (NonAssocRing.toAddGroupWithOne.{u1} k (Ring.toNonAssocRing.{u1} k (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_3))))))))) (HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.hasDiv) m n)) (HDiv.hDiv.{u1, u1, u1} k k k (instHDiv.{u1} k (DivInvMonoid.toHasDiv.{u1} k (DivisionRing.toDivInvMonoid.{u1} k (Field.toDivisionRing.{u1} k _inst_3)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat k (HasLiftT.mk.{1, succ u1} Nat k (CoeTCₓ.coe.{1, succ u1} Nat k (Nat.castCoe.{u1} k (AddMonoidWithOne.toNatCast.{u1} k (AddGroupWithOne.toAddMonoidWithOne.{u1} k (NonAssocRing.toAddGroupWithOne.{u1} k (Ring.toNonAssocRing.{u1} k (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_3))))))))) m) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat k (HasLiftT.mk.{1, succ u1} Nat k (CoeTCₓ.coe.{1, succ u1} Nat k (Nat.castCoe.{u1} k (AddMonoidWithOne.toNatCast.{u1} k (AddGroupWithOne.toAddMonoidWithOne.{u1} k (NonAssocRing.toAddGroupWithOne.{u1} k (Ring.toNonAssocRing.{u1} k (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_3))))))))) n)))
but is expected to have type
  forall {k : Type.{u1}} [_inst_3 : Field.{u1} k] [_inst_4 : CharZero.{u1} k (AddGroupWithOne.toAddMonoidWithOne.{u1} k (Ring.toAddGroupWithOne.{u1} k (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_3))))] {m : Nat} {n : Nat}, (Dvd.dvd.{0} Nat Nat.instDvdNat n m) -> (Eq.{succ u1} k (Nat.cast.{u1} k (NonAssocRing.toNatCast.{u1} k (Ring.toNonAssocRing.{u1} k (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_3)))) (HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.instDivNat) m n)) (HDiv.hDiv.{u1, u1, u1} k k k (instHDiv.{u1} k (Field.toDiv.{u1} k _inst_3)) (Nat.cast.{u1} k (NonAssocRing.toNatCast.{u1} k (Ring.toNonAssocRing.{u1} k (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_3)))) m) (Nat.cast.{u1} k (NonAssocRing.toNatCast.{u1} k (Ring.toNonAssocRing.{u1} k (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_3)))) n)))
Case conversion may be inaccurate. Consider using '#align nat.cast_div_char_zero Nat.cast_div_charZeroₓ'. -/
@[simp, norm_cast]
theorem cast_div_charZero {k : Type _} [Field k] [CharZero k] {m n : ℕ} (n_dvd : n ∣ m) :
    ((m / n : ℕ) : k) = m / n :=
  by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  · exact cast_div n_dvd (cast_ne_zero.2 hn)
#align nat.cast_div_char_zero Nat.cast_div_charZero

end Nat

section

variable (M : Type _) [AddMonoidWithOne M] [CharZero M]

/- warning: char_zero.ne_zero.two -> CharZero.NeZero.two is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) [_inst_1 : AddMonoidWithOne.{u1} M] [_inst_2 : CharZero.{u1} M _inst_1], NeZero.{u1} M (AddZeroClass.toHasZero.{u1} M (AddMonoid.toAddZeroClass.{u1} M (AddMonoidWithOne.toAddMonoid.{u1} M _inst_1))) (OfNat.ofNat.{u1} M 2 (OfNat.mk.{u1} M 2 (bit0.{u1} M (AddZeroClass.toHasAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M (AddMonoidWithOne.toAddMonoid.{u1} M _inst_1))) (One.one.{u1} M (AddMonoidWithOne.toOne.{u1} M _inst_1)))))
but is expected to have type
  forall (M : Type.{u1}) [_inst_1 : AddMonoidWithOne.{u1} M] [_inst_2 : CharZero.{u1} M _inst_1], NeZero.{u1} M (AddMonoid.toZero.{u1} M (AddMonoidWithOne.toAddMonoid.{u1} M _inst_1)) (OfNat.ofNat.{u1} M 2 (instOfNat.{u1} M 2 (AddMonoidWithOne.toNatCast.{u1} M _inst_1) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))
Case conversion may be inaccurate. Consider using '#align char_zero.ne_zero.two CharZero.NeZero.twoₓ'. -/
instance CharZero.NeZero.two : NeZero (2 : M) :=
  ⟨by
    have : ((2 : ℕ) : M) ≠ 0 := Nat.cast_ne_zero.2 (by decide)
    rwa [Nat.cast_two] at this⟩
#align char_zero.ne_zero.two CharZero.NeZero.two

end

section

variable {R : Type _} [NonAssocSemiring R] [NoZeroDivisors R] [CharZero R] {a : R}

/- warning: add_self_eq_zero -> add_self_eq_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))] [_inst_3 : CharZero.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R _inst_1))] {a : R}, Iff (Eq.{succ u1} R (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))) a a) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))))))) (Eq.{succ u1} R a (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)) (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R _inst_1))] [_inst_3 : CharZero.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R _inst_1))] {a : R}, Iff (Eq.{succ u1} R (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))) a a) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R _inst_1))))) (Eq.{succ u1} R a (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align add_self_eq_zero add_self_eq_zeroₓ'. -/
@[simp]
theorem add_self_eq_zero {a : R} : a + a = 0 ↔ a = 0 := by
  simp only [(two_mul a).symm, mul_eq_zero, two_ne_zero, false_or_iff]
#align add_self_eq_zero add_self_eq_zero

/- warning: bit0_eq_zero -> bit0_eq_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))] [_inst_3 : CharZero.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R _inst_1))] {a : R}, Iff (Eq.{succ u1} R (bit0.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) a) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))))))) (Eq.{succ u1} R a (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)) (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R _inst_1))] [_inst_3 : CharZero.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R _inst_1))] {a : R}, Iff (Eq.{succ u1} R (bit0.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) a) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R _inst_1))))) (Eq.{succ u1} R a (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align bit0_eq_zero bit0_eq_zeroₓ'. -/
@[simp]
theorem bit0_eq_zero {a : R} : bit0 a = 0 ↔ a = 0 :=
  add_self_eq_zero
#align bit0_eq_zero bit0_eq_zero

/- warning: zero_eq_bit0 -> zero_eq_bit0 is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))] [_inst_3 : CharZero.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R _inst_1))] {a : R}, Iff (Eq.{succ u1} R (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))) (bit0.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) a)) (Eq.{succ u1} R a (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)) (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R _inst_1))] [_inst_3 : CharZero.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R _inst_1))] {a : R}, Iff (Eq.{succ u1} R (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R _inst_1)))) (bit0.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) a)) (Eq.{succ u1} R a (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align zero_eq_bit0 zero_eq_bit0ₓ'. -/
@[simp]
theorem zero_eq_bit0 {a : R} : 0 = bit0 a ↔ a = 0 :=
  by
  rw [eq_comm]
  exact bit0_eq_zero
#align zero_eq_bit0 zero_eq_bit0

/- warning: bit0_ne_zero -> bit0_ne_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))] [_inst_3 : CharZero.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R _inst_1))] {a : R}, Iff (Ne.{succ u1} R (bit0.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) a) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))))))) (Ne.{succ u1} R a (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)) (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R _inst_1))] [_inst_3 : CharZero.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R _inst_1))] {a : R}, Iff (Ne.{succ u1} R (bit0.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) a) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R _inst_1))))) (Ne.{succ u1} R a (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align bit0_ne_zero bit0_ne_zeroₓ'. -/
theorem bit0_ne_zero : bit0 a ≠ 0 ↔ a ≠ 0 :=
  bit0_eq_zero.Not
#align bit0_ne_zero bit0_ne_zero

/- warning: zero_ne_bit0 -> zero_ne_bit0 is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))] [_inst_3 : CharZero.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R _inst_1))] {a : R}, Iff (Ne.{succ u1} R (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))) (bit0.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) a)) (Ne.{succ u1} R a (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)) (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R _inst_1))] [_inst_3 : CharZero.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R _inst_1))] {a : R}, Iff (Ne.{succ u1} R (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R _inst_1)))) (bit0.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) a)) (Ne.{succ u1} R a (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align zero_ne_bit0 zero_ne_bit0ₓ'. -/
theorem zero_ne_bit0 : 0 ≠ bit0 a ↔ a ≠ 0 :=
  zero_eq_bit0.Not
#align zero_ne_bit0 zero_ne_bit0

end

section

variable {R : Type _} [NonAssocRing R] [NoZeroDivisors R] [CharZero R]

/- warning: neg_eq_self_iff -> neg_eq_self_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonAssocRing.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))] [_inst_3 : CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))] {a : R}, Iff (Eq.{succ u1} R (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1)))) a) a) (Eq.{succ u1} R a (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonAssocRing.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R _inst_1)))] [_inst_3 : CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))] {a : R}, Iff (Eq.{succ u1} R (Neg.neg.{u1} R (AddGroupWithOne.toNeg.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1)) a) a) (Eq.{succ u1} R a (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R _inst_1))))))
Case conversion may be inaccurate. Consider using '#align neg_eq_self_iff neg_eq_self_iffₓ'. -/
theorem neg_eq_self_iff {a : R} : -a = a ↔ a = 0 :=
  neg_eq_iff_add_eq_zero.trans add_self_eq_zero
#align neg_eq_self_iff neg_eq_self_iff

/- warning: eq_neg_self_iff -> eq_neg_self_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonAssocRing.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))] [_inst_3 : CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))] {a : R}, Iff (Eq.{succ u1} R a (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1)))) a)) (Eq.{succ u1} R a (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonAssocRing.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R _inst_1)))] [_inst_3 : CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))] {a : R}, Iff (Eq.{succ u1} R a (Neg.neg.{u1} R (AddGroupWithOne.toNeg.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1)) a)) (Eq.{succ u1} R a (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R _inst_1))))))
Case conversion may be inaccurate. Consider using '#align eq_neg_self_iff eq_neg_self_iffₓ'. -/
theorem eq_neg_self_iff {a : R} : a = -a ↔ a = 0 :=
  eq_neg_iff_add_eq_zero.trans add_self_eq_zero
#align eq_neg_self_iff eq_neg_self_iff

/- warning: nat_mul_inj -> nat_mul_inj is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonAssocRing.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))] [_inst_3 : CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))] {n : Nat} {a : R} {b : R}, (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1)))))) n) a) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1)))))) n) b)) -> (Or (Eq.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Eq.{succ u1} R a b))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonAssocRing.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R _inst_1)))] [_inst_3 : CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))] {n : Nat} {a : R} {b : R}, (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1))) (Nat.cast.{u1} R (NonAssocRing.toNatCast.{u1} R _inst_1) n) a) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1))) (Nat.cast.{u1} R (NonAssocRing.toNatCast.{u1} R _inst_1) n) b)) -> (Or (Eq.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Eq.{succ u1} R a b))
Case conversion may be inaccurate. Consider using '#align nat_mul_inj nat_mul_injₓ'. -/
theorem nat_mul_inj {n : ℕ} {a b : R} (h : (n : R) * a = (n : R) * b) : n = 0 ∨ a = b :=
  by
  rw [← sub_eq_zero, ← mul_sub, mul_eq_zero, sub_eq_zero] at h
  exact_mod_cast h
#align nat_mul_inj nat_mul_inj

/- warning: nat_mul_inj' -> nat_mul_inj' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonAssocRing.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))] [_inst_3 : CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))] {n : Nat} {a : R} {b : R}, (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1)))))) n) a) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1)))))) n) b)) -> (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Eq.{succ u1} R a b)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonAssocRing.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R _inst_1)))] [_inst_3 : CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))] {n : Nat} {a : R} {b : R}, (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1))) (Nat.cast.{u1} R (NonAssocRing.toNatCast.{u1} R _inst_1) n) a) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1))) (Nat.cast.{u1} R (NonAssocRing.toNatCast.{u1} R _inst_1) n) b)) -> (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Eq.{succ u1} R a b)
Case conversion may be inaccurate. Consider using '#align nat_mul_inj' nat_mul_inj'ₓ'. -/
theorem nat_mul_inj' {n : ℕ} {a b : R} (h : (n : R) * a = (n : R) * b) (w : n ≠ 0) : a = b := by
  simpa [w] using nat_mul_inj h
#align nat_mul_inj' nat_mul_inj'

/- warning: bit0_injective -> bit0_injective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonAssocRing.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))] [_inst_3 : CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))], Function.Injective.{succ u1, succ u1} R R (bit0.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonAssocRing.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R _inst_1)))] [_inst_3 : CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))], Function.Injective.{succ u1, succ u1} R R (bit0.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align bit0_injective bit0_injectiveₓ'. -/
theorem bit0_injective : Function.Injective (bit0 : R → R) := fun a b h =>
  by
  dsimp [bit0] at h
  simp only [(two_mul a).symm, (two_mul b).symm] at h
  refine' nat_mul_inj' _ two_ne_zero
  exact_mod_cast h
#align bit0_injective bit0_injective

/- warning: bit1_injective -> bit1_injective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonAssocRing.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))] [_inst_3 : CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))], Function.Injective.{succ u1, succ u1} R R (bit1.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))) (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonAssocRing.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R _inst_1)))] [_inst_3 : CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))], Function.Injective.{succ u1, succ u1} R R (bit1.{u1} R (NonAssocRing.toOne.{u1} R _inst_1) (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align bit1_injective bit1_injectiveₓ'. -/
theorem bit1_injective : Function.Injective (bit1 : R → R) := fun a b h =>
  by
  simp only [bit1, add_left_inj] at h
  exact bit0_injective h
#align bit1_injective bit1_injective

/- warning: bit0_eq_bit0 -> bit0_eq_bit0 is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonAssocRing.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))] [_inst_3 : CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))] {a : R} {b : R}, Iff (Eq.{succ u1} R (bit0.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))) a) (bit0.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))) b)) (Eq.{succ u1} R a b)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonAssocRing.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R _inst_1)))] [_inst_3 : CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))] {a : R} {b : R}, Iff (Eq.{succ u1} R (bit0.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))) a) (bit0.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))) b)) (Eq.{succ u1} R a b)
Case conversion may be inaccurate. Consider using '#align bit0_eq_bit0 bit0_eq_bit0ₓ'. -/
@[simp]
theorem bit0_eq_bit0 {a b : R} : bit0 a = bit0 b ↔ a = b :=
  bit0_injective.eq_iff
#align bit0_eq_bit0 bit0_eq_bit0

/- warning: bit1_eq_bit1 -> bit1_eq_bit1 is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonAssocRing.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))] [_inst_3 : CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))] {a : R} {b : R}, Iff (Eq.{succ u1} R (bit1.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))) (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))) a) (bit1.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))) (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))) b)) (Eq.{succ u1} R a b)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonAssocRing.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R _inst_1)))] [_inst_3 : CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))] {a : R} {b : R}, Iff (Eq.{succ u1} R (bit1.{u1} R (NonAssocRing.toOne.{u1} R _inst_1) (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))) a) (bit1.{u1} R (NonAssocRing.toOne.{u1} R _inst_1) (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))) b)) (Eq.{succ u1} R a b)
Case conversion may be inaccurate. Consider using '#align bit1_eq_bit1 bit1_eq_bit1ₓ'. -/
@[simp]
theorem bit1_eq_bit1 {a b : R} : bit1 a = bit1 b ↔ a = b :=
  bit1_injective.eq_iff
#align bit1_eq_bit1 bit1_eq_bit1

/- warning: bit1_eq_one -> bit1_eq_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonAssocRing.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))] [_inst_3 : CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))] {a : R}, Iff (Eq.{succ u1} R (bit1.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))) (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))) a) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))))))) (Eq.{succ u1} R a (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonAssocRing.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R _inst_1)))] [_inst_3 : CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))] {a : R}, Iff (Eq.{succ u1} R (bit1.{u1} R (NonAssocRing.toOne.{u1} R _inst_1) (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))) a) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (NonAssocRing.toOne.{u1} R _inst_1)))) (Eq.{succ u1} R a (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R _inst_1))))))
Case conversion may be inaccurate. Consider using '#align bit1_eq_one bit1_eq_oneₓ'. -/
@[simp]
theorem bit1_eq_one {a : R} : bit1 a = 1 ↔ a = 0 := by
  rw [show (1 : R) = bit1 0 by simp, bit1_eq_bit1]
#align bit1_eq_one bit1_eq_one

/- warning: one_eq_bit1 -> one_eq_bit1 is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonAssocRing.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))] [_inst_3 : CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))] {a : R}, Iff (Eq.{succ u1} R (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1)))))) (bit1.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))) (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))) a)) (Eq.{succ u1} R a (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonAssocRing.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R _inst_1)))] [_inst_3 : CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))] {a : R}, Iff (Eq.{succ u1} R (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (NonAssocRing.toOne.{u1} R _inst_1))) (bit1.{u1} R (NonAssocRing.toOne.{u1} R _inst_1) (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))) a)) (Eq.{succ u1} R a (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R _inst_1))))))
Case conversion may be inaccurate. Consider using '#align one_eq_bit1 one_eq_bit1ₓ'. -/
@[simp]
theorem one_eq_bit1 {a : R} : 1 = bit1 a ↔ a = 0 :=
  by
  rw [eq_comm]
  exact bit1_eq_one
#align one_eq_bit1 one_eq_bit1

end

section

variable {R : Type _} [DivisionRing R] [CharZero R]

/- warning: half_add_self -> half_add_self is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : DivisionRing.{u1} R] [_inst_2 : CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1))))] (a : R), Eq.{succ u1} R (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (DivInvMonoid.toHasDiv.{u1} R (DivisionRing.toDivInvMonoid.{u1} R _inst_1))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (DivisionRing.toRing.{u1} R _inst_1)))) a a) (OfNat.ofNat.{u1} R 2 (OfNat.mk.{u1} R 2 (bit0.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (DivisionRing.toRing.{u1} R _inst_1))) (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1)))))))))) a
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : DivisionRing.{u1} R] [_inst_2 : CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (Ring.toAddGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R _inst_1)))] (a : R), Eq.{succ u1} R (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (DivisionRing.toDiv.{u1} R _inst_1)) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1))))))) a a) (OfNat.ofNat.{u1} R 2 (instOfNat.{u1} R 2 (NonAssocRing.toNatCast.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1))) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) a
Case conversion may be inaccurate. Consider using '#align half_add_self half_add_selfₓ'. -/
@[simp]
theorem half_add_self (a : R) : (a + a) / 2 = a := by rw [← mul_two, mul_div_cancel a two_ne_zero]
#align half_add_self half_add_self

/- warning: add_halves' -> add_halves' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : DivisionRing.{u1} R] [_inst_2 : CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1))))] (a : R), Eq.{succ u1} R (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (DivisionRing.toRing.{u1} R _inst_1)))) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (DivInvMonoid.toHasDiv.{u1} R (DivisionRing.toDivInvMonoid.{u1} R _inst_1))) a (OfNat.ofNat.{u1} R 2 (OfNat.mk.{u1} R 2 (bit0.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (DivisionRing.toRing.{u1} R _inst_1))) (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1)))))))))) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (DivInvMonoid.toHasDiv.{u1} R (DivisionRing.toDivInvMonoid.{u1} R _inst_1))) a (OfNat.ofNat.{u1} R 2 (OfNat.mk.{u1} R 2 (bit0.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (DivisionRing.toRing.{u1} R _inst_1))) (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1))))))))))) a
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : DivisionRing.{u1} R] [_inst_2 : CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (Ring.toAddGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R _inst_1)))] (a : R), Eq.{succ u1} R (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1))))))) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (DivisionRing.toDiv.{u1} R _inst_1)) a (OfNat.ofNat.{u1} R 2 (instOfNat.{u1} R 2 (NonAssocRing.toNatCast.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1))) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (DivisionRing.toDiv.{u1} R _inst_1)) a (OfNat.ofNat.{u1} R 2 (instOfNat.{u1} R 2 (NonAssocRing.toNatCast.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1))) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) a
Case conversion may be inaccurate. Consider using '#align add_halves' add_halves'ₓ'. -/
@[simp]
theorem add_halves' (a : R) : a / 2 + a / 2 = a := by rw [← add_div, half_add_self]
#align add_halves' add_halves'

/- warning: sub_half -> sub_half is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : DivisionRing.{u1} R] [_inst_2 : CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1))))] (a : R), Eq.{succ u1} R (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1))))))) a (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (DivInvMonoid.toHasDiv.{u1} R (DivisionRing.toDivInvMonoid.{u1} R _inst_1))) a (OfNat.ofNat.{u1} R 2 (OfNat.mk.{u1} R 2 (bit0.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (DivisionRing.toRing.{u1} R _inst_1))) (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1))))))))))) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (DivInvMonoid.toHasDiv.{u1} R (DivisionRing.toDivInvMonoid.{u1} R _inst_1))) a (OfNat.ofNat.{u1} R 2 (OfNat.mk.{u1} R 2 (bit0.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (DivisionRing.toRing.{u1} R _inst_1))) (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : DivisionRing.{u1} R] [_inst_2 : CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (Ring.toAddGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R _inst_1)))] (a : R), Eq.{succ u1} R (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (DivisionRing.toRing.{u1} R _inst_1))) a (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (DivisionRing.toDiv.{u1} R _inst_1)) a (OfNat.ofNat.{u1} R 2 (instOfNat.{u1} R 2 (NonAssocRing.toNatCast.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1))) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (DivisionRing.toDiv.{u1} R _inst_1)) a (OfNat.ofNat.{u1} R 2 (instOfNat.{u1} R 2 (NonAssocRing.toNatCast.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1))) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
Case conversion may be inaccurate. Consider using '#align sub_half sub_halfₓ'. -/
theorem sub_half (a : R) : a - a / 2 = a / 2 := by rw [sub_eq_iff_eq_add, add_halves']
#align sub_half sub_half

/- warning: half_sub -> half_sub is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : DivisionRing.{u1} R] [_inst_2 : CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1))))] (a : R), Eq.{succ u1} R (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1))))))) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (DivInvMonoid.toHasDiv.{u1} R (DivisionRing.toDivInvMonoid.{u1} R _inst_1))) a (OfNat.ofNat.{u1} R 2 (OfNat.mk.{u1} R 2 (bit0.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (DivisionRing.toRing.{u1} R _inst_1))) (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1)))))))))) a) (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (DivInvMonoid.toHasDiv.{u1} R (DivisionRing.toDivInvMonoid.{u1} R _inst_1))) a (OfNat.ofNat.{u1} R 2 (OfNat.mk.{u1} R 2 (bit0.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (DivisionRing.toRing.{u1} R _inst_1))) (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1)))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : DivisionRing.{u1} R] [_inst_2 : CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (Ring.toAddGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R _inst_1)))] (a : R), Eq.{succ u1} R (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (DivisionRing.toRing.{u1} R _inst_1))) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (DivisionRing.toDiv.{u1} R _inst_1)) a (OfNat.ofNat.{u1} R 2 (instOfNat.{u1} R 2 (NonAssocRing.toNatCast.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1))) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) a) (Neg.neg.{u1} R (Ring.toNeg.{u1} R (DivisionRing.toRing.{u1} R _inst_1)) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (DivisionRing.toDiv.{u1} R _inst_1)) a (OfNat.ofNat.{u1} R 2 (instOfNat.{u1} R 2 (NonAssocRing.toNatCast.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1))) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))
Case conversion may be inaccurate. Consider using '#align half_sub half_subₓ'. -/
theorem half_sub (a : R) : a / 2 - a = -(a / 2) := by rw [← neg_sub, sub_half]
#align half_sub half_sub

end

namespace WithTop

instance {R : Type _} [AddMonoidWithOne R] [CharZero R] : CharZero (WithTop R)
    where cast_injective m n h := by rwa [← coe_nat, ← coe_nat n, coe_eq_coe, Nat.cast_inj] at h

end WithTop

section RingHom

variable {R S : Type _} [NonAssocSemiring R] [NonAssocSemiring S]

/- warning: ring_hom.char_zero -> RingHom.charZero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : NonAssocSemiring.{u1} R] [_inst_2 : NonAssocSemiring.{u2} S], (RingHom.{u1, u2} R S _inst_1 _inst_2) -> (forall [hS : CharZero.{u2} S (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} S (NonAssocSemiring.toAddCommMonoidWithOne.{u2} S _inst_2))], CharZero.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R _inst_1)))
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u1}} [_inst_1 : NonAssocSemiring.{u2} R] [_inst_2 : NonAssocSemiring.{u1} S], (RingHom.{u2, u1} R S _inst_1 _inst_2) -> (forall [hS : CharZero.{u1} S (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} S (NonAssocSemiring.toAddCommMonoidWithOne.{u1} S _inst_2))], CharZero.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R _inst_1)))
Case conversion may be inaccurate. Consider using '#align ring_hom.char_zero RingHom.charZeroₓ'. -/
theorem RingHom.charZero (ϕ : R →+* S) [hS : CharZero S] : CharZero R :=
  ⟨fun a b h => CharZero.cast_injective (by rw [← map_nat_cast ϕ, ← map_nat_cast ϕ, h])⟩
#align ring_hom.char_zero RingHom.charZero

/- warning: ring_hom.char_zero_iff -> RingHom.charZero_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : NonAssocSemiring.{u1} R] [_inst_2 : NonAssocSemiring.{u2} S] {ϕ : RingHom.{u1, u2} R S _inst_1 _inst_2}, (Function.Injective.{succ u1, succ u2} R S (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S _inst_1 _inst_2) (fun (_x : RingHom.{u1, u2} R S _inst_1 _inst_2) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S _inst_1 _inst_2) ϕ)) -> (Iff (CharZero.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R _inst_1))) (CharZero.{u2} S (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} S (NonAssocSemiring.toAddCommMonoidWithOne.{u2} S _inst_2))))
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u1}} [_inst_1 : NonAssocSemiring.{u2} R] [_inst_2 : NonAssocSemiring.{u1} S] {ϕ : RingHom.{u2, u1} R S _inst_1 _inst_2}, (Function.Injective.{succ u2, succ u1} R S (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RingHom.{u2, u1} R S _inst_1 _inst_2) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S _inst_1 _inst_2) R S (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toMul.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S _inst_2)) (NonUnitalRingHomClass.toMulHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S _inst_1 _inst_2) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S _inst_2) (RingHomClass.toNonUnitalRingHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S _inst_1 _inst_2) R S _inst_1 _inst_2 (RingHom.instRingHomClassRingHom.{u2, u1} R S _inst_1 _inst_2)))) ϕ)) -> (Iff (CharZero.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R _inst_1))) (CharZero.{u1} S (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} S (NonAssocSemiring.toAddCommMonoidWithOne.{u1} S _inst_2))))
Case conversion may be inaccurate. Consider using '#align ring_hom.char_zero_iff RingHom.charZero_iffₓ'. -/
theorem RingHom.charZero_iff {ϕ : R →+* S} (hϕ : Function.Injective ϕ) : CharZero R ↔ CharZero S :=
  ⟨fun hR =>
    ⟨by intro a b h <;> rwa [← @Nat.cast_inj R, ← hϕ.eq_iff, map_nat_cast ϕ, map_nat_cast ϕ]⟩,
    fun hS => ϕ.char_zero⟩
#align ring_hom.char_zero_iff RingHom.charZero_iff

/- warning: ring_hom.injective_nat -> RingHom.injective_nat is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} R] (f : RingHom.{0, u1} Nat R (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring) _inst_1) [_inst_3 : CharZero.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R _inst_1))], Function.Injective.{1, succ u1} Nat R (coeFn.{succ u1, succ u1} (RingHom.{0, u1} Nat R (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring) _inst_1) (fun (_x : RingHom.{0, u1} Nat R (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring) _inst_1) => Nat -> R) (RingHom.hasCoeToFun.{0, u1} Nat R (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring) _inst_1) f)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} R] (f : RingHom.{0, u1} Nat R (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring) _inst_1) [_inst_3 : CharZero.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R _inst_1))], Function.Injective.{1, succ u1} Nat R (FunLike.coe.{succ u1, 1, succ u1} (RingHom.{0, u1} Nat R (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring) _inst_1) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Nat) => R) _x) (MulHomClass.toFunLike.{u1, 0, u1} (RingHom.{0, u1} Nat R (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring) _inst_1) Nat R (NonUnitalNonAssocSemiring.toMul.{0} Nat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)) (NonUnitalRingHomClass.toMulHomClass.{u1, 0, u1} (RingHom.{0, u1} Nat R (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring) _inst_1) Nat R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1) (RingHomClass.toNonUnitalRingHomClass.{u1, 0, u1} (RingHom.{0, u1} Nat R (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring) _inst_1) Nat R (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring) _inst_1 (RingHom.instRingHomClassRingHom.{0, u1} Nat R (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring) _inst_1)))) f)
Case conversion may be inaccurate. Consider using '#align ring_hom.injective_nat RingHom.injective_natₓ'. -/
theorem RingHom.injective_nat (f : ℕ →+* R) [CharZero R] : Function.Injective f :=
  Subsingleton.elim (Nat.castRingHom _) f ▸ Nat.cast_injective
#align ring_hom.injective_nat RingHom.injective_nat

end RingHom

