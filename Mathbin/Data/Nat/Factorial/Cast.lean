/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.nat.factorial.cast
! leanprover-community/mathlib commit 69c6a5a12d8a2b159f20933e60115a4f2de62b58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.Polynomial.Pochhammer

/-!
# Cast of factorials

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file allows calculating factorials (including ascending and descending ones) as elements of a
semiring.

This is particularly crucial for `nat.desc_factorial` as subtraction on `ℕ` does **not** correspond
to subtraction on a general semiring. For example, we can't rely on existing cast lemmas to prove
`↑(a.desc_factorial 2) = ↑a * (↑a - 1)`. We must use the fact that, whenever `↑(a - 1)` is not equal
to `↑a - 1`, the other factor is `0` anyway.
-/


open Nat

variable (S : Type _)

namespace Nat

section Semiring

variable [Semiring S] (a b : ℕ)

/- warning: nat.cast_asc_factorial -> Nat.cast_ascFactorial is a dubious translation:
lean 3 declaration is
  forall (S : Type.{u1}) [_inst_1 : Semiring.{u1} S] (a : Nat) (b : Nat), Eq.{succ u1} S ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat S (HasLiftT.mk.{1, succ u1} Nat S (CoeTCₓ.coe.{1, succ u1} Nat S (Nat.castCoe.{u1} S (AddMonoidWithOne.toNatCast.{u1} S (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} S (NonAssocSemiring.toAddCommMonoidWithOne.{u1} S (Semiring.toNonAssocSemiring.{u1} S _inst_1))))))) (Nat.ascFactorial a b)) (Polynomial.eval.{u1} S _inst_1 (HAdd.hAdd.{u1, u1, u1} S S S (instHAdd.{u1} S (Distrib.toHasAdd.{u1} S (NonUnitalNonAssocSemiring.toDistrib.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S _inst_1))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat S (HasLiftT.mk.{1, succ u1} Nat S (CoeTCₓ.coe.{1, succ u1} Nat S (Nat.castCoe.{u1} S (AddMonoidWithOne.toNatCast.{u1} S (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} S (NonAssocSemiring.toAddCommMonoidWithOne.{u1} S (Semiring.toNonAssocSemiring.{u1} S _inst_1))))))) a) (OfNat.ofNat.{u1} S 1 (OfNat.mk.{u1} S 1 (One.one.{u1} S (AddMonoidWithOne.toOne.{u1} S (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} S (NonAssocSemiring.toAddCommMonoidWithOne.{u1} S (Semiring.toNonAssocSemiring.{u1} S _inst_1)))))))) (pochhammer.{u1} S _inst_1 b))
but is expected to have type
  forall (S : Type.{u1}) [_inst_1 : Semiring.{u1} S] (a : Nat) (b : Nat), Eq.{succ u1} S (Nat.cast.{u1} S (Semiring.toNatCast.{u1} S _inst_1) (Nat.ascFactorial a b)) (Polynomial.eval.{u1} S _inst_1 (HAdd.hAdd.{u1, u1, u1} S S S (instHAdd.{u1} S (Distrib.toAdd.{u1} S (NonUnitalNonAssocSemiring.toDistrib.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S _inst_1))))) (Nat.cast.{u1} S (Semiring.toNatCast.{u1} S _inst_1) a) (OfNat.ofNat.{u1} S 1 (One.toOfNat1.{u1} S (Semiring.toOne.{u1} S _inst_1)))) (pochhammer.{u1} S _inst_1 b))
Case conversion may be inaccurate. Consider using '#align nat.cast_asc_factorial Nat.cast_ascFactorialₓ'. -/
theorem cast_ascFactorial : (a.ascFactorial b : S) = (pochhammer S b).eval (a + 1) := by
  rw [← pochhammer_nat_eq_ascFactorial, pochhammer_eval_cast, Nat.cast_add, Nat.cast_one]
#align nat.cast_asc_factorial Nat.cast_ascFactorial

#print Nat.cast_descFactorial /-
theorem cast_descFactorial : (a.descFactorial b : S) = (pochhammer S b).eval (a - (b - 1) : ℕ) :=
  by
  rw [← pochhammer_eval_cast, pochhammer_nat_eq_descFactorial]
  cases b
  · simp_rw [desc_factorial_zero]
  simp_rw [add_succ, succ_sub_one]
  obtain h | h := le_total a b
  · rw [desc_factorial_of_lt (lt_succ_of_le h), desc_factorial_of_lt (lt_succ_of_le _)]
    rw [tsub_eq_zero_iff_le.mpr h, zero_add]
  · rw [tsub_add_cancel_of_le h]
#align nat.cast_desc_factorial Nat.cast_descFactorial
-/

#print Nat.cast_factorial /-
theorem cast_factorial : (a ! : S) = (pochhammer S a).eval 1 := by
  rw [← zero_asc_factorial, cast_asc_factorial, cast_zero, zero_add]
#align nat.cast_factorial Nat.cast_factorial
-/

end Semiring

section Ring

variable [Ring S] (a b : ℕ)

/- warning: nat.cast_desc_factorial_two -> Nat.cast_descFactorial_two is a dubious translation:
lean 3 declaration is
  forall (S : Type.{u1}) [_inst_1 : Ring.{u1} S] (a : Nat), Eq.{succ u1} S ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat S (HasLiftT.mk.{1, succ u1} Nat S (CoeTCₓ.coe.{1, succ u1} Nat S (Nat.castCoe.{u1} S (AddMonoidWithOne.toNatCast.{u1} S (AddGroupWithOne.toAddMonoidWithOne.{u1} S (AddCommGroupWithOne.toAddGroupWithOne.{u1} S (Ring.toAddCommGroupWithOne.{u1} S _inst_1))))))) (Nat.descFactorial a (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (HMul.hMul.{u1, u1, u1} S S S (instHMul.{u1} S (Distrib.toHasMul.{u1} S (Ring.toDistrib.{u1} S _inst_1))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat S (HasLiftT.mk.{1, succ u1} Nat S (CoeTCₓ.coe.{1, succ u1} Nat S (Nat.castCoe.{u1} S (AddMonoidWithOne.toNatCast.{u1} S (AddGroupWithOne.toAddMonoidWithOne.{u1} S (AddCommGroupWithOne.toAddGroupWithOne.{u1} S (Ring.toAddCommGroupWithOne.{u1} S _inst_1))))))) a) (HSub.hSub.{u1, u1, u1} S S S (instHSub.{u1} S (SubNegMonoid.toHasSub.{u1} S (AddGroup.toSubNegMonoid.{u1} S (AddGroupWithOne.toAddGroup.{u1} S (AddCommGroupWithOne.toAddGroupWithOne.{u1} S (Ring.toAddCommGroupWithOne.{u1} S _inst_1)))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat S (HasLiftT.mk.{1, succ u1} Nat S (CoeTCₓ.coe.{1, succ u1} Nat S (Nat.castCoe.{u1} S (AddMonoidWithOne.toNatCast.{u1} S (AddGroupWithOne.toAddMonoidWithOne.{u1} S (AddCommGroupWithOne.toAddGroupWithOne.{u1} S (Ring.toAddCommGroupWithOne.{u1} S _inst_1))))))) a) (OfNat.ofNat.{u1} S 1 (OfNat.mk.{u1} S 1 (One.one.{u1} S (AddMonoidWithOne.toOne.{u1} S (AddGroupWithOne.toAddMonoidWithOne.{u1} S (AddCommGroupWithOne.toAddGroupWithOne.{u1} S (Ring.toAddCommGroupWithOne.{u1} S _inst_1)))))))))
but is expected to have type
  forall (S : Type.{u1}) [_inst_1 : Ring.{u1} S] (a : Nat), Eq.{succ u1} S (Nat.cast.{u1} S (NonAssocRing.toNatCast.{u1} S (Ring.toNonAssocRing.{u1} S _inst_1)) (Nat.descFactorial a (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) (HMul.hMul.{u1, u1, u1} S S S (instHMul.{u1} S (NonUnitalNonAssocRing.toMul.{u1} S (NonAssocRing.toNonUnitalNonAssocRing.{u1} S (Ring.toNonAssocRing.{u1} S _inst_1)))) (Nat.cast.{u1} S (NonAssocRing.toNatCast.{u1} S (Ring.toNonAssocRing.{u1} S _inst_1)) a) (HSub.hSub.{u1, u1, u1} S S S (instHSub.{u1} S (Ring.toSub.{u1} S _inst_1)) (Nat.cast.{u1} S (NonAssocRing.toNatCast.{u1} S (Ring.toNonAssocRing.{u1} S _inst_1)) a) (OfNat.ofNat.{u1} S 1 (One.toOfNat1.{u1} S (NonAssocRing.toOne.{u1} S (Ring.toNonAssocRing.{u1} S _inst_1))))))
Case conversion may be inaccurate. Consider using '#align nat.cast_desc_factorial_two Nat.cast_descFactorial_twoₓ'. -/
/-- Convenience lemma. The `a - 1` is not using truncated subtraction, as opposed to the definition
of `nat.desc_factorial` as a natural. -/
theorem cast_descFactorial_two : (a.descFactorial 2 : S) = a * (a - 1) :=
  by
  rw [cast_desc_factorial]
  cases a
  · rw [zero_tsub, cast_zero, pochhammer_ne_zero_eval_zero _ two_ne_zero, MulZeroClass.zero_mul]
  ·
    rw [succ_sub_succ, tsub_zero, cast_succ, add_sub_cancel, pochhammer_succ_right, pochhammer_one,
      Polynomial.X_mul, Polynomial.eval_mul_X, Polynomial.eval_add, Polynomial.eval_X, cast_one,
      Polynomial.eval_one]
#align nat.cast_desc_factorial_two Nat.cast_descFactorial_two

end Ring

end Nat

