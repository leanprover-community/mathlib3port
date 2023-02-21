/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module data.int.cast.field
! leanprover-community/mathlib commit bd9851ca476957ea4549eb19b40e7b5ade9428cc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Int.Cast.Lemmas
import Mathbin.Algebra.Field.Defs
import Mathbin.Algebra.GroupWithZero.Units.Lemmas

/-!
# Cast of integers into fields

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file concerns the canonical homomorphism `ℤ → F`, where `F` is a field.

## Main results

 * `int.cast_div`: if `n` divides `m`, then `↑(m / n) = ↑m / ↑n`
-/


namespace Int

open Nat

variable {α : Type _}

/- warning: int.cast_neg_nat_cast -> Int.cast_neg_natCast is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Field.{u1} R] (n : Nat), Eq.{succ u1} R ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int R (HasLiftT.mk.{1, succ u1} Int R (CoeTCₓ.coe.{1, succ u1} Int R (Int.castCoe.{u1} R (AddGroupWithOne.toHasIntCast.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R _inst_1)))))))) (Neg.neg.{0} Int Int.hasNeg ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n))) (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R _inst_1))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R _inst_1))))))))) n))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Field.{u1} R] (n : Nat), Eq.{succ u1} R (Int.cast.{u1} R (Ring.toIntCast.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R _inst_1))) (Neg.neg.{0} Int Int.instNegInt (Nat.cast.{0} Int Int.instNatCastInt n))) (Neg.neg.{u1} R (Ring.toNeg.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R _inst_1))) (Nat.cast.{u1} R (NonAssocRing.toNatCast.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R _inst_1)))) n))
Case conversion may be inaccurate. Consider using '#align int.cast_neg_nat_cast Int.cast_neg_natCastₓ'. -/
/-- Auxiliary lemma for norm_cast to move the cast `-↑n` upwards to `↑-↑n`.

(The restriction to `field` is necessary, otherwise this would also apply in the case where
`R = ℤ` and cause nontermination.)
-/
@[norm_cast]
theorem cast_neg_natCast {R} [Field R] (n : ℕ) : ((-n : ℤ) : R) = -n := by simp
#align int.cast_neg_nat_cast Int.cast_neg_natCast

/- warning: int.cast_div -> Int.cast_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Field.{u1} α] {m : Int} {n : Int}, (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) n m) -> (Ne.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α (Field.toDivisionRing.{u1} α _inst_1)))))))) n) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α (Field.toDivisionRing.{u1} α _inst_1))))))))))) -> (Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α (Field.toDivisionRing.{u1} α _inst_1)))))))) (HDiv.hDiv.{0, 0, 0} Int Int Int (instHDiv.{0} Int Int.hasDiv) m n)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionRing.toDivInvMonoid.{u1} α (Field.toDivisionRing.{u1} α _inst_1)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α (Field.toDivisionRing.{u1} α _inst_1)))))))) m) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α (Field.toDivisionRing.{u1} α _inst_1)))))))) n)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Field.{u1} α] {m : Int} {n : Int}, (Dvd.dvd.{0} Int Int.instDvdInt n m) -> (Ne.{succ u1} α (Int.cast.{u1} α (Ring.toIntCast.{u1} α (DivisionRing.toRing.{u1} α (Field.toDivisionRing.{u1} α _inst_1))) n) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CommGroupWithZero.toCommMonoidWithZero.{u1} α (Semifield.toCommGroupWithZero.{u1} α (Field.toSemifield.{u1} α _inst_1))))))) -> (Eq.{succ u1} α (Int.cast.{u1} α (Ring.toIntCast.{u1} α (DivisionRing.toRing.{u1} α (Field.toDivisionRing.{u1} α _inst_1))) (HDiv.hDiv.{0, 0, 0} Int Int Int (instHDiv.{0} Int Int.instDivInt_1) m n)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (Field.toDiv.{u1} α _inst_1)) (Int.cast.{u1} α (Ring.toIntCast.{u1} α (DivisionRing.toRing.{u1} α (Field.toDivisionRing.{u1} α _inst_1))) m) (Int.cast.{u1} α (Ring.toIntCast.{u1} α (DivisionRing.toRing.{u1} α (Field.toDivisionRing.{u1} α _inst_1))) n)))
Case conversion may be inaccurate. Consider using '#align int.cast_div Int.cast_divₓ'. -/
@[simp]
theorem cast_div [Field α] {m n : ℤ} (n_dvd : n ∣ m) (n_nonzero : (n : α) ≠ 0) :
    ((m / n : ℤ) : α) = m / n := by
  rcases n_dvd with ⟨k, rfl⟩
  have : n ≠ 0 := by
    rintro rfl
    simpa using n_nonzero
  rw [Int.mul_ediv_cancel_left _ this, Int.cast_mul, mul_div_cancel_left _ n_nonzero]
#align int.cast_div Int.cast_div

end Int

