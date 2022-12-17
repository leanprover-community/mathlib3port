/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner

! This file was ported from Lean 3 source module data.int.cast.basic
! leanprover-community/mathlib commit 706d88f2b8fdfeb0b22796433d7a6c1a010af9f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Int.Cast.Defs
import Mathbin.Algebra.Group.Basic

/-!
# Cast of integers (additional theorems)

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/670
> Any changes to this file require a corresponding PR to mathlib4.

This file proves additional properties about the *canonical* homomorphism from
the integers into an additive group with a one (`int.cast`).

There is also `data.int.cast.lemmas`,
which includes lemmas stated in terms of algebraic homomorphisms,
and results involving the order structure of `ℤ`.

By contrast, this file's only import beyond `data.int.cast.defs` is `algebra.group.basic`.
-/


universe u

namespace Nat

variable {R : Type u} [AddGroupWithOne R]

@[simp, norm_cast]
theorem cast_sub {m n} (h : m ≤ n) : ((n - m : ℕ) : R) = n - m :=
  eq_sub_of_add_eq <| by rw [← cast_add, Nat.sub_add_cancel h]
#align nat.cast_sub Nat.cast_subₓ

/- warning: nat.cast_pred -> Nat.cast_pred is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} R] {n : Nat}, (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) -> (Eq.{succ u1} R ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1))))) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R _inst_1)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1))))) n) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} R] {n : Nat}, (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) -> (Eq.{succ u1} R (Nat.cast.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (AddGroupWithOne.toSub.{u1} R _inst_1)) (Nat.cast.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)) n) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1))))))
Case conversion may be inaccurate. Consider using '#align nat.cast_pred Nat.cast_predₓ'. -/
@[simp, norm_cast]
theorem cast_pred : ∀ {n}, 0 < n → ((n - 1 : ℕ) : R) = n - 1
  | 0, h => by cases h
  | n + 1, h => by rw [cast_succ, add_sub_cancel] <;> rfl
#align nat.cast_pred Nat.cast_pred

end Nat

open Nat

namespace Int

variable {R : Type u} [AddGroupWithOne R]

@[simp]
theorem cast_negSucc (n : ℕ) : (-[n+1] : R) = -(n + 1 : ℕ) :=
  AddGroupWithOne.intCast_negSucc n
#align int.cast_neg_succ_of_nat Int.cast_negSuccₓ

@[simp, norm_cast]
theorem cast_zero : ((0 : ℤ) : R) = 0 :=
  (cast_of_nat 0).trans Nat.cast_zero
#align int.cast_zero Int.cast_zeroₓ

@[simp, norm_cast]
theorem cast_ofNat (n : ℕ) : ((n : ℤ) : R) = n :=
  cast_of_nat _
#align int.cast_coe_nat Int.cast_ofNatₓ

@[simp, norm_cast]
theorem cast_one : ((1 : ℤ) : R) = 1 :=
  show (((1 : ℕ) : ℤ) : R) = 1 by simp
#align int.cast_one Int.cast_oneₓ

@[simp, norm_cast]
theorem cast_neg : ∀ n, ((-n : ℤ) : R) = -n
  | (0 : ℕ) => by erw [cast_zero, neg_zero]
  | (n + 1 : ℕ) => by erw [cast_of_nat, cast_neg_succ_of_nat] <;> rfl
  | -[n+1] => by erw [cast_of_nat, cast_neg_succ_of_nat, neg_neg]
#align int.cast_neg Int.cast_negₓ

@[simp]
theorem cast_subNatNat (m n) : ((Int.subNatNat m n : ℤ) : R) = m - n := by
  unfold sub_nat_nat; cases e : n - m
  · simp only [sub_nat_nat, cast_of_nat]
    simp [e, Nat.le_of_sub_eq_zero e]
  ·
    rw [sub_nat_nat, cast_neg_succ_of_nat, Nat.add_one, ← e,
      Nat.cast_sub <| _root_.le_of_lt <| Nat.lt_of_sub_eq_succ e, neg_sub]
#align int.cast_sub_nat_nat Int.cast_subNatNatₓ

#print Int.negOfNat_eq /-
theorem negOfNat_eq (n : ℕ) : negOfNat n = -(n : ℤ) := by cases n <;> rfl
#align int.neg_of_nat_eq Int.negOfNat_eq
-/

/- warning: int.cast_neg_of_nat -> Int.cast_negOfNat is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} R] (n : Nat), Eq.{succ u1} R ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int R (HasLiftT.mk.{1, succ u1} Int R (CoeTCₓ.coe.{1, succ u1} Int R (Int.castCoe.{u1} R (AddGroupWithOne.toHasIntCast.{u1} R _inst_1)))) (Int.negOfNat n)) (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R _inst_1))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1))))) n))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} R] (n : Nat), Eq.{succ u1} R (Int.cast.{u1} R (AddGroupWithOne.toIntCast.{u1} R _inst_1) (Int.negOfNat n)) (Neg.neg.{u1} R (AddGroupWithOne.toNeg.{u1} R _inst_1) (Nat.cast.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)) n))
Case conversion may be inaccurate. Consider using '#align int.cast_neg_of_nat Int.cast_negOfNatₓ'. -/
@[simp]
theorem cast_negOfNat (n : ℕ) : ((negOfNat n : ℤ) : R) = -n := by simp [neg_of_nat_eq]
#align int.cast_neg_of_nat Int.cast_negOfNat

@[simp, norm_cast]
theorem cast_add : ∀ m n, ((m + n : ℤ) : R) = m + n
  | (m : ℕ), (n : ℕ) => by simp [← Int.ofNat_add]
  | (m : ℕ), -[n+1] => by erw [cast_sub_nat_nat, cast_coe_nat, cast_neg_succ_of_nat, sub_eq_add_neg]
  | -[m+1], (n : ℕ) => by
    erw [cast_sub_nat_nat, cast_coe_nat, cast_neg_succ_of_nat, sub_eq_iff_eq_add, add_assoc,
      eq_neg_add_iff_add_eq, ← Nat.cast_add, ← Nat.cast_add, Nat.add_comm]
  | -[m+1], -[n+1] =>
    show (-[m + n + 1+1] : R) = _ by
      rw [cast_neg_succ_of_nat, cast_neg_succ_of_nat, cast_neg_succ_of_nat, ← neg_add_rev, ←
        Nat.cast_add, Nat.add_right_comm m n 1, Nat.add_assoc, Nat.add_comm]
#align int.cast_add Int.cast_addₓ

@[simp, norm_cast]
theorem cast_sub (m n) : ((m - n : ℤ) : R) = m - n := by simp [Int.sub_eq_add_neg, sub_eq_add_neg]
#align int.cast_sub Int.cast_subₓ

#print Int.ofNat_bit0 /-
@[simp, norm_cast]
theorem ofNat_bit0 (n : ℕ) : (↑(bit0 n) : ℤ) = bit0 ↑n :=
  rfl
#align int.coe_nat_bit0 Int.ofNat_bit0
-/

#print Int.ofNat_bit1 /-
@[simp, norm_cast]
theorem ofNat_bit1 (n : ℕ) : (↑(bit1 n) : ℤ) = bit1 ↑n :=
  rfl
#align int.coe_nat_bit1 Int.ofNat_bit1
-/

/- warning: int.cast_bit0 -> Int.cast_bit0 is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} R] (n : Int), Eq.{succ u1} R ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int R (HasLiftT.mk.{1, succ u1} Int R (CoeTCₓ.coe.{1, succ u1} Int R (Int.castCoe.{u1} R (AddGroupWithOne.toHasIntCast.{u1} R _inst_1)))) (bit0.{0} Int Int.hasAdd n)) (bit0.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int R (HasLiftT.mk.{1, succ u1} Int R (CoeTCₓ.coe.{1, succ u1} Int R (Int.castCoe.{u1} R (AddGroupWithOne.toHasIntCast.{u1} R _inst_1)))) n))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} R] (n : Int), Eq.{succ u1} R (Int.cast.{u1} R (AddGroupWithOne.toIntCast.{u1} R _inst_1) (bit0.{0} Int Int.instAddInt n)) (bit0.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)))) (Int.cast.{u1} R (AddGroupWithOne.toIntCast.{u1} R _inst_1) n))
Case conversion may be inaccurate. Consider using '#align int.cast_bit0 Int.cast_bit0ₓ'. -/
@[simp, norm_cast]
theorem cast_bit0 (n : ℤ) : ((bit0 n : ℤ) : R) = bit0 n :=
  cast_add _ _
#align int.cast_bit0 Int.cast_bit0

/- warning: int.cast_bit1 -> Int.cast_bit1 is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} R] (n : Int), Eq.{succ u1} R ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int R (HasLiftT.mk.{1, succ u1} Int R (CoeTCₓ.coe.{1, succ u1} Int R (Int.castCoe.{u1} R (AddGroupWithOne.toHasIntCast.{u1} R _inst_1)))) (bit1.{0} Int Int.hasOne Int.hasAdd n)) (bit1.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)) (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int R (HasLiftT.mk.{1, succ u1} Int R (CoeTCₓ.coe.{1, succ u1} Int R (Int.castCoe.{u1} R (AddGroupWithOne.toHasIntCast.{u1} R _inst_1)))) n))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} R] (n : Int), Eq.{succ u1} R (Int.cast.{u1} R (AddGroupWithOne.toIntCast.{u1} R _inst_1) (bit1.{0} Int (One.ofOfNat1.{0} Int (instOfNatInt 1)) Int.instAddInt n)) (bit1.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)) (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)))) (Int.cast.{u1} R (AddGroupWithOne.toIntCast.{u1} R _inst_1) n))
Case conversion may be inaccurate. Consider using '#align int.cast_bit1 Int.cast_bit1ₓ'. -/
@[simp, norm_cast]
theorem cast_bit1 (n : ℤ) : ((bit1 n : ℤ) : R) = bit1 n := by
  rw [bit1, cast_add, cast_one, cast_bit0] <;> rfl
#align int.cast_bit1 Int.cast_bit1

/- warning: int.cast_two -> Int.cast_two is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} R], Eq.{succ u1} R ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int R (HasLiftT.mk.{1, succ u1} Int R (CoeTCₓ.coe.{1, succ u1} Int R (Int.castCoe.{u1} R (AddGroupWithOne.toHasIntCast.{u1} R _inst_1)))) (OfNat.ofNat.{0} Int 2 (OfNat.mk.{0} Int 2 (bit0.{0} Int Int.hasAdd (One.one.{0} Int Int.hasOne))))) (OfNat.ofNat.{u1} R 2 (OfNat.mk.{u1} R 2 (bit0.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)))) (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} R], Eq.{succ u1} R (Int.cast.{u1} R (AddGroupWithOne.toIntCast.{u1} R _inst_1) (OfNat.ofNat.{0} Int 2 (instOfNatInt 2))) (OfNat.ofNat.{u1} R 2 (instOfNat.{u1} R 2 (AddMonoidWithOne.toNatCast.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))
Case conversion may be inaccurate. Consider using '#align int.cast_two Int.cast_twoₓ'. -/
theorem cast_two : ((2 : ℤ) : R) = 2 := by simp
#align int.cast_two Int.cast_two

/- warning: int.cast_three -> Int.cast_three is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} R], Eq.{succ u1} R ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int R (HasLiftT.mk.{1, succ u1} Int R (CoeTCₓ.coe.{1, succ u1} Int R (Int.castCoe.{u1} R (AddGroupWithOne.toHasIntCast.{u1} R _inst_1)))) (OfNat.ofNat.{0} Int 3 (OfNat.mk.{0} Int 3 (bit1.{0} Int Int.hasOne Int.hasAdd (One.one.{0} Int Int.hasOne))))) (OfNat.ofNat.{u1} R 3 (OfNat.mk.{u1} R 3 (bit1.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)) (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)))) (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} R], Eq.{succ u1} R (Int.cast.{u1} R (AddGroupWithOne.toIntCast.{u1} R _inst_1) (OfNat.ofNat.{0} Int 3 (instOfNatInt 3))) (OfNat.ofNat.{u1} R 3 (instOfNat.{u1} R 3 (AddMonoidWithOne.toNatCast.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))
Case conversion may be inaccurate. Consider using '#align int.cast_three Int.cast_threeₓ'. -/
theorem cast_three : ((3 : ℤ) : R) = 3 := by simp
#align int.cast_three Int.cast_three

/- warning: int.cast_four -> Int.cast_four is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} R], Eq.{succ u1} R ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int R (HasLiftT.mk.{1, succ u1} Int R (CoeTCₓ.coe.{1, succ u1} Int R (Int.castCoe.{u1} R (AddGroupWithOne.toHasIntCast.{u1} R _inst_1)))) (OfNat.ofNat.{0} Int 4 (OfNat.mk.{0} Int 4 (bit0.{0} Int Int.hasAdd (bit0.{0} Int Int.hasAdd (One.one.{0} Int Int.hasOne)))))) (OfNat.ofNat.{u1} R 4 (OfNat.mk.{u1} R 4 (bit0.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)))) (bit0.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)))) (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} R], Eq.{succ u1} R (Int.cast.{u1} R (AddGroupWithOne.toIntCast.{u1} R _inst_1) (OfNat.ofNat.{0} Int 4 (instOfNatInt 4))) (OfNat.ofNat.{u1} R 4 (instOfNat.{u1} R 4 (AddMonoidWithOne.toNatCast.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))
Case conversion may be inaccurate. Consider using '#align int.cast_four Int.cast_fourₓ'. -/
theorem cast_four : ((4 : ℤ) : R) = 4 := by simp
#align int.cast_four Int.cast_four

end Int

