/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner
-/
import Mathbin.Data.Nat.Cast.Defs

/-!
# Cast of integers

This file defines the *canonical* homomorphism from the integers into an
additive group with a one (typically a `ring`).  In additive groups with a one
element, there exists a unique such homomorphism and we store it in the
`int_cast : ℤ → R` field.

Preferentially, the homomorphism is written as a coercion.

## Main declarations

* `int.cast`: Canonical homomorphism `ℤ → R`.
* `add_group_with_one`: Type class for `int.cast`.
-/


universe u

attribute [simp] Int.of_nat_eq_coe

/-- Default value for `add_group_with_one.int_cast`. -/
protected def Int.castDef {R : Type u} [HasNatCast R] [Neg R] : ℤ → R
  | (n : ℕ) => n
  | -[1 + n] => -(n + 1 : ℕ)

/-- Type class for the canonical homomorphism `ℤ → R`.
-/
class HasIntCast (R : Type u) where
  intCast : ℤ → R

/-- An `add_group_with_one` is an `add_group` with a `1`.
It also contains data for the unique homomorphisms `ℕ → R` and `ℤ → R`.
-/
@[protect_proj]
class AddGroupWithOne (R : Type u) extends HasIntCast R, AddGroup R, AddMonoidWithOne R where
  intCast := Int.castDef
  int_cast_of_nat : ∀ n : ℕ, int_cast n = (n : R) := by
    intros
    rfl
  int_cast_neg_succ_of_nat : ∀ n : ℕ, int_cast (-(n + 1 : ℕ)) = -((n + 1 : ℕ) : R) := by
    intros
    rfl

/-- An `add_comm_group_with_one` is an `add_group_with_one` satisfying `a + b = b + a`. -/
@[protect_proj]
class AddCommGroupWithOne (R : Type u) extends AddCommGroup R, AddGroupWithOne R

/- warning: int.cast -> Int.cast is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u}} [_inst_1 : HasIntCast.{u} R], Int -> R
but is expected to have type
  forall {R : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.719 : AddGroupWithOne.{u_1} R], Int -> R
Case conversion may be inaccurate. Consider using '#align int.cast Int.castₓ'. -/
/-- Canonical homomorphism from the integers to any ring(-like) structure `R` -/
protected def Int.cast {R : Type u} [HasIntCast R] (i : ℤ) : R :=
  HasIntCast.intCast i

namespace Nat

variable {R : Type u} [AddGroupWithOne R]

/- warning: nat.cast_sub -> Nat.cast_sub is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u}} [_inst_1 : AddGroupWithOne.{u} R] {m : Nat} {n : Nat}, (LE.le.{0} Nat Nat.hasLe m n) -> (Eq.{succ u} R ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Nat R (HasLiftT.mk.{1 succ u} Nat R (CoeTCₓ.coe.{1 succ u} Nat R (Nat.castCoe.{u} R (AddMonoidWithOne.toHasNatCast.{u} R (AddGroupWithOne.toAddMonoidWithOne.{u} R _inst_1))))) (HSub.hSub.{0 0 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n m)) (HSub.hSub.{u u u} R R R (instHSub.{u} R (SubNegMonoid.toHasSub.{u} R (AddGroup.toSubNegMonoid.{u} R (AddGroupWithOne.toAddGroup.{u} R _inst_1)))) ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Nat R (HasLiftT.mk.{1 succ u} Nat R (CoeTCₓ.coe.{1 succ u} Nat R (Nat.castCoe.{u} R (AddMonoidWithOne.toHasNatCast.{u} R (AddGroupWithOne.toAddMonoidWithOne.{u} R _inst_1))))) n) ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Nat R (HasLiftT.mk.{1 succ u} Nat R (CoeTCₓ.coe.{1 succ u} Nat R (Nat.castCoe.{u} R (AddMonoidWithOne.toHasNatCast.{u} R (AddGroupWithOne.toAddMonoidWithOne.{u} R _inst_1))))) m)))
but is expected to have type
  forall {R : Type.{u_1}} [inst._@.Mathlib.Data.Int.Cast.Defs._hyg.16 : AddGroupWithOne.{u_1} R] {m : Nat} {n : Nat}, (LE.le.{0} Nat instLENat m n) -> (Eq.{succ u_1} R (Nat.cast.{u_1} R (AddGroupWithOne.toAddMonoidWithOne.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.16) (HSub.hSub.{0 0 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n m)) (HSub.hSub.{u_1 u_1 u_1} R R R (instHSub.{u_1} R (AddGroupWithOne.toSub.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.16)) (Nat.cast.{u_1} R (AddGroupWithOne.toAddMonoidWithOne.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.16) n) (Nat.cast.{u_1} R (AddGroupWithOne.toAddMonoidWithOne.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.16) m)))
Case conversion may be inaccurate. Consider using '#align nat.cast_sub Nat.cast_subₓ'. -/
@[simp, norm_cast]
theorem cast_sub {m n} (h : m ≤ n) : ((n - m : ℕ) : R) = n - m :=
  eq_sub_of_add_eq <| by rw [← cast_add, Nat.sub_add_cancel h]

@[simp, norm_cast]
theorem cast_pred : ∀ {n}, 0 < n → ((n - 1 : ℕ) : R) = n - 1
  | 0, h => by cases h
  | n + 1, h => by rw [cast_succ, add_sub_cancel] <;> rfl

end Nat

open Nat

namespace Int

variable {R : Type u} [AddGroupWithOne R]

-- see Note [coercion into rings]
instance (priority := 900) castCoe {R} [HasIntCast R] : CoeTC ℤ R :=
  ⟨Int.cast⟩

theorem cast_of_nat (n : ℕ) : (ofNat n : R) = n :=
  AddGroupWithOne.int_cast_of_nat n

/- warning: int.cast_neg_succ_of_nat -> Int.cast_negSucc is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u}} [_inst_1 : AddGroupWithOne.{u} R] (n : Nat), Eq.{succ u} R ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Int R (HasLiftT.mk.{1 succ u} Int R (CoeTCₓ.coe.{1 succ u} Int R (Int.castCoe.{u} R (AddGroupWithOne.toHasIntCast.{u} R _inst_1)))) (Int.negSucc n)) (Neg.neg.{u} R (SubNegMonoid.toHasNeg.{u} R (AddGroup.toSubNegMonoid.{u} R (AddGroupWithOne.toAddGroup.{u} R _inst_1))) ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Nat R (HasLiftT.mk.{1 succ u} Nat R (CoeTCₓ.coe.{1 succ u} Nat R (Nat.castCoe.{u} R (AddMonoidWithOne.toHasNatCast.{u} R (AddGroupWithOne.toAddMonoidWithOne.{u} R _inst_1))))) (HAdd.hAdd.{0 0 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall {R : Type.{u_1}} {n : Nat} [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.811 : AddGroupWithOne.{u_1} R], Eq.{succ u_1} R (Int.cast.{u_1} R inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.811 (Int.negSucc n)) (Neg.neg.{u_1} R (AddGroupWithOne.toNeg.{u_1} R inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.811) (Nat.cast.{u_1} R (AddGroupWithOne.toAddMonoidWithOne.{u_1} R inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.811) (HAdd.hAdd.{0 0 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))
Case conversion may be inaccurate. Consider using '#align int.cast_neg_succ_of_nat Int.cast_negSuccₓ'. -/
@[simp]
theorem cast_negSucc (n : ℕ) : (-[1 + n] : R) = -(n + 1 : ℕ) :=
  AddGroupWithOne.int_cast_neg_succ_of_nat n

/- warning: int.cast_zero -> Int.cast_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u}} [_inst_1 : AddGroupWithOne.{u} R], Eq.{succ u} R ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Int R (HasLiftT.mk.{1 succ u} Int R (CoeTCₓ.coe.{1 succ u} Int R (Int.castCoe.{u} R (AddGroupWithOne.toHasIntCast.{u} R _inst_1)))) (Zero.zero.{0} Int Int.hasZero)) (Zero.zero.{u} R (AddZeroClass.toHasZero.{u} R (AddMonoid.toAddZeroClass.{u} R (AddMonoidWithOne.toAddMonoid.{u} R (AddGroupWithOne.toAddMonoidWithOne.{u} R _inst_1)))))
but is expected to have type
  forall {R : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.848 : AddGroupWithOne.{u_1} R], Eq.{succ u_1} R (Int.cast.{u_1} R inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.848 (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) (OfNat.ofNat.{u_1} R 0 (Zero.toOfNat0.{u_1} R (AddRightCancelMonoid.toZero.{u_1} R (AddCancelMonoid.toAddRightCancelMonoid.{u_1} R (AddGroup.toAddCancelMonoid.{u_1} R (AddGroupWithOne.toAddGroup.{u_1} R inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.848))))))
Case conversion may be inaccurate. Consider using '#align int.cast_zero Int.cast_zeroₓ'. -/
@[simp, norm_cast]
theorem cast_zero : ((0 : ℤ) : R) = 0 :=
  (cast_of_nat 0).trans Nat.cast_zero

/- warning: int.cast_coe_nat -> Int.cast_ofNat is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u}} [_inst_1 : AddGroupWithOne.{u} R] (n : Nat), Eq.{succ u} R ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Int R (HasLiftT.mk.{1 succ u} Int R (CoeTCₓ.coe.{1 succ u} Int R (Int.castCoe.{u} R (AddGroupWithOne.toHasIntCast.{u} R _inst_1)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1 1} a b] => self.0) Nat Int (HasLiftT.mk.{1 1} Nat Int (CoeTCₓ.coe.{1 1} Nat Int (CoeTCₓ.mk.{1 1} Nat Int Int.ofNat))) n)) ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Nat R (HasLiftT.mk.{1 succ u} Nat R (CoeTCₓ.coe.{1 succ u} Nat R (Nat.castCoe.{u} R (AddMonoidWithOne.toHasNatCast.{u} R (AddGroupWithOne.toAddMonoidWithOne.{u} R _inst_1))))) n)
but is expected to have type
  forall {R : Type.{u_1}} {n : Nat} [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.772 : AddGroupWithOne.{u_1} R], Eq.{succ u_1} R (Int.cast.{u_1} R inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.772 (Int.ofNat n)) (Nat.cast.{u_1} R (AddGroupWithOne.toAddMonoidWithOne.{u_1} R inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.772) n)
Case conversion may be inaccurate. Consider using '#align int.cast_coe_nat Int.cast_ofNatₓ'. -/
@[simp, norm_cast]
theorem cast_ofNat (n : ℕ) : ((n : ℤ) : R) = n :=
  cast_of_nat _

/- warning: int.cast_one -> Int.cast_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u}} [_inst_1 : AddGroupWithOne.{u} R], Eq.{succ u} R ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Int R (HasLiftT.mk.{1 succ u} Int R (CoeTCₓ.coe.{1 succ u} Int R (Int.castCoe.{u} R (AddGroupWithOne.toHasIntCast.{u} R _inst_1)))) (One.one.{0} Int Int.hasOne)) (One.one.{u} R (AddMonoidWithOne.toHasOne.{u} R (AddGroupWithOne.toAddMonoidWithOne.{u} R _inst_1)))
but is expected to have type
  forall {R : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.908 : AddGroupWithOne.{u_1} R], Eq.{succ u_1} R (Int.cast.{u_1} R inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.908 (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) (OfNat.ofNat.{u_1} R 1 (One.toOfNat1.{u_1} R (AddMonoidWithOne.toOne.{u_1} R (AddGroupWithOne.toAddMonoidWithOne.{u_1} R inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.908))))
Case conversion may be inaccurate. Consider using '#align int.cast_one Int.cast_oneₓ'. -/
@[simp, norm_cast]
theorem cast_one : ((1 : ℤ) : R) = 1 :=
  show (((1 : ℕ) : ℤ) : R) = 1 by simp

/- warning: int.cast_neg -> Int.cast_neg is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u}} [_inst_1 : AddGroupWithOne.{u} R] (n : Int), Eq.{succ u} R ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Int R (HasLiftT.mk.{1 succ u} Int R (CoeTCₓ.coe.{1 succ u} Int R (Int.castCoe.{u} R (AddGroupWithOne.toHasIntCast.{u} R _inst_1)))) (Neg.neg.{0} Int Int.hasNeg n)) (Neg.neg.{u} R (SubNegMonoid.toHasNeg.{u} R (AddGroup.toSubNegMonoid.{u} R (AddGroupWithOne.toAddGroup.{u} R _inst_1))) ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Int R (HasLiftT.mk.{1 succ u} Int R (CoeTCₓ.coe.{1 succ u} Int R (Int.castCoe.{u} R (AddGroupWithOne.toHasIntCast.{u} R _inst_1)))) n))
but is expected to have type
  forall {R : Type.{u_1}} [inst._@.Mathlib.Data.Int.Cast.Defs._hyg.97 : AddGroupWithOne.{u_1} R] (n : Int), Eq.{succ u_1} R (Int.cast.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.97 (Neg.neg.{0} Int Int.instNegInt n)) (Neg.neg.{u_1} R (AddGroupWithOne.toNeg.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.97) (Int.cast.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.97 n))
Case conversion may be inaccurate. Consider using '#align int.cast_neg Int.cast_negₓ'. -/
@[simp, norm_cast]
theorem cast_neg : ∀ n, ((-n : ℤ) : R) = -n
  | (0 : ℕ) => by erw [cast_zero, neg_zero]
  | (n + 1 : ℕ) => by erw [cast_of_nat, cast_neg_succ_of_nat] <;> rfl
  | -[1 + n] => by erw [cast_of_nat, cast_neg_succ_of_nat, neg_neg]

/- warning: int.cast_sub_nat_nat -> Int.cast_subNatNat is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u}} [_inst_1 : AddGroupWithOne.{u} R] (m : Nat) (n : Nat), Eq.{succ u} R ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Int R (HasLiftT.mk.{1 succ u} Int R (CoeTCₓ.coe.{1 succ u} Int R (Int.castCoe.{u} R (AddGroupWithOne.toHasIntCast.{u} R _inst_1)))) (Int.subNatNat m n)) (HSub.hSub.{u u u} R R R (instHSub.{u} R (SubNegMonoid.toHasSub.{u} R (AddGroup.toSubNegMonoid.{u} R (AddGroupWithOne.toAddGroup.{u} R _inst_1)))) ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Nat R (HasLiftT.mk.{1 succ u} Nat R (CoeTCₓ.coe.{1 succ u} Nat R (Nat.castCoe.{u} R (AddMonoidWithOne.toHasNatCast.{u} R (AddGroupWithOne.toAddMonoidWithOne.{u} R _inst_1))))) m) ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Nat R (HasLiftT.mk.{1 succ u} Nat R (CoeTCₓ.coe.{1 succ u} Nat R (Nat.castCoe.{u} R (AddMonoidWithOne.toHasNatCast.{u} R (AddGroupWithOne.toAddMonoidWithOne.{u} R _inst_1))))) n))
but is expected to have type
  forall {R : Type.{u_1}} [inst._@.Mathlib.Data.Int.Cast.Defs._hyg.297 : AddGroupWithOne.{u_1} R] (m : Nat) (n : Nat), Eq.{succ u_1} R (Int.cast.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.297 (Int.subNatNat m n)) (HSub.hSub.{u_1 u_1 u_1} R R R (instHSub.{u_1} R (AddGroupWithOne.toSub.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.297)) (Nat.cast.{u_1} R (AddGroupWithOne.toAddMonoidWithOne.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.297) m) (Nat.cast.{u_1} R (AddGroupWithOne.toAddMonoidWithOne.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.297) n))
Case conversion may be inaccurate. Consider using '#align int.cast_sub_nat_nat Int.cast_subNatNatₓ'. -/
@[simp]
theorem cast_subNatNat (m n) : ((Int.subNatNat m n : ℤ) : R) = m - n := by
  unfold sub_nat_nat
  cases e : n - m
  · simp only [sub_nat_nat, cast_of_nat]
    simp [e, Nat.le_of_sub_eq_zero e]
    
  · rw [sub_nat_nat, cast_neg_succ_of_nat, Nat.add_one, ← e, Nat.cast_sub <| _root_.le_of_lt <| Nat.lt_of_sub_eq_succ e,
      neg_sub]
    

theorem neg_of_nat_eq (n : ℕ) : negOfNat n = -(n : ℤ) := by cases n <;> rfl

@[simp]
theorem cast_neg_of_nat (n : ℕ) : ((negOfNat n : ℤ) : R) = -n := by simp [neg_of_nat_eq]

/- warning: int.cast_add -> Int.cast_add is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u}} [_inst_1 : AddGroupWithOne.{u} R] (m : Int) (n : Int), Eq.{succ u} R ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Int R (HasLiftT.mk.{1 succ u} Int R (CoeTCₓ.coe.{1 succ u} Int R (Int.castCoe.{u} R (AddGroupWithOne.toHasIntCast.{u} R _inst_1)))) (HAdd.hAdd.{0 0 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) m n)) (HAdd.hAdd.{u u u} R R R (instHAdd.{u} R (AddZeroClass.toHasAdd.{u} R (AddMonoid.toAddZeroClass.{u} R (AddMonoidWithOne.toAddMonoid.{u} R (AddGroupWithOne.toAddMonoidWithOne.{u} R _inst_1))))) ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Int R (HasLiftT.mk.{1 succ u} Int R (CoeTCₓ.coe.{1 succ u} Int R (Int.castCoe.{u} R (AddGroupWithOne.toHasIntCast.{u} R _inst_1)))) m) ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Int R (HasLiftT.mk.{1 succ u} Int R (CoeTCₓ.coe.{1 succ u} Int R (Int.castCoe.{u} R (AddGroupWithOne.toHasIntCast.{u} R _inst_1)))) n))
but is expected to have type
  forall {R : Type.{u_1}} [inst._@.Mathlib.Data.Int.Cast.Defs._hyg.392 : AddGroupWithOne.{u_1} R] (m : Int) (n : Int), Eq.{succ u_1} R (Int.cast.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.392 (HAdd.hAdd.{0 0 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) m n)) (HAdd.hAdd.{u_1 u_1 u_1} R R R (instHAdd.{u_1} R (AddZeroClass.toAdd.{u_1} R (AddMonoid.toAddZeroClass.{u_1} R (AddMonoidWithOne.toAddMonoid.{u_1} R (AddGroupWithOne.toAddMonoidWithOne.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.392))))) (Int.cast.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.392 m) (Int.cast.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.392 n))
Case conversion may be inaccurate. Consider using '#align int.cast_add Int.cast_addₓ'. -/
@[simp, norm_cast]
theorem cast_add : ∀ m n, ((m + n : ℤ) : R) = m + n
  | (m : ℕ), (n : ℕ) => by simp [← Int.coe_nat_add]
  | (m : ℕ), -[1 + n] => by erw [cast_sub_nat_nat, cast_coe_nat, cast_neg_succ_of_nat, sub_eq_add_neg]
  | -[1 + m], (n : ℕ) => by
    erw [cast_sub_nat_nat, cast_coe_nat, cast_neg_succ_of_nat, sub_eq_iff_eq_add, add_assoc, eq_neg_add_iff_add_eq, ←
      Nat.cast_add, ← Nat.cast_add, Nat.add_comm]
  | -[1 + m], -[1 + n] =>
    show (-[1 + (m + n + 1)] : R) = _ by
      rw [cast_neg_succ_of_nat, cast_neg_succ_of_nat, cast_neg_succ_of_nat, ← neg_add_rev, ← Nat.cast_add,
        Nat.add_right_comm m n 1, Nat.add_assoc, Nat.add_comm]

/- warning: int.cast_sub -> Int.cast_sub is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u}} [_inst_1 : AddGroupWithOne.{u} R] (m : Int) (n : Int), Eq.{succ u} R ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Int R (HasLiftT.mk.{1 succ u} Int R (CoeTCₓ.coe.{1 succ u} Int R (Int.castCoe.{u} R (AddGroupWithOne.toHasIntCast.{u} R _inst_1)))) (HSub.hSub.{0 0 0} Int Int Int (instHSub.{0} Int Int.hasSub) m n)) (HSub.hSub.{u u u} R R R (instHSub.{u} R (SubNegMonoid.toHasSub.{u} R (AddGroup.toSubNegMonoid.{u} R (AddGroupWithOne.toAddGroup.{u} R _inst_1)))) ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Int R (HasLiftT.mk.{1 succ u} Int R (CoeTCₓ.coe.{1 succ u} Int R (Int.castCoe.{u} R (AddGroupWithOne.toHasIntCast.{u} R _inst_1)))) m) ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Int R (HasLiftT.mk.{1 succ u} Int R (CoeTCₓ.coe.{1 succ u} Int R (Int.castCoe.{u} R (AddGroupWithOne.toHasIntCast.{u} R _inst_1)))) n))
but is expected to have type
  forall {R : Type.{u_1}} [inst._@.Mathlib.Data.Int.Cast.Defs._hyg.666 : AddGroupWithOne.{u_1} R] (m : Int) (n : Int), Eq.{succ u_1} R (Int.cast.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.666 (HSub.hSub.{0 0 0} Int Int Int (instHSub.{0} Int Int.instSubInt) m n)) (HSub.hSub.{u_1 u_1 u_1} R R R (instHSub.{u_1} R (AddGroupWithOne.toSub.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.666)) (Int.cast.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.666 m) (Int.cast.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.666 n))
Case conversion may be inaccurate. Consider using '#align int.cast_sub Int.cast_subₓ'. -/
@[simp, norm_cast]
theorem cast_sub (m n) : ((m - n : ℤ) : R) = m - n := by simp [Int.sub_eq_add_neg, sub_eq_add_neg]

@[simp, norm_cast]
theorem coe_nat_bit0 (n : ℕ) : (↑(bit0 n) : ℤ) = bit0 ↑n :=
  rfl

@[simp, norm_cast]
theorem coe_nat_bit1 (n : ℕ) : (↑(bit1 n) : ℤ) = bit1 ↑n :=
  rfl

@[simp, norm_cast]
theorem cast_bit0 (n : ℤ) : ((bit0 n : ℤ) : R) = bit0 n :=
  cast_add _ _

@[simp, norm_cast]
theorem cast_bit1 (n : ℤ) : ((bit1 n : ℤ) : R) = bit1 n := by rw [bit1, cast_add, cast_one, cast_bit0] <;> rfl

theorem cast_two : ((2 : ℤ) : R) = 2 := by simp

theorem cast_three : ((3 : ℤ) : R) = 3 := by simp

theorem cast_four : ((4 : ℤ) : R) = 4 := by simp

end Int

