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
  | -[n+1] => -(n + 1 : ℕ)

/-- Type class for the canonical homomorphism `ℤ → R`.
-/
class HasIntCast (R : Type u) where
  intCast : ℤ → R

#print AddGroupWithOne /-
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
-/

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

open Nat

namespace Int

variable {R : Type u} [AddGroupWithOne R]

-- see Note [coercion into rings]
instance (priority := 900) castCoe {R} [HasIntCast R] : CoeTC ℤ R :=
  ⟨Int.cast⟩

theorem cast_of_nat (n : ℕ) : (ofNat n : R) = n :=
  AddGroupWithOne.int_cast_of_nat n

end Int

