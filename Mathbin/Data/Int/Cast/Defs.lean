/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner

! This file was ported from Lean 3 source module data.int.cast.defs
! leanprover-community/mathlib commit 7c523cb78f4153682c2929e3006c863bfef463d0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Cast.Defs

/-!
# Cast of integers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

attribute [simp] Int.ofNat_eq_coe

#print Int.castDef /-
/-- Default value for `add_group_with_one.int_cast`. -/
protected def Int.castDef {R : Type u} [NatCast R] [Neg R] : ℤ → R
  | (n : ℕ) => n
  | -[n+1] => -(n + 1 : ℕ)
#align int.cast_def Int.castDef
-/

#print IntCast /-
/-- Type class for the canonical homomorphism `ℤ → R`.
-/
class IntCast (R : Type u) where
  intCast : ℤ → R
#align has_int_cast IntCast
-/

#print AddGroupWithOne /-
/-- An `add_group_with_one` is an `add_group` with a `1`.
It also contains data for the unique homomorphisms `ℕ → R` and `ℤ → R`.
-/
@[protect_proj]
class AddGroupWithOne (R : Type u) extends IntCast R, AddGroup R, AddMonoidWithOne R where
  intCast := Int.castDef
  int_cast_of_nat :
    ∀ n : ℕ, int_cast n = (n : R) := by
    intros
    rfl
  int_cast_neg_succ_of_nat :
    ∀ n : ℕ, int_cast (-(n + 1 : ℕ)) =
        -((n + 1 : ℕ) : R) := by
    intros
    rfl
#align add_group_with_one AddGroupWithOne
-/

#print AddCommGroupWithOne /-
/-- An `add_comm_group_with_one` is an `add_group_with_one` satisfying `a + b = b + a`. -/
@[protect_proj]
class AddCommGroupWithOne (R : Type u) extends AddCommGroup R, AddGroupWithOne R
#align add_comm_group_with_one AddCommGroupWithOne
-/

#print Int.cast /-
/-- Canonical homomorphism from the integers to any ring(-like) structure `R` -/
protected def Int.cast {R : Type u} [IntCast R] (i : ℤ) : R :=
  IntCast.intCast i
#align int.cast Int.cast
-/

open Nat

namespace Int

variable {R : Type u} [AddGroupWithOne R]

-- see Note [coercion into rings]
instance (priority := 900) castCoe {R} [IntCast R] : CoeTC ℤ R :=
  ⟨Int.cast⟩
#align int.cast_coe Int.castCoe

theorem cast_of_nat (n : ℕ) : (ofNat n : R) = n :=
  AddGroupWithOne.intCast_ofNat n
#align int.cast_of_nat Int.cast_of_nat

end Int

