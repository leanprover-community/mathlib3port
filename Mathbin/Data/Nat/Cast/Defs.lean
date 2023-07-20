/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner
-/
import Mathbin.Algebra.Group.Defs
import Mathbin.Algebra.NeZero

#align_import data.nat.cast.defs from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

/-!
# Cast of natural numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the *canonical* homomorphism from the natural numbers into an
`add_monoid` with a one.  In additive monoids with one, there exists a unique
such homomorphism and we store it in the `nat_cast : ℕ → R` field.

Preferentially, the homomorphism is written as a coercion.

## Main declarations

* `add_monoid_with_one`: Type class for `nat.cast`.
* `nat.cast`: Canonical homomorphism `ℕ → R`.
-/


universe u

#print Nat.unaryCast /-
/-- The numeral `((0+1)+⋯)+1`. -/
protected def Nat.unaryCast {R : Type u} [One R] [Zero R] [Add R] : ℕ → R
  | 0 => 0
  | n + 1 => Nat.unaryCast n + 1
#align nat.unary_cast Nat.unaryCast
-/

#print NatCast /-
/-- Type class for the canonical homomorphism `ℕ → R`.
-/
@[protect_proj]
class NatCast (R : Type u) where
  natCast : ℕ → R
#align has_nat_cast NatCast
-/

#print AddMonoidWithOne /-
/-- An `add_monoid_with_one` is an `add_monoid` with a `1`.
It also contains data for the unique homomorphism `ℕ → R`.
-/
@[protect_proj]
class AddMonoidWithOne (R : Type u) extends NatCast R, AddMonoid R, One R where
  natCast := Nat.unaryCast
  natCast_zero : nat_cast 0 = (0 : R) := by intros; rfl
  natCast_succ : ∀ n, nat_cast (n + 1) = (nat_cast n + 1 : R) := by intros; rfl
#align add_monoid_with_one AddMonoidWithOne
-/

#print Nat.cast /-
/-- Canonical homomorphism from `ℕ` to a additive monoid `R` with a `1`. -/
protected def Nat.cast {R : Type u} [NatCast R] : ℕ → R :=
  NatCast.natCast
#align nat.cast Nat.cast
-/

#print AddCommMonoidWithOne /-
/-- An `add_comm_monoid_with_one` is an `add_monoid_with_one` satisfying `a + b = b + a`.  -/
@[protect_proj]
class AddCommMonoidWithOne (R : Type _) extends AddMonoidWithOne R, AddCommMonoid R
#align add_comm_monoid_with_one AddCommMonoidWithOne
-/

section

variable {R : Type _} [AddMonoidWithOne R]

library_note "coercion into rings"/--
Coercions such as `nat.cast_coe` that go from a concrete structure such as
`ℕ` to an arbitrary ring `R` should be set up as follows:
```lean
@[priority 900] instance : has_coe_t ℕ R := ⟨...⟩
```

It needs to be `has_coe_t` instead of `has_coe` because otherwise type-class
inference would loop when constructing the transitive coercion `ℕ → ℕ → ℕ → ...`.
The reduced priority is necessary so that it doesn't conflict with instances
such as `has_coe_t R (option R)`.

For this to work, we reduce the priority of the `coe_base` and `coe_trans`
instances because we want the instances for `has_coe_t` to be tried in the
following order:

 1. `has_coe_t` instances declared in mathlib (such as `has_coe_t R (with_top R)`, etc.)
 2. `coe_base`, which contains instances such as `has_coe (fin n) n`
 3. `nat.cast_coe : has_coe_t ℕ R` etc.
 4. `coe_trans`

If `coe_trans` is tried first, then `nat.cast_coe` doesn't get a chance to apply.
-/


attribute [instance 950] coeBase

attribute [instance 500] coeTrans

namespace Nat

-- see note [coercion into rings]
instance (priority := 900) castCoe {R} [NatCast R] : CoeTC ℕ R :=
  ⟨Nat.cast⟩
#align nat.cast_coe Nat.castCoe

#print Nat.cast_zero /-
@[simp, norm_cast]
theorem cast_zero : ((0 : ℕ) : R) = 0 :=
  AddMonoidWithOne.natCast_zero
#align nat.cast_zero Nat.cast_zero
-/

#print Nat.cast_succ /-
-- Lemmas about nat.succ need to get a low priority, so that they are tried last.
-- This is because `nat.succ _` matches `1`, `3`, `x+1`, etc.
-- Rewriting would then produce really wrong terms.
@[simp, norm_cast]
theorem cast_succ (n : ℕ) : ((succ n : ℕ) : R) = n + 1 :=
  AddMonoidWithOne.natCast_succ _
#align nat.cast_succ Nat.cast_succ
-/

#print Nat.cast_add_one /-
theorem cast_add_one (n : ℕ) : ((n + 1 : ℕ) : R) = n + 1 :=
  cast_succ _
#align nat.cast_add_one Nat.cast_add_one
-/

#print Nat.cast_ite /-
@[simp, norm_cast]
theorem cast_ite (P : Prop) [Decidable P] (m n : ℕ) :
    ((ite P m n : ℕ) : R) = ite P (m : R) (n : R) := by split_ifs <;> rfl
#align nat.cast_ite Nat.cast_ite
-/

end Nat

end

namespace Nat

variable {R : Type _}

@[simp, norm_cast]
theorem cast_one [AddMonoidWithOne R] : ((1 : ℕ) : R) = 1 := by rw [cast_succ, cast_zero, zero_add]
#align nat.cast_one Nat.cast_oneₓ

@[simp, norm_cast]
theorem cast_add [AddMonoidWithOne R] (m n : ℕ) : ((m + n : ℕ) : R) = m + n := by
  induction n <;> simp [add_succ, add_assoc, Nat.add_zero, *]
#align nat.cast_add Nat.cast_addₓ

#print Nat.binCast /-
/-- Computationally friendlier cast than `nat.unary_cast`, using binary representation. -/
protected def binCast [Zero R] [One R] [Add R] (n : ℕ) : R :=
  @Nat.binaryRec (fun _ => R) 0 (fun odd k a => cond Odd (a + a + 1) (a + a)) n
#align nat.bin_cast Nat.binCast
-/

#print Nat.binCast_eq /-
@[simp]
theorem binCast_eq [AddMonoidWithOne R] (n : ℕ) : (Nat.binCast n : R) = ((n : ℕ) : R) :=
  by
  rw [Nat.binCast]
  apply binary_rec _ _ n
  · rw [binary_rec_zero, cast_zero]
  · intro b k h
    rw [binary_rec_eq, h]
    · cases b <;> simp [bit, bit0, bit1]
    · simp
#align nat.bin_cast_eq Nat.binCast_eq
-/

#print Nat.cast_bit0 /-
@[simp, norm_cast]
theorem cast_bit0 [AddMonoidWithOne R] (n : ℕ) : ((bit0 n : ℕ) : R) = bit0 n :=
  cast_add _ _
#align nat.cast_bit0 Nat.cast_bit0
-/

#print Nat.cast_bit1 /-
@[simp, norm_cast]
theorem cast_bit1 [AddMonoidWithOne R] (n : ℕ) : ((bit1 n : ℕ) : R) = bit1 n := by
  rw [bit1, cast_add_one, cast_bit0] <;> rfl
#align nat.cast_bit1 Nat.cast_bit1
-/

#print Nat.cast_two /-
theorem cast_two [AddMonoidWithOne R] : ((2 : ℕ) : R) = 2 := by rw [cast_add_one, cast_one, bit0]
#align nat.cast_two Nat.cast_two
-/

attribute [simp, norm_cast] Int.natAbs_ofNat

end Nat

#print AddMonoidWithOne.unary /-
/-- `add_monoid_with_one` implementation using unary recursion. -/
@[reducible]
protected def AddMonoidWithOne.unary {R : Type _} [AddMonoid R] [One R] : AddMonoidWithOne R :=
  { ‹One R›, ‹AddMonoid R› with }
#align add_monoid_with_one.unary AddMonoidWithOne.unary
-/

#print AddMonoidWithOne.binary /-
/-- `add_monoid_with_one` implementation using binary recursion. -/
@[reducible]
protected def AddMonoidWithOne.binary {R : Type _} [AddMonoid R] [One R] : AddMonoidWithOne R :=
  { ‹One R›, ‹AddMonoid R› with
    natCast := Nat.binCast
    natCast_zero := by simp [Nat.binCast, Nat.cast]
    natCast_succ := fun n => by
      simp only [Nat.cast]
      letI : AddMonoidWithOne R := AddMonoidWithOne.unary
      erw [Nat.binCast_eq, Nat.binCast_eq, Nat.cast_succ]
      rfl }
#align add_monoid_with_one.binary AddMonoidWithOne.binary
-/

namespace NeZero

#print NeZero.natCast_ne /-
theorem natCast_ne (n : ℕ) (R) [AddMonoidWithOne R] [h : NeZero (n : R)] : (n : R) ≠ 0 :=
  h.out
#align ne_zero.nat_cast_ne NeZero.natCast_ne
-/

#print NeZero.of_neZero_natCast /-
theorem of_neZero_natCast (R) [AddMonoidWithOne R] {n : ℕ} [h : NeZero (n : R)] : NeZero n :=
  ⟨by cases h; rintro rfl; · simpa using h⟩
#align ne_zero.of_ne_zero_coe NeZero.of_neZero_natCast
-/

#print NeZero.pos_of_neZero_natCast /-
theorem pos_of_neZero_natCast (R) [AddMonoidWithOne R] {n : ℕ} [NeZero (n : R)] : 0 < n :=
  Nat.pos_of_ne_zero (of_neZero_natCast R).out
#align ne_zero.pos_of_ne_zero_coe NeZero.pos_of_neZero_natCast
-/

end NeZero

