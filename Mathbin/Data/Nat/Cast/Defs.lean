/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner
-/
import Mathbin.Algebra.Group.Defs
import Mathbin.Algebra.NeZero

/-!
# Cast of natural numbers

This file defines the *canonical* homomorphism from the natural numbers into an
`add_monoid` with a one.  In additive monoids with one, there exists a unique
such homomorphism and we store it in the `nat_cast : ℕ → R` field.

Preferentially, the homomorphism is written as a coercion.

## Main declarations

* `add_monoid_with_one`: Type class for `nat.cast`.
* `nat.cast`: Canonical homomorphism `ℕ → R`.
-/


universe u

/-- The numeral `((0+1)+⋯)+1`. -/
protected def Nat.unaryCast {R : Type u} [One R] [Zero R] [Add R] : ℕ → R
  | 0 => 0
  | n + 1 => Nat.unaryCast n + 1
#align nat.unary_cast Nat.unaryCast

/-- Type class for the canonical homomorphism `ℕ → R`.
-/
@[protect_proj]
class HasNatCast (R : Type u) where
  natCast : ℕ → R
#align has_nat_cast HasNatCast

#print AddMonoidWithOne /-
/-- An `add_monoid_with_one` is an `add_monoid` with a `1`.
It also contains data for the unique homomorphism `ℕ → R`.
-/
@[protect_proj]
class AddMonoidWithOne (R : Type u) extends HasNatCast R, AddMonoid R, One R where
  natCast := Nat.unaryCast
  nat_cast_zero : nat_cast 0 = (0 : R) := by
    intros
    rfl
  nat_cast_succ : ∀ n, nat_cast (n + 1) = (nat_cast n + 1 : R) := by
    intros
    rfl
#align add_monoid_with_one AddMonoidWithOne
-/

/- warning: nat.cast -> Nat.cast is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u}} [_inst_1 : HasNatCast.{u} R], Nat -> R
but is expected to have type
  forall {R : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.257 : AddMonoidWithOne.{u_1} R], Nat -> R
Case conversion may be inaccurate. Consider using '#align nat.cast Nat.castₓ'. -/
/-- Canonical homomorphism from `ℕ` to a additive monoid `R` with a `1`. -/
protected def Nat.cast {R : Type u} [HasNatCast R] : ℕ → R :=
  HasNatCast.natCast
#align nat.cast Nat.cast

/-- An `add_comm_monoid_with_one` is an `add_monoid_with_one` satisfying `a + b = b + a`.  -/
@[protect_proj]
class AddCommMonoidWithOne (R : Type _) extends AddMonoidWithOne R, AddCommMonoid R
#align add_comm_monoid_with_one AddCommMonoidWithOne

section

variable {R : Type _} [AddMonoidWithOne R]

library_note "coercion into rings"/-- Coercions such as `nat.cast_coe` that go from a concrete structure such as
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


attribute [instance] coeBase

attribute [instance] coeTrans

namespace Nat

-- see note [coercion into rings]
instance (priority := 900) castCoe {R} [HasNatCast R] : CoeTC ℕ R :=
  ⟨Nat.cast⟩
#align nat.cast_coe Nat.castCoe

/- warning: nat.cast_zero -> Nat.cast_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u_1}} [_inst_1 : AddMonoidWithOne.{u_1} R], Eq.{succ u_1} R ((fun (a : Type) (b : Type.{u_1}) [self : HasLiftT.{1 succ u_1} a b] => self.0) Nat R (HasLiftT.mk.{1 succ u_1} Nat R (CoeTCₓ.coe.{1 succ u_1} Nat R (Nat.castCoe.{u_1} R (AddMonoidWithOne.toHasNatCast.{u_1} R _inst_1)))) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (OfNat.ofNat.{u_1} R 0 (OfNat.mk.{u_1} R 0 (Zero.zero.{u_1} R (AddZeroClass.toHasZero.{u_1} R (AddMonoid.toAddZeroClass.{u_1} R (AddMonoidWithOne.toAddMonoid.{u_1} R _inst_1))))))
but is expected to have type
  forall {R : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.318 : AddMonoidWithOne.{u_1} R], Eq.{succ u_1} R (Nat.cast.{u_1} R inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.318 (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (OfNat.ofNat.{u_1} R 0 (Zero.toOfNat0.{u_1} R (AddMonoid.toZero.{u_1} R (AddMonoidWithOne.toAddMonoid.{u_1} R inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.318))))
Case conversion may be inaccurate. Consider using '#align nat.cast_zero Nat.cast_zeroₓ'. -/
@[norm_cast]
theorem cast_zero : ((0 : ℕ) : R) = 0 :=
  AddMonoidWithOne.nat_cast_zero
#align nat.cast_zero Nat.cast_zero

/- warning: nat.cast_succ -> Nat.cast_succ is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u_1}} [_inst_1 : AddMonoidWithOne.{u_1} R] (n : Nat), Eq.{succ u_1} R ((fun (a : Type) (b : Type.{u_1}) [self : HasLiftT.{1 succ u_1} a b] => self.0) Nat R (HasLiftT.mk.{1 succ u_1} Nat R (CoeTCₓ.coe.{1 succ u_1} Nat R (Nat.castCoe.{u_1} R (AddMonoidWithOne.toHasNatCast.{u_1} R _inst_1)))) (Nat.succ n)) (HAdd.hAdd.{u_1 u_1 u_1} R R R (instHAdd.{u_1} R (AddZeroClass.toHasAdd.{u_1} R (AddMonoid.toAddZeroClass.{u_1} R (AddMonoidWithOne.toAddMonoid.{u_1} R _inst_1)))) ((fun (a : Type) (b : Type.{u_1}) [self : HasLiftT.{1 succ u_1} a b] => self.0) Nat R (HasLiftT.mk.{1 succ u_1} Nat R (CoeTCₓ.coe.{1 succ u_1} Nat R (Nat.castCoe.{u_1} R (AddMonoidWithOne.toHasNatCast.{u_1} R _inst_1)))) n) (OfNat.ofNat.{u_1} R 1 (OfNat.mk.{u_1} R 1 (One.one.{u_1} R (AddMonoidWithOne.toHasOne.{u_1} R _inst_1)))))
but is expected to have type
  forall {R : Type.{u_1}} {n : Nat} [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.361 : AddMonoidWithOne.{u_1} R], Eq.{succ u_1} R (Nat.cast.{u_1} R inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.361 (Nat.succ n)) (HAdd.hAdd.{u_1 u_1 u_1} R R R (instHAdd.{u_1} R (AddZeroClass.toAdd.{u_1} R (AddMonoid.toAddZeroClass.{u_1} R (AddMonoidWithOne.toAddMonoid.{u_1} R inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.361)))) (Nat.cast.{u_1} R inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.361 n) (OfNat.ofNat.{u_1} R 1 (One.toOfNat1.{u_1} R (AddMonoidWithOne.toOne.{u_1} R inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.361))))
Case conversion may be inaccurate. Consider using '#align nat.cast_succ Nat.cast_succₓ'. -/
-- Lemmas about nat.succ need to get a low priority, so that they are tried last.
-- This is because `nat.succ _` matches `1`, `3`, `x+1`, etc.
-- Rewriting would then produce really wrong terms.
@[simp, norm_cast]
theorem cast_succ (n : ℕ) : ((succ n : ℕ) : R) = n + 1 :=
  AddMonoidWithOne.nat_cast_succ _
#align nat.cast_succ Nat.cast_succ

theorem cast_add_one (n : ℕ) : ((n + 1 : ℕ) : R) = n + 1 :=
  cast_succ _
#align nat.cast_add_one Nat.cast_add_one

@[simp, norm_cast]
theorem cast_ite (P : Prop) [Decidable P] (m n : ℕ) : ((ite P m n : ℕ) : R) = ite P (m : R) (n : R) := by
  split_ifs <;> rfl
#align nat.cast_ite Nat.cast_ite

end Nat

end

namespace Nat

variable {R : Type _}

/- warning: nat.cast_one -> Nat.cast_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u_1}} [_inst_1 : AddMonoidWithOne.{u_1} R], Eq.{succ u_1} R ((fun (a : Type) (b : Type.{u_1}) [self : HasLiftT.{1 succ u_1} a b] => self.0) Nat R (HasLiftT.mk.{1 succ u_1} Nat R (CoeTCₓ.coe.{1 succ u_1} Nat R (Nat.castCoe.{u_1} R (AddMonoidWithOne.toHasNatCast.{u_1} R _inst_1)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{u_1} R 1 (OfNat.mk.{u_1} R 1 (One.one.{u_1} R (AddMonoidWithOne.toHasOne.{u_1} R _inst_1))))
but is expected to have type
  forall {R : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.395 : AddMonoidWithOne.{u_1} R], Eq.{succ u_1} R (Nat.cast.{u_1} R inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.395 (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{u_1} R 1 (One.toOfNat1.{u_1} R (AddMonoidWithOne.toOne.{u_1} R inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.395)))
Case conversion may be inaccurate. Consider using '#align nat.cast_one Nat.cast_oneₓ'. -/
@[norm_cast]
theorem cast_one [AddMonoidWithOne R] : ((1 : ℕ) : R) = 1 := by rw [cast_succ, Nat.cast_zero, zero_add]
#align nat.cast_one Nat.cast_one

/- warning: nat.cast_add -> Nat.cast_add is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u_1}} [_inst_1 : AddMonoidWithOne.{u_1} R] (m : Nat) (n : Nat), Eq.{succ u_1} R ((fun (a : Type) (b : Type.{u_1}) [self : HasLiftT.{1 succ u_1} a b] => self.0) Nat R (HasLiftT.mk.{1 succ u_1} Nat R (CoeTCₓ.coe.{1 succ u_1} Nat R (Nat.castCoe.{u_1} R (AddMonoidWithOne.toHasNatCast.{u_1} R _inst_1)))) (HAdd.hAdd.{0 0 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) (HAdd.hAdd.{u_1 u_1 u_1} R R R (instHAdd.{u_1} R (AddZeroClass.toHasAdd.{u_1} R (AddMonoid.toAddZeroClass.{u_1} R (AddMonoidWithOne.toAddMonoid.{u_1} R _inst_1)))) ((fun (a : Type) (b : Type.{u_1}) [self : HasLiftT.{1 succ u_1} a b] => self.0) Nat R (HasLiftT.mk.{1 succ u_1} Nat R (CoeTCₓ.coe.{1 succ u_1} Nat R (Nat.castCoe.{u_1} R (AddMonoidWithOne.toHasNatCast.{u_1} R _inst_1)))) m) ((fun (a : Type) (b : Type.{u_1}) [self : HasLiftT.{1 succ u_1} a b] => self.0) Nat R (HasLiftT.mk.{1 succ u_1} Nat R (CoeTCₓ.coe.{1 succ u_1} Nat R (Nat.castCoe.{u_1} R (AddMonoidWithOne.toHasNatCast.{u_1} R _inst_1)))) n))
but is expected to have type
  forall {R : Type.{u_1}} {m : Nat} {n : Nat} [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.463 : AddMonoidWithOne.{u_1} R], Eq.{succ u_1} R (Nat.cast.{u_1} R inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.463 (HAdd.hAdd.{0 0 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (HAdd.hAdd.{u_1 u_1 u_1} R R R (instHAdd.{u_1} R (AddZeroClass.toAdd.{u_1} R (AddMonoid.toAddZeroClass.{u_1} R (AddMonoidWithOne.toAddMonoid.{u_1} R inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.463)))) (Nat.cast.{u_1} R inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.463 m) (Nat.cast.{u_1} R inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.463 n))
Case conversion may be inaccurate. Consider using '#align nat.cast_add Nat.cast_addₓ'. -/
@[norm_cast]
theorem cast_add [AddMonoidWithOne R] (m n : ℕ) : ((m + n : ℕ) : R) = m + n := by
  induction n <;> simp [add_succ, add_assoc, Nat.add_zero, Nat.cast_one, Nat.cast_zero, *]
#align nat.cast_add Nat.cast_add

/-- Computationally friendlier cast than `nat.unary_cast`, using binary representation. -/
protected def binCast [Zero R] [One R] [Add R] (n : ℕ) : R :=
  @Nat.binaryRec (fun _ => R) 0 (fun odd k a => cond odd (a + a + 1) (a + a)) n
#align nat.bin_cast Nat.binCast

@[simp]
theorem bin_cast_eq [AddMonoidWithOne R] (n : ℕ) : (Nat.binCast n : R) = ((n : ℕ) : R) := by
  rw [Nat.binCast]
  apply binary_rec _ _ n
  · rw [binary_rec_zero, Nat.cast_zero]
    
  · intro b k h
    rw [binary_rec_eq, h]
    · cases b <;> simp [bit, bit0, bit1, Nat.cast_add, Nat.cast_zero]
      
    · simp
      
    
#align nat.bin_cast_eq Nat.bin_cast_eq

@[norm_cast]
theorem cast_bit0 [AddMonoidWithOne R] (n : ℕ) : ((bit0 n : ℕ) : R) = bit0 n :=
  Nat.cast_add _ _
#align nat.cast_bit0 Nat.cast_bit0

@[norm_cast]
theorem cast_bit1 [AddMonoidWithOne R] (n : ℕ) : ((bit1 n : ℕ) : R) = bit1 n := by
  rw [bit1, cast_add_one, cast_bit0] <;> rfl
#align nat.cast_bit1 Nat.cast_bit1

theorem cast_two [AddMonoidWithOne R] : ((2 : ℕ) : R) = 2 := by rw [cast_add_one, Nat.cast_one, bit0]
#align nat.cast_two Nat.cast_two

attribute [simp, norm_cast] Int.nat_abs_of_nat

end Nat

/-- `add_monoid_with_one` implementation using unary recursion. -/
@[reducible]
protected def AddMonoidWithOne.unary {R : Type _} [AddMonoid R] [One R] : AddMonoidWithOne R :=
  { ‹One R›, ‹AddMonoid R› with }
#align add_monoid_with_one.unary AddMonoidWithOne.unary

/-- `add_monoid_with_one` implementation using binary recursion. -/
@[reducible]
protected def AddMonoidWithOne.binary {R : Type _} [AddMonoid R] [One R] : AddMonoidWithOne R :=
  { ‹One R›, ‹AddMonoid R› with natCast := Nat.binCast, nat_cast_zero := by simp [Nat.binCast, Nat.cast],
    nat_cast_succ := fun n => by
      simp only [Nat.cast]
      letI : AddMonoidWithOne R := AddMonoidWithOne.unary
      erw [Nat.bin_cast_eq, Nat.bin_cast_eq, Nat.cast_succ]
      rfl }
#align add_monoid_with_one.binary AddMonoidWithOne.binary

namespace NeZero

theorem ne' (n : ℕ) (R) [AddMonoidWithOne R] [h : NeZero (n : R)] : (n : R) ≠ 0 :=
  h.out
#align ne_zero.ne' NeZero.ne'

theorem of_ne_zero_coe (R) [AddMonoidWithOne R] {n : ℕ} [h : NeZero (n : R)] : NeZero n :=
  ⟨by
    cases h
    rintro rfl
    · simpa [Nat.cast_zero] using h
      ⟩
#align ne_zero.of_ne_zero_coe NeZero.of_ne_zero_coe

theorem pos_of_ne_zero_coe (R) [AddMonoidWithOne R] {n : ℕ} [NeZero (n : R)] : 0 < n :=
  Nat.pos_of_ne_zero (of_ne_zero_coe R).out
#align ne_zero.pos_of_ne_zero_coe NeZero.pos_of_ne_zero_coe

end NeZero

