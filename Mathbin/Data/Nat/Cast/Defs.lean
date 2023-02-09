/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner

! This file was ported from Lean 3 source module data.nat.cast.defs
! leanprover-community/mathlib commit d101e93197bb5f6ea89bd7ba386b7f7dff1f3903
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Defs
import Mathbin.Algebra.NeZero

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
  natCast_zero : nat_cast 0 = (0 : R) := by
    intros
    rfl
  natCast_succ :
    ∀ n, nat_cast (n + 1) = (nat_cast n + 1 :
          R) := by
    intros
    rfl
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


attribute [instance] coeBase

attribute [instance] coeTrans

namespace Nat

-- see note [coercion into rings]
instance (priority := 900) castCoe {R} [NatCast R] : CoeTC ℕ R :=
  ⟨Nat.cast⟩
#align nat.cast_coe Nat.castCoe

/- warning: nat.cast_zero -> Nat.cast_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} R], Eq.{succ u1} R ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1)))) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} R], Eq.{succ u1} R (Nat.cast.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (AddMonoid.toZero.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align nat.cast_zero Nat.cast_zeroₓ'. -/
@[simp, norm_cast]
theorem cast_zero : ((0 : ℕ) : R) = 0 :=
  AddMonoidWithOne.natCast_zero
#align nat.cast_zero Nat.cast_zero

/- warning: nat.cast_succ -> Nat.cast_succ is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} R] (n : Nat), Eq.{succ u1} R ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1)))) (Nat.succ n)) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1)))) n) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R _inst_1)))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} R] (n : Nat), Eq.{succ u1} R (Nat.cast.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1) (Nat.succ n)) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1)))) (Nat.cast.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1) n) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (AddMonoidWithOne.toOne.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align nat.cast_succ Nat.cast_succₓ'. -/
-- Lemmas about nat.succ need to get a low priority, so that they are tried last.
-- This is because `nat.succ _` matches `1`, `3`, `x+1`, etc.
-- Rewriting would then produce really wrong terms.
@[simp, norm_cast]
theorem cast_succ (n : ℕ) : ((succ n : ℕ) : R) = n + 1 :=
  AddMonoidWithOne.natCast_succ _
#align nat.cast_succ Nat.cast_succ

/- warning: nat.cast_add_one -> Nat.cast_add_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} R] (n : Nat), Eq.{succ u1} R ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1)))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1)))) n) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R _inst_1)))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} R] (n : Nat), Eq.{succ u1} R (Nat.cast.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1)))) (Nat.cast.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1) n) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (AddMonoidWithOne.toOne.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align nat.cast_add_one Nat.cast_add_oneₓ'. -/
theorem cast_add_one (n : ℕ) : ((n + 1 : ℕ) : R) = n + 1 :=
  cast_succ _
#align nat.cast_add_one Nat.cast_add_one

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

/- warning: nat.bin_cast_eq -> Nat.binCast_eq is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} R] (n : Nat), Eq.{succ u1} R (Nat.binCast.{u1} R (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))) (AddMonoidWithOne.toOne.{u1} R _inst_1) (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))) n) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1)))) n)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} R] (n : Nat), Eq.{succ u1} R (Nat.binCast.{u1} R (AddMonoid.toZero.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1)) (AddMonoidWithOne.toOne.{u1} R _inst_1) (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))) n) (Nat.cast.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1) n)
Case conversion may be inaccurate. Consider using '#align nat.bin_cast_eq Nat.binCast_eqₓ'. -/
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

/- warning: nat.cast_bit0 -> Nat.cast_bit0 is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} R] (n : Nat), Eq.{succ u1} R ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1)))) (bit0.{0} Nat Nat.hasAdd n)) (bit0.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1)))) n))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} R] (n : Nat), Eq.{succ u1} R (Nat.cast.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1) (bit0.{0} Nat instAddNat n)) (bit0.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))) (Nat.cast.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1) n))
Case conversion may be inaccurate. Consider using '#align nat.cast_bit0 Nat.cast_bit0ₓ'. -/
@[simp, norm_cast]
theorem cast_bit0 [AddMonoidWithOne R] (n : ℕ) : ((bit0 n : ℕ) : R) = bit0 n :=
  cast_add _ _
#align nat.cast_bit0 Nat.cast_bit0

/- warning: nat.cast_bit1 -> Nat.cast_bit1 is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} R] (n : Nat), Eq.{succ u1} R ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1)))) (bit1.{0} Nat Nat.hasOne Nat.hasAdd n)) (bit1.{u1} R (AddMonoidWithOne.toOne.{u1} R _inst_1) (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1)))) n))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} R] (n : Nat), Eq.{succ u1} R (Nat.cast.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1) (bit1.{0} Nat (One.ofOfNat1.{0} Nat (instOfNatNat 1)) instAddNat n)) (bit1.{u1} R (AddMonoidWithOne.toOne.{u1} R _inst_1) (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))) (Nat.cast.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1) n))
Case conversion may be inaccurate. Consider using '#align nat.cast_bit1 Nat.cast_bit1ₓ'. -/
@[simp, norm_cast]
theorem cast_bit1 [AddMonoidWithOne R] (n : ℕ) : ((bit1 n : ℕ) : R) = bit1 n := by
  rw [bit1, cast_add_one, cast_bit0] <;> rfl
#align nat.cast_bit1 Nat.cast_bit1

/- warning: nat.cast_two -> Nat.cast_two is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} R], Eq.{succ u1} R ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1)))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (OfNat.ofNat.{u1} R 2 (OfNat.mk.{u1} R 2 (bit0.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))) (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R _inst_1)))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} R], Eq.{succ u1} R (Nat.cast.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (OfNat.ofNat.{u1} R 2 (instOfNat.{u1} R 2 (AddMonoidWithOne.toNatCast.{u1} R _inst_1) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))
Case conversion may be inaccurate. Consider using '#align nat.cast_two Nat.cast_twoₓ'. -/
theorem cast_two [AddMonoidWithOne R] : ((2 : ℕ) : R) = 2 := by rw [cast_add_one, cast_one, bit0]
#align nat.cast_two Nat.cast_two

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

/- warning: ne_zero.nat_cast_ne -> NeZero.natCast_ne is a dubious translation:
lean 3 declaration is
  forall (n : Nat) (R : Type.{u1}) [_inst_1 : AddMonoidWithOne.{u1} R] [h : NeZero.{u1} R (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1)))) n)], Ne.{succ u1} R ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1)))) n) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))))))
but is expected to have type
  forall (n : Nat) (R : Type.{u1}) [_inst_1 : AddMonoidWithOne.{u1} R] [h : NeZero.{u1} R (AddMonoid.toZero.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1)) (Nat.cast.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1) n)], Ne.{succ u1} R (Nat.cast.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1) n) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (AddMonoid.toZero.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align ne_zero.nat_cast_ne NeZero.natCast_neₓ'. -/
theorem natCast_ne (n : ℕ) (R) [AddMonoidWithOne R] [h : NeZero (n : R)] : (n : R) ≠ 0 :=
  h.out
#align ne_zero.nat_cast_ne NeZero.natCast_ne

/- warning: ne_zero.of_ne_zero_coe -> NeZero.of_neZero_natCast is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : AddMonoidWithOne.{u1} R] {n : Nat} [h : NeZero.{u1} R (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1)))) n)], NeZero.{0} Nat Nat.hasZero n
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : AddMonoidWithOne.{u1} R] {n : Nat} [h : NeZero.{u1} R (AddMonoid.toZero.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1)) (Nat.cast.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1) n)], NeZero.{0} Nat (Zero.ofOfNat0.{0} Nat (instOfNatNat 0)) n
Case conversion may be inaccurate. Consider using '#align ne_zero.of_ne_zero_coe NeZero.of_neZero_natCastₓ'. -/
theorem of_neZero_natCast (R) [AddMonoidWithOne R] {n : ℕ} [h : NeZero (n : R)] : NeZero n :=
  ⟨by
    cases h
    rintro rfl
    · simpa using h⟩
#align ne_zero.of_ne_zero_coe NeZero.of_neZero_natCast

/- warning: ne_zero.pos_of_ne_zero_coe -> NeZero.pos_of_neZero_natCast is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : AddMonoidWithOne.{u1} R] {n : Nat} [_inst_2 : NeZero.{u1} R (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1)))) n)], LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : AddMonoidWithOne.{u1} R] {n : Nat} [_inst_2 : NeZero.{u1} R (AddMonoid.toZero.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1)) (Nat.cast.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1) n)], LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n
Case conversion may be inaccurate. Consider using '#align ne_zero.pos_of_ne_zero_coe NeZero.pos_of_neZero_natCastₓ'. -/
theorem pos_of_neZero_natCast (R) [AddMonoidWithOne R] {n : ℕ} [NeZero (n : R)] : 0 < n :=
  Nat.pos_of_ne_zero (of_neZero_natCast R).out
#align ne_zero.pos_of_ne_zero_coe NeZero.pos_of_neZero_natCast

end NeZero

