/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module algebra.char_zero.defs
! leanprover-community/mathlib commit 7b78d1776212a91ecc94cf601f83bdcc46b04213
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Int.Cast.Defs

/-!
# Characteristic zero

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A ring `R` is called of characteristic zero if every natural number `n` is non-zero when considered
as an element of `R`. Since this definition doesn't mention the multiplicative structure of `R`
except for the existence of `1` in this file characteristic zero is defined for additive monoids
with `1`.

## Main definition

`char_zero` is the typeclass of an additive monoid with one such that the natural homomorphism
from the natural numbers into it is injective.

## TODO

* Unify with `char_p` (possibly using an out-parameter)
-/


#print CharZero /-
/-- Typeclass for monoids with characteristic zero.
  (This is usually stated on fields but it makes sense for any additive monoid with 1.)

*Warning*: for a semiring `R`, `char_zero R` and `char_p R 0` need not coincide.
* `char_zero R` requires an injection `ℕ ↪ R`;
* `char_p R 0` asks that only `0 : ℕ` maps to `0 : R` under the map `ℕ → R`.

For instance, endowing `{0, 1}` with addition given by `max` (i.e. `1` is absorbing), shows that
`char_zero {0, 1}` does not hold and yet `char_p {0, 1} 0` does.
This example is formalized in `counterexamples/char_p_zero_ne_char_zero`.
 -/
class CharZero (R : Type _) [AddMonoidWithOne R] : Prop where
  cast_injective : Function.Injective (coe : ℕ → R)
#align char_zero CharZero
-/

/- warning: char_zero_of_inj_zero -> charZero_of_inj_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} R], (forall (n : Nat), (Eq.{succ u1} R ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1))))) n) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)))))))) -> (Eq.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))) -> (CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} R], (forall (n : Nat), (Eq.{succ u1} R (Nat.cast.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1)) n) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (AddRightCancelMonoid.toZero.{u1} R (AddCancelMonoid.toAddRightCancelMonoid.{u1} R (AddGroup.toAddCancelMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R _inst_1))))))) -> (Eq.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))) -> (CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R _inst_1))
Case conversion may be inaccurate. Consider using '#align char_zero_of_inj_zero charZero_of_inj_zeroₓ'. -/
theorem charZero_of_inj_zero {R : Type _} [AddGroupWithOne R] (H : ∀ n : ℕ, (n : R) = 0 → n = 0) :
    CharZero R :=
  ⟨fun m n h => by
    induction' m with m ih generalizing n;
    · rw [H n]
      rw [← h, Nat.cast_zero]
    cases' n with n;
    · apply H
      rw [h, Nat.cast_zero]
    simp_rw [Nat.cast_succ, add_right_cancel_iff] at h; rwa [ih]⟩
#align char_zero_of_inj_zero charZero_of_inj_zero

namespace Nat

variable {R : Type _} [AddMonoidWithOne R] [CharZero R]

#print Nat.cast_injective /-
theorem cast_injective : Function.Injective (coe : ℕ → R) :=
  CharZero.cast_injective
#align nat.cast_injective Nat.cast_injective
-/

#print Nat.cast_inj /-
@[simp, norm_cast]
theorem cast_inj {m n : ℕ} : (m : R) = n ↔ m = n :=
  cast_injective.eq_iff
#align nat.cast_inj Nat.cast_inj
-/

/- warning: nat.cast_eq_zero -> Nat.cast_eq_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} R] [_inst_2 : CharZero.{u1} R _inst_1] {n : Nat}, Iff (Eq.{succ u1} R ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1)))) n) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))))))) (Eq.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} R] [_inst_2 : CharZero.{u1} R _inst_1] {n : Nat}, Iff (Eq.{succ u1} R (Nat.cast.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1) n) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (AddMonoid.toZero.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))))) (Eq.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))
Case conversion may be inaccurate. Consider using '#align nat.cast_eq_zero Nat.cast_eq_zeroₓ'. -/
@[simp, norm_cast]
theorem cast_eq_zero {n : ℕ} : (n : R) = 0 ↔ n = 0 := by rw [← cast_zero, cast_inj]
#align nat.cast_eq_zero Nat.cast_eq_zero

/- warning: nat.cast_ne_zero -> Nat.cast_ne_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} R] [_inst_2 : CharZero.{u1} R _inst_1] {n : Nat}, Iff (Ne.{succ u1} R ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1)))) n) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))))))) (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} R] [_inst_2 : CharZero.{u1} R _inst_1] {n : Nat}, Iff (Ne.{succ u1} R (Nat.cast.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1) n) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (AddMonoid.toZero.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))))) (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))
Case conversion may be inaccurate. Consider using '#align nat.cast_ne_zero Nat.cast_ne_zeroₓ'. -/
@[norm_cast]
theorem cast_ne_zero {n : ℕ} : (n : R) ≠ 0 ↔ n ≠ 0 :=
  not_congr cast_eq_zero
#align nat.cast_ne_zero Nat.cast_ne_zero

/- warning: nat.cast_add_one_ne_zero -> Nat.cast_add_one_ne_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} R] [_inst_2 : CharZero.{u1} R _inst_1] (n : Nat), Ne.{succ u1} R (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1)))) n) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R _inst_1))))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} R] [_inst_2 : CharZero.{u1} R _inst_1] (n : Nat), Ne.{succ u1} R (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1)))) (Nat.cast.{u1} R (AddMonoidWithOne.toNatCast.{u1} R _inst_1) n) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (AddMonoidWithOne.toOne.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (AddMonoid.toZero.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align nat.cast_add_one_ne_zero Nat.cast_add_one_ne_zeroₓ'. -/
theorem cast_add_one_ne_zero (n : ℕ) : (n + 1 : R) ≠ 0 := by exact_mod_cast n.succ_ne_zero
#align nat.cast_add_one_ne_zero Nat.cast_add_one_ne_zero

#print Nat.cast_eq_one /-
@[simp, norm_cast]
theorem cast_eq_one {n : ℕ} : (n : R) = 1 ↔ n = 1 := by rw [← cast_one, cast_inj]
#align nat.cast_eq_one Nat.cast_eq_one
-/

#print Nat.cast_ne_one /-
@[norm_cast]
theorem cast_ne_one {n : ℕ} : (n : R) ≠ 1 ↔ n ≠ 1 :=
  cast_eq_one.Not
#align nat.cast_ne_one Nat.cast_ne_one
-/

end Nat

namespace NeZero

/- warning: ne_zero.char_zero -> NeZero.charZero is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {n : Nat} [_inst_1 : NeZero.{0} Nat Nat.hasZero n] [_inst_2 : AddMonoidWithOne.{u1} M] [_inst_3 : CharZero.{u1} M _inst_2], NeZero.{u1} M (AddZeroClass.toHasZero.{u1} M (AddMonoid.toAddZeroClass.{u1} M (AddMonoidWithOne.toAddMonoid.{u1} M _inst_2))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat M (HasLiftT.mk.{1, succ u1} Nat M (CoeTCₓ.coe.{1, succ u1} Nat M (Nat.castCoe.{u1} M (AddMonoidWithOne.toNatCast.{u1} M _inst_2)))) n)
but is expected to have type
  forall {M : Type.{u1}} {n : Nat} [_inst_1 : NeZero.{0} Nat (Zero.ofOfNat0.{0} Nat (instOfNatNat 0)) n] [_inst_2 : AddMonoidWithOne.{u1} M] [_inst_3 : CharZero.{u1} M _inst_2], NeZero.{u1} M (AddMonoid.toZero.{u1} M (AddMonoidWithOne.toAddMonoid.{u1} M _inst_2)) (Nat.cast.{u1} M (AddMonoidWithOne.toNatCast.{u1} M _inst_2) n)
Case conversion may be inaccurate. Consider using '#align ne_zero.char_zero NeZero.charZeroₓ'. -/
instance charZero {M} {n : ℕ} [NeZero n] [AddMonoidWithOne M] [CharZero M] : NeZero (n : M) :=
  ⟨Nat.cast_ne_zero.mpr out⟩
#align ne_zero.char_zero NeZero.charZero

end NeZero

