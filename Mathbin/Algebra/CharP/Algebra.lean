/-
Copyright (c) 2021 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster, Eric Wieser

! This file was ported from Lean 3 source module algebra.char_p.algebra
! leanprover-community/mathlib commit 97eab48559068f3d6313da387714ef25768fb730
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.CharP.Basic
import Mathbin.RingTheory.Localization.FractionRing
import Mathbin.Algebra.FreeAlgebra

/-!
# Characteristics of algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we describe the characteristic of `R`-algebras.

In particular we are interested in the characteristic of free algebras over `R`
and the fraction field `fraction_ring R`.


## Main results

- `char_p_of_injective_algebra_map` If `R →+* A` is an injective algebra map
  then `A` has the same characteristic as `R`.

Instances constructed from this result:
- Any `free_algebra R X` has the same characteristic as `R`.
- The `fraction_ring R` of an integral domain `R` has the same characteristic as `R`.

-/


/- warning: char_p_of_injective_algebra_map -> charP_of_injective_algebraMap is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2], (Function.Injective.{succ u1, succ u2} R A (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) (fun (_x : RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) => R -> A) (RingHom.hasCoeToFun.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) (algebraMap.{u1, u2} R A _inst_1 _inst_2 _inst_3))) -> (forall (p : Nat) [_inst_4 : CharP.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) p], CharP.{u2} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) p)
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] [_inst_2 : Semiring.{u1} A] [_inst_3 : Algebra.{u2, u1} R A _inst_1 _inst_2], (Function.Injective.{succ u2, succ u1} R A (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RingHom.{u2, u1} R A (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} A _inst_2)) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => A) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (RingHom.{u2, u1} R A (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} A _inst_2)) R A (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u1} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R A (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} A _inst_2)) R A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R A (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} A _inst_2)) R A (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} A _inst_2) (RingHom.instRingHomClassRingHom.{u2, u1} R A (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} A _inst_2))))) (algebraMap.{u2, u1} R A _inst_1 _inst_2 _inst_3))) -> (forall (p : Nat) [_inst_4 : CharP.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) p], CharP.{u1} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} A (NonAssocSemiring.toAddCommMonoidWithOne.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_2))) p)
Case conversion may be inaccurate. Consider using '#align char_p_of_injective_algebra_map charP_of_injective_algebraMapₓ'. -/
/-- If the algebra map `R →+* A` is injective then `A` has the same characteristic as `R`. -/
theorem charP_of_injective_algebraMap {R A : Type _} [CommSemiring R] [Semiring A] [Algebra R A]
    (h : Function.Injective (algebraMap R A)) (p : ℕ) [CharP R p] : CharP A p :=
  {
    cast_eq_zero_iff := fun x => by
      rw [← CharP.cast_eq_zero_iff R p x]
      change algebraMap ℕ A x = 0 ↔ algebraMap ℕ R x = 0
      rw [IsScalarTower.algebraMap_apply ℕ R A x]
      refine' Iff.trans _ h.eq_iff
      rw [RingHom.map_zero] }
#align char_p_of_injective_algebra_map charP_of_injective_algebraMap

/- warning: char_p_of_injective_algebra_map' -> charP_of_injective_algebraMap' is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (A : Type.{u2}) [_inst_1 : Field.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A (Semifield.toCommSemiring.{u1} R (Field.toSemifield.{u1} R _inst_1)) _inst_2] [_inst_4 : Nontrivial.{u2} A] (p : Nat) [_inst_5 : CharP.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R _inst_1))))) p], CharP.{u2} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) p
but is expected to have type
  forall (R : Type.{u2}) (A : Type.{u1}) [_inst_1 : Field.{u2} R] [_inst_2 : Semiring.{u1} A] [_inst_3 : Algebra.{u2, u1} R A (Semifield.toCommSemiring.{u2} R (Field.toSemifield.{u2} R _inst_1)) _inst_2] [_inst_4 : Nontrivial.{u1} A] (p : Nat) [_inst_5 : CharP.{u2} R (AddGroupWithOne.toAddMonoidWithOne.{u2} R (Ring.toAddGroupWithOne.{u2} R (DivisionRing.toRing.{u2} R (Field.toDivisionRing.{u2} R _inst_1)))) p], CharP.{u1} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} A (NonAssocSemiring.toAddCommMonoidWithOne.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_2))) p
Case conversion may be inaccurate. Consider using '#align char_p_of_injective_algebra_map' charP_of_injective_algebraMap'ₓ'. -/
theorem charP_of_injective_algebraMap' (R A : Type _) [Field R] [Semiring A] [Algebra R A]
    [Nontrivial A] (p : ℕ) [CharP R p] : CharP A p :=
  charP_of_injective_algebraMap (algebraMap R A).Injective p
#align char_p_of_injective_algebra_map' charP_of_injective_algebraMap'

/- warning: char_zero_of_injective_algebra_map -> charZero_of_injective_algebraMap is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2], (Function.Injective.{succ u1, succ u2} R A (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) (fun (_x : RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) => R -> A) (RingHom.hasCoeToFun.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) (algebraMap.{u1, u2} R A _inst_1 _inst_2 _inst_3))) -> (forall [_inst_4 : CharZero.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))], CharZero.{u2} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))))
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] [_inst_2 : Semiring.{u1} A] [_inst_3 : Algebra.{u2, u1} R A _inst_1 _inst_2], (Function.Injective.{succ u2, succ u1} R A (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RingHom.{u2, u1} R A (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} A _inst_2)) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => A) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (RingHom.{u2, u1} R A (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} A _inst_2)) R A (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u1} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R A (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} A _inst_2)) R A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R A (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} A _inst_2)) R A (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} A _inst_2) (RingHom.instRingHomClassRingHom.{u2, u1} R A (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} A _inst_2))))) (algebraMap.{u2, u1} R A _inst_1 _inst_2 _inst_3))) -> (forall [_inst_4 : CharZero.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))], CharZero.{u1} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} A (NonAssocSemiring.toAddCommMonoidWithOne.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_2))))
Case conversion may be inaccurate. Consider using '#align char_zero_of_injective_algebra_map charZero_of_injective_algebraMapₓ'. -/
/-- If the algebra map `R →+* A` is injective and `R` has characteristic zero then so does `A`. -/
theorem charZero_of_injective_algebraMap {R A : Type _} [CommSemiring R] [Semiring A] [Algebra R A]
    (h : Function.Injective (algebraMap R A)) [CharZero R] : CharZero A :=
  {
    cast_injective := fun x y hxy =>
      by
      change algebraMap ℕ A x = algebraMap ℕ A y at hxy
      rw [IsScalarTower.algebraMap_apply ℕ R A x] at hxy
      rw [IsScalarTower.algebraMap_apply ℕ R A y] at hxy
      exact CharZero.cast_injective (h hxy) }
#align char_zero_of_injective_algebra_map charZero_of_injective_algebraMap

/-!
As an application, a `ℚ`-algebra has characteristic zero.
-/


-- `char_p.char_p_to_char_zero A _ (char_p_of_injective_algebra_map h 0)` does not work
-- here as it would require `ring A`.
section QAlgebra

variable (R : Type _) [Nontrivial R]

#print algebraRat.charP_zero /-
/-- A nontrivial `ℚ`-algebra has `char_p` equal to zero.

This cannot be a (local) instance because it would immediately form a loop with the
instance `algebra_rat`. It's probably easier to go the other way: prove `char_zero R` and
automatically receive an `algebra ℚ R` instance.
-/
theorem algebraRat.charP_zero [Semiring R] [Algebra ℚ R] : CharP R 0 :=
  charP_of_injective_algebraMap (algebraMap ℚ R).Injective 0
#align algebra_rat.char_p_zero algebraRat.charP_zero
-/

/- warning: algebra_rat.char_zero -> algebraRat.charZero is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : Nontrivial.{u1} R] [_inst_2 : Ring.{u1} R] [_inst_3 : Algebra.{0, u1} Rat R Rat.commSemiring (Ring.toSemiring.{u1} R _inst_2)], CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)))
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : Nontrivial.{u1} R] [_inst_2 : Ring.{u1} R] [_inst_3 : Algebra.{0, u1} Rat R Rat.commSemiring (Ring.toSemiring.{u1} R _inst_2)], CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_2))
Case conversion may be inaccurate. Consider using '#align algebra_rat.char_zero algebraRat.charZeroₓ'. -/
/-- A nontrivial `ℚ`-algebra has characteristic zero.

This cannot be a (local) instance because it would immediately form a loop with the
instance `algebra_rat`. It's probably easier to go the other way: prove `char_zero R` and
automatically receive an `algebra ℚ R` instance.
-/
theorem algebraRat.charZero [Ring R] [Algebra ℚ R] : CharZero R :=
  @CharP.charP_to_charZero R _ (algebraRat.charP_zero R)
#align algebra_rat.char_zero algebraRat.charZero

end QAlgebra

/-!
An algebra over a field has the same characteristic as the field.
-/


section

variable (K L : Type _) [Field K] [CommSemiring L] [Nontrivial L] [Algebra K L]

/- warning: algebra.char_p_iff -> Algebra.charP_iff is a dubious translation:
lean 3 declaration is
  forall (K : Type.{u1}) (L : Type.{u2}) [_inst_1 : Field.{u1} K] [_inst_2 : CommSemiring.{u2} L] [_inst_3 : Nontrivial.{u2} L] [_inst_4 : Algebra.{u1, u2} K L (Semifield.toCommSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1)) (CommSemiring.toSemiring.{u2} L _inst_2)] (p : Nat), Iff (CharP.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (NonAssocRing.toAddGroupWithOne.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))))) p) (CharP.{u2} L (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} L (NonAssocSemiring.toAddCommMonoidWithOne.{u2} L (Semiring.toNonAssocSemiring.{u2} L (CommSemiring.toSemiring.{u2} L _inst_2)))) p)
but is expected to have type
  forall (K : Type.{u2}) (L : Type.{u1}) [_inst_1 : Field.{u2} K] [_inst_2 : CommSemiring.{u1} L] [_inst_3 : Nontrivial.{u1} L] [_inst_4 : Algebra.{u2, u1} K L (Semifield.toCommSemiring.{u2} K (Field.toSemifield.{u2} K _inst_1)) (CommSemiring.toSemiring.{u1} L _inst_2)] (p : Nat), Iff (CharP.{u2} K (AddGroupWithOne.toAddMonoidWithOne.{u2} K (Ring.toAddGroupWithOne.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_1)))) p) (CharP.{u1} L (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} L (NonAssocSemiring.toAddCommMonoidWithOne.{u1} L (Semiring.toNonAssocSemiring.{u1} L (CommSemiring.toSemiring.{u1} L _inst_2)))) p)
Case conversion may be inaccurate. Consider using '#align algebra.char_p_iff Algebra.charP_iffₓ'. -/
theorem Algebra.charP_iff (p : ℕ) : CharP K p ↔ CharP L p :=
  (algebraMap K L).charP_iff_charP p
#align algebra.char_p_iff Algebra.charP_iff

/- warning: algebra.ring_char_eq -> Algebra.ringChar_eq is a dubious translation:
lean 3 declaration is
  forall (K : Type.{u1}) (L : Type.{u2}) [_inst_1 : Field.{u1} K] [_inst_2 : CommSemiring.{u2} L] [_inst_3 : Nontrivial.{u2} L] [_inst_4 : Algebra.{u1, u2} K L (Semifield.toCommSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1)) (CommSemiring.toSemiring.{u2} L _inst_2)], Eq.{1} Nat (ringChar.{u1} K (NonAssocRing.toNonAssocSemiring.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))))) (ringChar.{u2} L (Semiring.toNonAssocSemiring.{u2} L (CommSemiring.toSemiring.{u2} L _inst_2)))
but is expected to have type
  forall (K : Type.{u2}) (L : Type.{u1}) [_inst_1 : Field.{u2} K] [_inst_2 : CommSemiring.{u1} L] [_inst_3 : Nontrivial.{u1} L] [_inst_4 : Algebra.{u2, u1} K L (Semifield.toCommSemiring.{u2} K (Field.toSemifield.{u2} K _inst_1)) (CommSemiring.toSemiring.{u1} L _inst_2)], Eq.{1} Nat (ringChar.{u2} K (NonAssocRing.toNonAssocSemiring.{u2} K (Ring.toNonAssocRing.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_1))))) (ringChar.{u1} L (Semiring.toNonAssocSemiring.{u1} L (CommSemiring.toSemiring.{u1} L _inst_2)))
Case conversion may be inaccurate. Consider using '#align algebra.ring_char_eq Algebra.ringChar_eqₓ'. -/
theorem Algebra.ringChar_eq : ringChar K = ringChar L :=
  by
  rw [ringChar.eq_iff, Algebra.charP_iff K L]
  apply ringChar.charP
#align algebra.ring_char_eq Algebra.ringChar_eq

end

namespace FreeAlgebra

variable {R X : Type _} [CommSemiring R] (p : ℕ)

/- warning: free_algebra.char_p -> FreeAlgebra.charP is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {X : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] (p : Nat) [_inst_2 : CharP.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) p], CharP.{max u1 u2} (FreeAlgebra.{u1, u2} R _inst_1 X) (AddCommMonoidWithOne.toAddMonoidWithOne.{max u1 u2} (FreeAlgebra.{u1, u2} R _inst_1 X) (NonAssocSemiring.toAddCommMonoidWithOne.{max u1 u2} (FreeAlgebra.{u1, u2} R _inst_1 X) (Semiring.toNonAssocSemiring.{max u1 u2} (FreeAlgebra.{u1, u2} R _inst_1 X) (FreeAlgebra.semiring.{u1, u2} R _inst_1 X)))) p
but is expected to have type
  forall {R : Type.{u1}} {X : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] (p : Nat) [_inst_2 : CharP.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) p], CharP.{max u2 u1} (FreeAlgebra.{u1, u2} R _inst_1 X) (AddCommMonoidWithOne.toAddMonoidWithOne.{max u1 u2} (FreeAlgebra.{u1, u2} R _inst_1 X) (NonAssocSemiring.toAddCommMonoidWithOne.{max u1 u2} (FreeAlgebra.{u1, u2} R _inst_1 X) (Semiring.toNonAssocSemiring.{max u1 u2} (FreeAlgebra.{u1, u2} R _inst_1 X) (FreeAlgebra.instSemiringFreeAlgebra.{u1, u2} R _inst_1 X)))) p
Case conversion may be inaccurate. Consider using '#align free_algebra.char_p FreeAlgebra.charPₓ'. -/
/-- If `R` has characteristic `p`, then so does `free_algebra R X`. -/
instance charP [CharP R p] : CharP (FreeAlgebra R X) p :=
  charP_of_injective_algebraMap FreeAlgebra.algebraMap_leftInverse.Injective p
#align free_algebra.char_p FreeAlgebra.charP

/- warning: free_algebra.char_zero -> FreeAlgebra.charZero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {X : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : CharZero.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))], CharZero.{max u1 u2} (FreeAlgebra.{u1, u2} R _inst_1 X) (AddCommMonoidWithOne.toAddMonoidWithOne.{max u1 u2} (FreeAlgebra.{u1, u2} R _inst_1 X) (NonAssocSemiring.toAddCommMonoidWithOne.{max u1 u2} (FreeAlgebra.{u1, u2} R _inst_1 X) (Semiring.toNonAssocSemiring.{max u1 u2} (FreeAlgebra.{u1, u2} R _inst_1 X) (FreeAlgebra.semiring.{u1, u2} R _inst_1 X))))
but is expected to have type
  forall {R : Type.{u1}} {X : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : CharZero.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))], CharZero.{max u2 u1} (FreeAlgebra.{u1, u2} R _inst_1 X) (AddCommMonoidWithOne.toAddMonoidWithOne.{max u1 u2} (FreeAlgebra.{u1, u2} R _inst_1 X) (NonAssocSemiring.toAddCommMonoidWithOne.{max u1 u2} (FreeAlgebra.{u1, u2} R _inst_1 X) (Semiring.toNonAssocSemiring.{max u1 u2} (FreeAlgebra.{u1, u2} R _inst_1 X) (FreeAlgebra.instSemiringFreeAlgebra.{u1, u2} R _inst_1 X))))
Case conversion may be inaccurate. Consider using '#align free_algebra.char_zero FreeAlgebra.charZeroₓ'. -/
/-- If `R` has characteristic `0`, then so does `free_algebra R X`. -/
instance charZero [CharZero R] : CharZero (FreeAlgebra R X) :=
  charZero_of_injective_algebraMap FreeAlgebra.algebraMap_leftInverse.Injective
#align free_algebra.char_zero FreeAlgebra.charZero

end FreeAlgebra

namespace IsFractionRing

variable (R : Type _) {K : Type _} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]

variable (p : ℕ)

/- warning: is_fraction_ring.char_p_of_is_fraction_ring -> IsFractionRing.charP_of_isFractionRing is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {K : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Field.{u2} K] [_inst_3 : Algebra.{u1, u2} R K (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_2)))] [_inst_4 : IsFractionRing.{u1, u2} R _inst_1 K (Field.toCommRing.{u2} K _inst_2) _inst_3] (p : Nat) [_inst_5 : CharP.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))) p], CharP.{u2} K (AddGroupWithOne.toAddMonoidWithOne.{u2} K (NonAssocRing.toAddGroupWithOne.{u2} K (Ring.toNonAssocRing.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_2))))) p
but is expected to have type
  forall (R : Type.{u2}) {K : Type.{u1}} [_inst_1 : CommRing.{u2} R] [_inst_2 : Field.{u1} K] [_inst_3 : Algebra.{u2, u1} R K (CommRing.toCommSemiring.{u2} R _inst_1) (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_2)))] [_inst_4 : IsFractionRing.{u2, u1} R _inst_1 K (Field.toCommRing.{u1} K _inst_2) _inst_3] (p : Nat) [_inst_5 : CharP.{u2} R (AddGroupWithOne.toAddMonoidWithOne.{u2} R (Ring.toAddGroupWithOne.{u2} R (CommRing.toRing.{u2} R _inst_1))) p], CharP.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (Ring.toAddGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_2)))) p
Case conversion may be inaccurate. Consider using '#align is_fraction_ring.char_p_of_is_fraction_ring IsFractionRing.charP_of_isFractionRingₓ'. -/
/-- If `R` has characteristic `p`, then so does Frac(R). -/
theorem charP_of_isFractionRing [CharP R p] : CharP K p :=
  charP_of_injective_algebraMap (IsFractionRing.injective R K) p
#align is_fraction_ring.char_p_of_is_fraction_ring IsFractionRing.charP_of_isFractionRing

/- warning: is_fraction_ring.char_zero_of_is_fraction_ring -> IsFractionRing.charZero_of_isFractionRing is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {K : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Field.{u2} K] [_inst_3 : Algebra.{u1, u2} R K (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_2)))] [_inst_4 : IsFractionRing.{u1, u2} R _inst_1 K (Field.toCommRing.{u2} K _inst_2) _inst_3] [_inst_5 : CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))], CharZero.{u2} K (AddGroupWithOne.toAddMonoidWithOne.{u2} K (NonAssocRing.toAddGroupWithOne.{u2} K (Ring.toNonAssocRing.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_2)))))
but is expected to have type
  forall (R : Type.{u2}) {K : Type.{u1}} [_inst_1 : CommRing.{u2} R] [_inst_2 : Field.{u1} K] [_inst_3 : Algebra.{u2, u1} R K (CommRing.toCommSemiring.{u2} R _inst_1) (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_2)))] [_inst_4 : IsFractionRing.{u2, u1} R _inst_1 K (Field.toCommRing.{u1} K _inst_2) _inst_3] [_inst_5 : CharZero.{u2} R (AddGroupWithOne.toAddMonoidWithOne.{u2} R (Ring.toAddGroupWithOne.{u2} R (CommRing.toRing.{u2} R _inst_1)))], CharZero.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (Ring.toAddGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_2))))
Case conversion may be inaccurate. Consider using '#align is_fraction_ring.char_zero_of_is_fraction_ring IsFractionRing.charZero_of_isFractionRingₓ'. -/
/-- If `R` has characteristic `0`, then so does Frac(R). -/
theorem charZero_of_isFractionRing [CharZero R] : CharZero K :=
  @CharP.charP_to_charZero K _ (charP_of_isFractionRing R 0)
#align is_fraction_ring.char_zero_of_is_fraction_ring IsFractionRing.charZero_of_isFractionRing

variable [IsDomain R]

/- warning: is_fraction_ring.char_p -> IsFractionRing.charP is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : CommRing.{u1} R] (p : Nat) [_inst_5 : IsDomain.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))] [_inst_6 : CharP.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))) p], CharP.{u1} (FractionRing.{u1} R _inst_1) (AddGroupWithOne.toAddMonoidWithOne.{u1} (FractionRing.{u1} R _inst_1) (NonAssocRing.toAddGroupWithOne.{u1} (FractionRing.{u1} R _inst_1) (Ring.toNonAssocRing.{u1} (FractionRing.{u1} R _inst_1) (DivisionRing.toRing.{u1} (FractionRing.{u1} R _inst_1) (Field.toDivisionRing.{u1} (FractionRing.{u1} R _inst_1) (FractionRing.field.{u1} R _inst_1 _inst_5)))))) p
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : CommRing.{u1} R] (p : Nat) [_inst_5 : IsDomain.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))] [_inst_6 : CharP.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (Ring.toAddGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1))) p], CharP.{u1} (FractionRing.{u1} R _inst_1) (AddGroupWithOne.toAddMonoidWithOne.{u1} (FractionRing.{u1} R _inst_1) (Ring.toAddGroupWithOne.{u1} (FractionRing.{u1} R _inst_1) (DivisionRing.toRing.{u1} (FractionRing.{u1} R _inst_1) (Field.toDivisionRing.{u1} (FractionRing.{u1} R _inst_1) (FractionRing.instFieldFractionRing.{u1} R _inst_1 _inst_5))))) p
Case conversion may be inaccurate. Consider using '#align is_fraction_ring.char_p IsFractionRing.charPₓ'. -/
/-- If `R` has characteristic `p`, then so does `fraction_ring R`. -/
instance charP [CharP R p] : CharP (FractionRing R) p :=
  charP_of_isFractionRing R p
#align is_fraction_ring.char_p IsFractionRing.charP

/- warning: is_fraction_ring.char_zero -> IsFractionRing.charZero is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : CommRing.{u1} R] [_inst_5 : IsDomain.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))] [_inst_6 : CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))], CharZero.{u1} (FractionRing.{u1} R _inst_1) (AddGroupWithOne.toAddMonoidWithOne.{u1} (FractionRing.{u1} R _inst_1) (NonAssocRing.toAddGroupWithOne.{u1} (FractionRing.{u1} R _inst_1) (Ring.toNonAssocRing.{u1} (FractionRing.{u1} R _inst_1) (DivisionRing.toRing.{u1} (FractionRing.{u1} R _inst_1) (Field.toDivisionRing.{u1} (FractionRing.{u1} R _inst_1) (FractionRing.field.{u1} R _inst_1 _inst_5))))))
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : CommRing.{u1} R] [_inst_5 : IsDomain.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))] [_inst_6 : CharZero.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (Ring.toAddGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1)))], CharZero.{u1} (FractionRing.{u1} R _inst_1) (AddGroupWithOne.toAddMonoidWithOne.{u1} (FractionRing.{u1} R _inst_1) (Ring.toAddGroupWithOne.{u1} (FractionRing.{u1} R _inst_1) (DivisionRing.toRing.{u1} (FractionRing.{u1} R _inst_1) (Field.toDivisionRing.{u1} (FractionRing.{u1} R _inst_1) (FractionRing.instFieldFractionRing.{u1} R _inst_1 _inst_5)))))
Case conversion may be inaccurate. Consider using '#align is_fraction_ring.char_zero IsFractionRing.charZeroₓ'. -/
/-- If `R` has characteristic `0`, then so does `fraction_ring R`. -/
instance charZero [CharZero R] : CharZero (FractionRing R) :=
  charZero_of_isFractionRing R
#align is_fraction_ring.char_zero IsFractionRing.charZero

end IsFractionRing

