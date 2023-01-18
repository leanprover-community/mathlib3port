/-
Copyright (c) 2021 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster, Eric Wieser

! This file was ported from Lean 3 source module algebra.char_p.algebra
! leanprover-community/mathlib commit 008205aa645b3f194c1da47025c5f110c8406eab
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.CharP.Basic
import Mathbin.RingTheory.Localization.FractionRing
import Mathbin.Algebra.FreeAlgebra

/-!
# Characteristics of algebras

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


/-- If the algebra map `R →+* A` is injective then `A` has the same characteristic as `R`. -/
theorem char_p_of_injective_algebra_map {R A : Type _} [CommSemiring R] [Semiring A] [Algebra R A]
    (h : Function.Injective (algebraMap R A)) (p : ℕ) [CharP R p] : CharP A p :=
  {
    cast_eq_zero_iff := fun x => by
      rw [← CharP.cast_eq_zero_iff R p x]
      change algebraMap ℕ A x = 0 ↔ algebraMap ℕ R x = 0
      rw [IsScalarTower.algebra_map_apply ℕ R A x]
      refine' Iff.trans _ h.eq_iff
      rw [RingHom.map_zero] }
#align char_p_of_injective_algebra_map char_p_of_injective_algebra_map

theorem char_p_of_injective_algebra_map' (R A : Type _) [Field R] [Semiring A] [Algebra R A]
    [Nontrivial A] (p : ℕ) [CharP R p] : CharP A p :=
  char_p_of_injective_algebra_map (algebraMap R A).Injective p
#align char_p_of_injective_algebra_map' char_p_of_injective_algebra_map'

/-- If the algebra map `R →+* A` is injective and `R` has characteristic zero then so does `A`. -/
theorem char_zero_of_injective_algebra_map {R A : Type _} [CommSemiring R] [Semiring A]
    [Algebra R A] (h : Function.Injective (algebraMap R A)) [CharZero R] : CharZero A :=
  {
    cast_injective := fun x y hxy =>
      by
      change algebraMap ℕ A x = algebraMap ℕ A y at hxy
      rw [IsScalarTower.algebra_map_apply ℕ R A x] at hxy
      rw [IsScalarTower.algebra_map_apply ℕ R A y] at hxy
      exact CharZero.cast_injective (h hxy) }
#align char_zero_of_injective_algebra_map char_zero_of_injective_algebra_map

/-!
As an application, a `ℚ`-algebra has characteristic zero.
-/


-- `char_p.char_p_to_char_zero A _ (char_p_of_injective_algebra_map h 0)` does not work
-- here as it would require `ring A`.
section QAlgebra

variable (R : Type _) [Nontrivial R]

/-- A nontrivial `ℚ`-algebra has `char_p` equal to zero.

This cannot be a (local) instance because it would immediately form a loop with the
instance `algebra_rat`. It's probably easier to go the other way: prove `char_zero R` and
automatically receive an `algebra ℚ R` instance.
-/
theorem algebraRat.char_p_zero [Semiring R] [Algebra ℚ R] : CharP R 0 :=
  char_p_of_injective_algebra_map (algebraMap ℚ R).Injective 0
#align algebra_rat.char_p_zero algebraRat.char_p_zero

/-- A nontrivial `ℚ`-algebra has characteristic zero.

This cannot be a (local) instance because it would immediately form a loop with the
instance `algebra_rat`. It's probably easier to go the other way: prove `char_zero R` and
automatically receive an `algebra ℚ R` instance.
-/
theorem algebraRat.char_zero [Ring R] [Algebra ℚ R] : CharZero R :=
  @CharP.char_p_to_char_zero R _ (algebraRat.char_p_zero R)
#align algebra_rat.char_zero algebraRat.char_zero

end QAlgebra

/-!
An algebra over a field has the same characteristic as the field.
-/


section

variable (K L : Type _) [Field K] [CommSemiring L] [Nontrivial L] [Algebra K L]

theorem Algebra.char_p_iff (p : ℕ) : CharP K p ↔ CharP L p :=
  (algebraMap K L).char_p_iff_char_p p
#align algebra.char_p_iff Algebra.char_p_iff

theorem Algebra.ring_char_eq : ringChar K = ringChar L :=
  by
  rw [ringChar.eq_iff, Algebra.char_p_iff K L]
  apply ringChar.char_p
#align algebra.ring_char_eq Algebra.ring_char_eq

end

namespace FreeAlgebra

variable {R X : Type _} [CommSemiring R] (p : ℕ)

/-- If `R` has characteristic `p`, then so does `free_algebra R X`. -/
instance char_p [CharP R p] : CharP (FreeAlgebra R X) p :=
  char_p_of_injective_algebra_map FreeAlgebra.algebra_map_left_inverse.Injective p
#align free_algebra.char_p FreeAlgebra.char_p

/-- If `R` has characteristic `0`, then so does `free_algebra R X`. -/
instance char_zero [CharZero R] : CharZero (FreeAlgebra R X) :=
  char_zero_of_injective_algebra_map FreeAlgebra.algebra_map_left_inverse.Injective
#align free_algebra.char_zero FreeAlgebra.char_zero

end FreeAlgebra

namespace IsFractionRing

variable (R : Type _) {K : Type _} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]

variable (p : ℕ)

/-- If `R` has characteristic `p`, then so does Frac(R). -/
theorem char_p_of_is_fraction_ring [CharP R p] : CharP K p :=
  char_p_of_injective_algebra_map (IsFractionRing.injective R K) p
#align is_fraction_ring.char_p_of_is_fraction_ring IsFractionRing.char_p_of_is_fraction_ring

/-- If `R` has characteristic `0`, then so does Frac(R). -/
theorem char_zero_of_is_fraction_ring [CharZero R] : CharZero K :=
  @CharP.char_p_to_char_zero K _ (char_p_of_is_fraction_ring R 0)
#align is_fraction_ring.char_zero_of_is_fraction_ring IsFractionRing.char_zero_of_is_fraction_ring

variable [IsDomain R]

/-- If `R` has characteristic `p`, then so does `fraction_ring R`. -/
instance char_p [CharP R p] : CharP (FractionRing R) p :=
  char_p_of_is_fraction_ring R p
#align is_fraction_ring.char_p IsFractionRing.char_p

/-- If `R` has characteristic `0`, then so does `fraction_ring R`. -/
instance char_zero [CharZero R] : CharZero (FractionRing R) :=
  char_zero_of_is_fraction_ring R
#align is_fraction_ring.char_zero IsFractionRing.char_zero

end IsFractionRing

