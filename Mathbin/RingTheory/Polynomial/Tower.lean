/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yuyang Zhao

! This file was ported from Lean 3 source module ring_theory.polynomial.tower
! leanprover-community/mathlib commit e001509c11c4d0f549d91d89da95b4a0b43c714f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Tower
import Mathbin.Data.Polynomial.AlgebraMap

/-!
# Algebra towers for polynomial

This file proves some basic results about the algebra tower structure for the type `R[X]`.

This structure itself is provided elsewhere as `polynomial.is_scalar_tower`

When you update this file, you can also try to make a corresponding update in
`ring_theory.mv_polynomial.tower`.
-/


open Polynomial

variable (R A B : Type _)

namespace Polynomial

section Semiring

variable [CommSemiring R] [CommSemiring A] [Semiring B]

variable [Algebra R A] [Algebra A B] [Algebra R B]

variable [IsScalarTower R A B]

variable {R B}

@[simp]
theorem aeval_map_algebra_map (x : B) (p : R[X]) : aeval x (map (algebraMap R A) p) = aeval x p :=
  by rw [aeval_def, aeval_def, eval₂_map, IsScalarTower.algebra_map_eq R A B]
#align polynomial.aeval_map_algebra_map Polynomial.aeval_map_algebra_map

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring A] [Semiring B]

variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

variable {R A}

theorem aeval_algebra_map_apply (x : A) (p : R[X]) :
    aeval (algebraMap A B x) p = algebraMap A B (aeval x p) := by
  rw [aeval_def, aeval_def, hom_eval₂, ← IsScalarTower.algebra_map_eq]
#align polynomial.aeval_algebra_map_apply Polynomial.aeval_algebra_map_apply

@[simp]
theorem aeval_algebra_map_eq_zero_iff [NoZeroSMulDivisors A B] [Nontrivial B] (x : A) (p : R[X]) :
    aeval (algebraMap A B x) p = 0 ↔ aeval x p = 0 := by
  rw [aeval_algebra_map_apply, Algebra.algebra_map_eq_smul_one, smul_eq_zero,
    iff_false_intro (one_ne_zero' B), or_false_iff]
#align polynomial.aeval_algebra_map_eq_zero_iff Polynomial.aeval_algebra_map_eq_zero_iff

variable {B}

theorem aeval_algebra_map_eq_zero_iff_of_injective {x : A} {p : R[X]}
    (h : Function.Injective (algebraMap A B)) : aeval (algebraMap A B x) p = 0 ↔ aeval x p = 0 := by
  rw [aeval_algebra_map_apply, ← (algebraMap A B).map_zero, h.eq_iff]
#align
  polynomial.aeval_algebra_map_eq_zero_iff_of_injective Polynomial.aeval_algebra_map_eq_zero_iff_of_injective

end CommSemiring

end Polynomial

namespace Subalgebra

open Polynomial

section CommSemiring

variable {R A} [CommSemiring R] [CommSemiring A] [Algebra R A]

@[simp]
theorem aeval_coe (S : Subalgebra R A) (x : S) (p : R[X]) : aeval (x : A) p = aeval x p :=
  aeval_algebra_map_apply A x p
#align subalgebra.aeval_coe Subalgebra.aeval_coe

end CommSemiring

end Subalgebra

