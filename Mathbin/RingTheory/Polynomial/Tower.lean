/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yuyang Zhao
-/
import Algebra.Algebra.Tower
import Data.Polynomial.AlgebraMap

#align_import ring_theory.polynomial.tower from "leanprover-community/mathlib"@"10bf4f825ad729c5653adc039dafa3622e7f93c9"

/-!
# Algebra towers for polynomial

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves some basic results about the algebra tower structure for the type `R[X]`.

This structure itself is provided elsewhere as `polynomial.is_scalar_tower`

When you update this file, you can also try to make a corresponding update in
`ring_theory.mv_polynomial.tower`.
-/


open scoped Polynomial

variable (R A B : Type _)

namespace Polynomial

section Semiring

variable [CommSemiring R] [CommSemiring A] [Semiring B]

variable [Algebra R A] [Algebra A B] [Algebra R B]

variable [IsScalarTower R A B]

variable {R B}

#print Polynomial.aeval_map_algebraMap /-
@[simp]
theorem aeval_map_algebraMap (x : B) (p : R[X]) : aeval x (map (algebraMap R A) p) = aeval x p := by
  rw [aeval_def, aeval_def, eval₂_map, IsScalarTower.algebraMap_eq R A B]
#align polynomial.aeval_map_algebra_map Polynomial.aeval_map_algebraMap
-/

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring A] [Semiring B]

variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

variable {R A}

#print Polynomial.aeval_algebraMap_apply /-
theorem aeval_algebraMap_apply (x : A) (p : R[X]) :
    aeval (algebraMap A B x) p = algebraMap A B (aeval x p) := by
  rw [aeval_def, aeval_def, hom_eval₂, ← IsScalarTower.algebraMap_eq]
#align polynomial.aeval_algebra_map_apply Polynomial.aeval_algebraMap_apply
-/

#print Polynomial.aeval_algebraMap_eq_zero_iff /-
@[simp]
theorem aeval_algebraMap_eq_zero_iff [NoZeroSMulDivisors A B] [Nontrivial B] (x : A) (p : R[X]) :
    aeval (algebraMap A B x) p = 0 ↔ aeval x p = 0 := by
  rw [aeval_algebra_map_apply, Algebra.algebraMap_eq_smul_one, smul_eq_zero,
    iff_false_intro (one_ne_zero' B), or_false_iff]
#align polynomial.aeval_algebra_map_eq_zero_iff Polynomial.aeval_algebraMap_eq_zero_iff
-/

variable {B}

#print Polynomial.aeval_algebraMap_eq_zero_iff_of_injective /-
theorem aeval_algebraMap_eq_zero_iff_of_injective {x : A} {p : R[X]}
    (h : Function.Injective (algebraMap A B)) : aeval (algebraMap A B x) p = 0 ↔ aeval x p = 0 := by
  rw [aeval_algebra_map_apply, ← (algebraMap A B).map_zero, h.eq_iff]
#align polynomial.aeval_algebra_map_eq_zero_iff_of_injective Polynomial.aeval_algebraMap_eq_zero_iff_of_injective
-/

end CommSemiring

end Polynomial

namespace Subalgebra

open Polynomial

section CommSemiring

variable {R A} [CommSemiring R] [CommSemiring A] [Algebra R A]

#print Subalgebra.aeval_coe /-
@[simp]
theorem aeval_coe (S : Subalgebra R A) (x : S) (p : R[X]) : aeval (x : A) p = aeval x p :=
  aeval_algebraMap_apply A x p
#align subalgebra.aeval_coe Subalgebra.aeval_coe
-/

end CommSemiring

end Subalgebra

