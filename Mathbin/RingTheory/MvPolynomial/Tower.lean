/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao

! This file was ported from Lean 3 source module ring_theory.mv_polynomial.tower
! leanprover-community/mathlib commit 09597669f02422ed388036273d8848119699c22f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Tower
import Mathbin.Data.MvPolynomial.Basic

/-!
# Algebra towers for multivariate polynomial

This file proves some basic results about the algebra tower structure for the type
`mv_polynomial σ R`.

This structure itself is provided elsewhere as `mv_polynomial.is_scalar_tower`

When you update this file, you can also try to make a corresponding update in
`ring_theory.polynomial.tower`.
-/


variable (R A B : Type _) {σ : Type _}

namespace MvPolynomial

section Semiring

variable [CommSemiring R] [CommSemiring A] [CommSemiring B]

variable [Algebra R A] [Algebra A B] [Algebra R B]

variable [IsScalarTower R A B]

variable {R B}

theorem aeval_map_algebra_map (x : σ → B) (p : MvPolynomial σ R) :
    aeval x (map (algebraMap R A) p) = aeval x p := by
  rw [aeval_def, aeval_def, eval₂_map, IsScalarTower.algebra_map_eq R A B]
#align mv_polynomial.aeval_map_algebra_map MvPolynomial.aeval_map_algebra_map

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring A] [CommSemiring B]

variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

variable {R A}

theorem aeval_algebra_map_apply (x : σ → A) (p : MvPolynomial σ R) :
    aeval (algebraMap A B ∘ x) p = algebraMap A B (MvPolynomial.aeval x p) := by
  rw [aeval_def, aeval_def, ← coe_eval₂_hom, ← coe_eval₂_hom, map_eval₂_hom, ←
    IsScalarTower.algebra_map_eq]
#align mv_polynomial.aeval_algebra_map_apply MvPolynomial.aeval_algebra_map_apply

theorem aeval_algebra_map_eq_zero_iff [NoZeroSmulDivisors A B] [Nontrivial B] (x : σ → A)
    (p : MvPolynomial σ R) : aeval (algebraMap A B ∘ x) p = 0 ↔ aeval x p = 0 := by
  rw [aeval_algebra_map_apply, Algebra.algebra_map_eq_smul_one, smul_eq_zero,
    iff_false_intro (one_ne_zero' B), or_false_iff]
#align mv_polynomial.aeval_algebra_map_eq_zero_iff MvPolynomial.aeval_algebra_map_eq_zero_iff

theorem aeval_algebra_map_eq_zero_iff_of_injective {x : σ → A} {p : MvPolynomial σ R}
    (h : Function.Injective (algebraMap A B)) : aeval (algebraMap A B ∘ x) p = 0 ↔ aeval x p = 0 :=
  by rw [aeval_algebra_map_apply, ← (algebraMap A B).map_zero, h.eq_iff]
#align
  mv_polynomial.aeval_algebra_map_eq_zero_iff_of_injective MvPolynomial.aeval_algebra_map_eq_zero_iff_of_injective

end CommSemiring

end MvPolynomial

namespace Subalgebra

open MvPolynomial

section CommSemiring

variable {R A} [CommSemiring R] [CommSemiring A] [Algebra R A]

@[simp]
theorem mv_polynomial_aeval_coe (S : Subalgebra R A) (x : σ → S) (p : MvPolynomial σ R) :
    aeval (fun i => (x i : A)) p = aeval x p := by convert aeval_algebra_map_apply A x p
#align subalgebra.mv_polynomial_aeval_coe Subalgebra.mv_polynomial_aeval_coe

end CommSemiring

end Subalgebra

