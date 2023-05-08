/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module analysis.special_functions.trigonometric.chebyshev
! leanprover-community/mathlib commit fe8d0ff42c3c24d789f491dc2622b6cac3d61564
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Complex.Exponential
import Mathbin.Data.Complex.Module
import Mathbin.Data.Polynomial.AlgebraMap
import Mathbin.RingTheory.Polynomial.Chebyshev

/-!
# Multiple angle formulas in terms of Chebyshev polynomials

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file gives the trigonometric characterizations of Chebyshev polynomials, for both the real
(`real.cos`) and complex (`complex.cos`) cosine.
-/


namespace Polynomial.Chebyshev

open Polynomial

variable {R A : Type _} [CommRing R] [CommRing A] [Algebra R A]

#print Polynomial.Chebyshev.aeval_T /-
@[simp]
theorem aeval_T (x : A) (n : ℕ) : aeval x (T R n) = (T A n).eval x := by
  rw [aeval_def, eval₂_eq_eval_map, map_T]
#align polynomial.chebyshev.aeval_T Polynomial.Chebyshev.aeval_T
-/

#print Polynomial.Chebyshev.aeval_U /-
@[simp]
theorem aeval_U (x : A) (n : ℕ) : aeval x (U R n) = (U A n).eval x := by
  rw [aeval_def, eval₂_eq_eval_map, map_U]
#align polynomial.chebyshev.aeval_U Polynomial.Chebyshev.aeval_U
-/

/- warning: polynomial.chebyshev.algebra_map_eval_T -> Polynomial.Chebyshev.algebraMap_eval_T is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : CommRing.{u2} A] [_inst_3 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))] (x : R) (n : Nat), Eq.{succ u2} A (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)))) (fun (_x : RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)))) => R -> A) (RingHom.hasCoeToFun.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)))) (algebraMap.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)) _inst_3) (Polynomial.eval.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) x (Polynomial.Chebyshev.T.{u1} R _inst_1 n))) (Polynomial.eval.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)))) (fun (_x : RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)))) => R -> A) (RingHom.hasCoeToFun.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)))) (algebraMap.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)) _inst_3) x) (Polynomial.Chebyshev.T.{u2} A _inst_2 n))
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : CommRing.{u2} A] [_inst_3 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))] (x : R) (n : Nat), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => A) (Polynomial.eval.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) x (Polynomial.Chebyshev.T.{u1} R _inst_1 n))) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => A) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)))) R A (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) (NonUnitalNonAssocSemiring.toMul.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)))) R A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)))) R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))) (RingHom.instRingHomClassRingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))))))) (algebraMap.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)) _inst_3) (Polynomial.eval.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) x (Polynomial.Chebyshev.T.{u1} R _inst_1 n))) (Polynomial.eval.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => A) x) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => A) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)))) R A (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) (NonUnitalNonAssocSemiring.toMul.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)))) R A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)))) R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))) (RingHom.instRingHomClassRingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))))))) (algebraMap.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)) _inst_3) x) (Polynomial.Chebyshev.T.{u2} A _inst_2 n))
Case conversion may be inaccurate. Consider using '#align polynomial.chebyshev.algebra_map_eval_T Polynomial.Chebyshev.algebraMap_eval_Tₓ'. -/
@[simp]
theorem algebraMap_eval_T (x : R) (n : ℕ) :
    algebraMap R A ((T R n).eval x) = (T A n).eval (algebraMap R A x) := by
  rw [← aeval_algebra_map_apply_eq_algebra_map_eval, aeval_T]
#align polynomial.chebyshev.algebra_map_eval_T Polynomial.Chebyshev.algebraMap_eval_T

/- warning: polynomial.chebyshev.algebra_map_eval_U -> Polynomial.Chebyshev.algebraMap_eval_U is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : CommRing.{u2} A] [_inst_3 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))] (x : R) (n : Nat), Eq.{succ u2} A (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)))) (fun (_x : RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)))) => R -> A) (RingHom.hasCoeToFun.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)))) (algebraMap.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)) _inst_3) (Polynomial.eval.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) x (Polynomial.Chebyshev.U.{u1} R _inst_1 n))) (Polynomial.eval.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)))) (fun (_x : RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)))) => R -> A) (RingHom.hasCoeToFun.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)))) (algebraMap.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)) _inst_3) x) (Polynomial.Chebyshev.U.{u2} A _inst_2 n))
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : CommRing.{u2} A] [_inst_3 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))] (x : R) (n : Nat), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => A) (Polynomial.eval.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) x (Polynomial.Chebyshev.U.{u1} R _inst_1 n))) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => A) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)))) R A (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) (NonUnitalNonAssocSemiring.toMul.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)))) R A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)))) R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))) (RingHom.instRingHomClassRingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))))))) (algebraMap.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)) _inst_3) (Polynomial.eval.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) x (Polynomial.Chebyshev.U.{u1} R _inst_1 n))) (Polynomial.eval.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => A) x) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => A) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)))) R A (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) (NonUnitalNonAssocSemiring.toMul.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)))) R A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)))) R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))) (RingHom.instRingHomClassRingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))))))) (algebraMap.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)) _inst_3) x) (Polynomial.Chebyshev.U.{u2} A _inst_2 n))
Case conversion may be inaccurate. Consider using '#align polynomial.chebyshev.algebra_map_eval_U Polynomial.Chebyshev.algebraMap_eval_Uₓ'. -/
@[simp]
theorem algebraMap_eval_U (x : R) (n : ℕ) :
    algebraMap R A ((U R n).eval x) = (U A n).eval (algebraMap R A x) := by
  rw [← aeval_algebra_map_apply_eq_algebra_map_eval, aeval_U]
#align polynomial.chebyshev.algebra_map_eval_U Polynomial.Chebyshev.algebraMap_eval_U

/- warning: polynomial.chebyshev.complex_of_real_eval_T -> Polynomial.Chebyshev.complex_of_real_eval_T is a dubious translation:
lean 3 declaration is
  forall (x : Real) (n : Nat), Eq.{1} Complex ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Polynomial.eval.{0} Real (Ring.toSemiring.{0} Real (CommRing.toRing.{0} Real Real.commRing)) x (Polynomial.Chebyshev.T.{0} Real Real.commRing n))) (Polynomial.eval.{0} Complex (Ring.toSemiring.{0} Complex (CommRing.toRing.{0} Complex Complex.commRing)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) x) (Polynomial.Chebyshev.T.{0} Complex Complex.commRing n))
but is expected to have type
  forall (x : Real) (n : Nat), Eq.{1} Complex (Complex.ofReal' (Polynomial.eval.{0} Real (CommSemiring.toSemiring.{0} Real (CommRing.toCommSemiring.{0} Real Real.commRing)) x (Polynomial.Chebyshev.T.{0} Real Real.commRing n))) (Polynomial.eval.{0} Complex (CommSemiring.toSemiring.{0} Complex (CommRing.toCommSemiring.{0} Complex Complex.commRing)) (Complex.ofReal' x) (Polynomial.Chebyshev.T.{0} Complex Complex.commRing n))
Case conversion may be inaccurate. Consider using '#align polynomial.chebyshev.complex_of_real_eval_T Polynomial.Chebyshev.complex_of_real_eval_Tₓ'. -/
@[simp, norm_cast]
theorem complex_of_real_eval_T : ∀ x n, ((T ℝ n).eval x : ℂ) = (T ℂ n).eval x :=
  @algebraMap_eval_T ℝ ℂ _ _ _
#align polynomial.chebyshev.complex_of_real_eval_T Polynomial.Chebyshev.complex_of_real_eval_T

/- warning: polynomial.chebyshev.complex_of_real_eval_U -> Polynomial.Chebyshev.complex_of_real_eval_U is a dubious translation:
lean 3 declaration is
  forall (x : Real) (n : Nat), Eq.{1} Complex ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Polynomial.eval.{0} Real (Ring.toSemiring.{0} Real (CommRing.toRing.{0} Real Real.commRing)) x (Polynomial.Chebyshev.U.{0} Real Real.commRing n))) (Polynomial.eval.{0} Complex (Ring.toSemiring.{0} Complex (CommRing.toRing.{0} Complex Complex.commRing)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) x) (Polynomial.Chebyshev.U.{0} Complex Complex.commRing n))
but is expected to have type
  forall (x : Real) (n : Nat), Eq.{1} Complex (Complex.ofReal' (Polynomial.eval.{0} Real (CommSemiring.toSemiring.{0} Real (CommRing.toCommSemiring.{0} Real Real.commRing)) x (Polynomial.Chebyshev.U.{0} Real Real.commRing n))) (Polynomial.eval.{0} Complex (CommSemiring.toSemiring.{0} Complex (CommRing.toCommSemiring.{0} Complex Complex.commRing)) (Complex.ofReal' x) (Polynomial.Chebyshev.U.{0} Complex Complex.commRing n))
Case conversion may be inaccurate. Consider using '#align polynomial.chebyshev.complex_of_real_eval_U Polynomial.Chebyshev.complex_of_real_eval_Uₓ'. -/
@[simp, norm_cast]
theorem complex_of_real_eval_U : ∀ x n, ((U ℝ n).eval x : ℂ) = (U ℂ n).eval x :=
  @algebraMap_eval_U ℝ ℂ _ _ _
#align polynomial.chebyshev.complex_of_real_eval_U Polynomial.Chebyshev.complex_of_real_eval_U

/-! ### Complex versions -/


section Complex

open Complex

variable (θ : ℂ)

#print Polynomial.Chebyshev.T_complex_cos /-
/-- The `n`-th Chebyshev polynomial of the first kind evaluates on `cos θ` to the
value `cos (n * θ)`. -/
@[simp]
theorem T_complex_cos : ∀ n, (T ℂ n).eval (cos θ) = cos (n * θ)
  | 0 => by simp only [T_zero, eval_one, Nat.cast_zero, MulZeroClass.zero_mul, cos_zero]
  | 1 => by simp only [eval_X, one_mul, T_one, Nat.cast_one]
  | n + 2 =>
    by
    simp only [eval_X, eval_one, T_add_two, eval_sub, eval_bit0, Nat.cast_succ, eval_mul]
    rw [T_complex_cos (n + 1), T_complex_cos n]
    have aux : sin θ * sin θ = 1 - cos θ * cos θ :=
      by
      rw [← sin_sq_add_cos_sq θ]
      ring
    simp only [Nat.cast_add, Nat.cast_one, add_mul, cos_add, one_mul, sin_add, mul_assoc, aux]
    ring
#align polynomial.chebyshev.T_complex_cos Polynomial.Chebyshev.T_complex_cos
-/

/- warning: polynomial.chebyshev.U_complex_cos -> Polynomial.Chebyshev.U_complex_cos is a dubious translation:
lean 3 declaration is
  forall (θ : Complex) (n : Nat), Eq.{1} Complex (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Polynomial.eval.{0} Complex (Ring.toSemiring.{0} Complex (CommRing.toRing.{0} Complex Complex.commRing)) (Complex.cos θ) (Polynomial.Chebyshev.U.{0} Complex Complex.commRing n)) (Complex.sin θ)) (Complex.sin (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Complex (HasLiftT.mk.{1, 1} Nat Complex (CoeTCₓ.coe.{1, 1} Nat Complex (Nat.castCoe.{0} Complex (AddMonoidWithOne.toNatCast.{0} Complex (AddGroupWithOne.toAddMonoidWithOne.{0} Complex Complex.addGroupWithOne))))) n) (OfNat.ofNat.{0} Complex 1 (OfNat.mk.{0} Complex 1 (One.one.{0} Complex Complex.hasOne)))) θ))
but is expected to have type
  forall (θ : Complex) (n : Nat), Eq.{1} Complex (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Polynomial.eval.{0} Complex (CommSemiring.toSemiring.{0} Complex (CommRing.toCommSemiring.{0} Complex Complex.commRing)) (Complex.cos θ) (Polynomial.Chebyshev.U.{0} Complex Complex.commRing n)) (Complex.sin θ)) (Complex.sin (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (Nat.cast.{0} Complex (Semiring.toNatCast.{0} Complex Complex.instSemiringComplex) n) (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex))) θ))
Case conversion may be inaccurate. Consider using '#align polynomial.chebyshev.U_complex_cos Polynomial.Chebyshev.U_complex_cosₓ'. -/
/-- The `n`-th Chebyshev polynomial of the second kind evaluates on `cos θ` to the
value `sin ((n + 1) * θ) / sin θ`. -/
@[simp]
theorem U_complex_cos (n : ℕ) : (U ℂ n).eval (cos θ) * sin θ = sin ((n + 1) * θ) :=
  by
  induction' n with d hd
  · simp only [U_zero, Nat.cast_zero, eval_one, mul_one, zero_add, one_mul]
  · rw [U_eq_X_mul_U_add_T]
    simp only [eval_add, eval_mul, eval_X, T_complex_cos, add_mul, mul_assoc, hd, one_mul]
    conv_rhs => rw [sin_add, mul_comm]
    push_cast
    simp only [add_mul, one_mul]
#align polynomial.chebyshev.U_complex_cos Polynomial.Chebyshev.U_complex_cos

end Complex

-- ### Real versions
section Real

open Real

variable (θ : ℝ) (n : ℕ)

#print Polynomial.Chebyshev.T_real_cos /-
/-- The `n`-th Chebyshev polynomial of the first kind evaluates on `cos θ` to the
value `cos (n * θ)`. -/
@[simp]
theorem T_real_cos : (T ℝ n).eval (cos θ) = cos (n * θ) := by exact_mod_cast T_complex_cos θ n
#align polynomial.chebyshev.T_real_cos Polynomial.Chebyshev.T_real_cos
-/

/- warning: polynomial.chebyshev.U_real_cos -> Polynomial.Chebyshev.U_real_cos is a dubious translation:
lean 3 declaration is
  forall (θ : Real) (n : Nat), Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Polynomial.eval.{0} Real (Ring.toSemiring.{0} Real (CommRing.toRing.{0} Real Real.commRing)) (Real.cos θ) (Polynomial.Chebyshev.U.{0} Real Real.commRing n)) (Real.sin θ)) (Real.sin (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) θ))
but is expected to have type
  forall (θ : Real) (n : Nat), Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Polynomial.eval.{0} Real (CommSemiring.toSemiring.{0} Real (CommRing.toCommSemiring.{0} Real Real.commRing)) (Real.cos θ) (Polynomial.Chebyshev.U.{0} Real Real.commRing n)) (Real.sin θ)) (Real.sin (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Nat.cast.{0} Real Real.natCast n) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) θ))
Case conversion may be inaccurate. Consider using '#align polynomial.chebyshev.U_real_cos Polynomial.Chebyshev.U_real_cosₓ'. -/
/-- The `n`-th Chebyshev polynomial of the second kind evaluates on `cos θ` to the
value `sin ((n + 1) * θ) / sin θ`. -/
@[simp]
theorem U_real_cos : (U ℝ n).eval (cos θ) * sin θ = sin ((n + 1) * θ) := by
  exact_mod_cast U_complex_cos θ n
#align polynomial.chebyshev.U_real_cos Polynomial.Chebyshev.U_real_cos

end Real

end Polynomial.Chebyshev

