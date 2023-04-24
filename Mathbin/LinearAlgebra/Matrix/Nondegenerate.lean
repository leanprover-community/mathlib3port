/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module linear_algebra.matrix.nondegenerate
! leanprover-community/mathlib commit 4f81bc21e32048db7344b7867946e992cf5f68cc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Matrix.Basic
import Mathbin.LinearAlgebra.Matrix.Determinant
import Mathbin.LinearAlgebra.Matrix.Adjugate

/-!
# Matrices associated with non-degenerate bilinear forms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `matrix.nondegenerate A`: the proposition that when interpreted as a bilinear form, the matrix `A`
  is nondegenerate.

-/


namespace Matrix

variable {m R A : Type _} [Fintype m] [CommRing R]

#print Matrix.Nondegenerate /-
/-- A matrix `M` is nondegenerate if for all `v ≠ 0`, there is a `w ≠ 0` with `w ⬝ M ⬝ v ≠ 0`. -/
def Nondegenerate (M : Matrix m m R) :=
  ∀ v, (∀ w, Matrix.dotProduct v (mulVec M w) = 0) → v = 0
#align matrix.nondegenerate Matrix.Nondegenerate
-/

/- warning: matrix.nondegenerate.eq_zero_of_ortho -> Matrix.Nondegenerate.eq_zero_of_ortho is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {R : Type.{u2}} [_inst_1 : Fintype.{u1} m] [_inst_2 : CommRing.{u2} R] {M : Matrix.{u1, u1, u2} m m R}, (Matrix.Nondegenerate.{u1, u2} m R _inst_1 _inst_2 M) -> (forall {v : m -> R}, (forall (w : m -> R), Eq.{succ u2} R (Matrix.dotProduct.{u2, u1} m R _inst_1 (Distrib.toHasMul.{u2} R (Ring.toDistrib.{u2} R (CommRing.toRing.{u2} R _inst_2))) (AddCommGroup.toAddCommMonoid.{u2} R (NonUnitalNonAssocRing.toAddCommGroup.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_2))))) v (Matrix.mulVec.{u2, u1, u1} m m R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_2)))) _inst_1 M w)) (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_2)))))))))) -> (Eq.{max (succ u1) (succ u2)} (m -> R) v (OfNat.ofNat.{max u1 u2} (m -> R) 0 (OfNat.mk.{max u1 u2} (m -> R) 0 (Zero.zero.{max u1 u2} (m -> R) (Pi.instZero.{u1, u2} m (fun (ᾰ : m) => R) (fun (i : m) => MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_2))))))))))))
but is expected to have type
  forall {m : Type.{u2}} {R : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_2 : CommRing.{u1} R] {M : Matrix.{u2, u2, u1} m m R}, (Matrix.Nondegenerate.{u2, u1} m R _inst_1 _inst_2 M) -> (forall {v : m -> R}, (forall (w : m -> R), Eq.{succ u1} R (Matrix.dotProduct.{u1, u2} m R _inst_1 (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_2)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_2))))) v (Matrix.mulVec.{u1, u2, u2} m m R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_2)))) _inst_1 M w)) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R _inst_2)))))) -> (Eq.{max (succ u2) (succ u1)} (m -> R) v (OfNat.ofNat.{max u2 u1} (m -> R) 0 (Zero.toOfNat0.{max u2 u1} (m -> R) (Pi.instZero.{u2, u1} m (fun (a._@.Mathlib.LinearAlgebra.Matrix.Nondegenerate._hyg.79 : m) => R) (fun (i : m) => CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R _inst_2))))))))
Case conversion may be inaccurate. Consider using '#align matrix.nondegenerate.eq_zero_of_ortho Matrix.Nondegenerate.eq_zero_of_orthoₓ'. -/
/-- If `M` is nondegenerate and `w ⬝ M ⬝ v = 0` for all `w`, then `v = 0`. -/
theorem Nondegenerate.eq_zero_of_ortho {M : Matrix m m R} (hM : Nondegenerate M) {v : m → R}
    (hv : ∀ w, Matrix.dotProduct v (mulVec M w) = 0) : v = 0 :=
  hM v hv
#align matrix.nondegenerate.eq_zero_of_ortho Matrix.Nondegenerate.eq_zero_of_ortho

/- warning: matrix.nondegenerate.exists_not_ortho_of_ne_zero -> Matrix.Nondegenerate.exists_not_ortho_of_ne_zero is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {R : Type.{u2}} [_inst_1 : Fintype.{u1} m] [_inst_2 : CommRing.{u2} R] {M : Matrix.{u1, u1, u2} m m R}, (Matrix.Nondegenerate.{u1, u2} m R _inst_1 _inst_2 M) -> (forall {v : m -> R}, (Ne.{max (succ u1) (succ u2)} (m -> R) v (OfNat.ofNat.{max u1 u2} (m -> R) 0 (OfNat.mk.{max u1 u2} (m -> R) 0 (Zero.zero.{max u1 u2} (m -> R) (Pi.instZero.{u1, u2} m (fun (ᾰ : m) => R) (fun (i : m) => MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_2))))))))))) -> (Exists.{max (succ u1) (succ u2)} (m -> R) (fun (w : m -> R) => Ne.{succ u2} R (Matrix.dotProduct.{u2, u1} m R _inst_1 (Distrib.toHasMul.{u2} R (Ring.toDistrib.{u2} R (CommRing.toRing.{u2} R _inst_2))) (AddCommGroup.toAddCommMonoid.{u2} R (NonUnitalNonAssocRing.toAddCommGroup.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_2))))) v (Matrix.mulVec.{u2, u1, u1} m m R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_2)))) _inst_1 M w)) (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_2))))))))))))
but is expected to have type
  forall {m : Type.{u2}} {R : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_2 : CommRing.{u1} R] {M : Matrix.{u2, u2, u1} m m R}, (Matrix.Nondegenerate.{u2, u1} m R _inst_1 _inst_2 M) -> (forall {v : m -> R}, (Ne.{max (succ u2) (succ u1)} (m -> R) v (OfNat.ofNat.{max u2 u1} (m -> R) 0 (Zero.toOfNat0.{max u2 u1} (m -> R) (Pi.instZero.{u2, u1} m (fun (a._@.Mathlib.LinearAlgebra.Matrix.Nondegenerate._hyg.125 : m) => R) (fun (i : m) => CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R _inst_2))))))) -> (Exists.{max (succ u2) (succ u1)} (m -> R) (fun (w : m -> R) => Ne.{succ u1} R (Matrix.dotProduct.{u1, u2} m R _inst_1 (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_2)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_2))))) v (Matrix.mulVec.{u1, u2, u2} m m R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_2)))) _inst_1 M w)) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R _inst_2))))))))
Case conversion may be inaccurate. Consider using '#align matrix.nondegenerate.exists_not_ortho_of_ne_zero Matrix.Nondegenerate.exists_not_ortho_of_ne_zeroₓ'. -/
/-- If `M` is nondegenerate and `v ≠ 0`, then there is some `w` such that `w ⬝ M ⬝ v ≠ 0`. -/
theorem Nondegenerate.exists_not_ortho_of_ne_zero {M : Matrix m m R} (hM : Nondegenerate M)
    {v : m → R} (hv : v ≠ 0) : ∃ w, Matrix.dotProduct v (mulVec M w) ≠ 0 :=
  not_forall.mp (mt hM.eq_zero_of_ortho hv)
#align matrix.nondegenerate.exists_not_ortho_of_ne_zero Matrix.Nondegenerate.exists_not_ortho_of_ne_zero

variable [CommRing A] [IsDomain A]

/- warning: matrix.nondegenerate_of_det_ne_zero -> Matrix.nondegenerate_of_det_ne_zero is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {A : Type.{u2}} [_inst_1 : Fintype.{u1} m] [_inst_3 : CommRing.{u2} A] [_inst_4 : IsDomain.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_3))] [_inst_5 : DecidableEq.{succ u1} m] {M : Matrix.{u1, u1, u2} m m A}, (Ne.{succ u2} A (Matrix.det.{u2, u1} m (fun (a : m) (b : m) => _inst_5 a b) _inst_1 A _inst_3 M) (OfNat.ofNat.{u2} A 0 (OfNat.mk.{u2} A 0 (Zero.zero.{u2} A (MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_3)))))))))) -> (Matrix.Nondegenerate.{u1, u2} m A _inst_1 _inst_3 M)
but is expected to have type
  forall {m : Type.{u2}} {A : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_3 : CommRing.{u1} A] [_inst_4 : IsDomain.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_3))] [_inst_5 : DecidableEq.{succ u2} m] {M : Matrix.{u2, u2, u1} m m A}, (Ne.{succ u1} A (Matrix.det.{u1, u2} m (fun (a : m) (b : m) => _inst_5 a b) _inst_1 A _inst_3 M) (OfNat.ofNat.{u1} A 0 (Zero.toOfNat0.{u1} A (CommMonoidWithZero.toZero.{u1} A (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} A (IsDomain.toCancelCommMonoidWithZero.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3) _inst_4)))))) -> (Matrix.Nondegenerate.{u2, u1} m A _inst_1 _inst_3 M)
Case conversion may be inaccurate. Consider using '#align matrix.nondegenerate_of_det_ne_zero Matrix.nondegenerate_of_det_ne_zeroₓ'. -/
/-- If `M` has a nonzero determinant, then `M` as a bilinear form on `n → A` is nondegenerate.

See also `bilin_form.nondegenerate_of_det_ne_zero'` and `bilin_form.nondegenerate_of_det_ne_zero`.
-/
theorem nondegenerate_of_det_ne_zero [DecidableEq m] {M : Matrix m m A} (hM : M.det ≠ 0) :
    Nondegenerate M := by
  intro v hv
  ext i
  specialize hv (M.cramer (Pi.single i 1))
  refine' (mul_eq_zero.mp _).resolve_right hM
  convert hv
  simp only [mul_vec_cramer M (Pi.single i 1), dot_product, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i, Pi.single_eq_same, mul_one]
  · intro j _ hj
    simp [hj]
  · intros
    have := Finset.mem_univ i
    contradiction
#align matrix.nondegenerate_of_det_ne_zero Matrix.nondegenerate_of_det_ne_zero

/- warning: matrix.eq_zero_of_vec_mul_eq_zero -> Matrix.eq_zero_of_vecMul_eq_zero is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {A : Type.{u2}} [_inst_1 : Fintype.{u1} m] [_inst_3 : CommRing.{u2} A] [_inst_4 : IsDomain.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_3))] [_inst_5 : DecidableEq.{succ u1} m] {M : Matrix.{u1, u1, u2} m m A}, (Ne.{succ u2} A (Matrix.det.{u2, u1} m (fun (a : m) (b : m) => _inst_5 a b) _inst_1 A _inst_3 M) (OfNat.ofNat.{u2} A 0 (OfNat.mk.{u2} A 0 (Zero.zero.{u2} A (MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_3)))))))))) -> (forall {v : m -> A}, (Eq.{max (succ u1) (succ u2)} (m -> A) (Matrix.vecMul.{u2, u1, u1} m m A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_3)))) _inst_1 v M) (OfNat.ofNat.{max u1 u2} (m -> A) 0 (OfNat.mk.{max u1 u2} (m -> A) 0 (Zero.zero.{max u1 u2} (m -> A) (Pi.instZero.{u1, u2} m (fun (ᾰ : m) => A) (fun (i : m) => MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_3))))))))))) -> (Eq.{max (succ u1) (succ u2)} (m -> A) v (OfNat.ofNat.{max u1 u2} (m -> A) 0 (OfNat.mk.{max u1 u2} (m -> A) 0 (Zero.zero.{max u1 u2} (m -> A) (Pi.instZero.{u1, u2} m (fun (ᾰ : m) => A) (fun (i : m) => MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_3))))))))))))
but is expected to have type
  forall {m : Type.{u2}} {A : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_3 : CommRing.{u1} A] [_inst_4 : IsDomain.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_3))] [_inst_5 : DecidableEq.{succ u2} m] {M : Matrix.{u2, u2, u1} m m A}, (Ne.{succ u1} A (Matrix.det.{u1, u2} m (fun (a : m) (b : m) => _inst_5 a b) _inst_1 A _inst_3 M) (OfNat.ofNat.{u1} A 0 (Zero.toOfNat0.{u1} A (CommMonoidWithZero.toZero.{u1} A (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} A (IsDomain.toCancelCommMonoidWithZero.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3) _inst_4)))))) -> (forall {v : m -> A}, (Eq.{max (succ u2) (succ u1)} (m -> A) (Matrix.vecMul.{u1, u2, u2} m m A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} A (NonAssocRing.toNonUnitalNonAssocRing.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_3)))) _inst_1 v M) (OfNat.ofNat.{max u2 u1} (m -> A) 0 (Zero.toOfNat0.{max u2 u1} (m -> A) (Pi.instZero.{u2, u1} m (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.18134 : m) => A) (fun (i : m) => CommMonoidWithZero.toZero.{u1} A (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} A (IsDomain.toCancelCommMonoidWithZero.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3) _inst_4))))))) -> (Eq.{max (succ u2) (succ u1)} (m -> A) v (OfNat.ofNat.{max u2 u1} (m -> A) 0 (Zero.toOfNat0.{max u2 u1} (m -> A) (Pi.instZero.{u2, u1} m (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.18134 : m) => A) (fun (i : m) => CommMonoidWithZero.toZero.{u1} A (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} A (IsDomain.toCancelCommMonoidWithZero.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3) _inst_4))))))))
Case conversion may be inaccurate. Consider using '#align matrix.eq_zero_of_vec_mul_eq_zero Matrix.eq_zero_of_vecMul_eq_zeroₓ'. -/
theorem eq_zero_of_vecMul_eq_zero [DecidableEq m] {M : Matrix m m A} (hM : M.det ≠ 0) {v : m → A}
    (hv : M.vecMul v = 0) : v = 0 :=
  (nondegenerate_of_det_ne_zero hM).eq_zero_of_ortho fun w => by
    rw [dot_product_mul_vec, hv, zero_dot_product]
#align matrix.eq_zero_of_vec_mul_eq_zero Matrix.eq_zero_of_vecMul_eq_zero

/- warning: matrix.eq_zero_of_mul_vec_eq_zero -> Matrix.eq_zero_of_mulVec_eq_zero is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {A : Type.{u2}} [_inst_1 : Fintype.{u1} m] [_inst_3 : CommRing.{u2} A] [_inst_4 : IsDomain.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_3))] [_inst_5 : DecidableEq.{succ u1} m] {M : Matrix.{u1, u1, u2} m m A}, (Ne.{succ u2} A (Matrix.det.{u2, u1} m (fun (a : m) (b : m) => _inst_5 a b) _inst_1 A _inst_3 M) (OfNat.ofNat.{u2} A 0 (OfNat.mk.{u2} A 0 (Zero.zero.{u2} A (MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_3)))))))))) -> (forall {v : m -> A}, (Eq.{max (succ u1) (succ u2)} (m -> A) (Matrix.mulVec.{u2, u1, u1} m m A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_3)))) _inst_1 M v) (OfNat.ofNat.{max u1 u2} (m -> A) 0 (OfNat.mk.{max u1 u2} (m -> A) 0 (Zero.zero.{max u1 u2} (m -> A) (Pi.instZero.{u1, u2} m (fun (ᾰ : m) => A) (fun (i : m) => MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_3))))))))))) -> (Eq.{max (succ u1) (succ u2)} (m -> A) v (OfNat.ofNat.{max u1 u2} (m -> A) 0 (OfNat.mk.{max u1 u2} (m -> A) 0 (Zero.zero.{max u1 u2} (m -> A) (Pi.instZero.{u1, u2} m (fun (ᾰ : m) => A) (fun (i : m) => MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_3))))))))))))
but is expected to have type
  forall {m : Type.{u2}} {A : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_3 : CommRing.{u1} A] [_inst_4 : IsDomain.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_3))] [_inst_5 : DecidableEq.{succ u2} m] {M : Matrix.{u2, u2, u1} m m A}, (Ne.{succ u1} A (Matrix.det.{u1, u2} m (fun (a : m) (b : m) => _inst_5 a b) _inst_1 A _inst_3 M) (OfNat.ofNat.{u1} A 0 (Zero.toOfNat0.{u1} A (CommMonoidWithZero.toZero.{u1} A (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} A (IsDomain.toCancelCommMonoidWithZero.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3) _inst_4)))))) -> (forall {v : m -> A}, (Eq.{max (succ u2) (succ u1)} (m -> A) (Matrix.mulVec.{u1, u2, u2} m m A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} A (NonAssocRing.toNonUnitalNonAssocRing.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_3)))) _inst_1 M v) (OfNat.ofNat.{max u2 u1} (m -> A) 0 (Zero.toOfNat0.{max u2 u1} (m -> A) (Pi.instZero.{u2, u1} m (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.18076 : m) => A) (fun (i : m) => CommMonoidWithZero.toZero.{u1} A (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} A (IsDomain.toCancelCommMonoidWithZero.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3) _inst_4))))))) -> (Eq.{max (succ u2) (succ u1)} (m -> A) v (OfNat.ofNat.{max u2 u1} (m -> A) 0 (Zero.toOfNat0.{max u2 u1} (m -> A) (Pi.instZero.{u2, u1} m (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.18076 : m) => A) (fun (i : m) => CommMonoidWithZero.toZero.{u1} A (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} A (IsDomain.toCancelCommMonoidWithZero.{u1} A (CommRing.toCommSemiring.{u1} A _inst_3) _inst_4))))))))
Case conversion may be inaccurate. Consider using '#align matrix.eq_zero_of_mul_vec_eq_zero Matrix.eq_zero_of_mulVec_eq_zeroₓ'. -/
theorem eq_zero_of_mulVec_eq_zero [DecidableEq m] {M : Matrix m m A} (hM : M.det ≠ 0) {v : m → A}
    (hv : M.mulVec v = 0) : v = 0 :=
  eq_zero_of_vecMul_eq_zero (by rwa [det_transpose]) ((vecMul_transpose M v).trans hv)
#align matrix.eq_zero_of_mul_vec_eq_zero Matrix.eq_zero_of_mulVec_eq_zero

end Matrix

