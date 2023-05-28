/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen

! This file was ported from Lean 3 source module linear_algebra.matrix.to_linear_equiv
! leanprover-community/mathlib commit a87d22575d946e1e156fc1edd1e1269600a8a282
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.FiniteDimensional
import Mathbin.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathbin.LinearAlgebra.Matrix.Nondegenerate
import Mathbin.LinearAlgebra.Matrix.NonsingularInverse
import Mathbin.LinearAlgebra.Matrix.ToLin
import Mathbin.RingTheory.Localization.FractionRing
import Mathbin.RingTheory.Localization.Integer

/-!
# Matrices and linear equivalences

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file gives the map `matrix.to_linear_equiv` from matrices with invertible determinant,
to linear equivs.

## Main definitions

 * `matrix.to_linear_equiv`: a matrix with an invertible determinant forms a linear equiv

## Main results

 * `matrix.exists_mul_vec_eq_zero_iff`: `M` maps some `v ≠ 0` to zero iff `det M = 0`

## Tags

matrix, linear_equiv, determinant, inverse

-/


namespace Matrix

open LinearMap

variable {R M : Type _} [CommRing R] [AddCommGroup M] [Module R M]

variable {n : Type _} [Fintype n]

section ToLinearEquiv'

variable [DecidableEq n]

/- warning: matrix.to_linear_equiv' -> Matrix.toLinearEquiv' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {n : Type.{u2}} [_inst_4 : Fintype.{u2} n] [_inst_5 : DecidableEq.{succ u2} n] (P : Matrix.{u2, u2, u1} n n R), (Invertible.{max u2 u1} (Matrix.{u2, u2, u1} n n R) (Matrix.hasMul.{u1, u2} n R _inst_4 (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (Matrix.hasOne.{u1, u2} n R (fun (a : n) (b : n) => _inst_5 a b) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) P) -> (LinearEquiv.{u1, u1, max u2 u1, max u2 u1} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (Matrix.toLinearEquiv'._proof_1.{u1} R _inst_1) (Matrix.toLinearEquiv'._proof_2.{u1} R _inst_1) (n -> R) (n -> R) (Pi.addCommMonoid.{u2, u1} n (fun (ᾰ : n) => R) (fun (i : n) => AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (Pi.addCommMonoid.{u2, u1} n (fun (ᾰ : n) => R) (fun (i : n) => AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (Pi.Function.module.{u2, u1, u1} n R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (Pi.Function.module.{u2, u1, u1} n R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {n : Type.{u2}} [_inst_4 : Fintype.{u2} n] [_inst_5 : DecidableEq.{succ u2} n] (P : Matrix.{u2, u2, u1} n n R), (Invertible.{max u1 u2} (Matrix.{u2, u2, u1} n n R) (Matrix.instMulMatrix.{u1, u2} n R _inst_4 (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (Matrix.one.{u1, u2} n R (fun (a : n) (b : n) => _inst_5 a b) (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toOne.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) P) -> (LinearEquiv.{u1, u1, max u1 u2, max u1 u2} R R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) (RingHomInvPair.ids.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (RingHomInvPair.ids.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (n -> R) (n -> R) (Pi.addCommMonoid.{u2, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (Pi.addCommMonoid.{u2, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (Pi.module.{u2, u1, u1} n (fun (a._@.Mathlib.LinearAlgebra.Matrix.ToLinearEquiv._hyg.100 : n) => R) R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (fun (i : n) => Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) (Pi.module.{u2, u1, u1} n (fun (a._@.Mathlib.LinearAlgebra.Matrix.ToLinearEquiv._hyg.100 : n) => R) R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (fun (i : n) => Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align matrix.to_linear_equiv' Matrix.toLinearEquiv'ₓ'. -/
/-- An invertible matrix yields a linear equivalence from the free module to itself.

See `matrix.to_linear_equiv` for the same map on arbitrary modules.
-/
def toLinearEquiv' (P : Matrix n n R) (h : Invertible P) : (n → R) ≃ₗ[R] n → R :=
  GeneralLinearGroup.generalLinearEquiv _ _ <|
    Matrix.GeneralLinearGroup.toLinear <| unitOfInvertible P
#align matrix.to_linear_equiv' Matrix.toLinearEquiv'

/- warning: matrix.to_linear_equiv'_apply -> Matrix.toLinearEquiv'_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_linear_equiv'_apply Matrix.toLinearEquiv'_applyₓ'. -/
@[simp]
theorem toLinearEquiv'_apply (P : Matrix n n R) (h : Invertible P) :
    (↑(P.toLinearEquiv' h) : Module.End R (n → R)) = P.toLin' :=
  rfl
#align matrix.to_linear_equiv'_apply Matrix.toLinearEquiv'_apply

/- warning: matrix.to_linear_equiv'_symm_apply -> Matrix.toLinearEquiv'_symm_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_linear_equiv'_symm_apply Matrix.toLinearEquiv'_symm_applyₓ'. -/
@[simp]
theorem toLinearEquiv'_symm_apply (P : Matrix n n R) (h : Invertible P) :
    (↑(P.toLinearEquiv' h).symm : Module.End R (n → R)) = (⅟ P).toLin' :=
  rfl
#align matrix.to_linear_equiv'_symm_apply Matrix.toLinearEquiv'_symm_apply

end ToLinearEquiv'

section ToLinearEquiv

variable (b : Basis n R M)

include b

/- warning: matrix.to_linear_equiv -> Matrix.toLinearEquiv is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {n : Type.{u3}} [_inst_4 : Fintype.{u3} n], (Basis.{u3, u1, u2} n R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) -> (forall [_inst_5 : DecidableEq.{succ u3} n] (A : Matrix.{u3, u3, u1} n n R), (IsUnit.{u1} R (Ring.toMonoid.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Matrix.det.{u1, u3} n (fun (a : n) (b : n) => _inst_5 a b) _inst_4 R _inst_1 A)) -> (LinearEquiv.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (Matrix.toLinearEquiv._proof_1.{u1} R _inst_1) (Matrix.toLinearEquiv._proof_2.{u1} R _inst_1) M M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3))
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {n : Type.{u3}} [_inst_4 : Fintype.{u3} n], (Basis.{u3, u1, u2} n R M (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) -> (forall [_inst_5 : DecidableEq.{succ u3} n] (A : Matrix.{u3, u3, u1} n n R), (IsUnit.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) (Matrix.det.{u1, u3} n (fun (a : n) (b : n) => _inst_5 a b) _inst_4 R _inst_1 A)) -> (LinearEquiv.{u1, u1, u2, u2} R R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) (RingHomInvPair.ids.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (RingHomInvPair.ids.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3))
Case conversion may be inaccurate. Consider using '#align matrix.to_linear_equiv Matrix.toLinearEquivₓ'. -/
/-- Given `hA : is_unit A.det` and `b : basis R b`, `A.to_linear_equiv b hA` is
the `linear_equiv` arising from `to_lin b b A`.

See `matrix.to_linear_equiv'` for this result on `n → R`.
-/
@[simps apply]
noncomputable def toLinearEquiv [DecidableEq n] (A : Matrix n n R) (hA : IsUnit A.det) :
    M ≃ₗ[R] M := by
  refine'
        { to_lin b b A with
          toFun := to_lin b b A
          invFun := to_lin b b A⁻¹
          left_inv := fun x => _
          right_inv := fun x => _ } <;>
      rw [← LinearMap.comp_apply] <;>
    simp only [← Matrix.toLin_mul b b b, Matrix.nonsing_inv_mul _ hA, Matrix.mul_nonsing_inv _ hA,
      to_lin_one, LinearMap.id_apply]
#align matrix.to_linear_equiv Matrix.toLinearEquiv

/- warning: matrix.ker_to_lin_eq_bot -> Matrix.ker_toLin_eq_bot is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.ker_to_lin_eq_bot Matrix.ker_toLin_eq_botₓ'. -/
theorem ker_toLin_eq_bot [DecidableEq n] (A : Matrix n n R) (hA : IsUnit A.det) :
    (toLin b b A).ker = ⊥ :=
  ker_eq_bot.mpr (toLinearEquiv b A hA).Injective
#align matrix.ker_to_lin_eq_bot Matrix.ker_toLin_eq_bot

/- warning: matrix.range_to_lin_eq_top -> Matrix.range_toLin_eq_top is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.range_to_lin_eq_top Matrix.range_toLin_eq_topₓ'. -/
theorem range_toLin_eq_top [DecidableEq n] (A : Matrix n n R) (hA : IsUnit A.det) :
    (toLin b b A).range = ⊤ :=
  range_eq_top.mpr (toLinearEquiv b A hA).Surjective
#align matrix.range_to_lin_eq_top Matrix.range_toLin_eq_top

end ToLinearEquiv

section Nondegenerate

open Matrix

/- warning: matrix.exists_mul_vec_eq_zero_iff_aux -> Matrix.exists_mulVec_eq_zero_iff_aux is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} [_inst_4 : Fintype.{u1} n] {K : Type.{u2}} [_inst_5 : DecidableEq.{succ u1} n] [_inst_6 : Field.{u2} K] {M : Matrix.{u1, u1, u2} n n K}, Iff (Exists.{succ (max u1 u2)} (n -> K) (fun (v : n -> K) => Exists.{0} (Ne.{succ (max u1 u2)} (n -> K) v (OfNat.ofNat.{max u1 u2} (n -> K) 0 (OfNat.mk.{max u1 u2} (n -> K) 0 (Zero.zero.{max u1 u2} (n -> K) (Pi.instZero.{u1, u2} n (fun (ᾰ : n) => K) (fun (i : n) => MulZeroClass.toHasZero.{u2} K (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} K (NonAssocRing.toNonUnitalNonAssocRing.{u2} K (Ring.toNonAssocRing.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_6)))))))))))) (fun (H : Ne.{succ (max u1 u2)} (n -> K) v (OfNat.ofNat.{max u1 u2} (n -> K) 0 (OfNat.mk.{max u1 u2} (n -> K) 0 (Zero.zero.{max u1 u2} (n -> K) (Pi.instZero.{u1, u2} n (fun (ᾰ : n) => K) (fun (i : n) => MulZeroClass.toHasZero.{u2} K (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} K (NonAssocRing.toNonUnitalNonAssocRing.{u2} K (Ring.toNonAssocRing.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_6)))))))))))) => Eq.{max (succ u1) (succ u2)} (n -> K) (Matrix.mulVec.{u2, u1, u1} n n K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} K (NonAssocRing.toNonUnitalNonAssocRing.{u2} K (Ring.toNonAssocRing.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_6))))) _inst_4 M v) (OfNat.ofNat.{max u1 u2} (n -> K) 0 (OfNat.mk.{max u1 u2} (n -> K) 0 (Zero.zero.{max u1 u2} (n -> K) (Pi.instZero.{u1, u2} n (fun (ᾰ : n) => K) (fun (i : n) => MulZeroClass.toHasZero.{u2} K (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} K (NonAssocRing.toNonUnitalNonAssocRing.{u2} K (Ring.toNonAssocRing.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_6)))))))))))))) (Eq.{succ u2} K (Matrix.det.{u2, u1} n (fun (a : n) (b : n) => _inst_5 a b) _inst_4 K (EuclideanDomain.toCommRing.{u2} K (Field.toEuclideanDomain.{u2} K _inst_6)) M) (OfNat.ofNat.{u2} K 0 (OfNat.mk.{u2} K 0 (Zero.zero.{u2} K (MulZeroClass.toHasZero.{u2} K (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} K (NonAssocRing.toNonUnitalNonAssocRing.{u2} K (Ring.toNonAssocRing.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_6)))))))))))
but is expected to have type
  forall {n : Type.{u1}} [_inst_4 : Fintype.{u1} n] {K : Type.{u2}} [_inst_5 : DecidableEq.{succ u1} n] [_inst_6 : Field.{u2} K] {M : Matrix.{u1, u1, u2} n n K}, Iff (Exists.{succ (max u1 u2)} (n -> K) (fun (v : n -> K) => Exists.{0} (Ne.{succ (max u1 u2)} (n -> K) v (OfNat.ofNat.{max u1 u2} (n -> K) 0 (Zero.toOfNat0.{max u1 u2} (n -> K) (Pi.instZero.{u1, u2} n (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.18074 : n) => K) (fun (i : n) => CommMonoidWithZero.toZero.{u2} K (CommGroupWithZero.toCommMonoidWithZero.{u2} K (Semifield.toCommGroupWithZero.{u2} K (Field.toSemifield.{u2} K _inst_6)))))))) (fun (H : Ne.{succ (max u1 u2)} (n -> K) v (OfNat.ofNat.{max u1 u2} (n -> K) 0 (Zero.toOfNat0.{max u1 u2} (n -> K) (Pi.instZero.{u1, u2} n (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.18074 : n) => K) (fun (i : n) => CommMonoidWithZero.toZero.{u2} K (CommGroupWithZero.toCommMonoidWithZero.{u2} K (Semifield.toCommGroupWithZero.{u2} K (Field.toSemifield.{u2} K _inst_6)))))))) => Eq.{max (succ u1) (succ u2)} (n -> K) (Matrix.mulVec.{u2, u1, u1} n n K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} K (NonAssocRing.toNonUnitalNonAssocRing.{u2} K (Ring.toNonAssocRing.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_6))))) _inst_4 M v) (OfNat.ofNat.{max u1 u2} (n -> K) 0 (Zero.toOfNat0.{max u1 u2} (n -> K) (Pi.instZero.{u1, u2} n (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.18074 : n) => K) (fun (i : n) => CommMonoidWithZero.toZero.{u2} K (CommGroupWithZero.toCommMonoidWithZero.{u2} K (Semifield.toCommGroupWithZero.{u2} K (Field.toSemifield.{u2} K _inst_6)))))))))) (Eq.{succ u2} K (Matrix.det.{u2, u1} n (fun (a : n) (b : n) => _inst_5 a b) _inst_4 K (EuclideanDomain.toCommRing.{u2} K (Field.toEuclideanDomain.{u2} K _inst_6)) M) (OfNat.ofNat.{u2} K 0 (Zero.toOfNat0.{u2} K (CommMonoidWithZero.toZero.{u2} K (CommGroupWithZero.toCommMonoidWithZero.{u2} K (Semifield.toCommGroupWithZero.{u2} K (Field.toSemifield.{u2} K _inst_6)))))))
Case conversion may be inaccurate. Consider using '#align matrix.exists_mul_vec_eq_zero_iff_aux Matrix.exists_mulVec_eq_zero_iff_auxₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (v «expr ≠ » 0) -/
/-- This holds for all integral domains (see `matrix.exists_mul_vec_eq_zero_iff`),
not just fields, but it's easier to prove it for the field of fractions first. -/
theorem exists_mulVec_eq_zero_iff_aux {K : Type _} [DecidableEq n] [Field K] {M : Matrix n n K} :
    (∃ (v : _)(_ : v ≠ 0), M.mulVec v = 0) ↔ M.det = 0 :=
  by
  constructor
  · rintro ⟨v, hv, mul_eq⟩
    contrapose! hv
    exact eq_zero_of_mul_vec_eq_zero hv mul_eq
  · contrapose!
    intro h
    have : Function.Injective M.to_lin' := by
      simpa only [← LinearMap.ker_eq_bot, ker_to_lin'_eq_bot_iff, not_imp_not] using h
    have :
      M ⬝
          LinearMap.toMatrix'
            ((LinearEquiv.ofInjectiveEndo M.to_lin' this).symm : (n → K) →ₗ[K] n → K) =
        1 :=
      by
      refine' matrix.to_lin'.injective (LinearMap.ext fun v => _)
      rw [Matrix.toLin'_mul, Matrix.toLin'_one, Matrix.toLin'_toMatrix', LinearMap.comp_apply]
      exact (LinearEquiv.ofInjectiveEndo M.to_lin' this).apply_symm_apply v
    exact Matrix.det_ne_zero_of_right_inverse this
#align matrix.exists_mul_vec_eq_zero_iff_aux Matrix.exists_mulVec_eq_zero_iff_aux

/- warning: matrix.exists_mul_vec_eq_zero_iff' -> Matrix.exists_mulVec_eq_zero_iff' is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} [_inst_4 : Fintype.{u1} n] {A : Type.{u2}} (K : Type.{u3}) [_inst_5 : DecidableEq.{succ u1} n] [_inst_6 : CommRing.{u2} A] [_inst_7 : Nontrivial.{u2} A] [_inst_8 : Field.{u3} K] [_inst_9 : Algebra.{u2, u3} A K (CommRing.toCommSemiring.{u2} A _inst_6) (Ring.toSemiring.{u3} K (DivisionRing.toRing.{u3} K (Field.toDivisionRing.{u3} K _inst_8)))] [_inst_10 : IsFractionRing.{u2, u3} A _inst_6 K (EuclideanDomain.toCommRing.{u3} K (Field.toEuclideanDomain.{u3} K _inst_8)) _inst_9] {M : Matrix.{u1, u1, u2} n n A}, Iff (Exists.{succ (max u1 u2)} (n -> A) (fun (v : n -> A) => Exists.{0} (Ne.{succ (max u1 u2)} (n -> A) v (OfNat.ofNat.{max u1 u2} (n -> A) 0 (OfNat.mk.{max u1 u2} (n -> A) 0 (Zero.zero.{max u1 u2} (n -> A) (Pi.instZero.{u1, u2} n (fun (ᾰ : n) => A) (fun (i : n) => MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_6))))))))))) (fun (H : Ne.{succ (max u1 u2)} (n -> A) v (OfNat.ofNat.{max u1 u2} (n -> A) 0 (OfNat.mk.{max u1 u2} (n -> A) 0 (Zero.zero.{max u1 u2} (n -> A) (Pi.instZero.{u1, u2} n (fun (ᾰ : n) => A) (fun (i : n) => MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_6))))))))))) => Eq.{max (succ u1) (succ u2)} (n -> A) (Matrix.mulVec.{u2, u1, u1} n n A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_6)))) _inst_4 M v) (OfNat.ofNat.{max u1 u2} (n -> A) 0 (OfNat.mk.{max u1 u2} (n -> A) 0 (Zero.zero.{max u1 u2} (n -> A) (Pi.instZero.{u1, u2} n (fun (ᾰ : n) => A) (fun (i : n) => MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_6))))))))))))) (Eq.{succ u2} A (Matrix.det.{u2, u1} n (fun (a : n) (b : n) => _inst_5 a b) _inst_4 A _inst_6 M) (OfNat.ofNat.{u2} A 0 (OfNat.mk.{u2} A 0 (Zero.zero.{u2} A (MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_6))))))))))
but is expected to have type
  forall {n : Type.{u1}} [_inst_4 : Fintype.{u1} n] {A : Type.{u3}} (K : Type.{u2}) [_inst_5 : DecidableEq.{succ u1} n] [_inst_6 : CommRing.{u3} A] [_inst_7 : Nontrivial.{u3} A] [_inst_8 : Field.{u2} K] [_inst_9 : Algebra.{u3, u2} A K (CommRing.toCommSemiring.{u3} A _inst_6) (DivisionSemiring.toSemiring.{u2} K (Semifield.toDivisionSemiring.{u2} K (Field.toSemifield.{u2} K _inst_8)))] [_inst_10 : IsFractionRing.{u3, u2} A _inst_6 K (EuclideanDomain.toCommRing.{u2} K (Field.toEuclideanDomain.{u2} K _inst_8)) _inst_9] {M : Matrix.{u1, u1, u3} n n A}, Iff (Exists.{succ (max u1 u3)} (n -> A) (fun (v : n -> A) => Exists.{0} (Ne.{succ (max u1 u3)} (n -> A) v (OfNat.ofNat.{max u1 u3} (n -> A) 0 (Zero.toOfNat0.{max u1 u3} (n -> A) (Pi.instZero.{u1, u3} n (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.18074 : n) => A) (fun (i : n) => CommMonoidWithZero.toZero.{u3} A (CommSemiring.toCommMonoidWithZero.{u3} A (CommRing.toCommSemiring.{u3} A _inst_6))))))) (fun (H : Ne.{succ (max u1 u3)} (n -> A) v (OfNat.ofNat.{max u1 u3} (n -> A) 0 (Zero.toOfNat0.{max u1 u3} (n -> A) (Pi.instZero.{u1, u3} n (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.18074 : n) => A) (fun (i : n) => CommMonoidWithZero.toZero.{u3} A (CommSemiring.toCommMonoidWithZero.{u3} A (CommRing.toCommSemiring.{u3} A _inst_6))))))) => Eq.{max (succ u1) (succ u3)} (n -> A) (Matrix.mulVec.{u3, u1, u1} n n A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_6)))) _inst_4 M v) (OfNat.ofNat.{max u1 u3} (n -> A) 0 (Zero.toOfNat0.{max u1 u3} (n -> A) (Pi.instZero.{u1, u3} n (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.18074 : n) => A) (fun (i : n) => CommMonoidWithZero.toZero.{u3} A (CommSemiring.toCommMonoidWithZero.{u3} A (CommRing.toCommSemiring.{u3} A _inst_6))))))))) (Eq.{succ u3} A (Matrix.det.{u3, u1} n (fun (a : n) (b : n) => _inst_5 a b) _inst_4 A _inst_6 M) (OfNat.ofNat.{u3} A 0 (Zero.toOfNat0.{u3} A (CommMonoidWithZero.toZero.{u3} A (CommSemiring.toCommMonoidWithZero.{u3} A (CommRing.toCommSemiring.{u3} A _inst_6))))))
Case conversion may be inaccurate. Consider using '#align matrix.exists_mul_vec_eq_zero_iff' Matrix.exists_mulVec_eq_zero_iff'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (v «expr ≠ » 0) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (v «expr ≠ » 0) -/
theorem exists_mulVec_eq_zero_iff' {A : Type _} (K : Type _) [DecidableEq n] [CommRing A]
    [Nontrivial A] [Field K] [Algebra A K] [IsFractionRing A K] {M : Matrix n n A} :
    (∃ (v : _)(_ : v ≠ 0), M.mulVec v = 0) ↔ M.det = 0 :=
  by
  have : (∃ (v : _)(_ : v ≠ 0), mul_vec ((algebraMap A K).mapMatrix M) v = 0) ↔ _ :=
    exists_mul_vec_eq_zero_iff_aux
  rw [← RingHom.map_det, IsFractionRing.to_map_eq_zero_iff] at this
  refine' Iff.trans _ this; constructor <;> rintro ⟨v, hv, mul_eq⟩
  · refine' ⟨fun i => algebraMap _ _ (v i), mt (fun h => funext fun i => _) hv, _⟩
    · exact is_fraction_ring.to_map_eq_zero_iff.mp (congr_fun h i)
    · ext i
      refine' (RingHom.map_mulVec _ _ _ i).symm.trans _
      rw [mul_eq, Pi.zero_apply, RingHom.map_zero, Pi.zero_apply]
  · letI := Classical.decEq K
    obtain ⟨⟨b, hb⟩, ba_eq⟩ :=
      IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A) (finset.univ.image v)
    choose f hf using ba_eq
    refine'
      ⟨fun i => f _ (finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩),
        mt (fun h => funext fun i => _) hv, _⟩
    · have := congr_arg (algebraMap A K) (congr_fun h i)
      rw [hf, Subtype.coe_mk, Pi.zero_apply, RingHom.map_zero, Algebra.smul_def, mul_eq_zero,
        IsFractionRing.to_map_eq_zero_iff] at this
      exact this.resolve_left (nonZeroDivisors.ne_zero hb)
    · ext i
      refine' IsFractionRing.injective A K _
      calc
        algebraMap A K (M.mul_vec (fun i : n => f (v i) _) i) =
            ((algebraMap A K).mapMatrix M).mulVec (algebraMap _ K b • v) i :=
          _
        _ = 0 := _
        _ = algebraMap A K 0 := (RingHom.map_zero _).symm
        
      ·
        simp_rw [RingHom.map_mulVec, mul_vec, dot_product, Function.comp_apply, hf, Subtype.coe_mk,
          RingHom.mapMatrix_apply, Pi.smul_apply, smul_eq_mul, Algebra.smul_def]
      · rw [mul_vec_smul, mul_eq, Pi.smul_apply, Pi.zero_apply, smul_zero]
#align matrix.exists_mul_vec_eq_zero_iff' Matrix.exists_mulVec_eq_zero_iff'

/- warning: matrix.exists_mul_vec_eq_zero_iff -> Matrix.exists_mulVec_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} [_inst_4 : Fintype.{u1} n] {A : Type.{u2}} [_inst_5 : DecidableEq.{succ u1} n] [_inst_6 : CommRing.{u2} A] [_inst_7 : IsDomain.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_6))] {M : Matrix.{u1, u1, u2} n n A}, Iff (Exists.{succ (max u1 u2)} (n -> A) (fun (v : n -> A) => Exists.{0} (Ne.{succ (max u1 u2)} (n -> A) v (OfNat.ofNat.{max u1 u2} (n -> A) 0 (OfNat.mk.{max u1 u2} (n -> A) 0 (Zero.zero.{max u1 u2} (n -> A) (Pi.instZero.{u1, u2} n (fun (ᾰ : n) => A) (fun (i : n) => MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_6))))))))))) (fun (H : Ne.{succ (max u1 u2)} (n -> A) v (OfNat.ofNat.{max u1 u2} (n -> A) 0 (OfNat.mk.{max u1 u2} (n -> A) 0 (Zero.zero.{max u1 u2} (n -> A) (Pi.instZero.{u1, u2} n (fun (ᾰ : n) => A) (fun (i : n) => MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_6))))))))))) => Eq.{max (succ u1) (succ u2)} (n -> A) (Matrix.mulVec.{u2, u1, u1} n n A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_6)))) _inst_4 M v) (OfNat.ofNat.{max u1 u2} (n -> A) 0 (OfNat.mk.{max u1 u2} (n -> A) 0 (Zero.zero.{max u1 u2} (n -> A) (Pi.instZero.{u1, u2} n (fun (ᾰ : n) => A) (fun (i : n) => MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_6))))))))))))) (Eq.{succ u2} A (Matrix.det.{u2, u1} n (fun (a : n) (b : n) => _inst_5 a b) _inst_4 A _inst_6 M) (OfNat.ofNat.{u2} A 0 (OfNat.mk.{u2} A 0 (Zero.zero.{u2} A (MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_6))))))))))
but is expected to have type
  forall {n : Type.{u1}} [_inst_4 : Fintype.{u1} n] {A : Type.{u2}} [_inst_5 : DecidableEq.{succ u1} n] [_inst_6 : CommRing.{u2} A] [_inst_7 : IsDomain.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_6))] {M : Matrix.{u1, u1, u2} n n A}, Iff (Exists.{succ (max u1 u2)} (n -> A) (fun (v : n -> A) => Exists.{0} (Ne.{succ (max u1 u2)} (n -> A) v (OfNat.ofNat.{max u1 u2} (n -> A) 0 (Zero.toOfNat0.{max u1 u2} (n -> A) (Pi.instZero.{u1, u2} n (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.18074 : n) => A) (fun (i : n) => CommMonoidWithZero.toZero.{u2} A (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} A (IsDomain.toCancelCommMonoidWithZero.{u2} A (CommRing.toCommSemiring.{u2} A _inst_6) _inst_7))))))) (fun (H : Ne.{succ (max u1 u2)} (n -> A) v (OfNat.ofNat.{max u1 u2} (n -> A) 0 (Zero.toOfNat0.{max u1 u2} (n -> A) (Pi.instZero.{u1, u2} n (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.18074 : n) => A) (fun (i : n) => CommMonoidWithZero.toZero.{u2} A (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} A (IsDomain.toCancelCommMonoidWithZero.{u2} A (CommRing.toCommSemiring.{u2} A _inst_6) _inst_7))))))) => Eq.{max (succ u1) (succ u2)} (n -> A) (Matrix.mulVec.{u2, u1, u1} n n A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_6)))) _inst_4 M v) (OfNat.ofNat.{max u1 u2} (n -> A) 0 (Zero.toOfNat0.{max u1 u2} (n -> A) (Pi.instZero.{u1, u2} n (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.18074 : n) => A) (fun (i : n) => CommMonoidWithZero.toZero.{u2} A (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} A (IsDomain.toCancelCommMonoidWithZero.{u2} A (CommRing.toCommSemiring.{u2} A _inst_6) _inst_7))))))))) (Eq.{succ u2} A (Matrix.det.{u2, u1} n (fun (a : n) (b : n) => _inst_5 a b) _inst_4 A _inst_6 M) (OfNat.ofNat.{u2} A 0 (Zero.toOfNat0.{u2} A (CommMonoidWithZero.toZero.{u2} A (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} A (IsDomain.toCancelCommMonoidWithZero.{u2} A (CommRing.toCommSemiring.{u2} A _inst_6) _inst_7))))))
Case conversion may be inaccurate. Consider using '#align matrix.exists_mul_vec_eq_zero_iff Matrix.exists_mulVec_eq_zero_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (v «expr ≠ » 0) -/
theorem exists_mulVec_eq_zero_iff {A : Type _} [DecidableEq n] [CommRing A] [IsDomain A]
    {M : Matrix n n A} : (∃ (v : _)(_ : v ≠ 0), M.mulVec v = 0) ↔ M.det = 0 :=
  exists_mulVec_eq_zero_iff' (FractionRing A)
#align matrix.exists_mul_vec_eq_zero_iff Matrix.exists_mulVec_eq_zero_iff

/- warning: matrix.exists_vec_mul_eq_zero_iff -> Matrix.exists_vecMul_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} [_inst_4 : Fintype.{u1} n] {A : Type.{u2}} [_inst_5 : DecidableEq.{succ u1} n] [_inst_6 : CommRing.{u2} A] [_inst_7 : IsDomain.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_6))] {M : Matrix.{u1, u1, u2} n n A}, Iff (Exists.{succ (max u1 u2)} (n -> A) (fun (v : n -> A) => Exists.{0} (Ne.{succ (max u1 u2)} (n -> A) v (OfNat.ofNat.{max u1 u2} (n -> A) 0 (OfNat.mk.{max u1 u2} (n -> A) 0 (Zero.zero.{max u1 u2} (n -> A) (Pi.instZero.{u1, u2} n (fun (ᾰ : n) => A) (fun (i : n) => MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_6))))))))))) (fun (H : Ne.{succ (max u1 u2)} (n -> A) v (OfNat.ofNat.{max u1 u2} (n -> A) 0 (OfNat.mk.{max u1 u2} (n -> A) 0 (Zero.zero.{max u1 u2} (n -> A) (Pi.instZero.{u1, u2} n (fun (ᾰ : n) => A) (fun (i : n) => MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_6))))))))))) => Eq.{max (succ u1) (succ u2)} (n -> A) (Matrix.vecMul.{u2, u1, u1} n n A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_6)))) _inst_4 v M) (OfNat.ofNat.{max u1 u2} (n -> A) 0 (OfNat.mk.{max u1 u2} (n -> A) 0 (Zero.zero.{max u1 u2} (n -> A) (Pi.instZero.{u1, u2} n (fun (ᾰ : n) => A) (fun (i : n) => MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_6))))))))))))) (Eq.{succ u2} A (Matrix.det.{u2, u1} n (fun (a : n) (b : n) => _inst_5 a b) _inst_4 A _inst_6 M) (OfNat.ofNat.{u2} A 0 (OfNat.mk.{u2} A 0 (Zero.zero.{u2} A (MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_6))))))))))
but is expected to have type
  forall {n : Type.{u1}} [_inst_4 : Fintype.{u1} n] {A : Type.{u2}} [_inst_5 : DecidableEq.{succ u1} n] [_inst_6 : CommRing.{u2} A] [_inst_7 : IsDomain.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_6))] {M : Matrix.{u1, u1, u2} n n A}, Iff (Exists.{succ (max u1 u2)} (n -> A) (fun (v : n -> A) => Exists.{0} (Ne.{succ (max u1 u2)} (n -> A) v (OfNat.ofNat.{max u1 u2} (n -> A) 0 (Zero.toOfNat0.{max u1 u2} (n -> A) (Pi.instZero.{u1, u2} n (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.18132 : n) => A) (fun (i : n) => CommMonoidWithZero.toZero.{u2} A (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} A (IsDomain.toCancelCommMonoidWithZero.{u2} A (CommRing.toCommSemiring.{u2} A _inst_6) _inst_7))))))) (fun (H : Ne.{succ (max u1 u2)} (n -> A) v (OfNat.ofNat.{max u1 u2} (n -> A) 0 (Zero.toOfNat0.{max u1 u2} (n -> A) (Pi.instZero.{u1, u2} n (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.18132 : n) => A) (fun (i : n) => CommMonoidWithZero.toZero.{u2} A (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} A (IsDomain.toCancelCommMonoidWithZero.{u2} A (CommRing.toCommSemiring.{u2} A _inst_6) _inst_7))))))) => Eq.{max (succ u1) (succ u2)} (n -> A) (Matrix.vecMul.{u2, u1, u1} n n A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_6)))) _inst_4 v M) (OfNat.ofNat.{max u1 u2} (n -> A) 0 (Zero.toOfNat0.{max u1 u2} (n -> A) (Pi.instZero.{u1, u2} n (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.18132 : n) => A) (fun (i : n) => CommMonoidWithZero.toZero.{u2} A (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} A (IsDomain.toCancelCommMonoidWithZero.{u2} A (CommRing.toCommSemiring.{u2} A _inst_6) _inst_7))))))))) (Eq.{succ u2} A (Matrix.det.{u2, u1} n (fun (a : n) (b : n) => _inst_5 a b) _inst_4 A _inst_6 M) (OfNat.ofNat.{u2} A 0 (Zero.toOfNat0.{u2} A (CommMonoidWithZero.toZero.{u2} A (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} A (IsDomain.toCancelCommMonoidWithZero.{u2} A (CommRing.toCommSemiring.{u2} A _inst_6) _inst_7))))))
Case conversion may be inaccurate. Consider using '#align matrix.exists_vec_mul_eq_zero_iff Matrix.exists_vecMul_eq_zero_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (v «expr ≠ » 0) -/
theorem exists_vecMul_eq_zero_iff {A : Type _} [DecidableEq n] [CommRing A] [IsDomain A]
    {M : Matrix n n A} : (∃ (v : _)(_ : v ≠ 0), M.vecMul v = 0) ↔ M.det = 0 := by
  simpa only [← M.det_transpose, ← mul_vec_transpose] using exists_mul_vec_eq_zero_iff
#align matrix.exists_vec_mul_eq_zero_iff Matrix.exists_vecMul_eq_zero_iff

/- warning: matrix.nondegenerate_iff_det_ne_zero -> Matrix.nondegenerate_iff_det_ne_zero is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} [_inst_4 : Fintype.{u1} n] {A : Type.{u2}} [_inst_5 : DecidableEq.{succ u1} n] [_inst_6 : CommRing.{u2} A] [_inst_7 : IsDomain.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_6))] {M : Matrix.{u1, u1, u2} n n A}, Iff (Matrix.Nondegenerate.{u1, u2} n A _inst_4 _inst_6 M) (Ne.{succ u2} A (Matrix.det.{u2, u1} n (fun (a : n) (b : n) => _inst_5 a b) _inst_4 A _inst_6 M) (OfNat.ofNat.{u2} A 0 (OfNat.mk.{u2} A 0 (Zero.zero.{u2} A (MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_6))))))))))
but is expected to have type
  forall {n : Type.{u1}} [_inst_4 : Fintype.{u1} n] {A : Type.{u2}} [_inst_5 : DecidableEq.{succ u1} n] [_inst_6 : CommRing.{u2} A] [_inst_7 : IsDomain.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_6))] {M : Matrix.{u1, u1, u2} n n A}, Iff (Matrix.Nondegenerate.{u1, u2} n A _inst_4 _inst_6 M) (Ne.{succ u2} A (Matrix.det.{u2, u1} n (fun (a : n) (b : n) => _inst_5 a b) _inst_4 A _inst_6 M) (OfNat.ofNat.{u2} A 0 (Zero.toOfNat0.{u2} A (CommMonoidWithZero.toZero.{u2} A (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} A (IsDomain.toCancelCommMonoidWithZero.{u2} A (CommRing.toCommSemiring.{u2} A _inst_6) _inst_7))))))
Case conversion may be inaccurate. Consider using '#align matrix.nondegenerate_iff_det_ne_zero Matrix.nondegenerate_iff_det_ne_zeroₓ'. -/
theorem nondegenerate_iff_det_ne_zero {A : Type _} [DecidableEq n] [CommRing A] [IsDomain A]
    {M : Matrix n n A} : Nondegenerate M ↔ M.det ≠ 0 :=
  by
  refine' Iff.trans _ (not_iff_not.mpr exists_vec_mul_eq_zero_iff)
  simp only [not_exists]
  constructor
  · intro hM v hv hMv
    obtain ⟨w, hwMv⟩ := hM.exists_not_ortho_of_ne_zero hv
    simpa only [dot_product_mul_vec, hMv, zero_dot_product] using hwMv
  · intro h v hv
    refine' not_imp_not.mp (h v) (funext fun i => _)
    simpa only [dot_product_mul_vec, dot_product_single, mul_one] using hv (Pi.single i 1)
#align matrix.nondegenerate_iff_det_ne_zero Matrix.nondegenerate_iff_det_ne_zero

/- warning: matrix.nondegenerate.det_ne_zero -> Matrix.Nondegenerate.det_ne_zero is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} [_inst_4 : Fintype.{u1} n] {A : Type.{u2}} [_inst_5 : DecidableEq.{succ u1} n] [_inst_6 : CommRing.{u2} A] [_inst_7 : IsDomain.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_6))] {M : Matrix.{u1, u1, u2} n n A}, (Matrix.Nondegenerate.{u1, u2} n A _inst_4 _inst_6 M) -> (Ne.{succ u2} A (Matrix.det.{u2, u1} n (fun (a : n) (b : n) => _inst_5 a b) _inst_4 A _inst_6 M) (OfNat.ofNat.{u2} A 0 (OfNat.mk.{u2} A 0 (Zero.zero.{u2} A (MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_6))))))))))
but is expected to have type
  forall {n : Type.{u1}} [_inst_4 : Fintype.{u1} n] {A : Type.{u2}} [_inst_5 : DecidableEq.{succ u1} n] [_inst_6 : CommRing.{u2} A] [_inst_7 : IsDomain.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_6))] {M : Matrix.{u1, u1, u2} n n A}, (Matrix.Nondegenerate.{u1, u2} n A _inst_4 _inst_6 M) -> (Ne.{succ u2} A (Matrix.det.{u2, u1} n (fun (a : n) (b : n) => _inst_5 a b) _inst_4 A _inst_6 M) (OfNat.ofNat.{u2} A 0 (Zero.toOfNat0.{u2} A (CommMonoidWithZero.toZero.{u2} A (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} A (IsDomain.toCancelCommMonoidWithZero.{u2} A (CommRing.toCommSemiring.{u2} A _inst_6) _inst_7))))))
Case conversion may be inaccurate. Consider using '#align matrix.nondegenerate.det_ne_zero Matrix.Nondegenerate.det_ne_zeroₓ'. -/
/- warning: matrix.nondegenerate.of_det_ne_zero -> Matrix.Nondegenerate.of_det_ne_zero is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} [_inst_4 : Fintype.{u1} n] {A : Type.{u2}} [_inst_5 : DecidableEq.{succ u1} n] [_inst_6 : CommRing.{u2} A] [_inst_7 : IsDomain.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_6))] {M : Matrix.{u1, u1, u2} n n A}, (Ne.{succ u2} A (Matrix.det.{u2, u1} n (fun (a : n) (b : n) => _inst_5 a b) _inst_4 A _inst_6 M) (OfNat.ofNat.{u2} A 0 (OfNat.mk.{u2} A 0 (Zero.zero.{u2} A (MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_6)))))))))) -> (Matrix.Nondegenerate.{u1, u2} n A _inst_4 _inst_6 M)
but is expected to have type
  forall {n : Type.{u1}} [_inst_4 : Fintype.{u1} n] {A : Type.{u2}} [_inst_5 : DecidableEq.{succ u1} n] [_inst_6 : CommRing.{u2} A] [_inst_7 : IsDomain.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_6))] {M : Matrix.{u1, u1, u2} n n A}, (Ne.{succ u2} A (Matrix.det.{u2, u1} n (fun (a : n) (b : n) => _inst_5 a b) _inst_4 A _inst_6 M) (OfNat.ofNat.{u2} A 0 (Zero.toOfNat0.{u2} A (CommMonoidWithZero.toZero.{u2} A (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} A (IsDomain.toCancelCommMonoidWithZero.{u2} A (CommRing.toCommSemiring.{u2} A _inst_6) _inst_7)))))) -> (Matrix.Nondegenerate.{u1, u2} n A _inst_4 _inst_6 M)
Case conversion may be inaccurate. Consider using '#align matrix.nondegenerate.of_det_ne_zero Matrix.Nondegenerate.of_det_ne_zeroₓ'. -/
alias nondegenerate_iff_det_ne_zero ↔ nondegenerate.det_ne_zero nondegenerate.of_det_ne_zero
#align matrix.nondegenerate.det_ne_zero Matrix.Nondegenerate.det_ne_zero
#align matrix.nondegenerate.of_det_ne_zero Matrix.Nondegenerate.of_det_ne_zero

end Nondegenerate

end Matrix

