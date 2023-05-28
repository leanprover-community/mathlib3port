/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen

! This file was ported from Lean 3 source module linear_algebra.matrix.basis
! leanprover-community/mathlib commit f2b757fc5c341d88741b9c4630b1e8ba973c5726
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Matrix.Reindex
import Mathbin.LinearAlgebra.Matrix.ToLin

/-!
# Bases and matrices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the map `basis.to_matrix` that sends a family of vectors to
the matrix of their coordinates with respect to some basis.

## Main definitions

 * `basis.to_matrix e v` is the matrix whose `i, j`th entry is `e.repr (v j) i`
 * `basis.to_matrix_equiv` is `basis.to_matrix` bundled as a linear equiv

## Main results

 * `linear_map.to_matrix_id_eq_basis_to_matrix`: `linear_map.to_matrix b c id`
   is equal to `basis.to_matrix b c`
 * `basis.to_matrix_mul_to_matrix`: multiplying `basis.to_matrix` with another
   `basis.to_matrix` gives a `basis.to_matrix`

## Tags

matrix, basis
-/


noncomputable section

open LinearMap Matrix Set Submodule

open BigOperators

open Matrix

section BasisToMatrix

variable {ι ι' κ κ' : Type _}

variable {R M : Type _} [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {R₂ M₂ : Type _} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

open Function Matrix

#print Basis.toMatrix /-
/-- From a basis `e : ι → M` and a family of vectors `v : ι' → M`, make the matrix whose columns
are the vectors `v i` written in the basis `e`. -/
def Basis.toMatrix (e : Basis ι R M) (v : ι' → M) : Matrix ι ι' R := fun i j => e.repr (v j) i
#align basis.to_matrix Basis.toMatrix
-/

variable (e : Basis ι R M) (v : ι' → M) (i : ι) (j : ι')

namespace Basis

/- warning: basis.to_matrix_apply -> Basis.toMatrix_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.to_matrix_apply Basis.toMatrix_applyₓ'. -/
theorem toMatrix_apply : e.toMatrix v i j = e.repr (v j) i :=
  rfl
#align basis.to_matrix_apply Basis.toMatrix_apply

/- warning: basis.to_matrix_transpose_apply -> Basis.toMatrix_transpose_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.to_matrix_transpose_apply Basis.toMatrix_transpose_applyₓ'. -/
theorem toMatrix_transpose_apply : (e.toMatrix v)ᵀ j = e.repr (v j) :=
  funext fun _ => rfl
#align basis.to_matrix_transpose_apply Basis.toMatrix_transpose_apply

/- warning: basis.to_matrix_eq_to_matrix_constr -> Basis.toMatrix_eq_toMatrix_constr is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.to_matrix_eq_to_matrix_constr Basis.toMatrix_eq_toMatrix_constrₓ'. -/
theorem toMatrix_eq_toMatrix_constr [Fintype ι] [DecidableEq ι] (v : ι → M) :
    e.toMatrix v = LinearMap.toMatrix e e (e.constr ℕ v) := by ext;
  rw [Basis.toMatrix_apply, LinearMap.toMatrix_apply, Basis.constr_basis]
#align basis.to_matrix_eq_to_matrix_constr Basis.toMatrix_eq_toMatrix_constr

/- warning: basis.coe_pi_basis_fun.to_matrix_eq_transpose -> Basis.coePiBasisFun.toMatrix_eq_transpose is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_1 : CommSemiring.{u2} R] [_inst_7 : Fintype.{u1} ι], Eq.{max (max (succ u1) (succ u2)) (succ (max u1 u2))} ((ι -> ι -> R) -> (Matrix.{u1, u1, u2} ι ι R)) (Basis.toMatrix.{u1, u1, u2, max u1 u2} ι ι R (ι -> R) _inst_1 (Pi.addCommMonoid.{u1, u2} ι (fun (j : ι) => R) (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (Pi.Function.module.{u1, u2, u2} ι R R (CommSemiring.toSemiring.{u2} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) (Pi.basisFun.{u2, u1} R ι (CommSemiring.toSemiring.{u2} R _inst_1) _inst_7)) (Matrix.transpose.{u2, u1, u1} ι ι R)
but is expected to have type
  forall {ι : Type.{u2}} {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_7 : Fintype.{u2} ι], Eq.{max (succ u2) (succ u1)} ((ι -> ι -> R) -> (Matrix.{u2, u2, u1} ι ι R)) (Basis.toMatrix.{u2, u2, u1, max u2 u1} ι ι R (ι -> R) _inst_1 (Pi.addCommMonoid.{u2, u1} ι (fun (j : ι) => R) (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.module.{u2, u1, u1} ι (fun (x._@.Mathlib.LinearAlgebra.StdBasis._hyg.3573 : ι) => R) R (CommSemiring.toSemiring.{u1} R _inst_1) (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (fun (i : ι) => Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (Pi.basisFun.{u1, u2} R ι (CommSemiring.toSemiring.{u1} R _inst_1) _inst_7)) (Matrix.transpose.{u1, u2, u2} ι ι R)
Case conversion may be inaccurate. Consider using '#align basis.coe_pi_basis_fun.to_matrix_eq_transpose Basis.coePiBasisFun.toMatrix_eq_transposeₓ'. -/
-- TODO (maybe) Adjust the definition of `basis.to_matrix` to eliminate the transpose.
theorem coePiBasisFun.toMatrix_eq_transpose [Fintype ι] :
    ((Pi.basisFun R ι).toMatrix : Matrix ι ι R → Matrix ι ι R) = Matrix.transpose := by ext (M i j);
  rfl
#align basis.coe_pi_basis_fun.to_matrix_eq_transpose Basis.coePiBasisFun.toMatrix_eq_transpose

/- warning: basis.to_matrix_self -> Basis.toMatrix_self is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : CommSemiring.{u2} R] [_inst_2 : AddCommMonoid.{u3} M] [_inst_3 : Module.{u2, u3} R M (CommSemiring.toSemiring.{u2} R _inst_1) _inst_2] (e : Basis.{u1, u2, u3} ι R M (CommSemiring.toSemiring.{u2} R _inst_1) _inst_2 _inst_3) [_inst_7 : DecidableEq.{succ u1} ι], Eq.{succ (max u1 u2)} (Matrix.{u1, u1, u2} ι ι R) (Basis.toMatrix.{u1, u1, u2, u3} ι ι R M _inst_1 _inst_2 _inst_3 e (coeFn.{max (succ u1) (succ u2) (succ u3), max (succ u1) (succ u3)} (Basis.{u1, u2, u3} ι R M (CommSemiring.toSemiring.{u2} R _inst_1) _inst_2 _inst_3) (fun (_x : Basis.{u1, u2, u3} ι R M (CommSemiring.toSemiring.{u2} R _inst_1) _inst_2 _inst_3) => ι -> M) (FunLike.hasCoeToFun.{max (succ u1) (succ u2) (succ u3), succ u1, succ u3} (Basis.{u1, u2, u3} ι R M (CommSemiring.toSemiring.{u2} R _inst_1) _inst_2 _inst_3) ι (fun (_x : ι) => M) (Basis.funLike.{u1, u2, u3} ι R M (CommSemiring.toSemiring.{u2} R _inst_1) _inst_2 _inst_3)) e)) (OfNat.ofNat.{max u1 u2} (Matrix.{u1, u1, u2} ι ι R) 1 (OfNat.mk.{max u1 u2} (Matrix.{u1, u1, u2} ι ι R) 1 (One.one.{max u1 u2} (Matrix.{u1, u1, u2} ι ι R) (Matrix.hasOne.{u2, u1} ι R (fun (a : ι) (b : ι) => _inst_7 a b) (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (AddMonoidWithOne.toOne.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))))))))
but is expected to have type
  forall {ι : Type.{u3}} {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] [_inst_2 : AddCommMonoid.{u1} M] [_inst_3 : Module.{u2, u1} R M (CommSemiring.toSemiring.{u2} R _inst_1) _inst_2] (e : Basis.{u3, u2, u1} ι R M (CommSemiring.toSemiring.{u2} R _inst_1) _inst_2 _inst_3) [_inst_7 : DecidableEq.{succ u3} ι], Eq.{max (succ u3) (succ u2)} (Matrix.{u3, u3, u2} ι ι R) (Basis.toMatrix.{u3, u3, u2, u1} ι ι R M _inst_1 _inst_2 _inst_3 e (FunLike.coe.{max (max (succ u3) (succ u2)) (succ u1), succ u3, succ u1} (Basis.{u3, u2, u1} ι R M (CommSemiring.toSemiring.{u2} R _inst_1) _inst_2 _inst_3) ι (fun (_x : ι) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) _x) (Basis.funLike.{u3, u2, u1} ι R M (CommSemiring.toSemiring.{u2} R _inst_1) _inst_2 _inst_3) e)) (OfNat.ofNat.{max u3 u2} (Matrix.{u3, u3, u2} ι ι R) 1 (One.toOfNat1.{max u3 u2} (Matrix.{u3, u3, u2} ι ι R) (Matrix.one.{u2, u3} ι R (fun (a : ι) (b : ι) => _inst_7 a b) (CommMonoidWithZero.toZero.{u2} R (CommSemiring.toCommMonoidWithZero.{u2} R _inst_1)) (Semiring.toOne.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align basis.to_matrix_self Basis.toMatrix_selfₓ'. -/
@[simp]
theorem toMatrix_self [DecidableEq ι] : e.toMatrix e = 1 :=
  by
  rw [Basis.toMatrix]
  ext (i j)
  simp [Basis.equivFun, Matrix.one_apply, Finsupp.single_apply, eq_comm]
#align basis.to_matrix_self Basis.toMatrix_self

/- warning: basis.to_matrix_update -> Basis.toMatrix_update is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.to_matrix_update Basis.toMatrix_updateₓ'. -/
theorem toMatrix_update [DecidableEq ι'] (x : M) :
    e.toMatrix (Function.update v j x) = Matrix.updateColumn (e.toMatrix v) j (e.repr x) :=
  by
  ext (i' k)
  rw [Basis.toMatrix, Matrix.updateColumn_apply, e.to_matrix_apply]
  split_ifs
  · rw [h, update_same j x v]
  · rw [update_noteq h]
#align basis.to_matrix_update Basis.toMatrix_update

/- warning: basis.to_matrix_units_smul -> Basis.toMatrix_unitsSMul is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R₂ : Type.{u2}} {M₂ : Type.{u3}} [_inst_4 : CommRing.{u2} R₂] [_inst_5 : AddCommGroup.{u3} M₂] [_inst_6 : Module.{u2, u3} R₂ M₂ (Ring.toSemiring.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_5)] [_inst_7 : DecidableEq.{succ u1} ι] (e : Basis.{u1, u2, u3} ι R₂ M₂ (Ring.toSemiring.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_5) _inst_6) (w : ι -> (Units.{u2} R₂ (Ring.toMonoid.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4)))), Eq.{succ (max u1 u2)} (Matrix.{u1, u1, u2} ι ι R₂) (Basis.toMatrix.{u1, u1, u2, u3} ι ι R₂ M₂ (CommRing.toCommSemiring.{u2} R₂ _inst_4) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_5) _inst_6 e (coeFn.{max (succ u1) (succ u2) (succ u3), max (succ u1) (succ u3)} (Basis.{u1, u2, u3} ι R₂ M₂ (Ring.toSemiring.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_5) _inst_6) (fun (_x : Basis.{u1, u2, u3} ι R₂ M₂ (Ring.toSemiring.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_5) _inst_6) => ι -> M₂) (FunLike.hasCoeToFun.{max (succ u1) (succ u2) (succ u3), succ u1, succ u3} (Basis.{u1, u2, u3} ι R₂ M₂ (Ring.toSemiring.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_5) _inst_6) ι (fun (_x : ι) => M₂) (Basis.funLike.{u1, u2, u3} ι R₂ M₂ (Ring.toSemiring.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_5) _inst_6)) (Basis.unitsSMul.{u1, u2, u3} ι R₂ M₂ (CommRing.toRing.{u2} R₂ _inst_4) _inst_5 _inst_6 e w))) (Matrix.diagonal.{u2, u1} ι R₂ (fun (a : ι) (b : ι) => _inst_7 a b) (MulZeroClass.toHasZero.{u2} R₂ (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R₂ (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R₂ (NonAssocRing.toNonUnitalNonAssocRing.{u2} R₂ (Ring.toNonAssocRing.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4)))))) (Function.comp.{succ u1, succ u2, succ u2} ι (Units.{u2} R₂ (Ring.toMonoid.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4))) R₂ ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Units.{u2} R₂ (Ring.toMonoid.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4))) R₂ (HasLiftT.mk.{succ u2, succ u2} (Units.{u2} R₂ (Ring.toMonoid.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4))) R₂ (CoeTCₓ.coe.{succ u2, succ u2} (Units.{u2} R₂ (Ring.toMonoid.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4))) R₂ (coeBase.{succ u2, succ u2} (Units.{u2} R₂ (Ring.toMonoid.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4))) R₂ (Units.hasCoe.{u2} R₂ (Ring.toMonoid.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4))))))) w))
but is expected to have type
  forall {ι : Type.{u3}} {R₂ : Type.{u2}} {M₂ : Type.{u1}} [_inst_4 : CommRing.{u2} R₂] [_inst_5 : AddCommGroup.{u1} M₂] [_inst_6 : Module.{u2, u1} R₂ M₂ (CommSemiring.toSemiring.{u2} R₂ (CommRing.toCommSemiring.{u2} R₂ _inst_4)) (AddCommGroup.toAddCommMonoid.{u1} M₂ _inst_5)] [_inst_7 : DecidableEq.{succ u3} ι] (e : Basis.{u3, u2, u1} ι R₂ M₂ (CommSemiring.toSemiring.{u2} R₂ (CommRing.toCommSemiring.{u2} R₂ _inst_4)) (AddCommGroup.toAddCommMonoid.{u1} M₂ _inst_5) _inst_6) (w : ι -> (Units.{u2} R₂ (MonoidWithZero.toMonoid.{u2} R₂ (Semiring.toMonoidWithZero.{u2} R₂ (CommSemiring.toSemiring.{u2} R₂ (CommRing.toCommSemiring.{u2} R₂ _inst_4)))))), Eq.{max (succ u3) (succ u2)} (Matrix.{u3, u3, u2} ι ι R₂) (Basis.toMatrix.{u3, u3, u2, u1} ι ι R₂ M₂ (CommRing.toCommSemiring.{u2} R₂ _inst_4) (AddCommGroup.toAddCommMonoid.{u1} M₂ _inst_5) _inst_6 e (FunLike.coe.{max (max (succ u3) (succ u2)) (succ u1), succ u3, succ u1} (Basis.{u3, u2, u1} ι R₂ M₂ (Ring.toSemiring.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4)) (AddCommGroup.toAddCommMonoid.{u1} M₂ _inst_5) _inst_6) ι (fun (_x : ι) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M₂) _x) (Basis.funLike.{u3, u2, u1} ι R₂ M₂ (Ring.toSemiring.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4)) (AddCommGroup.toAddCommMonoid.{u1} M₂ _inst_5) _inst_6) (Basis.unitsSMul.{u3, u2, u1} ι R₂ M₂ (CommRing.toRing.{u2} R₂ _inst_4) _inst_5 _inst_6 e w))) (Matrix.diagonal.{u2, u3} ι R₂ (fun (a : ι) (b : ι) => _inst_7 a b) (CommMonoidWithZero.toZero.{u2} R₂ (CommSemiring.toCommMonoidWithZero.{u2} R₂ (CommRing.toCommSemiring.{u2} R₂ _inst_4))) (Function.comp.{succ u3, succ u2, succ u2} ι (Units.{u2} R₂ (MonoidWithZero.toMonoid.{u2} R₂ (Semiring.toMonoidWithZero.{u2} R₂ (CommSemiring.toSemiring.{u2} R₂ (CommRing.toCommSemiring.{u2} R₂ _inst_4))))) R₂ (Units.val.{u2} R₂ (MonoidWithZero.toMonoid.{u2} R₂ (Semiring.toMonoidWithZero.{u2} R₂ (CommSemiring.toSemiring.{u2} R₂ (CommRing.toCommSemiring.{u2} R₂ _inst_4))))) w))
Case conversion may be inaccurate. Consider using '#align basis.to_matrix_units_smul Basis.toMatrix_unitsSMulₓ'. -/
/-- The basis constructed by `units_smul` has vectors given by a diagonal matrix. -/
@[simp]
theorem toMatrix_unitsSMul [DecidableEq ι] (e : Basis ι R₂ M₂) (w : ι → R₂ˣ) :
    e.toMatrix (e.units_smul w) = diagonal (coe ∘ w) :=
  by
  ext (i j)
  by_cases h : i = j
  · simp [h, to_matrix_apply, units_smul_apply, Units.smul_def]
  · simp [h, to_matrix_apply, units_smul_apply, Units.smul_def, Ne.symm h]
#align basis.to_matrix_units_smul Basis.toMatrix_unitsSMul

/- warning: basis.to_matrix_is_unit_smul -> Basis.toMatrix_isUnitSMul is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R₂ : Type.{u2}} {M₂ : Type.{u3}} [_inst_4 : CommRing.{u2} R₂] [_inst_5 : AddCommGroup.{u3} M₂] [_inst_6 : Module.{u2, u3} R₂ M₂ (Ring.toSemiring.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_5)] [_inst_7 : DecidableEq.{succ u1} ι] (e : Basis.{u1, u2, u3} ι R₂ M₂ (Ring.toSemiring.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_5) _inst_6) {w : ι -> R₂} (hw : forall (i : ι), IsUnit.{u2} R₂ (Ring.toMonoid.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4)) (w i)), Eq.{succ (max u1 u2)} (Matrix.{u1, u1, u2} ι ι R₂) (Basis.toMatrix.{u1, u1, u2, u3} ι ι R₂ M₂ (CommRing.toCommSemiring.{u2} R₂ _inst_4) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_5) _inst_6 e (coeFn.{max (succ u1) (succ u2) (succ u3), max (succ u1) (succ u3)} (Basis.{u1, u2, u3} ι R₂ M₂ (Ring.toSemiring.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_5) _inst_6) (fun (_x : Basis.{u1, u2, u3} ι R₂ M₂ (Ring.toSemiring.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_5) _inst_6) => ι -> M₂) (FunLike.hasCoeToFun.{max (succ u1) (succ u2) (succ u3), succ u1, succ u3} (Basis.{u1, u2, u3} ι R₂ M₂ (Ring.toSemiring.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_5) _inst_6) ι (fun (_x : ι) => M₂) (Basis.funLike.{u1, u2, u3} ι R₂ M₂ (Ring.toSemiring.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_5) _inst_6)) (Basis.isUnitSMul.{u1, u2, u3} ι R₂ M₂ (CommRing.toRing.{u2} R₂ _inst_4) _inst_5 _inst_6 e (fun (i : ι) => w i) hw))) (Matrix.diagonal.{u2, u1} ι R₂ (fun (a : ι) (b : ι) => _inst_7 a b) (MulZeroClass.toHasZero.{u2} R₂ (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R₂ (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R₂ (NonAssocRing.toNonUnitalNonAssocRing.{u2} R₂ (Ring.toNonAssocRing.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4)))))) w)
but is expected to have type
  forall {ι : Type.{u3}} {R₂ : Type.{u2}} {M₂ : Type.{u1}} [_inst_4 : CommRing.{u2} R₂] [_inst_5 : AddCommGroup.{u1} M₂] [_inst_6 : Module.{u2, u1} R₂ M₂ (CommSemiring.toSemiring.{u2} R₂ (CommRing.toCommSemiring.{u2} R₂ _inst_4)) (AddCommGroup.toAddCommMonoid.{u1} M₂ _inst_5)] [_inst_7 : DecidableEq.{succ u3} ι] (e : Basis.{u3, u2, u1} ι R₂ M₂ (CommSemiring.toSemiring.{u2} R₂ (CommRing.toCommSemiring.{u2} R₂ _inst_4)) (AddCommGroup.toAddCommMonoid.{u1} M₂ _inst_5) _inst_6) {w : ι -> R₂} (hw : forall (i : ι), IsUnit.{u2} R₂ (MonoidWithZero.toMonoid.{u2} R₂ (Semiring.toMonoidWithZero.{u2} R₂ (CommSemiring.toSemiring.{u2} R₂ (CommRing.toCommSemiring.{u2} R₂ _inst_4)))) (w i)), Eq.{max (succ u3) (succ u2)} (Matrix.{u3, u3, u2} ι ι R₂) (Basis.toMatrix.{u3, u3, u2, u1} ι ι R₂ M₂ (CommRing.toCommSemiring.{u2} R₂ _inst_4) (AddCommGroup.toAddCommMonoid.{u1} M₂ _inst_5) _inst_6 e (FunLike.coe.{max (max (succ u3) (succ u2)) (succ u1), succ u3, succ u1} (Basis.{u3, u2, u1} ι R₂ M₂ (Ring.toSemiring.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4)) (AddCommGroup.toAddCommMonoid.{u1} M₂ _inst_5) _inst_6) ι (fun (_x : ι) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M₂) _x) (Basis.funLike.{u3, u2, u1} ι R₂ M₂ (Ring.toSemiring.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4)) (AddCommGroup.toAddCommMonoid.{u1} M₂ _inst_5) _inst_6) (Basis.isUnitSMul.{u3, u2, u1} ι R₂ M₂ (CommRing.toRing.{u2} R₂ _inst_4) _inst_5 _inst_6 e (fun (i : ι) => w i) hw))) (Matrix.diagonal.{u2, u3} ι R₂ (fun (a : ι) (b : ι) => _inst_7 a b) (CommMonoidWithZero.toZero.{u2} R₂ (CommSemiring.toCommMonoidWithZero.{u2} R₂ (CommRing.toCommSemiring.{u2} R₂ _inst_4))) w)
Case conversion may be inaccurate. Consider using '#align basis.to_matrix_is_unit_smul Basis.toMatrix_isUnitSMulₓ'. -/
/-- The basis constructed by `is_unit_smul` has vectors given by a diagonal matrix. -/
@[simp]
theorem toMatrix_isUnitSMul [DecidableEq ι] (e : Basis ι R₂ M₂) {w : ι → R₂}
    (hw : ∀ i, IsUnit (w i)) : e.toMatrix (e.isUnitSMul hw) = diagonal w :=
  e.toMatrix_unitsSMul _
#align basis.to_matrix_is_unit_smul Basis.toMatrix_isUnitSMul

/- warning: basis.sum_to_matrix_smul_self -> Basis.sum_toMatrix_smul_self is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {R : Type.{u3}} {M : Type.{u4}} [_inst_1 : CommSemiring.{u3} R] [_inst_2 : AddCommMonoid.{u4} M] [_inst_3 : Module.{u3, u4} R M (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2] (e : Basis.{u1, u3, u4} ι R M (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 _inst_3) (v : ι' -> M) (j : ι') [_inst_7 : Fintype.{u1} ι], Eq.{succ u4} M (Finset.sum.{u4, u1} M ι _inst_2 (Finset.univ.{u1} ι _inst_7) (fun (i : ι) => SMul.smul.{u3, u4} R M (SMulZeroClass.toHasSmul.{u3, u4} R M (AddZeroClass.toHasZero.{u4} M (AddMonoid.toAddZeroClass.{u4} M (AddCommMonoid.toAddMonoid.{u4} M _inst_2))) (SMulWithZero.toSmulZeroClass.{u3, u4} R M (MulZeroClass.toHasZero.{u3} R (MulZeroOneClass.toMulZeroClass.{u3} R (MonoidWithZero.toMulZeroOneClass.{u3} R (Semiring.toMonoidWithZero.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1))))) (AddZeroClass.toHasZero.{u4} M (AddMonoid.toAddZeroClass.{u4} M (AddCommMonoid.toAddMonoid.{u4} M _inst_2))) (MulActionWithZero.toSMulWithZero.{u3, u4} R M (Semiring.toMonoidWithZero.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)) (AddZeroClass.toHasZero.{u4} M (AddMonoid.toAddZeroClass.{u4} M (AddCommMonoid.toAddMonoid.{u4} M _inst_2))) (Module.toMulActionWithZero.{u3, u4} R M (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 _inst_3)))) (Basis.toMatrix.{u1, u2, u3, u4} ι ι' R M _inst_1 _inst_2 _inst_3 e v i j) (coeFn.{max (succ u1) (succ u3) (succ u4), max (succ u1) (succ u4)} (Basis.{u1, u3, u4} ι R M (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 _inst_3) (fun (_x : Basis.{u1, u3, u4} ι R M (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 _inst_3) => ι -> M) (FunLike.hasCoeToFun.{max (succ u1) (succ u3) (succ u4), succ u1, succ u4} (Basis.{u1, u3, u4} ι R M (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 _inst_3) ι (fun (_x : ι) => M) (Basis.funLike.{u1, u3, u4} ι R M (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 _inst_3)) e i))) (v j)
but is expected to have type
  forall {ι : Type.{u4}} {ι' : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : CommSemiring.{u2} R] [_inst_2 : AddCommMonoid.{u3} M] [_inst_3 : Module.{u2, u3} R M (CommSemiring.toSemiring.{u2} R _inst_1) _inst_2] (e : Basis.{u4, u2, u3} ι R M (CommSemiring.toSemiring.{u2} R _inst_1) _inst_2 _inst_3) (v : ι' -> M) (j : ι') [_inst_7 : Fintype.{u4} ι], Eq.{succ u3} M (Finset.sum.{u3, u4} M ι _inst_2 (Finset.univ.{u4} ι _inst_7) (fun (i : ι) => HSMul.hSMul.{u2, u3, u3} R ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (instHSMul.{u2, u3} R ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (SMulZeroClass.toSMul.{u2, u3} R ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (AddMonoid.toZero.{u3} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (AddCommMonoid.toAddMonoid.{u3} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) _inst_2)) (SMulWithZero.toSMulZeroClass.{u2, u3} R ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (CommMonoidWithZero.toZero.{u2} R (CommSemiring.toCommMonoidWithZero.{u2} R _inst_1)) (AddMonoid.toZero.{u3} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (AddCommMonoid.toAddMonoid.{u3} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) _inst_2)) (MulActionWithZero.toSMulWithZero.{u2, u3} R ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (AddMonoid.toZero.{u3} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (AddCommMonoid.toAddMonoid.{u3} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) _inst_2)) (Module.toMulActionWithZero.{u2, u3} R ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (CommSemiring.toSemiring.{u2} R _inst_1) _inst_2 _inst_3))))) (Basis.toMatrix.{u4, u1, u2, u3} ι ι' R M _inst_1 _inst_2 _inst_3 e v i j) (FunLike.coe.{max (max (succ u4) (succ u2)) (succ u3), succ u4, succ u3} (Basis.{u4, u2, u3} ι R M (CommSemiring.toSemiring.{u2} R _inst_1) _inst_2 _inst_3) ι (fun (_x : ι) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) _x) (Basis.funLike.{u4, u2, u3} ι R M (CommSemiring.toSemiring.{u2} R _inst_1) _inst_2 _inst_3) e i))) (v j)
Case conversion may be inaccurate. Consider using '#align basis.sum_to_matrix_smul_self Basis.sum_toMatrix_smul_selfₓ'. -/
@[simp]
theorem sum_toMatrix_smul_self [Fintype ι] : (∑ i : ι, e.toMatrix v i j • e i) = v j := by
  simp_rw [e.to_matrix_apply, e.sum_repr]
#align basis.sum_to_matrix_smul_self Basis.sum_toMatrix_smul_self

/- warning: basis.to_matrix_map_vec_mul -> Basis.toMatrix_map_vecMul is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {R : Type.{u3}} [_inst_1 : CommSemiring.{u3} R] {S : Type.{u4}} [_inst_7 : Ring.{u4} S] [_inst_8 : Algebra.{u3, u4} R S _inst_1 (Ring.toSemiring.{u4} S _inst_7)] [_inst_9 : Fintype.{u1} ι] (b : Basis.{u1, u3, u4} ι R S (CommSemiring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u4} S (NonUnitalNonAssocRing.toAddCommGroup.{u4} S (NonAssocRing.toNonUnitalNonAssocRing.{u4} S (Ring.toNonAssocRing.{u4} S _inst_7)))) (Algebra.toModule.{u3, u4} R S _inst_1 (Ring.toSemiring.{u4} S _inst_7) _inst_8)) (v : ι' -> S), Eq.{max (succ u2) (succ u4)} (ι' -> S) (Matrix.vecMul.{u4, u1, u2} ι ι' S (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u4} S (NonAssocRing.toNonUnitalNonAssocRing.{u4} S (Ring.toNonAssocRing.{u4} S _inst_7))) _inst_9 (coeFn.{max (succ u1) (succ u3) (succ u4), max (succ u1) (succ u4)} (Basis.{u1, u3, u4} ι R S (CommSemiring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u4} S (NonUnitalNonAssocRing.toAddCommGroup.{u4} S (NonAssocRing.toNonUnitalNonAssocRing.{u4} S (Ring.toNonAssocRing.{u4} S _inst_7)))) (Algebra.toModule.{u3, u4} R S _inst_1 (Ring.toSemiring.{u4} S _inst_7) _inst_8)) (fun (_x : Basis.{u1, u3, u4} ι R S (CommSemiring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u4} S (NonUnitalNonAssocRing.toAddCommGroup.{u4} S (NonAssocRing.toNonUnitalNonAssocRing.{u4} S (Ring.toNonAssocRing.{u4} S _inst_7)))) (Algebra.toModule.{u3, u4} R S _inst_1 (Ring.toSemiring.{u4} S _inst_7) _inst_8)) => ι -> S) (FunLike.hasCoeToFun.{max (succ u1) (succ u3) (succ u4), succ u1, succ u4} (Basis.{u1, u3, u4} ι R S (CommSemiring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u4} S (NonUnitalNonAssocRing.toAddCommGroup.{u4} S (NonAssocRing.toNonUnitalNonAssocRing.{u4} S (Ring.toNonAssocRing.{u4} S _inst_7)))) (Algebra.toModule.{u3, u4} R S _inst_1 (Ring.toSemiring.{u4} S _inst_7) _inst_8)) ι (fun (_x : ι) => S) (Basis.funLike.{u1, u3, u4} ι R S (CommSemiring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u4} S (NonUnitalNonAssocRing.toAddCommGroup.{u4} S (NonAssocRing.toNonUnitalNonAssocRing.{u4} S (Ring.toNonAssocRing.{u4} S _inst_7)))) (Algebra.toModule.{u3, u4} R S _inst_1 (Ring.toSemiring.{u4} S _inst_7) _inst_8))) b) (Matrix.map.{u3, u4, u1, u2} ι ι' R S (Basis.toMatrix.{u1, u2, u3, u4} ι ι' R S _inst_1 (AddCommGroup.toAddCommMonoid.{u4} S (NonUnitalNonAssocRing.toAddCommGroup.{u4} S (NonAssocRing.toNonUnitalNonAssocRing.{u4} S (Ring.toNonAssocRing.{u4} S _inst_7)))) (Algebra.toModule.{u3, u4} R S _inst_1 (Ring.toSemiring.{u4} S _inst_7) _inst_8) b v) (coeFn.{max (succ u3) (succ u4), max (succ u3) (succ u4)} (RingHom.{u3, u4} R S (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)) (Semiring.toNonAssocSemiring.{u4} S (Ring.toSemiring.{u4} S _inst_7))) (fun (_x : RingHom.{u3, u4} R S (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)) (Semiring.toNonAssocSemiring.{u4} S (Ring.toSemiring.{u4} S _inst_7))) => R -> S) (RingHom.hasCoeToFun.{u3, u4} R S (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)) (Semiring.toNonAssocSemiring.{u4} S (Ring.toSemiring.{u4} S _inst_7))) (algebraMap.{u3, u4} R S _inst_1 (Ring.toSemiring.{u4} S _inst_7) _inst_8)))) v
but is expected to have type
  forall {ι : Type.{u2}} {ι' : Type.{u1}} {R : Type.{u3}} [_inst_1 : CommSemiring.{u3} R] {S : Type.{u4}} [_inst_7 : Ring.{u4} S] [_inst_8 : Algebra.{u3, u4} R S _inst_1 (Ring.toSemiring.{u4} S _inst_7)] [_inst_9 : Fintype.{u2} ι] (b : Basis.{u2, u3, u4} ι R S (CommSemiring.toSemiring.{u3} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} S (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u4} S (NonAssocRing.toNonUnitalNonAssocRing.{u4} S (Ring.toNonAssocRing.{u4} S _inst_7)))) (Algebra.toModule.{u3, u4} R S _inst_1 (Ring.toSemiring.{u4} S _inst_7) _inst_8)) (v : ι' -> S), Eq.{max (succ u1) (succ u4)} (ι' -> S) (Matrix.vecMul.{u4, u2, u1} ι ι' S (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u4} S (NonAssocRing.toNonUnitalNonAssocRing.{u4} S (Ring.toNonAssocRing.{u4} S _inst_7))) _inst_9 (FunLike.coe.{max (max (succ u2) (succ u3)) (succ u4), succ u2, succ u4} (Basis.{u2, u3, u4} ι R S (CommSemiring.toSemiring.{u3} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} S (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u4} S (NonAssocRing.toNonUnitalNonAssocRing.{u4} S (Ring.toNonAssocRing.{u4} S _inst_7)))) (Algebra.toModule.{u3, u4} R S _inst_1 (Ring.toSemiring.{u4} S _inst_7) _inst_8)) ι (fun (_x : ι) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => S) _x) (Basis.funLike.{u2, u3, u4} ι R S (CommSemiring.toSemiring.{u3} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} S (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u4} S (NonAssocRing.toNonUnitalNonAssocRing.{u4} S (Ring.toNonAssocRing.{u4} S _inst_7)))) (Algebra.toModule.{u3, u4} R S _inst_1 (Ring.toSemiring.{u4} S _inst_7) _inst_8)) b) (Matrix.map.{u3, u4, u2, u1} ι ι' R S (Basis.toMatrix.{u2, u1, u3, u4} ι ι' R S _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} S (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u4} S (NonAssocRing.toNonUnitalNonAssocRing.{u4} S (Ring.toNonAssocRing.{u4} S _inst_7)))) (Algebra.toModule.{u3, u4} R S _inst_1 (Ring.toSemiring.{u4} S _inst_7) _inst_8) b v) (FunLike.coe.{max (succ u3) (succ u4), succ u3, succ u4} (RingHom.{u3, u4} R S (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)) (Semiring.toNonAssocSemiring.{u4} S (Ring.toSemiring.{u4} S _inst_7))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) _x) (MulHomClass.toFunLike.{max u3 u4, u3, u4} (RingHom.{u3, u4} R S (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)) (Semiring.toNonAssocSemiring.{u4} S (Ring.toSemiring.{u4} S _inst_7))) R S (NonUnitalNonAssocSemiring.toMul.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u4} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} S (Semiring.toNonAssocSemiring.{u4} S (Ring.toSemiring.{u4} S _inst_7)))) (NonUnitalRingHomClass.toMulHomClass.{max u3 u4, u3, u4} (RingHom.{u3, u4} R S (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)) (Semiring.toNonAssocSemiring.{u4} S (Ring.toSemiring.{u4} S _inst_7))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} S (Semiring.toNonAssocSemiring.{u4} S (Ring.toSemiring.{u4} S _inst_7))) (RingHomClass.toNonUnitalRingHomClass.{max u3 u4, u3, u4} (RingHom.{u3, u4} R S (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)) (Semiring.toNonAssocSemiring.{u4} S (Ring.toSemiring.{u4} S _inst_7))) R S (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)) (Semiring.toNonAssocSemiring.{u4} S (Ring.toSemiring.{u4} S _inst_7)) (RingHom.instRingHomClassRingHom.{u3, u4} R S (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)) (Semiring.toNonAssocSemiring.{u4} S (Ring.toSemiring.{u4} S _inst_7)))))) (algebraMap.{u3, u4} R S _inst_1 (Ring.toSemiring.{u4} S _inst_7) _inst_8)))) v
Case conversion may be inaccurate. Consider using '#align basis.to_matrix_map_vec_mul Basis.toMatrix_map_vecMulₓ'. -/
theorem toMatrix_map_vecMul {S : Type _} [Ring S] [Algebra R S] [Fintype ι] (b : Basis ι R S)
    (v : ι' → S) : ((b.toMatrix v).map <| algebraMap R S).vecMul b = v :=
  by
  ext i
  simp_rw [vec_mul, dot_product, Matrix.map_apply, ← Algebra.commutes, ← Algebra.smul_def,
    sum_to_matrix_smul_self]
#align basis.to_matrix_map_vec_mul Basis.toMatrix_map_vecMul

/- warning: basis.to_lin_to_matrix -> Basis.toLin_toMatrix is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.to_lin_to_matrix Basis.toLin_toMatrixₓ'. -/
@[simp]
theorem toLin_toMatrix [Fintype ι] [Fintype ι'] [DecidableEq ι'] (v : Basis ι' R M) :
    Matrix.toLin v e (e.toMatrix v) = id :=
  v.ext fun i => by rw [to_lin_self, id_apply, e.sum_to_matrix_smul_self]
#align basis.to_lin_to_matrix Basis.toLin_toMatrix

#print Basis.toMatrixEquiv /-
/-- From a basis `e : ι → M`, build a linear equivalence between families of vectors `v : ι → M`,
and matrices, making the matrix whose columns are the vectors `v i` written in the basis `e`. -/
def toMatrixEquiv [Fintype ι] (e : Basis ι R M) : (ι → M) ≃ₗ[R] Matrix ι ι R
    where
  toFun := e.toMatrix
  map_add' v w := by
    ext (i j)
    change _ = _ + _
    rw [e.to_matrix_apply, Pi.add_apply, LinearEquiv.map_add]
    rfl
  map_smul' := by
    intro c v
    ext (i j)
    rw [e.to_matrix_apply, Pi.smul_apply, LinearEquiv.map_smul]
    rfl
  invFun m j := ∑ i, m i j • e i
  left_inv := by
    intro v
    ext j
    exact e.sum_to_matrix_smul_self v j
  right_inv := by
    intro m
    ext (k l)
    simp only [e.to_matrix_apply, ← e.equiv_fun_apply, ← e.equiv_fun_symm_apply,
      LinearEquiv.apply_symm_apply]
#align basis.to_matrix_equiv Basis.toMatrixEquiv
-/

end Basis

section MulLinearMapToMatrix

variable {N : Type _} [AddCommMonoid N] [Module R N]

variable (b : Basis ι R M) (b' : Basis ι' R M) (c : Basis κ R N) (c' : Basis κ' R N)

variable (f : M →ₗ[R] N)

open LinearMap

section Fintype

variable [Fintype ι'] [Fintype κ] [Fintype κ']

/- warning: basis_to_matrix_mul_linear_map_to_matrix -> basis_toMatrix_mul_linearMap_toMatrix is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis_to_matrix_mul_linear_map_to_matrix basis_toMatrix_mul_linearMap_toMatrixₓ'. -/
@[simp]
theorem basis_toMatrix_mul_linearMap_toMatrix [DecidableEq ι'] :
    c.toMatrix c' ⬝ LinearMap.toMatrix b' c' f = LinearMap.toMatrix b' c f :=
  (Matrix.toLin b' c).Injective
    (by
      haveI := Classical.decEq κ' <;>
        rw [to_lin_to_matrix, to_lin_mul b' c' c, to_lin_to_matrix, c.to_lin_to_matrix, id_comp])
#align basis_to_matrix_mul_linear_map_to_matrix basis_toMatrix_mul_linearMap_toMatrix

variable [Fintype ι]

/- warning: linear_map_to_matrix_mul_basis_to_matrix -> linearMap_toMatrix_mul_basis_toMatrix is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map_to_matrix_mul_basis_to_matrix linearMap_toMatrix_mul_basis_toMatrixₓ'. -/
@[simp]
theorem linearMap_toMatrix_mul_basis_toMatrix [DecidableEq ι] [DecidableEq ι'] :
    LinearMap.toMatrix b' c' f ⬝ b'.toMatrix b = LinearMap.toMatrix b c' f :=
  (Matrix.toLin b c').Injective
    (by rw [to_lin_to_matrix, to_lin_mul b b' c', to_lin_to_matrix, b'.to_lin_to_matrix, comp_id])
#align linear_map_to_matrix_mul_basis_to_matrix linearMap_toMatrix_mul_basis_toMatrix

/- warning: basis_to_matrix_mul_linear_map_to_matrix_mul_basis_to_matrix -> basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis_to_matrix_mul_linear_map_to_matrix_mul_basis_to_matrix basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrixₓ'. -/
theorem basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix [DecidableEq ι] [DecidableEq ι'] :
    c.toMatrix c' ⬝ LinearMap.toMatrix b' c' f ⬝ b'.toMatrix b = LinearMap.toMatrix b c f := by
  rw [basis_toMatrix_mul_linearMap_toMatrix, linearMap_toMatrix_mul_basis_toMatrix]
#align basis_to_matrix_mul_linear_map_to_matrix_mul_basis_to_matrix basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix

/- warning: basis_to_matrix_mul -> basis_toMatrix_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis_to_matrix_mul basis_toMatrix_mulₓ'. -/
theorem basis_toMatrix_mul [DecidableEq κ] (b₁ : Basis ι R M) (b₂ : Basis ι' R M) (b₃ : Basis κ R N)
    (A : Matrix ι' κ R) : b₁.toMatrix b₂ ⬝ A = LinearMap.toMatrix b₃ b₁ (toLin b₃ b₂ A) :=
  by
  have := basis_toMatrix_mul_linearMap_toMatrix b₃ b₁ b₂ (Matrix.toLin b₃ b₂ A)
  rwa [LinearMap.toMatrix_toLin] at this
#align basis_to_matrix_mul basis_toMatrix_mul

/- warning: mul_basis_to_matrix -> mul_basis_toMatrix is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mul_basis_to_matrix mul_basis_toMatrixₓ'. -/
theorem mul_basis_toMatrix [DecidableEq ι] [DecidableEq ι'] (b₁ : Basis ι R M) (b₂ : Basis ι' R M)
    (b₃ : Basis κ R N) (A : Matrix κ ι R) :
    A ⬝ b₁.toMatrix b₂ = LinearMap.toMatrix b₂ b₃ (toLin b₁ b₃ A) :=
  by
  have := linearMap_toMatrix_mul_basis_toMatrix b₂ b₁ b₃ (Matrix.toLin b₁ b₃ A)
  rwa [LinearMap.toMatrix_toLin] at this
#align mul_basis_to_matrix mul_basis_toMatrix

/- warning: basis_to_matrix_basis_fun_mul -> basis_toMatrix_basisFun_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis_to_matrix_basis_fun_mul basis_toMatrix_basisFun_mulₓ'. -/
theorem basis_toMatrix_basisFun_mul (b : Basis ι R (ι → R)) (A : Matrix ι ι R) :
    b.toMatrix (Pi.basisFun R ι) ⬝ A = of fun i j => b.repr (Aᵀ j) i := by
  classical
    simp only [basis_toMatrix_mul _ _ (Pi.basisFun R ι), Matrix.toLin_eq_toLin']
    ext (i j)
    rw [LinearMap.toMatrix_apply, Matrix.toLin'_apply, Pi.basisFun_apply,
      Matrix.mulVec_stdBasis_apply, Matrix.of_apply]
#align basis_to_matrix_basis_fun_mul basis_toMatrix_basisFun_mul

/- warning: linear_map.to_matrix_id_eq_basis_to_matrix -> LinearMap.toMatrix_id_eq_basis_toMatrix is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_id_eq_basis_to_matrix LinearMap.toMatrix_id_eq_basis_toMatrixₓ'. -/
/-- A generalization of `linear_map.to_matrix_id`. -/
@[simp]
theorem LinearMap.toMatrix_id_eq_basis_toMatrix [DecidableEq ι] :
    LinearMap.toMatrix b b' id = b'.toMatrix b :=
  by
  haveI := Classical.decEq ι'
  rw [← @basis_toMatrix_mul_linearMap_toMatrix _ _ ι, to_matrix_id, Matrix.mul_one]
#align linear_map.to_matrix_id_eq_basis_to_matrix LinearMap.toMatrix_id_eq_basis_toMatrix

/- warning: basis.to_matrix_reindex' -> Basis.toMatrix_reindex' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.to_matrix_reindex' Basis.toMatrix_reindex'ₓ'. -/
/-- See also `basis.to_matrix_reindex` which gives the `simp` normal form of this result. -/
theorem Basis.toMatrix_reindex' [DecidableEq ι] [DecidableEq ι'] (b : Basis ι R M) (v : ι' → M)
    (e : ι ≃ ι') : (b.reindex e).toMatrix v = Matrix.reindexAlgEquiv _ e (b.toMatrix (v ∘ e)) := by
  ext;
  simp only [Basis.toMatrix_apply, Basis.repr_reindex, Matrix.reindexAlgEquiv_apply,
    Matrix.reindex_apply, Matrix.submatrix_apply, Function.comp_apply, e.apply_symm_apply,
    Finsupp.mapDomain_equiv_apply]
#align basis.to_matrix_reindex' Basis.toMatrix_reindex'

end Fintype

/- warning: basis.to_matrix_mul_to_matrix -> Basis.toMatrix_mul_toMatrix is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {R : Type.{u3}} {M : Type.{u4}} [_inst_1 : CommSemiring.{u3} R] [_inst_2 : AddCommMonoid.{u4} M] [_inst_3 : Module.{u3, u4} R M (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2] (b : Basis.{u1, u3, u4} ι R M (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 _inst_3) (b' : Basis.{u2, u3, u4} ι' R M (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 _inst_3) {ι'' : Type.{u5}} [_inst_9 : Fintype.{u2} ι'] (b'' : ι'' -> M), Eq.{succ (max u1 u5 u3)} (Matrix.{u1, u5, u3} ι ι'' R) (Matrix.mul.{u3, u1, u2, u5} ι ι' ι'' R _inst_9 (Distrib.toHasMul.{u3} R (NonUnitalNonAssocSemiring.toDistrib.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1))))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)))) (Basis.toMatrix.{u1, u2, u3, u4} ι ι' R M _inst_1 _inst_2 _inst_3 b (coeFn.{max (succ u2) (succ u3) (succ u4), max (succ u2) (succ u4)} (Basis.{u2, u3, u4} ι' R M (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 _inst_3) (fun (_x : Basis.{u2, u3, u4} ι' R M (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 _inst_3) => ι' -> M) (FunLike.hasCoeToFun.{max (succ u2) (succ u3) (succ u4), succ u2, succ u4} (Basis.{u2, u3, u4} ι' R M (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 _inst_3) ι' (fun (_x : ι') => M) (Basis.funLike.{u2, u3, u4} ι' R M (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 _inst_3)) b')) (Basis.toMatrix.{u2, u5, u3, u4} ι' ι'' R M _inst_1 _inst_2 _inst_3 b' b'')) (Basis.toMatrix.{u1, u5, u3, u4} ι ι'' R M _inst_1 _inst_2 _inst_3 b b'')
but is expected to have type
  forall {ι : Type.{u3}} {ι' : Type.{u4}} {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] [_inst_2 : AddCommMonoid.{u1} M] [_inst_3 : Module.{u2, u1} R M (CommSemiring.toSemiring.{u2} R _inst_1) _inst_2] (b : Basis.{u3, u2, u1} ι R M (CommSemiring.toSemiring.{u2} R _inst_1) _inst_2 _inst_3) (b' : Basis.{u4, u2, u1} ι' R M (CommSemiring.toSemiring.{u2} R _inst_1) _inst_2 _inst_3) {ι'' : Type.{u5}} [_inst_9 : Fintype.{u4} ι'] (b'' : ι'' -> M), Eq.{max (max (succ u3) (succ u2)) (succ u5)} (Matrix.{u3, u5, u2} ι ι'' R) (Matrix.mul.{u2, u3, u4, u5} ι ι' ι'' R _inst_9 (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (Basis.toMatrix.{u3, u4, u2, u1} ι ι' R M _inst_1 _inst_2 _inst_3 b (FunLike.coe.{max (max (succ u4) (succ u2)) (succ u1), succ u4, succ u1} (Basis.{u4, u2, u1} ι' R M (CommSemiring.toSemiring.{u2} R _inst_1) _inst_2 _inst_3) ι' (fun (_x : ι') => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι') => M) _x) (Basis.funLike.{u4, u2, u1} ι' R M (CommSemiring.toSemiring.{u2} R _inst_1) _inst_2 _inst_3) b')) (Basis.toMatrix.{u4, u5, u2, u1} ι' ι'' R M _inst_1 _inst_2 _inst_3 b' b'')) (Basis.toMatrix.{u3, u5, u2, u1} ι ι'' R M _inst_1 _inst_2 _inst_3 b b'')
Case conversion may be inaccurate. Consider using '#align basis.to_matrix_mul_to_matrix Basis.toMatrix_mul_toMatrixₓ'. -/
/-- A generalization of `basis.to_matrix_self`, in the opposite direction. -/
@[simp]
theorem Basis.toMatrix_mul_toMatrix {ι'' : Type _} [Fintype ι'] (b'' : ι'' → M) :
    b.toMatrix b' ⬝ b'.toMatrix b'' = b.toMatrix b'' :=
  by
  have := Classical.decEq ι
  have := Classical.decEq ι'
  haveI := Classical.decEq ι''
  ext (i j)
  simp only [Matrix.mul_apply, Basis.toMatrix_apply, Basis.sum_repr_mul_repr]
#align basis.to_matrix_mul_to_matrix Basis.toMatrix_mul_toMatrix

/- warning: basis.to_matrix_mul_to_matrix_flip -> Basis.toMatrix_mul_toMatrix_flip is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {R : Type.{u3}} {M : Type.{u4}} [_inst_1 : CommSemiring.{u3} R] [_inst_2 : AddCommMonoid.{u4} M] [_inst_3 : Module.{u3, u4} R M (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2] (b : Basis.{u1, u3, u4} ι R M (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 _inst_3) (b' : Basis.{u2, u3, u4} ι' R M (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 _inst_3) [_inst_9 : DecidableEq.{succ u1} ι] [_inst_10 : Fintype.{u2} ι'], Eq.{succ (max u1 u3)} (Matrix.{u1, u1, u3} ι ι R) (Matrix.mul.{u3, u1, u2, u1} ι ι' ι R _inst_10 (Distrib.toHasMul.{u3} R (NonUnitalNonAssocSemiring.toDistrib.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1))))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)))) (Basis.toMatrix.{u1, u2, u3, u4} ι ι' R M _inst_1 _inst_2 _inst_3 b (coeFn.{max (succ u2) (succ u3) (succ u4), max (succ u2) (succ u4)} (Basis.{u2, u3, u4} ι' R M (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 _inst_3) (fun (_x : Basis.{u2, u3, u4} ι' R M (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 _inst_3) => ι' -> M) (FunLike.hasCoeToFun.{max (succ u2) (succ u3) (succ u4), succ u2, succ u4} (Basis.{u2, u3, u4} ι' R M (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 _inst_3) ι' (fun (_x : ι') => M) (Basis.funLike.{u2, u3, u4} ι' R M (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 _inst_3)) b')) (Basis.toMatrix.{u2, u1, u3, u4} ι' ι R M _inst_1 _inst_2 _inst_3 b' (coeFn.{max (succ u1) (succ u3) (succ u4), max (succ u1) (succ u4)} (Basis.{u1, u3, u4} ι R M (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 _inst_3) (fun (_x : Basis.{u1, u3, u4} ι R M (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 _inst_3) => ι -> M) (FunLike.hasCoeToFun.{max (succ u1) (succ u3) (succ u4), succ u1, succ u4} (Basis.{u1, u3, u4} ι R M (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 _inst_3) ι (fun (_x : ι) => M) (Basis.funLike.{u1, u3, u4} ι R M (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 _inst_3)) b))) (OfNat.ofNat.{max u1 u3} (Matrix.{u1, u1, u3} ι ι R) 1 (OfNat.mk.{max u1 u3} (Matrix.{u1, u1, u3} ι ι R) 1 (One.one.{max u1 u3} (Matrix.{u1, u1, u3} ι ι R) (Matrix.hasOne.{u3, u1} ι R (fun (a : ι) (b : ι) => _inst_9 a b) (MulZeroClass.toHasZero.{u3} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1))))) (AddMonoidWithOne.toOne.{u3} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} R (NonAssocSemiring.toAddCommMonoidWithOne.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)))))))))
but is expected to have type
  forall {ι : Type.{u4}} {ι' : Type.{u3}} {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] [_inst_2 : AddCommMonoid.{u1} M] [_inst_3 : Module.{u2, u1} R M (CommSemiring.toSemiring.{u2} R _inst_1) _inst_2] (b : Basis.{u4, u2, u1} ι R M (CommSemiring.toSemiring.{u2} R _inst_1) _inst_2 _inst_3) (b' : Basis.{u3, u2, u1} ι' R M (CommSemiring.toSemiring.{u2} R _inst_1) _inst_2 _inst_3) [_inst_9 : DecidableEq.{succ u4} ι] [_inst_10 : Fintype.{u3} ι'], Eq.{max (succ u4) (succ u2)} (Matrix.{u4, u4, u2} ι ι R) (Matrix.mul.{u2, u4, u3, u4} ι ι' ι R _inst_10 (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (Basis.toMatrix.{u4, u3, u2, u1} ι ι' R M _inst_1 _inst_2 _inst_3 b (FunLike.coe.{max (max (succ u3) (succ u2)) (succ u1), succ u3, succ u1} (Basis.{u3, u2, u1} ι' R M (CommSemiring.toSemiring.{u2} R _inst_1) _inst_2 _inst_3) ι' (fun (_x : ι') => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι') => M) _x) (Basis.funLike.{u3, u2, u1} ι' R M (CommSemiring.toSemiring.{u2} R _inst_1) _inst_2 _inst_3) b')) (Basis.toMatrix.{u3, u4, u2, u1} ι' ι R M _inst_1 _inst_2 _inst_3 b' (FunLike.coe.{max (max (succ u4) (succ u2)) (succ u1), succ u4, succ u1} (Basis.{u4, u2, u1} ι R M (CommSemiring.toSemiring.{u2} R _inst_1) _inst_2 _inst_3) ι (fun (_x : ι) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) _x) (Basis.funLike.{u4, u2, u1} ι R M (CommSemiring.toSemiring.{u2} R _inst_1) _inst_2 _inst_3) b))) (OfNat.ofNat.{max u4 u2} (Matrix.{u4, u4, u2} ι ι R) 1 (One.toOfNat1.{max u4 u2} (Matrix.{u4, u4, u2} ι ι R) (Matrix.one.{u2, u4} ι R (fun (a : ι) (b : ι) => _inst_9 a b) (CommMonoidWithZero.toZero.{u2} R (CommSemiring.toCommMonoidWithZero.{u2} R _inst_1)) (Semiring.toOne.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align basis.to_matrix_mul_to_matrix_flip Basis.toMatrix_mul_toMatrix_flipₓ'. -/
/-- `b.to_matrix b'` and `b'.to_matrix b` are inverses. -/
theorem Basis.toMatrix_mul_toMatrix_flip [DecidableEq ι] [Fintype ι'] :
    b.toMatrix b' ⬝ b'.toMatrix b = 1 := by rw [Basis.toMatrix_mul_toMatrix, Basis.toMatrix_self]
#align basis.to_matrix_mul_to_matrix_flip Basis.toMatrix_mul_toMatrix_flip

/- warning: basis.invertible_to_matrix -> Basis.invertibleToMatrix is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R₂ : Type.{u2}} {M₂ : Type.{u3}} [_inst_4 : CommRing.{u2} R₂] [_inst_5 : AddCommGroup.{u3} M₂] [_inst_6 : Module.{u2, u3} R₂ M₂ (Ring.toSemiring.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_5)] [_inst_9 : DecidableEq.{succ u1} ι] [_inst_10 : Fintype.{u1} ι] (b : Basis.{u1, u2, u3} ι R₂ M₂ (Ring.toSemiring.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_5) _inst_6) (b' : Basis.{u1, u2, u3} ι R₂ M₂ (Ring.toSemiring.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_5) _inst_6), Invertible.{max u1 u2} (Matrix.{u1, u1, u2} ι ι R₂) (Matrix.hasMul.{u2, u1} ι R₂ _inst_10 (Distrib.toHasMul.{u2} R₂ (Ring.toDistrib.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4))) (AddCommGroup.toAddCommMonoid.{u2} R₂ (NonUnitalNonAssocRing.toAddCommGroup.{u2} R₂ (NonAssocRing.toNonUnitalNonAssocRing.{u2} R₂ (Ring.toNonAssocRing.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4)))))) (Matrix.hasOne.{u2, u1} ι R₂ (fun (a : ι) (b : ι) => _inst_9 a b) (MulZeroClass.toHasZero.{u2} R₂ (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R₂ (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R₂ (NonAssocRing.toNonUnitalNonAssocRing.{u2} R₂ (Ring.toNonAssocRing.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4)))))) (AddMonoidWithOne.toOne.{u2} R₂ (AddGroupWithOne.toAddMonoidWithOne.{u2} R₂ (AddCommGroupWithOne.toAddGroupWithOne.{u2} R₂ (Ring.toAddCommGroupWithOne.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4)))))) (Basis.toMatrix.{u1, u1, u2, u3} ι ι R₂ M₂ (CommRing.toCommSemiring.{u2} R₂ _inst_4) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_5) _inst_6 b (coeFn.{max (succ u1) (succ u2) (succ u3), max (succ u1) (succ u3)} (Basis.{u1, u2, u3} ι R₂ M₂ (Ring.toSemiring.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_5) _inst_6) (fun (_x : Basis.{u1, u2, u3} ι R₂ M₂ (Ring.toSemiring.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_5) _inst_6) => ι -> M₂) (FunLike.hasCoeToFun.{max (succ u1) (succ u2) (succ u3), succ u1, succ u3} (Basis.{u1, u2, u3} ι R₂ M₂ (Ring.toSemiring.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_5) _inst_6) ι (fun (_x : ι) => M₂) (Basis.funLike.{u1, u2, u3} ι R₂ M₂ (Ring.toSemiring.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_5) _inst_6)) b'))
but is expected to have type
  forall {ι : Type.{u1}} {R₂ : Type.{u2}} {M₂ : Type.{u3}} [_inst_4 : CommRing.{u2} R₂] [_inst_5 : AddCommGroup.{u3} M₂] [_inst_6 : Module.{u2, u3} R₂ M₂ (CommSemiring.toSemiring.{u2} R₂ (CommRing.toCommSemiring.{u2} R₂ _inst_4)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_5)] [_inst_9 : DecidableEq.{succ u1} ι] [_inst_10 : Fintype.{u1} ι] (b : Basis.{u1, u2, u3} ι R₂ M₂ (CommSemiring.toSemiring.{u2} R₂ (CommRing.toCommSemiring.{u2} R₂ _inst_4)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_5) _inst_6) (b' : Basis.{u1, u2, u3} ι R₂ M₂ (CommSemiring.toSemiring.{u2} R₂ (CommRing.toCommSemiring.{u2} R₂ _inst_4)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_5) _inst_6), Invertible.{max u1 u2} (Matrix.{u1, u1, u2} ι ι R₂) (Matrix.instMulMatrix.{u2, u1} ι R₂ _inst_10 (NonUnitalNonAssocRing.toMul.{u2} R₂ (NonAssocRing.toNonUnitalNonAssocRing.{u2} R₂ (Ring.toNonAssocRing.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R₂ (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R₂ (NonAssocRing.toNonUnitalNonAssocRing.{u2} R₂ (Ring.toNonAssocRing.{u2} R₂ (CommRing.toRing.{u2} R₂ _inst_4)))))) (Matrix.one.{u2, u1} ι R₂ (fun (a : ι) (b : ι) => _inst_9 a b) (CommMonoidWithZero.toZero.{u2} R₂ (CommSemiring.toCommMonoidWithZero.{u2} R₂ (CommRing.toCommSemiring.{u2} R₂ _inst_4))) (Semiring.toOne.{u2} R₂ (CommSemiring.toSemiring.{u2} R₂ (CommRing.toCommSemiring.{u2} R₂ _inst_4)))) (Basis.toMatrix.{u1, u1, u2, u3} ι ι R₂ M₂ (CommRing.toCommSemiring.{u2} R₂ _inst_4) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_5) _inst_6 b (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u3), succ u1, succ u3} (Basis.{u1, u2, u3} ι R₂ M₂ (CommSemiring.toSemiring.{u2} R₂ (CommRing.toCommSemiring.{u2} R₂ _inst_4)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_5) _inst_6) ι (fun (_x : ι) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M₂) _x) (Basis.funLike.{u1, u2, u3} ι R₂ M₂ (CommSemiring.toSemiring.{u2} R₂ (CommRing.toCommSemiring.{u2} R₂ _inst_4)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_5) _inst_6) b'))
Case conversion may be inaccurate. Consider using '#align basis.invertible_to_matrix Basis.invertibleToMatrixₓ'. -/
/-- A matrix whose columns form a basis `b'`, expressed w.r.t. a basis `b`, is invertible. -/
def Basis.invertibleToMatrix [DecidableEq ι] [Fintype ι] (b b' : Basis ι R₂ M₂) :
    Invertible (b.toMatrix b') :=
  ⟨b'.toMatrix b, Basis.toMatrix_mul_toMatrix_flip _ _, Basis.toMatrix_mul_toMatrix_flip _ _⟩
#align basis.invertible_to_matrix Basis.invertibleToMatrix

/- warning: basis.to_matrix_reindex -> Basis.toMatrix_reindex is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {R : Type.{u3}} {M : Type.{u4}} [_inst_1 : CommSemiring.{u3} R] [_inst_2 : AddCommMonoid.{u4} M] [_inst_3 : Module.{u3, u4} R M (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2] (b : Basis.{u1, u3, u4} ι R M (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 _inst_3) (v : ι' -> M) (e : Equiv.{succ u1, succ u2} ι ι'), Eq.{succ (max u2 u3)} (Matrix.{u2, u2, u3} ι' ι' R) (Basis.toMatrix.{u2, u2, u3, u4} ι' ι' R M _inst_1 _inst_2 _inst_3 (Basis.reindex.{u1, u2, u3, u4} ι ι' R M (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 _inst_3 b e) v) (Matrix.submatrix.{u3, u2, u1, u2, u2} ι' ι ι' ι' R (Basis.toMatrix.{u1, u2, u3, u4} ι ι' R M _inst_1 _inst_2 _inst_3 b v) (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} ι' ι) (fun (_x : Equiv.{succ u2, succ u1} ι' ι) => ι' -> ι) (Equiv.hasCoeToFun.{succ u2, succ u1} ι' ι) (Equiv.symm.{succ u1, succ u2} ι ι' e)) (id.{succ u2} ι'))
but is expected to have type
  forall {ι : Type.{u4}} {ι' : Type.{u1}} {R : Type.{u3}} {M : Type.{u2}} [_inst_1 : CommSemiring.{u3} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : Module.{u3, u2} R M (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2] (b : Basis.{u4, u3, u2} ι R M (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 _inst_3) (v : ι' -> M) (e : Equiv.{succ u4, succ u1} ι ι'), Eq.{max (succ u1) (succ u3)} (Matrix.{u1, u1, u3} ι' ι' R) (Basis.toMatrix.{u1, u1, u3, u2} ι' ι' R M _inst_1 _inst_2 _inst_3 (Basis.reindex.{u4, u1, u3, u2} ι ι' R M (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 _inst_3 b e) v) (Matrix.submatrix.{u3, u1, u4, u1, u1} ι' ι ι' ι' R (Basis.toMatrix.{u4, u1, u3, u2} ι ι' R M _inst_1 _inst_2 _inst_3 b v) (FunLike.coe.{max (succ u4) (succ u1), succ u1, succ u4} (Equiv.{succ u1, succ u4} ι' ι) ι' (fun (_x : ι') => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : ι') => ι) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u4} ι' ι) (Equiv.symm.{succ u4, succ u1} ι ι' e)) (id.{succ u1} ι'))
Case conversion may be inaccurate. Consider using '#align basis.to_matrix_reindex Basis.toMatrix_reindexₓ'. -/
@[simp]
theorem Basis.toMatrix_reindex (b : Basis ι R M) (v : ι' → M) (e : ι ≃ ι') :
    (b.reindex e).toMatrix v = (b.toMatrix v).submatrix e.symm id := by ext;
  simp only [Basis.toMatrix_apply, Basis.repr_reindex, Matrix.submatrix_apply, id.def,
    Finsupp.mapDomain_equiv_apply]
#align basis.to_matrix_reindex Basis.toMatrix_reindex

/- warning: basis.to_matrix_map -> Basis.toMatrix_map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.to_matrix_map Basis.toMatrix_mapₓ'. -/
@[simp]
theorem Basis.toMatrix_map (b : Basis ι R M) (f : M ≃ₗ[R] N) (v : ι → N) :
    (b.map f).toMatrix v = b.toMatrix (f.symm ∘ v) := by ext;
  simp only [Basis.toMatrix_apply, Basis.map, LinearEquiv.trans_apply]
#align basis.to_matrix_map Basis.toMatrix_map

end MulLinearMapToMatrix

end BasisToMatrix

