/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck

! This file was ported from Lean 3 source module linear_algebra.matrix.general_linear_group
! leanprover-community/mathlib commit a87d22575d946e1e156fc1edd1e1269600a8a282
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.GeneralLinearGroup
import Mathbin.LinearAlgebra.Matrix.NonsingularInverse
import Mathbin.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# The General Linear group $GL(n, R)$

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the elements of the General Linear group `general_linear_group n R`,
consisting of all invertible `n` by `n` `R`-matrices.

## Main definitions

* `matrix.general_linear_group` is the type of matrices over R which are units in the matrix ring.
* `matrix.GL_pos` gives the subgroup of matrices with
  positive determinant (over a linear ordered ring).

## Tags

matrix group, group, matrix inverse
-/


namespace Matrix

universe u v

open Matrix

open LinearMap

-- disable this instance so we do not accidentally use it in lemmas.
attribute [-instance] special_linear_group.has_coe_to_fun

#print Matrix.GeneralLinearGroup /-
/-- `GL n R` is the group of `n` by `n` `R`-matrices with unit determinant.
Defined as a subtype of matrices-/
abbrev GeneralLinearGroup (n : Type u) (R : Type v) [DecidableEq n] [Fintype n] [CommRing R] :
    Type _ :=
  (Matrix n n R)ˣ
#align matrix.general_linear_group Matrix.GeneralLinearGroup
-/

-- mathport name: exprGL
notation "GL" => GeneralLinearGroup

namespace GeneralLinearGroup

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

/- warning: matrix.general_linear_group.det -> Matrix.GeneralLinearGroup.det is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Fintype.{u1} n] {R : Type.{u2}} [_inst_3 : CommRing.{u2} R], MonoidHom.{max u1 u2, u2} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Units.{u2} R (Ring.toMonoid.{u2} R (CommRing.toRing.{u2} R _inst_3))) (Units.mulOneClass.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Ring.toMonoid.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.ring.{u2, u1} n R _inst_2 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_1 a b) a b) (CommRing.toRing.{u2} R _inst_3)))) (Units.mulOneClass.{u2} R (Ring.toMonoid.{u2} R (CommRing.toRing.{u2} R _inst_3)))
but is expected to have type
  forall {n : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Fintype.{u1} n] {R : Type.{u2}} [_inst_3 : CommRing.{u2} R], MonoidHom.{max u2 u1, u2} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Units.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3))))) (Units.instMulOneClassUnits.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (MonoidWithZero.toMonoid.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Semiring.toMonoidWithZero.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.semiring.{u2, u1} n R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3)) _inst_2 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_1 a b) a b))))) (Units.instMulOneClassUnits.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3)))))
Case conversion may be inaccurate. Consider using '#align matrix.general_linear_group.det Matrix.GeneralLinearGroup.detₓ'. -/
/-- The determinant of a unit matrix is itself a unit. -/
@[simps]
def det : GL n R →* Rˣ
    where
  toFun A :=
    { val := (↑A : Matrix n n R).det
      inv := (↑A⁻¹ : Matrix n n R).det
      val_inv := by rw [← det_mul, ← mul_eq_mul, A.mul_inv, det_one]
      inv_val := by rw [← det_mul, ← mul_eq_mul, A.inv_mul, det_one] }
  map_one' := Units.ext det_one
  map_mul' A B := Units.ext <| det_mul _ _
#align matrix.general_linear_group.det Matrix.GeneralLinearGroup.det

/- warning: matrix.general_linear_group.to_lin -> Matrix.GeneralLinearGroup.toLin is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.general_linear_group.to_lin Matrix.GeneralLinearGroup.toLinₓ'. -/
/-- The `GL n R` and `general_linear_group R n` groups are multiplicatively equivalent-/
def toLin : GL n R ≃* LinearMap.GeneralLinearGroup R (n → R) :=
  Units.mapEquiv toLinAlgEquiv'.toMulEquiv
#align matrix.general_linear_group.to_lin Matrix.GeneralLinearGroup.toLin

/- warning: matrix.general_linear_group.mk' -> Matrix.GeneralLinearGroup.mk' is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Fintype.{u1} n] {R : Type.{u2}} [_inst_3 : CommRing.{u2} R] (A : Matrix.{u1, u1, u2} n n R), (Invertible.{u2} R (Distrib.toHasMul.{u2} R (Ring.toDistrib.{u2} R (CommRing.toRing.{u2} R _inst_3))) (AddMonoidWithOne.toOne.{u2} R (AddGroupWithOne.toAddMonoidWithOne.{u2} R (AddCommGroupWithOne.toAddGroupWithOne.{u2} R (Ring.toAddCommGroupWithOne.{u2} R (CommRing.toRing.{u2} R _inst_3))))) (Matrix.det.{u2, u1} n (fun (a : n) (b : n) => _inst_1 a b) _inst_2 R _inst_3 A)) -> (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3)
but is expected to have type
  forall {n : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Fintype.{u1} n] {R : Type.{u2}} [_inst_3 : CommRing.{u2} R] (A : Matrix.{u1, u1, u2} n n R), (Invertible.{u2} R (NonUnitalNonAssocRing.toMul.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_3)))) (Semiring.toOne.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3))) (Matrix.det.{u2, u1} n (fun (a : n) (b : n) => _inst_1 a b) _inst_2 R _inst_3 A)) -> (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3)
Case conversion may be inaccurate. Consider using '#align matrix.general_linear_group.mk' Matrix.GeneralLinearGroup.mk'ₓ'. -/
/-- Given a matrix with invertible determinant we get an element of `GL n R`-/
def mk' (A : Matrix n n R) (h : Invertible (Matrix.det A)) : GL n R :=
  unitOfDetInvertible A
#align matrix.general_linear_group.mk' Matrix.GeneralLinearGroup.mk'

/- warning: matrix.general_linear_group.mk'' -> Matrix.GeneralLinearGroup.mk'' is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Fintype.{u1} n] {R : Type.{u2}} [_inst_3 : CommRing.{u2} R] (A : Matrix.{u1, u1, u2} n n R), (IsUnit.{u2} R (Ring.toMonoid.{u2} R (CommRing.toRing.{u2} R _inst_3)) (Matrix.det.{u2, u1} n (fun (a : n) (b : n) => _inst_1 a b) _inst_2 R _inst_3 A)) -> (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3)
but is expected to have type
  forall {n : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Fintype.{u1} n] {R : Type.{u2}} [_inst_3 : CommRing.{u2} R] (A : Matrix.{u1, u1, u2} n n R), (IsUnit.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3)))) (Matrix.det.{u2, u1} n (fun (a : n) (b : n) => _inst_1 a b) _inst_2 R _inst_3 A)) -> (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3)
Case conversion may be inaccurate. Consider using '#align matrix.general_linear_group.mk'' Matrix.GeneralLinearGroup.mk''ₓ'. -/
/-- Given a matrix with unit determinant we get an element of `GL n R`-/
noncomputable def mk'' (A : Matrix n n R) (h : IsUnit (Matrix.det A)) : GL n R :=
  nonsingInvUnit A h
#align matrix.general_linear_group.mk'' Matrix.GeneralLinearGroup.mk''

/- warning: matrix.general_linear_group.mk_of_det_ne_zero -> Matrix.GeneralLinearGroup.mkOfDetNeZero is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Fintype.{u1} n] {K : Type.{u2}} [_inst_4 : Field.{u2} K] (A : Matrix.{u1, u1, u2} n n K), (Ne.{succ u2} K (Matrix.det.{u2, u1} n (fun (a : n) (b : n) => _inst_1 a b) _inst_2 K (EuclideanDomain.toCommRing.{u2} K (Field.toEuclideanDomain.{u2} K _inst_4)) A) (OfNat.ofNat.{u2} K 0 (OfNat.mk.{u2} K 0 (Zero.zero.{u2} K (MulZeroClass.toHasZero.{u2} K (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} K (NonAssocRing.toNonUnitalNonAssocRing.{u2} K (Ring.toNonAssocRing.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_4))))))))))) -> (Matrix.GeneralLinearGroup.{u1, u2} n K (fun (a : n) (b : n) => _inst_1 a b) _inst_2 (EuclideanDomain.toCommRing.{u2} K (Field.toEuclideanDomain.{u2} K _inst_4)))
but is expected to have type
  forall {n : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Fintype.{u1} n] {K : Type.{u2}} [_inst_4 : Field.{u2} K] (A : Matrix.{u1, u1, u2} n n K), (Ne.{succ u2} K (Matrix.det.{u2, u1} n (fun (a : n) (b : n) => _inst_1 a b) _inst_2 K (EuclideanDomain.toCommRing.{u2} K (Field.toEuclideanDomain.{u2} K _inst_4)) A) (OfNat.ofNat.{u2} K 0 (Zero.toOfNat0.{u2} K (CommMonoidWithZero.toZero.{u2} K (CommGroupWithZero.toCommMonoidWithZero.{u2} K (Semifield.toCommGroupWithZero.{u2} K (Field.toSemifield.{u2} K _inst_4))))))) -> (Matrix.GeneralLinearGroup.{u1, u2} n K (fun (a : n) (b : n) => _inst_1 a b) _inst_2 (EuclideanDomain.toCommRing.{u2} K (Field.toEuclideanDomain.{u2} K _inst_4)))
Case conversion may be inaccurate. Consider using '#align matrix.general_linear_group.mk_of_det_ne_zero Matrix.GeneralLinearGroup.mkOfDetNeZeroₓ'. -/
/-- Given a matrix with non-zero determinant over a field, we get an element of `GL n K`-/
def mkOfDetNeZero {K : Type _} [Field K] (A : Matrix n n K) (h : Matrix.det A ≠ 0) : GL n K :=
  mk' A (invertibleOfNonzero h)
#align matrix.general_linear_group.mk_of_det_ne_zero Matrix.GeneralLinearGroup.mkOfDetNeZero

#print Matrix.GeneralLinearGroup.ext_iff /-
theorem ext_iff (A B : GL n R) : A = B ↔ ∀ i j, (A : Matrix n n R) i j = (B : Matrix n n R) i j :=
  Units.ext_iff.trans Matrix.ext_iff.symm
#align matrix.general_linear_group.ext_iff Matrix.GeneralLinearGroup.ext_iff
-/

#print Matrix.GeneralLinearGroup.ext /-
/-- Not marked `@[ext]` as the `ext` tactic already solves this. -/
theorem ext ⦃A B : GL n R⦄ (h : ∀ i j, (A : Matrix n n R) i j = (B : Matrix n n R) i j) : A = B :=
  Units.ext <| Matrix.ext h
#align matrix.general_linear_group.ext Matrix.GeneralLinearGroup.ext
-/

section CoeLemmas

variable (A B : GL n R)

/- warning: matrix.general_linear_group.coe_mul -> Matrix.GeneralLinearGroup.coe_mul is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Fintype.{u1} n] {R : Type.{u2}} [_inst_3 : CommRing.{u2} R] (A : Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (B : Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3), Eq.{succ (max u1 u2)} (Matrix.{u1, u1, u2} n n R) ((fun (a : Type.{max u1 u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ (max u1 u2), succ (max u1 u2)} a b] => self.0) (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Matrix.{u1, u1, u2} n n R) (HasLiftT.mk.{succ (max u1 u2), succ (max u1 u2)} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Matrix.{u1, u1, u2} n n R) (CoeTCₓ.coe.{succ (max u1 u2), succ (max u1 u2)} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Matrix.{u1, u1, u2} n n R) (coeBase.{succ (max u1 u2), succ (max u1 u2)} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Matrix.{u1, u1, u2} n n R) (Units.hasCoe.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Ring.toMonoid.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.ring.{u2, u1} n R _inst_2 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_1 a b) a b) (CommRing.toRing.{u2} R _inst_3))))))) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (instHMul.{max u1 u2} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (MulOneClass.toHasMul.{max u1 u2} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Units.mulOneClass.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Ring.toMonoid.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.ring.{u2, u1} n R _inst_2 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_1 a b) a b) (CommRing.toRing.{u2} R _inst_3)))))) A B)) (Matrix.mul.{u2, u1, u1, u1} n n n R _inst_2 (Distrib.toHasMul.{u2} R (Ring.toDistrib.{u2} R (CommRing.toRing.{u2} R _inst_3))) (AddCommGroup.toAddCommMonoid.{u2} R (NonUnitalNonAssocRing.toAddCommGroup.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_3))))) ((fun (a : Type.{max u1 u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ (max u1 u2), succ (max u1 u2)} a b] => self.0) (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Matrix.{u1, u1, u2} n n R) (HasLiftT.mk.{succ (max u1 u2), succ (max u1 u2)} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Matrix.{u1, u1, u2} n n R) (CoeTCₓ.coe.{succ (max u1 u2), succ (max u1 u2)} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Matrix.{u1, u1, u2} n n R) (coeBase.{succ (max u1 u2), succ (max u1 u2)} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Matrix.{u1, u1, u2} n n R) (Units.hasCoe.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Ring.toMonoid.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.ring.{u2, u1} n R _inst_2 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_1 a b) a b) (CommRing.toRing.{u2} R _inst_3))))))) A) ((fun (a : Type.{max u1 u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ (max u1 u2), succ (max u1 u2)} a b] => self.0) (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Matrix.{u1, u1, u2} n n R) (HasLiftT.mk.{succ (max u1 u2), succ (max u1 u2)} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Matrix.{u1, u1, u2} n n R) (CoeTCₓ.coe.{succ (max u1 u2), succ (max u1 u2)} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Matrix.{u1, u1, u2} n n R) (coeBase.{succ (max u1 u2), succ (max u1 u2)} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Matrix.{u1, u1, u2} n n R) (Units.hasCoe.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Ring.toMonoid.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.ring.{u2, u1} n R _inst_2 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_1 a b) a b) (CommRing.toRing.{u2} R _inst_3))))))) B))
but is expected to have type
  forall {n : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Fintype.{u1} n] {R : Type.{u2}} [_inst_3 : CommRing.{u2} R] (A : Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (B : Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3), Eq.{max (succ u1) (succ u2)} (Matrix.{u1, u1, u2} n n R) (Units.val.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (MonoidWithZero.toMonoid.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Semiring.toMonoidWithZero.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.semiring.{u2, u1} n R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3)) _inst_2 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_1 a b) a b)))) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (instHMul.{max u1 u2} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (MulOneClass.toMul.{max u1 u2} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Units.instMulOneClassUnits.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (MonoidWithZero.toMonoid.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Semiring.toMonoidWithZero.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.semiring.{u2, u1} n R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3)) _inst_2 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_1 a b) a b))))))) A B)) (Matrix.mul.{u2, u1, u1, u1} n n n R _inst_2 (NonUnitalNonAssocRing.toMul.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_3)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_3))))) (Units.val.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (MonoidWithZero.toMonoid.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Semiring.toMonoidWithZero.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.semiring.{u2, u1} n R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3)) _inst_2 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_1 a b) a b)))) A) (Units.val.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (MonoidWithZero.toMonoid.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Semiring.toMonoidWithZero.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.semiring.{u2, u1} n R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3)) _inst_2 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_1 a b) a b)))) B))
Case conversion may be inaccurate. Consider using '#align matrix.general_linear_group.coe_mul Matrix.GeneralLinearGroup.coe_mulₓ'. -/
@[simp]
theorem coe_mul : ↑(A * B) = (↑A : Matrix n n R) ⬝ (↑B : Matrix n n R) :=
  rfl
#align matrix.general_linear_group.coe_mul Matrix.GeneralLinearGroup.coe_mul

/- warning: matrix.general_linear_group.coe_one -> Matrix.GeneralLinearGroup.coe_one is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Fintype.{u1} n] {R : Type.{u2}} [_inst_3 : CommRing.{u2} R], Eq.{succ (max u1 u2)} (Matrix.{u1, u1, u2} n n R) ((fun (a : Type.{max u1 u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ (max u1 u2), succ (max u1 u2)} a b] => self.0) (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Matrix.{u1, u1, u2} n n R) (HasLiftT.mk.{succ (max u1 u2), succ (max u1 u2)} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Matrix.{u1, u1, u2} n n R) (CoeTCₓ.coe.{succ (max u1 u2), succ (max u1 u2)} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Matrix.{u1, u1, u2} n n R) (coeBase.{succ (max u1 u2), succ (max u1 u2)} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Matrix.{u1, u1, u2} n n R) (Units.hasCoe.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Ring.toMonoid.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.ring.{u2, u1} n R _inst_2 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_1 a b) a b) (CommRing.toRing.{u2} R _inst_3))))))) (OfNat.ofNat.{max u1 u2} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) 1 (OfNat.mk.{max u1 u2} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) 1 (One.one.{max u1 u2} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (MulOneClass.toHasOne.{max u1 u2} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Units.mulOneClass.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Ring.toMonoid.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.ring.{u2, u1} n R _inst_2 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_1 a b) a b) (CommRing.toRing.{u2} R _inst_3))))))))) (OfNat.ofNat.{max u1 u2} (Matrix.{u1, u1, u2} n n R) 1 (OfNat.mk.{max u1 u2} (Matrix.{u1, u1, u2} n n R) 1 (One.one.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.hasOne.{u2, u1} n R (fun (a : n) (b : n) => _inst_1 a b) (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_3)))))) (AddMonoidWithOne.toOne.{u2} R (AddGroupWithOne.toAddMonoidWithOne.{u2} R (AddCommGroupWithOne.toAddGroupWithOne.{u2} R (Ring.toAddCommGroupWithOne.{u2} R (CommRing.toRing.{u2} R _inst_3)))))))))
but is expected to have type
  forall {n : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Fintype.{u1} n] {R : Type.{u2}} [_inst_3 : CommRing.{u2} R], Eq.{max (succ u1) (succ u2)} (Matrix.{u1, u1, u2} n n R) (Units.val.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (MonoidWithZero.toMonoid.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Semiring.toMonoidWithZero.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.semiring.{u2, u1} n R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3)) _inst_2 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_1 a b) a b)))) (OfNat.ofNat.{max u1 u2} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) 1 (One.toOfNat1.{max u1 u2} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (InvOneClass.toOne.{max u1 u2} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (DivInvOneMonoid.toInvOneClass.{max u1 u2} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (DivisionMonoid.toDivInvOneMonoid.{max u1 u2} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Group.toDivisionMonoid.{max u1 u2} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Units.instGroupUnits.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (MonoidWithZero.toMonoid.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Semiring.toMonoidWithZero.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.semiring.{u2, u1} n R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3)) _inst_2 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_1 a b) a b)))))))))))) (OfNat.ofNat.{max u1 u2} (Matrix.{u1, u1, u2} n n R) 1 (One.toOfNat1.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.one.{u2, u1} n R (fun (a : n) (b : n) => _inst_1 a b) (CommMonoidWithZero.toZero.{u2} R (CommSemiring.toCommMonoidWithZero.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3))) (Semiring.toOne.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3))))))
Case conversion may be inaccurate. Consider using '#align matrix.general_linear_group.coe_one Matrix.GeneralLinearGroup.coe_oneₓ'. -/
@[simp]
theorem coe_one : ↑(1 : GL n R) = (1 : Matrix n n R) :=
  rfl
#align matrix.general_linear_group.coe_one Matrix.GeneralLinearGroup.coe_one

/- warning: matrix.general_linear_group.coe_inv -> Matrix.GeneralLinearGroup.coe_inv is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Fintype.{u1} n] {R : Type.{u2}} [_inst_3 : CommRing.{u2} R] (A : Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3), Eq.{succ (max u1 u2)} (Matrix.{u1, u1, u2} n n R) ((fun (a : Type.{max u1 u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ (max u1 u2), succ (max u1 u2)} a b] => self.0) (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Matrix.{u1, u1, u2} n n R) (HasLiftT.mk.{succ (max u1 u2), succ (max u1 u2)} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Matrix.{u1, u1, u2} n n R) (CoeTCₓ.coe.{succ (max u1 u2), succ (max u1 u2)} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Matrix.{u1, u1, u2} n n R) (coeBase.{succ (max u1 u2), succ (max u1 u2)} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Matrix.{u1, u1, u2} n n R) (Units.hasCoe.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Ring.toMonoid.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.ring.{u2, u1} n R _inst_2 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_1 a b) a b) (CommRing.toRing.{u2} R _inst_3))))))) (Inv.inv.{max u1 u2} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Units.hasInv.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Ring.toMonoid.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.ring.{u2, u1} n R _inst_2 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_1 a b) a b) (CommRing.toRing.{u2} R _inst_3)))) A)) (Inv.inv.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.hasInv.{u1, u2} n R _inst_2 (fun (a : n) (b : n) => _inst_1 a b) _inst_3) ((fun (a : Type.{max u1 u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ (max u1 u2), succ (max u1 u2)} a b] => self.0) (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Matrix.{u1, u1, u2} n n R) (HasLiftT.mk.{succ (max u1 u2), succ (max u1 u2)} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Matrix.{u1, u1, u2} n n R) (CoeTCₓ.coe.{succ (max u1 u2), succ (max u1 u2)} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Matrix.{u1, u1, u2} n n R) (coeBase.{succ (max u1 u2), succ (max u1 u2)} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Matrix.{u1, u1, u2} n n R) (Units.hasCoe.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Ring.toMonoid.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.ring.{u2, u1} n R _inst_2 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_1 a b) a b) (CommRing.toRing.{u2} R _inst_3))))))) A))
but is expected to have type
  forall {n : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Fintype.{u1} n] {R : Type.{u2}} [_inst_3 : CommRing.{u2} R] (A : Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3), Eq.{max (succ u1) (succ u2)} (Matrix.{u1, u1, u2} n n R) (Units.val.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (MonoidWithZero.toMonoid.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Semiring.toMonoidWithZero.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.semiring.{u2, u1} n R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3)) _inst_2 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_1 a b) a b)))) (Inv.inv.{max u1 u2} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (Units.instInv.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (MonoidWithZero.toMonoid.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Semiring.toMonoidWithZero.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.semiring.{u2, u1} n R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3)) _inst_2 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_1 a b) a b))))) A)) (Inv.inv.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.inv.{u1, u2} n R _inst_2 (fun (a : n) (b : n) => _inst_1 a b) _inst_3) (Units.val.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (MonoidWithZero.toMonoid.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Semiring.toMonoidWithZero.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.semiring.{u2, u1} n R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3)) _inst_2 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_1 a b) a b)))) A))
Case conversion may be inaccurate. Consider using '#align matrix.general_linear_group.coe_inv Matrix.GeneralLinearGroup.coe_invₓ'. -/
theorem coe_inv : ↑A⁻¹ = (↑A : Matrix n n R)⁻¹ :=
  letI := A.invertible
  inv_of_eq_nonsing_inv (↑A : Matrix n n R)
#align matrix.general_linear_group.coe_inv Matrix.GeneralLinearGroup.coe_inv

/- warning: matrix.general_linear_group.to_linear -> Matrix.GeneralLinearGroup.toLinear is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.general_linear_group.to_linear Matrix.GeneralLinearGroup.toLinearₓ'. -/
/-- An element of the matrix general linear group on `(n) [fintype n]` can be considered as an
element of the endomorphism general linear group on `n → R`. -/
def toLinear : GeneralLinearGroup n R ≃* LinearMap.GeneralLinearGroup R (n → R) :=
  Units.mapEquiv Matrix.toLinAlgEquiv'.toRingEquiv.toMulEquiv
#align matrix.general_linear_group.to_linear Matrix.GeneralLinearGroup.toLinear

/- warning: matrix.general_linear_group.coe_to_linear -> Matrix.GeneralLinearGroup.coe_toLinear is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.general_linear_group.coe_to_linear Matrix.GeneralLinearGroup.coe_toLinearₓ'. -/
-- Note that without the `@` and `‹_›`, lean infers `λ a b, _inst a b` instead of `_inst` as the
-- decidability argument, which prevents `simp` from obtaining the instance by unification.
-- These `λ a b, _inst a b` terms also appear in the type of `A`, but simp doesn't get confused by
-- them so for now we do not care.
@[simp]
theorem coe_toLinear : (@toLinear n ‹_› ‹_› _ _ A : (n → R) →ₗ[R] n → R) = Matrix.mulVecLin A :=
  rfl
#align matrix.general_linear_group.coe_to_linear Matrix.GeneralLinearGroup.coe_toLinear

/- warning: matrix.general_linear_group.to_linear_apply -> Matrix.GeneralLinearGroup.toLinear_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.general_linear_group.to_linear_apply Matrix.GeneralLinearGroup.toLinear_applyₓ'. -/
@[simp]
theorem toLinear_apply (v : n → R) : (@toLinear n ‹_› ‹_› _ _ A) v = Matrix.mulVecLin (↑A) v :=
  rfl
#align matrix.general_linear_group.to_linear_apply Matrix.GeneralLinearGroup.toLinear_apply

end CoeLemmas

end GeneralLinearGroup

namespace SpecialLinearGroup

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

#print Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup /-
instance hasCoeToGeneralLinearGroup : Coe (SpecialLinearGroup n R) (GL n R) :=
  ⟨fun A => ⟨↑A, ↑A⁻¹, congr_arg coe (mul_right_inv A), congr_arg coe (mul_left_inv A)⟩⟩
#align matrix.special_linear_group.has_coe_to_general_linear_group Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
-/

/- warning: matrix.special_linear_group.coe_to_GL_det -> Matrix.SpecialLinearGroup.coeToGL_det is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.special_linear_group.coe_to_GL_det Matrix.SpecialLinearGroup.coeToGL_detₓ'. -/
@[simp]
theorem coeToGL_det (g : SpecialLinearGroup n R) : (g : GL n R).det = 1 :=
  Units.ext g.Prop
#align matrix.special_linear_group.coe_to_GL_det Matrix.SpecialLinearGroup.coeToGL_det

end SpecialLinearGroup

section

variable {n : Type u} {R : Type v} [DecidableEq n] [Fintype n] [LinearOrderedCommRing R]

section

variable (n R)

/- warning: matrix.GL_pos -> Matrix.GLPos is a dubious translation:
lean 3 declaration is
  forall (n : Type.{u1}) (R : Type.{u2}) [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Fintype.{u1} n] [_inst_3 : LinearOrderedCommRing.{u2} R], Subgroup.{max u1 u2} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 (StrictOrderedCommRing.toCommRing.{u2} R (LinearOrderedCommRing.toStrictOrderedCommRing.{u2} R _inst_3))) (Units.group.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Ring.toMonoid.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.ring.{u2, u1} n R _inst_2 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_1 a b) a b) (CommRing.toRing.{u2} R (StrictOrderedCommRing.toCommRing.{u2} R (LinearOrderedCommRing.toStrictOrderedCommRing.{u2} R _inst_3))))))
but is expected to have type
  forall (n : Type.{u1}) (R : Type.{u2}) [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Fintype.{u1} n] [_inst_3 : LinearOrderedCommRing.{u2} R], Subgroup.{max u2 u1} (Matrix.GeneralLinearGroup.{u1, u2} n R (fun (a : n) (b : n) => _inst_1 a b) _inst_2 (StrictOrderedCommRing.toCommRing.{u2} R (LinearOrderedCommRing.toStrictOrderedCommRing.{u2} R _inst_3))) (Units.instGroupUnits.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (MonoidWithZero.toMonoid.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Semiring.toMonoidWithZero.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.semiring.{u2, u1} n R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R (StrictOrderedCommRing.toCommRing.{u2} R (LinearOrderedCommRing.toStrictOrderedCommRing.{u2} R _inst_3)))) _inst_2 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_1 a b) a b)))))
Case conversion may be inaccurate. Consider using '#align matrix.GL_pos Matrix.GLPosₓ'. -/
/-- This is the subgroup of `nxn` matrices with entries over a
linear ordered ring and positive determinant. -/
def GLPos : Subgroup (GL n R) :=
  (Units.posSubgroup R).comap GeneralLinearGroup.det
#align matrix.GL_pos Matrix.GLPos

end

/- warning: matrix.mem_GL_pos -> Matrix.mem_glpos is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.mem_GL_pos Matrix.mem_glposₓ'. -/
@[simp]
theorem mem_glpos (A : GL n R) : A ∈ GLPos n R ↔ 0 < (A.det : R) :=
  Iff.rfl
#align matrix.mem_GL_pos Matrix.mem_glpos

/- warning: matrix.GL_pos.det_ne_zero -> Matrix.GLPos.det_ne_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.GL_pos.det_ne_zero Matrix.GLPos.det_ne_zeroₓ'. -/
theorem GLPos.det_ne_zero (A : GLPos n R) : (A : Matrix n n R).det ≠ 0 :=
  ne_of_gt A.Prop
#align matrix.GL_pos.det_ne_zero Matrix.GLPos.det_ne_zero

end

section Neg

variable {n : Type u} {R : Type v} [DecidableEq n] [Fintype n] [LinearOrderedCommRing R]
  [Fact (Even (Fintype.card n))]

/-- Formal operation of negation on general linear group on even cardinality `n` given by negating
each element. -/
instance : Neg (GLPos n R) :=
  ⟨fun g =>
    ⟨-g,
      by
      rw [mem_GL_pos, general_linear_group.coe_det_apply, Units.val_neg, det_neg,
        (Fact.out <| Even <| Fintype.card n).neg_one_pow, one_mul]
      exact g.prop⟩⟩

/- warning: matrix.GL_pos.coe_neg_GL -> Matrix.GLPos.coe_neg_GL is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.GL_pos.coe_neg_GL Matrix.GLPos.coe_neg_GLₓ'. -/
@[simp]
theorem GLPos.coe_neg_GL (g : GLPos n R) : ↑(-g) = -(g : GL n R) :=
  rfl
#align matrix.GL_pos.coe_neg_GL Matrix.GLPos.coe_neg_GL

/- warning: matrix.GL_pos.coe_neg -> Matrix.GLPos.coe_neg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.GL_pos.coe_neg Matrix.GLPos.coe_negₓ'. -/
@[simp]
theorem GLPos.coe_neg (g : GLPos n R) : ↑(-g) = -(g : Matrix n n R) :=
  rfl
#align matrix.GL_pos.coe_neg Matrix.GLPos.coe_neg

/- warning: matrix.GL_pos.coe_neg_apply -> Matrix.GLPos.coe_neg_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.GL_pos.coe_neg_apply Matrix.GLPos.coe_neg_applyₓ'. -/
@[simp]
theorem GLPos.coe_neg_apply (g : GLPos n R) (i j : n) :
    (↑(-g) : Matrix n n R) i j = -(↑g : Matrix n n R) i j :=
  rfl
#align matrix.GL_pos.coe_neg_apply Matrix.GLPos.coe_neg_apply

instance : HasDistribNeg (GLPos n R) :=
  Subtype.coe_injective.HasDistribNeg _ GLPos.coe_neg_GL (GLPos n R).val_mul

end Neg

namespace SpecialLinearGroup

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [LinearOrderedCommRing R]

/- warning: matrix.special_linear_group.to_GL_pos -> Matrix.SpecialLinearGroup.toGLPos is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.special_linear_group.to_GL_pos Matrix.SpecialLinearGroup.toGLPosₓ'. -/
/-- `special_linear_group n R` embeds into `GL_pos n R` -/
def toGLPos : SpecialLinearGroup n R →* GLPos n R
    where
  toFun A := ⟨(A : GL n R), show 0 < (↑A : Matrix n n R).det from A.Prop.symm ▸ zero_lt_one⟩
  map_one' := Subtype.ext <| Units.ext <| rfl
  map_mul' A₁ A₂ := Subtype.ext <| Units.ext <| rfl
#align matrix.special_linear_group.to_GL_pos Matrix.SpecialLinearGroup.toGLPos

instance : Coe (SpecialLinearGroup n R) (GLPos n R) :=
  ⟨toGLPos⟩

/- warning: matrix.special_linear_group.coe_eq_to_GL_pos clashes with [anonymous] -> [anonymous]
warning: matrix.special_linear_group.coe_eq_to_GL_pos -> [anonymous] is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.special_linear_group.coe_eq_to_GL_pos [anonymous]ₓ'. -/
theorem [anonymous] : (coe : SpecialLinearGroup n R → GLPos n R) = toGLPos :=
  rfl
#align matrix.special_linear_group.coe_eq_to_GL_pos [anonymous]

/- warning: matrix.special_linear_group.to_GL_pos_injective -> Matrix.SpecialLinearGroup.toGLPos_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.special_linear_group.to_GL_pos_injective Matrix.SpecialLinearGroup.toGLPos_injectiveₓ'. -/
theorem toGLPos_injective : Function.Injective (toGLPos : SpecialLinearGroup n R → GLPos n R) :=
  (show Function.Injective ((coe : GLPos n R → Matrix n n R) ∘ toGLPos) from
      Subtype.coe_injective).of_comp
#align matrix.special_linear_group.to_GL_pos_injective Matrix.SpecialLinearGroup.toGLPos_injective

/- warning: matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix -> Matrix.SpecialLinearGroup.coe_GLPos_coe_GL_coe_matrix is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix Matrix.SpecialLinearGroup.coe_GLPos_coe_GL_coe_matrixₓ'. -/
/-- Coercing a `special_linear_group` via `GL_pos` and `GL` is the same as coercing striaght to a
matrix. -/
@[simp]
theorem coe_GLPos_coe_GL_coe_matrix (g : SpecialLinearGroup n R) :
    (↑(↑(↑g : GLPos n R) : GL n R) : Matrix n n R) = ↑g :=
  rfl
#align matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix Matrix.SpecialLinearGroup.coe_GLPos_coe_GL_coe_matrix

/- warning: matrix.special_linear_group.coe_to_GL_pos_to_GL_det -> Matrix.SpecialLinearGroup.coe_to_GLPos_to_GL_det is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.special_linear_group.coe_to_GL_pos_to_GL_det Matrix.SpecialLinearGroup.coe_to_GLPos_to_GL_detₓ'. -/
@[simp]
theorem coe_to_GLPos_to_GL_det (g : SpecialLinearGroup n R) : ((g : GLPos n R) : GL n R).det = 1 :=
  Units.ext g.Prop
#align matrix.special_linear_group.coe_to_GL_pos_to_GL_det Matrix.SpecialLinearGroup.coe_to_GLPos_to_GL_det

variable [Fact (Even (Fintype.card n))]

/- warning: matrix.special_linear_group.coe_GL_pos_neg -> Matrix.SpecialLinearGroup.coe_GLPos_neg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.special_linear_group.coe_GL_pos_neg Matrix.SpecialLinearGroup.coe_GLPos_negₓ'. -/
@[norm_cast]
theorem coe_GLPos_neg (g : SpecialLinearGroup n R) : ↑(-g) = -(↑g : GLPos n R) :=
  Subtype.ext <| Units.ext rfl
#align matrix.special_linear_group.coe_GL_pos_neg Matrix.SpecialLinearGroup.coe_GLPos_neg

end SpecialLinearGroup

section Examples

/- warning: matrix.plane_conformal_matrix -> Matrix.planeConformalMatrix is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Field.{u1} R] (a : R) (b : R), (Ne.{succ u1} R (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R _inst_1))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R _inst_1))))) a (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R _inst_1))))) b (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R _inst_1))))))))))) -> (Matrix.GeneralLinearGroup.{0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (b : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (EuclideanDomain.toCommRing.{u1} R (Field.toEuclideanDomain.{u1} R _inst_1)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Field.{u1} R] (a : R) (b : R), (Ne.{succ u1} R (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R _inst_1)))))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (DivisionSemiring.toSemiring.{u1} R (Semifield.toDivisionSemiring.{u1} R (Field.toSemifield.{u1} R _inst_1))))))) a (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (DivisionSemiring.toSemiring.{u1} R (Semifield.toDivisionSemiring.{u1} R (Field.toSemifield.{u1} R _inst_1))))))) b (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommGroupWithZero.toCommMonoidWithZero.{u1} R (Semifield.toCommGroupWithZero.{u1} R (Field.toSemifield.{u1} R _inst_1))))))) -> (Matrix.GeneralLinearGroup.{0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) R (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (b : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => instDecidableEqFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (EuclideanDomain.toCommRing.{u1} R (Field.toEuclideanDomain.{u1} R _inst_1)))
Case conversion may be inaccurate. Consider using '#align matrix.plane_conformal_matrix Matrix.planeConformalMatrixₓ'. -/
/-- The matrix [a, -b; b, a] (inspired by multiplication by a complex number); it is an element of
$GL_2(R)$ if `a ^ 2 + b ^ 2` is nonzero. -/
@[simps (config := { fullyApplied := false }) coe]
def planeConformalMatrix {R} [Field R] (a b : R) (hab : a ^ 2 + b ^ 2 ≠ 0) :
    Matrix.GeneralLinearGroup (Fin 2) R :=
  GeneralLinearGroup.mkOfDetNeZero !![a, -b; b, a] (by simpa [det_fin_two, sq] using hab)
#align matrix.plane_conformal_matrix Matrix.planeConformalMatrix

/- TODO: Add Iwasawa matrices `n_x=!![1,x; 0,1]`, `a_t=!![exp(t/2),0;0,exp(-t/2)]` and
  `k_θ=!![cos θ, sin θ; -sin θ, cos θ]`
-/
end Examples

namespace GeneralLinearGroup

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

-- this section should be last to ensure we do not use it in lemmas
section CoeFnInstance

/-- This instance is here for convenience, but is not the simp-normal form. -/
instance : CoeFun (GL n R) fun _ => n → n → R where coe A := A.val

@[simp]
theorem coeFn_eq_coe (A : GL n R) : ⇑A = (↑A : Matrix n n R) :=
  rfl
#align matrix.general_linear_group.coe_fn_eq_coe Matrix.GeneralLinearGroup.coeFn_eq_coe

end CoeFnInstance

end GeneralLinearGroup

end Matrix

