/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module linear_algebra.matrix.special_linear_group
! leanprover-community/mathlib commit 61db041ab8e4aaf8cb5c7dc10a7d4ff261997536
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.GeneralLinearGroup
import Mathbin.LinearAlgebra.Matrix.Adjugate
import Mathbin.LinearAlgebra.Matrix.ToLin

/-!
# The Special Linear group $SL(n, R)$

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the elements of the Special Linear group `special_linear_group n R`, consisting
of all square `R`-matrices with determinant `1` on the fintype `n` by `n`.  In addition, we define
the group structure on `special_linear_group n R` and the embedding into the general linear group
`general_linear_group R (n → R)`.

## Main definitions

 * `matrix.special_linear_group` is the type of matrices with determinant 1
 * `matrix.special_linear_group.group` gives the group structure (under multiplication)
 * `matrix.special_linear_group.to_GL` is the embedding `SLₙ(R) → GLₙ(R)`

## Notation

For `m : ℕ`, we introduce the notation `SL(m,R)` for the special linear group on the fintype
`n = fin m`, in the locale `matrix_groups`.

## Implementation notes
The inverse operation in the `special_linear_group` is defined to be the adjugate
matrix, so that `special_linear_group n R` has a group structure for all `comm_ring R`.

We define the elements of `special_linear_group` to be matrices, since we need to
compute their determinant. This is in contrast with `general_linear_group R M`,
which consists of invertible `R`-linear maps on `M`.

We provide `matrix.special_linear_group.has_coe_to_fun` for convenience, but do not state any
lemmas about it, and use `matrix.special_linear_group.coe_fn_eq_coe` to eliminate it `⇑` in favor
of a regular `↑` coercion.

## References

 * https://en.wikipedia.org/wiki/Special_linear_group

## Tags

matrix group, group, matrix inverse
-/


namespace Matrix

universe u v

open Matrix

open LinearMap

section

variable (n : Type u) [DecidableEq n] [Fintype n] (R : Type v) [CommRing R]

#print Matrix.SpecialLinearGroup /-
/-- `special_linear_group n R` is the group of `n` by `n` `R`-matrices with determinant equal to 1.
-/
def SpecialLinearGroup :=
  { A : Matrix n n R // A.det = 1 }
#align matrix.special_linear_group Matrix.SpecialLinearGroup
-/

end

-- mathport name: special_linear_group.fin
scoped[MatrixGroups] notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

namespace SpecialLinearGroup

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

#print Matrix.SpecialLinearGroup.hasCoeToMatrix /-
instance hasCoeToMatrix : Coe (SpecialLinearGroup n R) (Matrix n n R) :=
  ⟨fun A => A.val⟩
#align matrix.special_linear_group.has_coe_to_matrix Matrix.SpecialLinearGroup.hasCoeToMatrix
-/

-- mathport name: «expr↑ₘ »
/- In this file, Lean often has a hard time working out the values of `n` and `R` for an expression
like `det ↑A`. Rather than writing `(A : matrix n n R)` everywhere in this file which is annoyingly
verbose, or `A.val` which is not the simp-normal form for subtypes, we create a local notation
`↑ₘA`. This notation references the local `n` and `R` variables, so is not valid as a global
notation. -/
local prefix:1024 "↑ₘ" => @coe _ (Matrix n n R) _

#print Matrix.SpecialLinearGroup.ext_iff /-
theorem ext_iff (A B : SpecialLinearGroup n R) : A = B ↔ ∀ i j, ↑ₘA i j = ↑ₘB i j :=
  Subtype.ext_iff.trans Matrix.ext_iff.symm
#align matrix.special_linear_group.ext_iff Matrix.SpecialLinearGroup.ext_iff
-/

#print Matrix.SpecialLinearGroup.ext /-
@[ext]
theorem ext (A B : SpecialLinearGroup n R) : (∀ i j, ↑ₘA i j = ↑ₘB i j) → A = B :=
  (SpecialLinearGroup.ext_iff A B).mpr
#align matrix.special_linear_group.ext Matrix.SpecialLinearGroup.ext
-/

#print Matrix.SpecialLinearGroup.hasInv /-
instance hasInv : Inv (SpecialLinearGroup n R) :=
  ⟨fun A => ⟨adjugate A, by rw [det_adjugate, A.prop, one_pow]⟩⟩
#align matrix.special_linear_group.has_inv Matrix.SpecialLinearGroup.hasInv
-/

#print Matrix.SpecialLinearGroup.hasMul /-
instance hasMul : Mul (SpecialLinearGroup n R) :=
  ⟨fun A B => ⟨A.1 ⬝ B.1, by erw [det_mul, A.2, B.2, one_mul]⟩⟩
#align matrix.special_linear_group.has_mul Matrix.SpecialLinearGroup.hasMul
-/

#print Matrix.SpecialLinearGroup.hasOne /-
instance hasOne : One (SpecialLinearGroup n R) :=
  ⟨⟨1, det_one⟩⟩
#align matrix.special_linear_group.has_one Matrix.SpecialLinearGroup.hasOne
-/

instance : Pow (SpecialLinearGroup n R) ℕ
    where pow x n := ⟨x ^ n, (det_pow _ _).trans <| x.Prop.symm ▸ one_pow _⟩

instance : Inhabited (SpecialLinearGroup n R) :=
  ⟨1⟩

section CoeLemmas

variable (A B : SpecialLinearGroup n R)

/- warning: matrix.special_linear_group.coe_mk -> Matrix.SpecialLinearGroup.coe_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.special_linear_group.coe_mk Matrix.SpecialLinearGroup.coe_mkₓ'. -/
@[simp]
theorem coe_mk (A : Matrix n n R) (h : det A = 1) : ↑(⟨A, h⟩ : SpecialLinearGroup n R) = A :=
  rfl
#align matrix.special_linear_group.coe_mk Matrix.SpecialLinearGroup.coe_mk

#print Matrix.SpecialLinearGroup.coe_inv /-
@[simp]
theorem coe_inv : ↑ₘA⁻¹ = adjugate A :=
  rfl
#align matrix.special_linear_group.coe_inv Matrix.SpecialLinearGroup.coe_inv
-/

/- warning: matrix.special_linear_group.coe_mul -> Matrix.SpecialLinearGroup.coe_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.special_linear_group.coe_mul Matrix.SpecialLinearGroup.coe_mulₓ'. -/
@[simp]
theorem coe_mul : ↑ₘ(A * B) = ↑ₘA ⬝ ↑ₘB :=
  rfl
#align matrix.special_linear_group.coe_mul Matrix.SpecialLinearGroup.coe_mul

/- warning: matrix.special_linear_group.coe_one -> Matrix.SpecialLinearGroup.coe_one is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Fintype.{u1} n] {R : Type.{u2}} [_inst_3 : CommRing.{u2} R], Eq.{succ (max u1 u2)} (Matrix.{u1, u1, u2} n n R) ((fun (a : Type.{max u1 u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ (max u1 u2), succ (max u1 u2)} a b] => self.0) (Matrix.SpecialLinearGroup.{u1, u2} n (fun (a : n) (b : n) => _inst_1 a b) _inst_2 R _inst_3) (Matrix.{u1, u1, u2} n n R) (HasLiftT.mk.{succ (max u1 u2), succ (max u1 u2)} (Matrix.SpecialLinearGroup.{u1, u2} n (fun (a : n) (b : n) => _inst_1 a b) _inst_2 R _inst_3) (Matrix.{u1, u1, u2} n n R) (CoeTCₓ.coe.{succ (max u1 u2), succ (max u1 u2)} (Matrix.SpecialLinearGroup.{u1, u2} n (fun (a : n) (b : n) => _inst_1 a b) _inst_2 R _inst_3) (Matrix.{u1, u1, u2} n n R) (coeBase.{succ (max u1 u2), succ (max u1 u2)} (Matrix.SpecialLinearGroup.{u1, u2} n (fun (a : n) (b : n) => _inst_1 a b) _inst_2 R _inst_3) (Matrix.{u1, u1, u2} n n R) (Matrix.SpecialLinearGroup.hasCoeToMatrix.{u1, u2} n (fun (a : n) (b : n) => _inst_1 a b) _inst_2 R _inst_3)))) (OfNat.ofNat.{max u1 u2} (Matrix.SpecialLinearGroup.{u1, u2} n (fun (a : n) (b : n) => _inst_1 a b) _inst_2 R _inst_3) 1 (OfNat.mk.{max u1 u2} (Matrix.SpecialLinearGroup.{u1, u2} n (fun (a : n) (b : n) => _inst_1 a b) _inst_2 R _inst_3) 1 (One.one.{max u1 u2} (Matrix.SpecialLinearGroup.{u1, u2} n (fun (a : n) (b : n) => _inst_1 a b) _inst_2 R _inst_3) (Matrix.SpecialLinearGroup.hasOne.{u1, u2} n (fun (a : n) (b : n) => _inst_1 a b) _inst_2 R _inst_3))))) (OfNat.ofNat.{max u1 u2} (Matrix.{u1, u1, u2} n n R) 1 (OfNat.mk.{max u1 u2} (Matrix.{u1, u1, u2} n n R) 1 (One.one.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.hasOne.{u2, u1} n R (fun (a : n) (b : n) => _inst_1 a b) (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_3)))))) (AddMonoidWithOne.toOne.{u2} R (AddGroupWithOne.toAddMonoidWithOne.{u2} R (AddCommGroupWithOne.toAddGroupWithOne.{u2} R (Ring.toAddCommGroupWithOne.{u2} R (CommRing.toRing.{u2} R _inst_3)))))))))
but is expected to have type
  forall {n : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Fintype.{u1} n] {R : Type.{u2}} [_inst_3 : CommRing.{u2} R], Eq.{max (succ u1) (succ u2)} (Matrix.{u1, u1, u2} n n R) (Subtype.val.{max (succ u1) (succ u2)} (Matrix.{u1, u1, u2} n n R) (fun (A : Matrix.{u1, u1, u2} n n R) => Eq.{succ u2} R (Matrix.det.{u2, u1} n (fun (a : n) (b : n) => (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_1 a b) a b) a b) _inst_2 R _inst_3 A) (OfNat.ofNat.{u2} R 1 (One.toOfNat1.{u2} R (Semiring.toOne.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3)))))) (OfNat.ofNat.{max u1 u2} (Matrix.SpecialLinearGroup.{u1, u2} n (fun (a : n) (b : n) => _inst_1 a b) _inst_2 R _inst_3) 1 (One.toOfNat1.{max u1 u2} (Matrix.SpecialLinearGroup.{u1, u2} n (fun (a : n) (b : n) => _inst_1 a b) _inst_2 R _inst_3) (Matrix.SpecialLinearGroup.hasOne.{u1, u2} n (fun (a : n) (b : n) => _inst_1 a b) _inst_2 R _inst_3)))) (OfNat.ofNat.{max u1 u2} (Matrix.{u1, u1, u2} n n R) 1 (One.toOfNat1.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.one.{u2, u1} n R (fun (a : n) (b : n) => _inst_1 a b) (CommMonoidWithZero.toZero.{u2} R (CommSemiring.toCommMonoidWithZero.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3))) (Semiring.toOne.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3))))))
Case conversion may be inaccurate. Consider using '#align matrix.special_linear_group.coe_one Matrix.SpecialLinearGroup.coe_oneₓ'. -/
@[simp]
theorem coe_one : ↑ₘ(1 : SpecialLinearGroup n R) = (1 : Matrix n n R) :=
  rfl
#align matrix.special_linear_group.coe_one Matrix.SpecialLinearGroup.coe_one

/- warning: matrix.special_linear_group.det_coe -> Matrix.SpecialLinearGroup.det_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.special_linear_group.det_coe Matrix.SpecialLinearGroup.det_coeₓ'. -/
@[simp]
theorem det_coe : det ↑ₘA = 1 :=
  A.2
#align matrix.special_linear_group.det_coe Matrix.SpecialLinearGroup.det_coe

/- warning: matrix.special_linear_group.coe_pow -> Matrix.SpecialLinearGroup.coe_pow is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.special_linear_group.coe_pow Matrix.SpecialLinearGroup.coe_powₓ'. -/
@[simp]
theorem coe_pow (m : ℕ) : ↑ₘ(A ^ m) = ↑ₘA ^ m :=
  rfl
#align matrix.special_linear_group.coe_pow Matrix.SpecialLinearGroup.coe_pow

/- warning: matrix.special_linear_group.det_ne_zero -> Matrix.SpecialLinearGroup.det_ne_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.special_linear_group.det_ne_zero Matrix.SpecialLinearGroup.det_ne_zeroₓ'. -/
theorem det_ne_zero [Nontrivial R] (g : SpecialLinearGroup n R) : det ↑ₘg ≠ 0 :=
  by
  rw [g.det_coe]
  norm_num
#align matrix.special_linear_group.det_ne_zero Matrix.SpecialLinearGroup.det_ne_zero

/- warning: matrix.special_linear_group.row_ne_zero -> Matrix.SpecialLinearGroup.row_ne_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.special_linear_group.row_ne_zero Matrix.SpecialLinearGroup.row_ne_zeroₓ'. -/
theorem row_ne_zero [Nontrivial R] (g : SpecialLinearGroup n R) (i : n) : ↑ₘg i ≠ 0 := fun h =>
  g.det_ne_zero <| det_eq_zero_of_row_eq_zero i <| by simp [h]
#align matrix.special_linear_group.row_ne_zero Matrix.SpecialLinearGroup.row_ne_zero

end CoeLemmas

instance : Monoid (SpecialLinearGroup n R) :=
  Function.Injective.monoid coe Subtype.coe_injective coe_one coe_mul coe_pow

instance : Group (SpecialLinearGroup n R) :=
  { SpecialLinearGroup.monoid, SpecialLinearGroup.hasInv with
    mul_left_inv := fun A => by
      ext1
      simp [adjugate_mul] }

#print Matrix.SpecialLinearGroup.toLin' /-
/-- A version of `matrix.to_lin' A` that produces linear equivalences. -/
def toLin' : SpecialLinearGroup n R →* (n → R) ≃ₗ[R] n → R
    where
  toFun A :=
    LinearEquiv.ofLinear (Matrix.toLin' ↑ₘA) (Matrix.toLin' ↑ₘA⁻¹)
      (by rw [← to_lin'_mul, ← coe_mul, mul_right_inv, coe_one, to_lin'_one])
      (by rw [← to_lin'_mul, ← coe_mul, mul_left_inv, coe_one, to_lin'_one])
  map_one' := LinearEquiv.toLinearMap_injective Matrix.toLin'_one
  map_mul' A B := LinearEquiv.toLinearMap_injective <| Matrix.toLin'_mul A B
#align matrix.special_linear_group.to_lin' Matrix.SpecialLinearGroup.toLin'
-/

/- warning: matrix.special_linear_group.to_lin'_apply -> Matrix.SpecialLinearGroup.toLin'_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.special_linear_group.to_lin'_apply Matrix.SpecialLinearGroup.toLin'_applyₓ'. -/
theorem toLin'_apply (A : SpecialLinearGroup n R) (v : n → R) :
    SpecialLinearGroup.toLin' A v = Matrix.toLin' (↑ₘA) v :=
  rfl
#align matrix.special_linear_group.to_lin'_apply Matrix.SpecialLinearGroup.toLin'_apply

/- warning: matrix.special_linear_group.to_lin'_to_linear_map -> Matrix.SpecialLinearGroup.toLin'_to_linearMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.special_linear_group.to_lin'_to_linear_map Matrix.SpecialLinearGroup.toLin'_to_linearMapₓ'. -/
theorem toLin'_to_linearMap (A : SpecialLinearGroup n R) :
    ↑(SpecialLinearGroup.toLin' A) = Matrix.toLin' ↑ₘA :=
  rfl
#align matrix.special_linear_group.to_lin'_to_linear_map Matrix.SpecialLinearGroup.toLin'_to_linearMap

/- warning: matrix.special_linear_group.to_lin'_symm_apply -> Matrix.SpecialLinearGroup.toLin'_symm_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.special_linear_group.to_lin'_symm_apply Matrix.SpecialLinearGroup.toLin'_symm_applyₓ'. -/
theorem toLin'_symm_apply (A : SpecialLinearGroup n R) (v : n → R) :
    A.toLin'.symm v = Matrix.toLin' (↑ₘA⁻¹) v :=
  rfl
#align matrix.special_linear_group.to_lin'_symm_apply Matrix.SpecialLinearGroup.toLin'_symm_apply

/- warning: matrix.special_linear_group.to_lin'_symm_to_linear_map -> Matrix.SpecialLinearGroup.toLin'_symm_to_linearMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.special_linear_group.to_lin'_symm_to_linear_map Matrix.SpecialLinearGroup.toLin'_symm_to_linearMapₓ'. -/
theorem toLin'_symm_to_linearMap (A : SpecialLinearGroup n R) :
    ↑A.toLin'.symm = Matrix.toLin' ↑ₘA⁻¹ :=
  rfl
#align matrix.special_linear_group.to_lin'_symm_to_linear_map Matrix.SpecialLinearGroup.toLin'_symm_to_linearMap

/- warning: matrix.special_linear_group.to_lin'_injective -> Matrix.SpecialLinearGroup.toLin'_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.special_linear_group.to_lin'_injective Matrix.SpecialLinearGroup.toLin'_injectiveₓ'. -/
theorem toLin'_injective :
    Function.Injective ⇑(toLin' : SpecialLinearGroup n R →* (n → R) ≃ₗ[R] n → R) := fun A B h =>
  Subtype.coe_injective <| Matrix.toLin'.Injective <| LinearEquiv.toLinearMap_injective.eq_iff.mpr h
#align matrix.special_linear_group.to_lin'_injective Matrix.SpecialLinearGroup.toLin'_injective

/- warning: matrix.special_linear_group.to_GL -> Matrix.SpecialLinearGroup.toGL is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Fintype.{u1} n] {R : Type.{u2}} [_inst_3 : CommRing.{u2} R], MonoidHom.{max u1 u2, max u1 u2} (Matrix.SpecialLinearGroup.{u1, u2} n (fun (a : n) (b : n) => _inst_1 a b) _inst_2 R _inst_3) (LinearMap.GeneralLinearGroup.{u2, max u1 u2} R (n -> R) (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (Pi.addCommMonoid.{u1, u2} n (fun (ᾰ : n) => R) (fun (i : n) => AddCommGroup.toAddCommMonoid.{u2} R (NonUnitalNonAssocRing.toAddCommGroup.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_3)))))) (Pi.Function.module.{u1, u2, u2} n R R (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (AddCommGroup.toAddCommMonoid.{u2} R (NonUnitalNonAssocRing.toAddCommGroup.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_3))))) (Semiring.toModule.{u2} R (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3))))) (Monoid.toMulOneClass.{max u1 u2} (Matrix.SpecialLinearGroup.{u1, u2} n (fun (a : n) (b : n) => _inst_1 a b) _inst_2 R _inst_3) (Matrix.SpecialLinearGroup.monoid.{u1, u2} n (fun (a : n) (b : n) => _inst_1 a b) _inst_2 R _inst_3)) (Units.mulOneClass.{max u1 u2} (LinearMap.{u2, u2, max u1 u2, max u1 u2} R R (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)))) (n -> R) (n -> R) (Pi.addCommMonoid.{u1, u2} n (fun (ᾰ : n) => R) (fun (i : n) => AddCommGroup.toAddCommMonoid.{u2} R (NonUnitalNonAssocRing.toAddCommGroup.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_3)))))) (Pi.addCommMonoid.{u1, u2} n (fun (ᾰ : n) => R) (fun (i : n) => AddCommGroup.toAddCommMonoid.{u2} R (NonUnitalNonAssocRing.toAddCommGroup.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_3)))))) (Pi.Function.module.{u1, u2, u2} n R R (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (AddCommGroup.toAddCommMonoid.{u2} R (NonUnitalNonAssocRing.toAddCommGroup.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_3))))) (Semiring.toModule.{u2} R (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)))) (Pi.Function.module.{u1, u2, u2} n R R (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (AddCommGroup.toAddCommMonoid.{u2} R (NonUnitalNonAssocRing.toAddCommGroup.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_3))))) (Semiring.toModule.{u2} R (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3))))) (Module.End.monoid.{u2, max u1 u2} R (n -> R) (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (Pi.addCommMonoid.{u1, u2} n (fun (ᾰ : n) => R) (fun (i : n) => AddCommGroup.toAddCommMonoid.{u2} R (NonUnitalNonAssocRing.toAddCommGroup.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_3)))))) (Pi.Function.module.{u1, u2, u2} n R R (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (AddCommGroup.toAddCommMonoid.{u2} R (NonUnitalNonAssocRing.toAddCommGroup.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_3))))) (Semiring.toModule.{u2} R (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3))))))
but is expected to have type
  forall {n : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Fintype.{u1} n] {R : Type.{u2}} [_inst_3 : CommRing.{u2} R], MonoidHom.{max u2 u1, max u1 u2} (Matrix.SpecialLinearGroup.{u1, u2} n (fun (a : n) (b : n) => _inst_1 a b) _inst_2 R _inst_3) (LinearMap.GeneralLinearGroup.{u2, max u1 u2} R (n -> R) (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3)) (Pi.addCommMonoid.{u1, u2} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_3)))))) (Pi.module.{u1, u2, u2} n (fun (a._@.Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup._hyg.3925 : n) => R) R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3)) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_3))))) (fun (i : n) => Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3))))) (Monoid.toMulOneClass.{max u1 u2} (Matrix.SpecialLinearGroup.{u1, u2} n (fun (a : n) (b : n) => _inst_1 a b) _inst_2 R _inst_3) (Matrix.SpecialLinearGroup.monoid.{u1, u2} n (fun (a : n) (b : n) => _inst_1 a b) _inst_2 R _inst_3)) (Units.instMulOneClassUnits.{max u1 u2} (LinearMap.{u2, u2, max u1 u2, max u1 u2} R R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3)) (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3)) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3)))) (n -> R) (n -> R) (Pi.addCommMonoid.{u1, u2} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_3)))))) (Pi.addCommMonoid.{u1, u2} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_3)))))) (Pi.module.{u1, u2, u2} n (fun (a._@.Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup._hyg.3925 : n) => R) R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3)) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_3))))) (fun (i : n) => Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3)))) (Pi.module.{u1, u2, u2} n (fun (a._@.Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup._hyg.3925 : n) => R) R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3)) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_3))))) (fun (i : n) => Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3))))) (Module.End.monoid.{u2, max u1 u2} R (n -> R) (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3)) (Pi.addCommMonoid.{u1, u2} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_3)))))) (Pi.module.{u1, u2, u2} n (fun (a._@.Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup._hyg.3925 : n) => R) R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3)) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_3))))) (fun (i : n) => Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3))))))
Case conversion may be inaccurate. Consider using '#align matrix.special_linear_group.to_GL Matrix.SpecialLinearGroup.toGLₓ'. -/
/-- `to_GL` is the map from the special linear group to the general linear group -/
def toGL : SpecialLinearGroup n R →* GeneralLinearGroup R (n → R) :=
  (GeneralLinearGroup.generalLinearEquiv _ _).symm.toMonoidHom.comp toLin'
#align matrix.special_linear_group.to_GL Matrix.SpecialLinearGroup.toGL

/- warning: matrix.special_linear_group.coe_to_GL -> Matrix.SpecialLinearGroup.coe_toGL is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.special_linear_group.coe_to_GL Matrix.SpecialLinearGroup.coe_toGLₓ'. -/
theorem coe_toGL (A : SpecialLinearGroup n R) : ↑A.toGL = A.toLin'.toLinearMap :=
  rfl
#align matrix.special_linear_group.coe_to_GL Matrix.SpecialLinearGroup.coe_toGL

variable {S : Type _} [CommRing S]

#print Matrix.SpecialLinearGroup.map /-
/-- A ring homomorphism from `R` to `S` induces a group homomorphism from
`special_linear_group n R` to `special_linear_group n S`. -/
@[simps]
def map (f : R →+* S) : SpecialLinearGroup n R →* SpecialLinearGroup n S
    where
  toFun g :=
    ⟨f.mapMatrix ↑g, by
      rw [← f.map_det]
      simp [g.2]⟩
  map_one' := Subtype.ext <| f.mapMatrix.map_one
  map_mul' x y := Subtype.ext <| f.mapMatrix.map_mul x y
#align matrix.special_linear_group.map Matrix.SpecialLinearGroup.map
-/

section cast

/-- Coercion of SL `n` `ℤ` to SL `n` `R` for a commutative ring `R`. -/
instance : Coe (SpecialLinearGroup n ℤ) (SpecialLinearGroup n R) :=
  ⟨fun x => map (Int.castRingHom R) x⟩

/- warning: matrix.special_linear_group.coe_matrix_coe -> Matrix.SpecialLinearGroup.coe_matrix_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.special_linear_group.coe_matrix_coe Matrix.SpecialLinearGroup.coe_matrix_coeₓ'. -/
@[simp]
theorem coe_matrix_coe (g : SpecialLinearGroup n ℤ) :
    ↑(g : SpecialLinearGroup n R) = (↑g : Matrix n n ℤ).map (Int.castRingHom R) :=
  map_apply_coe (Int.castRingHom R) g
#align matrix.special_linear_group.coe_matrix_coe Matrix.SpecialLinearGroup.coe_matrix_coe

end cast

section Neg

variable [Fact (Even (Fintype.card n))]

/-- Formal operation of negation on special linear group on even cardinality `n` given by negating
each element. -/
instance : Neg (SpecialLinearGroup n R) :=
  ⟨fun g =>
    ⟨-g, by
      simpa [(Fact.out <| Even <| Fintype.card n).neg_one_pow, g.det_coe] using
        det_smul (↑ₘg) (-1)⟩⟩

/- warning: matrix.special_linear_group.coe_neg -> Matrix.SpecialLinearGroup.coe_neg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.special_linear_group.coe_neg Matrix.SpecialLinearGroup.coe_negₓ'. -/
@[simp]
theorem coe_neg (g : SpecialLinearGroup n R) : ↑(-g) = -(g : Matrix n n R) :=
  rfl
#align matrix.special_linear_group.coe_neg Matrix.SpecialLinearGroup.coe_neg

instance : HasDistribNeg (SpecialLinearGroup n R) :=
  Function.Injective.hasDistribNeg _ Subtype.coe_injective coe_neg coe_mul

/- warning: matrix.special_linear_group.coe_int_neg -> Matrix.SpecialLinearGroup.coe_int_neg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.special_linear_group.coe_int_neg Matrix.SpecialLinearGroup.coe_int_negₓ'. -/
@[simp]
theorem coe_int_neg (g : SpecialLinearGroup n ℤ) : ↑(-g) = (-↑g : SpecialLinearGroup n R) :=
  Subtype.ext <| (@RingHom.mapMatrix n _ _ _ _ _ _ (Int.castRingHom R)).map_neg ↑g
#align matrix.special_linear_group.coe_int_neg Matrix.SpecialLinearGroup.coe_int_neg

end Neg

section SpecialCases

/- warning: matrix.special_linear_group.SL2_inv_expl_det -> Matrix.SpecialLinearGroup.SL2_inv_expl_det is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.special_linear_group.SL2_inv_expl_det Matrix.SpecialLinearGroup.SL2_inv_expl_detₓ'. -/
theorem SL2_inv_expl_det (A : SL(2, R)) : det ![![A.1 1 1, -A.1 0 1], ![-A.1 1 0, A.1 0 0]] = 1 :=
  by
  rw [Matrix.det_fin_two, mul_comm]
  simp only [Subtype.val_eq_coe, cons_val_zero, cons_val_one, head_cons, mul_neg, neg_mul, neg_neg]
  have := A.2
  rw [Matrix.det_fin_two] at this
  convert this
#align matrix.special_linear_group.SL2_inv_expl_det Matrix.SpecialLinearGroup.SL2_inv_expl_det

#print Matrix.SpecialLinearGroup.SL2_inv_expl /-
theorem SL2_inv_expl (A : SL(2, R)) :
    A⁻¹ = ⟨![![A.1 1 1, -A.1 0 1], ![-A.1 1 0, A.1 0 0]], SL2_inv_expl_det A⟩ :=
  by
  ext
  have := Matrix.adjugate_fin_two A.1
  simp only [Subtype.val_eq_coe] at this
  rw [coe_inv, this]
  rfl
#align matrix.special_linear_group.SL2_inv_expl Matrix.SpecialLinearGroup.SL2_inv_expl
-/

/- warning: matrix.special_linear_group.fin_two_induction -> Matrix.SpecialLinearGroup.fin_two_induction is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.special_linear_group.fin_two_induction Matrix.SpecialLinearGroup.fin_two_inductionₓ'. -/
theorem fin_two_induction (P : SL(2, R) → Prop)
    (h : ∀ (a b c d : R) (hdet : a * d - b * c = 1), P ⟨!![a, b; c, d], by rwa [det_fin_two_of]⟩)
    (g : SL(2, R)) : P g := by
  obtain ⟨m, hm⟩ := g
  convert h (m 0 0) (m 0 1) (m 1 0) (m 1 1) (by rwa [det_fin_two] at hm)
  ext (i j); fin_cases i <;> fin_cases j <;> rfl
#align matrix.special_linear_group.fin_two_induction Matrix.SpecialLinearGroup.fin_two_induction

/- warning: matrix.special_linear_group.fin_two_exists_eq_mk_of_apply_zero_one_eq_zero -> Matrix.SpecialLinearGroup.fin_two_exists_eq_mk_of_apply_zero_one_eq_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.special_linear_group.fin_two_exists_eq_mk_of_apply_zero_one_eq_zero Matrix.SpecialLinearGroup.fin_two_exists_eq_mk_of_apply_zero_one_eq_zeroₓ'. -/
theorem fin_two_exists_eq_mk_of_apply_zero_one_eq_zero {R : Type _} [Field R] (g : SL(2, R))
    (hg : (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0) :
    ∃ (a b : R)(h : a ≠ 0), g = (⟨!![a, b; 0, a⁻¹], by simp [h]⟩ : SL(2, R)) :=
  by
  induction' g using Matrix.SpecialLinearGroup.fin_two_induction with a b c d h_det
  replace hg : c = 0 := by simpa using hg
  have had : a * d = 1 := by rwa [hg, MulZeroClass.mul_zero, sub_zero] at h_det
  refine' ⟨a, b, left_ne_zero_of_mul_eq_one had, _⟩
  simp_rw [eq_inv_of_mul_eq_one_right had, hg]
#align matrix.special_linear_group.fin_two_exists_eq_mk_of_apply_zero_one_eq_zero Matrix.SpecialLinearGroup.fin_two_exists_eq_mk_of_apply_zero_one_eq_zero

end SpecialCases

-- this section should be last to ensure we do not use it in lemmas
section CoeFnInstance

/-- This instance is here for convenience, but is not the simp-normal form. -/
instance : CoeFun (SpecialLinearGroup n R) fun _ => n → n → R where coe A := A.val

@[simp]
theorem coeFn_eq_coe (s : SpecialLinearGroup n R) : ⇑s = ↑ₘs :=
  rfl
#align matrix.special_linear_group.coe_fn_eq_coe Matrix.SpecialLinearGroup.coeFn_eq_coe

end CoeFnInstance

end SpecialLinearGroup

end Matrix

namespace ModularGroup

open MatrixGroups

open Matrix Matrix.SpecialLinearGroup

-- mathport name: «expr↑ₘ »
local prefix:1024 "↑ₘ" => @coe _ (Matrix (Fin 2) (Fin 2) ℤ) _

/- warning: modular_group.S -> ModularGroup.S is a dubious translation:
lean 3 declaration is
  Matrix.SpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (b : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) Int Int.commRing
but is expected to have type
  Matrix.SpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (b : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => instDecidableEqFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Int Int.instCommRingInt
Case conversion may be inaccurate. Consider using '#align modular_group.S ModularGroup.Sₓ'. -/
/-- The matrix `S = [[0, -1], [1, 0]]` as an element of `SL(2, ℤ)`.

This element acts naturally on the Euclidean plane as a rotation about the origin by `π / 2`.

This element also acts naturally on the hyperbolic plane as rotation about `i` by `π`. It
represents the Mobiüs transformation `z ↦ -1/z` and is an involutive elliptic isometry. -/
def S : SL(2, ℤ) :=
  ⟨!![0, -1; 1, 0], by norm_num [Matrix.det_fin_two_of] ⟩
#align modular_group.S ModularGroup.S

/- warning: modular_group.T -> ModularGroup.T is a dubious translation:
lean 3 declaration is
  Matrix.SpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (b : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) Int Int.commRing
but is expected to have type
  Matrix.SpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (b : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => instDecidableEqFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Int Int.instCommRingInt
Case conversion may be inaccurate. Consider using '#align modular_group.T ModularGroup.Tₓ'. -/
/-- The matrix `T = [[1, 1], [0, 1]]` as an element of `SL(2, ℤ)` -/
def T : SL(2, ℤ) :=
  ⟨!![1, 1; 0, 1], by norm_num [Matrix.det_fin_two_of] ⟩
#align modular_group.T ModularGroup.T

#print ModularGroup.coe_S /-
theorem coe_S : ↑ₘS = !![0, -1; 1, 0] :=
  rfl
#align modular_group.coe_S ModularGroup.coe_S
-/

#print ModularGroup.coe_T /-
theorem coe_T : ↑ₘT = !![1, 1; 0, 1] :=
  rfl
#align modular_group.coe_T ModularGroup.coe_T
-/

/- warning: modular_group.coe_T_inv -> ModularGroup.coe_T_inv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align modular_group.coe_T_inv ModularGroup.coe_T_invₓ'. -/
theorem coe_T_inv : ↑ₘT⁻¹ = !![1, -1; 0, 1] := by simp [coe_inv, coe_T, adjugate_fin_two]
#align modular_group.coe_T_inv ModularGroup.coe_T_inv

/- warning: modular_group.coe_T_zpow -> ModularGroup.coe_T_zpow is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align modular_group.coe_T_zpow ModularGroup.coe_T_zpowₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, ",", expr _, ";", expr _, ",", expr _, "]"] [])]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, ",", expr _, ";", expr _, ",", expr _, "]"] [])]] -/
theorem coe_T_zpow (n : ℤ) : ↑ₘ(T ^ n) = !![1, n; 0, 1] :=
  by
  induction' n using Int.induction_on with n h n h
  · rw [zpow_zero, coe_one, Matrix.one_fin_two]
  · simp_rw [zpow_add, zpow_one, coe_mul, h, coe_T, Matrix.mul_fin_two]
    trace
      "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \",\", expr _, \";\", expr _, \",\", expr _, \"]\"] [])]]"
    rw [mul_one, mul_one, add_comm]
  · simp_rw [zpow_sub, zpow_one, coe_mul, h, coe_T_inv, Matrix.mul_fin_two]
    trace
        "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \",\", expr _, \";\", expr _, \",\", expr _, \"]\"] [])]]" <;>
      ring
#align modular_group.coe_T_zpow ModularGroup.coe_T_zpow

/- warning: modular_group.T_pow_mul_apply_one -> ModularGroup.T_pow_mul_apply_one is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align modular_group.T_pow_mul_apply_one ModularGroup.T_pow_mul_apply_oneₓ'. -/
@[simp]
theorem T_pow_mul_apply_one (n : ℤ) (g : SL(2, ℤ)) : ↑ₘ(T ^ n * g) 1 = ↑ₘg 1 := by
  simp [coe_T_zpow, Matrix.mul, Matrix.dotProduct, Fin.sum_univ_succ]
#align modular_group.T_pow_mul_apply_one ModularGroup.T_pow_mul_apply_one

/- warning: modular_group.T_mul_apply_one -> ModularGroup.T_mul_apply_one is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align modular_group.T_mul_apply_one ModularGroup.T_mul_apply_oneₓ'. -/
@[simp]
theorem T_mul_apply_one (g : SL(2, ℤ)) : ↑ₘ(T * g) 1 = ↑ₘg 1 := by
  simpa using T_pow_mul_apply_one 1 g
#align modular_group.T_mul_apply_one ModularGroup.T_mul_apply_one

/- warning: modular_group.T_inv_mul_apply_one -> ModularGroup.T_inv_mul_apply_one is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align modular_group.T_inv_mul_apply_one ModularGroup.T_inv_mul_apply_oneₓ'. -/
@[simp]
theorem T_inv_mul_apply_one (g : SL(2, ℤ)) : ↑ₘ(T⁻¹ * g) 1 = ↑ₘg 1 := by
  simpa using T_pow_mul_apply_one (-1) g
#align modular_group.T_inv_mul_apply_one ModularGroup.T_inv_mul_apply_one

end ModularGroup

