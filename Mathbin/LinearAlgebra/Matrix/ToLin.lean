/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen

! This file was ported from Lean 3 source module linear_algebra.matrix.to_lin
! leanprover-community/mathlib commit f2b757fc5c341d88741b9c4630b1e8ba973c5726
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Matrix.Block
import Mathbin.Data.Matrix.Notation
import Mathbin.LinearAlgebra.StdBasis
import Mathbin.RingTheory.AlgebraTower
import Mathbin.Algebra.Module.Algebra
import Mathbin.Algebra.Algebra.Subalgebra.Tower

/-!
# Linear maps and matrices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the maps to send matrices to a linear map,
and to send linear maps between modules with a finite bases
to matrices. This defines a linear equivalence between linear maps
between finite-dimensional vector spaces and matrices indexed by
the respective bases.

## Main definitions

In the list below, and in all this file, `R` is a commutative ring (semiring
is sometimes enough), `M` and its variations are `R`-modules, `ι`, `κ`, `n` and `m` are finite
types used for indexing.

 * `linear_map.to_matrix`: given bases `v₁ : ι → M₁` and `v₂ : κ → M₂`,
   the `R`-linear equivalence from `M₁ →ₗ[R] M₂` to `matrix κ ι R`
 * `matrix.to_lin`: the inverse of `linear_map.to_matrix`
 * `linear_map.to_matrix'`: the `R`-linear equivalence from `(m → R) →ₗ[R] (n → R)`
   to `matrix m n R` (with the standard basis on `m → R` and `n → R`)
 * `matrix.to_lin'`: the inverse of `linear_map.to_matrix'`
 * `alg_equiv_matrix`: given a basis indexed by `n`, the `R`-algebra equivalence between
   `R`-endomorphisms of `M` and `matrix n n R`

## Issues

This file was originally written without attention to non-commutative rings,
and so mostly only works in the commutative setting. This should be fixed.

In particular, `matrix.mul_vec` gives us a linear equivalence
`matrix m n R ≃ₗ[R] (n → R) →ₗ[Rᵐᵒᵖ] (m → R)`
while `matrix.vec_mul` gives us a linear equivalence
`matrix m n R ≃ₗ[Rᵐᵒᵖ] (m → R) →ₗ[R] (n → R)`.
At present, the first equivalence is developed in detail but only for commutative rings
(and we omit the distinction between `Rᵐᵒᵖ` and `R`),
while the second equivalence is developed only in brief, but for not-necessarily-commutative rings.

Naming is slightly inconsistent between the two developments.
In the original (commutative) development `linear` is abbreviated to `lin`,
although this is not consistent with the rest of mathlib.
In the new (non-commutative) development `linear` is not abbreviated, and declarations use `_right`
to indicate they use the right action of matrices on vectors (via `matrix.vec_mul`).
When the two developments are made uniform, the names should be made uniform, too,
by choosing between `linear` and `lin` consistently,
and (presumably) adding `_left` where necessary.

## Tags

linear_map, matrix, linear_equiv, diagonal, det, trace
-/


noncomputable section

open LinearMap Matrix Set Submodule

open BigOperators

open Matrix

universe u v w

instance {n m} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (R) [Fintype R] :
    Fintype (Matrix m n R) := by unfold Matrix <;> infer_instance

section ToMatrixRight

variable {R : Type _} [Semiring R]

variable {l m n : Type _}

#print Matrix.vecMulLinear /-
/-- `matrix.vec_mul M` is a linear map. -/
@[simps]
def Matrix.vecMulLinear [Fintype m] (M : Matrix m n R) : (m → R) →ₗ[R] n → R
    where
  toFun x := M.vecMul x
  map_add' v w := funext fun i => add_dotProduct _ _ _
  map_smul' c v := funext fun i => smul_dotProduct _ _ _
#align matrix.vec_mul_linear Matrix.vecMulLinear
-/

variable [Fintype m] [DecidableEq m]

/- warning: matrix.vec_mul_std_basis -> Matrix.vecMul_stdBasis is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.vec_mul_std_basis Matrix.vecMul_stdBasisₓ'. -/
@[simp]
theorem Matrix.vecMul_stdBasis (M : Matrix m n R) (i j) :
    M.vecMul (stdBasis R (fun _ => R) i 1) j = M i j :=
  by
  have : (∑ i', (if i = i' then 1 else 0) * M i' j) = M i j := by
    simp_rw [boole_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  convert this
  ext
  split_ifs with h <;> simp only [std_basis_apply]
  · rw [h, Function.update_same]
  · rw [Function.update_noteq (Ne.symm h), Pi.zero_apply]
#align matrix.vec_mul_std_basis Matrix.vecMul_stdBasis

#print LinearMap.toMatrixRight' /-
/-- Linear maps `(m → R) →ₗ[R] (n → R)` are linearly equivalent over `Rᵐᵒᵖ` to `matrix m n R`,
by having matrices act by right multiplication.
 -/
def LinearMap.toMatrixRight' : ((m → R) →ₗ[R] n → R) ≃ₗ[Rᵐᵒᵖ] Matrix m n R
    where
  toFun f i j := f (stdBasis R (fun _ => R) i 1) j
  invFun := Matrix.vecMulLinear
  right_inv M := by ext (i j); simp only [Matrix.vecMul_stdBasis, Matrix.vecMulLinear_apply]
  left_inv f := by
    apply (Pi.basisFun R m).ext
    intro j; ext i
    simp only [Pi.basisFun_apply, Matrix.vecMul_stdBasis, Matrix.vecMulLinear_apply]
  map_add' f g := by ext (i j); simp only [Pi.add_apply, LinearMap.add_apply]
  map_smul' c f := by ext (i j); simp only [Pi.smul_apply, LinearMap.smul_apply, RingHom.id_apply]
#align linear_map.to_matrix_right' LinearMap.toMatrixRight'
-/

#print Matrix.toLinearMapRight' /-
/-- A `matrix m n R` is linearly equivalent over `Rᵐᵒᵖ` to a linear map `(m → R) →ₗ[R] (n → R)`,
by having matrices act by right multiplication. -/
abbrev Matrix.toLinearMapRight' : Matrix m n R ≃ₗ[Rᵐᵒᵖ] (m → R) →ₗ[R] n → R :=
  LinearMap.toMatrixRight'.symm
#align matrix.to_linear_map_right' Matrix.toLinearMapRight'
-/

/- warning: matrix.to_linear_map_right'_apply -> Matrix.toLinearMapRight'_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_linear_map_right'_apply Matrix.toLinearMapRight'_applyₓ'. -/
@[simp]
theorem Matrix.toLinearMapRight'_apply (M : Matrix m n R) (v : m → R) :
    Matrix.toLinearMapRight' M v = M.vecMul v :=
  rfl
#align matrix.to_linear_map_right'_apply Matrix.toLinearMapRight'_apply

/- warning: matrix.to_linear_map_right'_mul -> Matrix.toLinearMapRight'_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_linear_map_right'_mul Matrix.toLinearMapRight'_mulₓ'. -/
@[simp]
theorem Matrix.toLinearMapRight'_mul [Fintype l] [DecidableEq l] (M : Matrix l m R)
    (N : Matrix m n R) :
    Matrix.toLinearMapRight' (M ⬝ N) =
      (Matrix.toLinearMapRight' N).comp (Matrix.toLinearMapRight' M) :=
  LinearMap.ext fun x => (vecMul_vecMul _ M N).symm
#align matrix.to_linear_map_right'_mul Matrix.toLinearMapRight'_mul

/- warning: matrix.to_linear_map_right'_mul_apply -> Matrix.toLinearMapRight'_mul_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_linear_map_right'_mul_apply Matrix.toLinearMapRight'_mul_applyₓ'. -/
theorem Matrix.toLinearMapRight'_mul_apply [Fintype l] [DecidableEq l] (M : Matrix l m R)
    (N : Matrix m n R) (x) :
    Matrix.toLinearMapRight' (M ⬝ N) x =
      Matrix.toLinearMapRight' N (Matrix.toLinearMapRight' M x) :=
  (vecMul_vecMul _ M N).symm
#align matrix.to_linear_map_right'_mul_apply Matrix.toLinearMapRight'_mul_apply

/- warning: matrix.to_linear_map_right'_one -> Matrix.toLinearMapRight'_one is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_linear_map_right'_one Matrix.toLinearMapRight'_oneₓ'. -/
@[simp]
theorem Matrix.toLinearMapRight'_one : Matrix.toLinearMapRight' (1 : Matrix m m R) = id := by ext;
  simp [LinearMap.one_apply, std_basis_apply]
#align matrix.to_linear_map_right'_one Matrix.toLinearMapRight'_one

/- warning: matrix.to_linear_equiv_right'_of_inv -> Matrix.toLinearEquivRight'OfInv is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {m : Type.{u2}} {n : Type.{u3}} [_inst_2 : Fintype.{u2} m] [_inst_3 : DecidableEq.{succ u2} m] [_inst_4 : Fintype.{u3} n] [_inst_5 : DecidableEq.{succ u3} n] {M : Matrix.{u2, u3, u1} m n R} {M' : Matrix.{u3, u2, u1} n m R}, (Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} m m R) (Matrix.mul.{u1, u2, u3, u2} m n m R _inst_4 (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) M M') (OfNat.ofNat.{max u2 u1} (Matrix.{u2, u2, u1} m m R) 1 (OfNat.mk.{max u2 u1} (Matrix.{u2, u2, u1} m m R) 1 (One.one.{max u2 u1} (Matrix.{u2, u2, u1} m m R) (Matrix.hasOne.{u1, u2} m R (fun (a : m) (b : m) => _inst_3 a b) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))))))) -> (Eq.{succ (max u3 u1)} (Matrix.{u3, u3, u1} n n R) (Matrix.mul.{u1, u3, u2, u3} n m n R _inst_2 (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) M' M) (OfNat.ofNat.{max u3 u1} (Matrix.{u3, u3, u1} n n R) 1 (OfNat.mk.{max u3 u1} (Matrix.{u3, u3, u1} n n R) 1 (One.one.{max u3 u1} (Matrix.{u3, u3, u1} n n R) (Matrix.hasOne.{u1, u3} n R (fun (a : n) (b : n) => _inst_5 a b) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))))))) -> (LinearEquiv.{u1, u1, max u3 u1, max u2 u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) (n -> R) (m -> R) (Pi.addCommMonoid.{u3, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.addCommMonoid.{u2, u1} m (fun (ᾰ : m) => R) (fun (i : m) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.Function.module.{u3, u1, u1} n R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1)) (Pi.Function.module.{u2, u1, u1} m R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {m : Type.{u2}} {n : Type.{u3}} [_inst_2 : Fintype.{u2} m] [_inst_3 : DecidableEq.{succ u2} m] [_inst_4 : Fintype.{u3} n] [_inst_5 : DecidableEq.{succ u3} n] {M : Matrix.{u2, u3, u1} m n R} {M' : Matrix.{u3, u2, u1} n m R}, (Eq.{max (succ u1) (succ u2)} (Matrix.{u2, u2, u1} m m R) (Matrix.mul.{u1, u2, u3, u2} m n m R _inst_4 (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) M M') (OfNat.ofNat.{max u1 u2} (Matrix.{u2, u2, u1} m m R) 1 (One.toOfNat1.{max u1 u2} (Matrix.{u2, u2, u1} m m R) (Matrix.one.{u1, u2} m R (fun (a : m) (b : m) => _inst_3 a b) (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)) (Semiring.toOne.{u1} R _inst_1))))) -> (Eq.{max (succ u1) (succ u3)} (Matrix.{u3, u3, u1} n n R) (Matrix.mul.{u1, u3, u2, u3} n m n R _inst_2 (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) M' M) (OfNat.ofNat.{max u1 u3} (Matrix.{u3, u3, u1} n n R) 1 (One.toOfNat1.{max u1 u3} (Matrix.{u3, u3, u1} n n R) (Matrix.one.{u1, u3} n R (fun (a : n) (b : n) => _inst_5 a b) (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)) (Semiring.toOne.{u1} R _inst_1))))) -> (LinearEquiv.{u1, u1, max u1 u3, max u1 u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) (n -> R) (m -> R) (Pi.addCommMonoid.{u3, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.addCommMonoid.{u2, u1} m (fun (ᾰ : m) => R) (fun (i : m) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.module.{u3, u1, u1} n (fun (a._@.Mathlib.LinearAlgebra.Matrix.ToLin._hyg.977 : n) => R) R _inst_1 (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (fun (i : n) => Semiring.toModule.{u1} R _inst_1)) (Pi.module.{u2, u1, u1} m (fun (a._@.Mathlib.LinearAlgebra.Matrix.ToLin._hyg.980 : m) => R) R _inst_1 (fun (i : m) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (fun (i : m) => Semiring.toModule.{u1} R _inst_1)))
Case conversion may be inaccurate. Consider using '#align matrix.to_linear_equiv_right'_of_inv Matrix.toLinearEquivRight'OfInvₓ'. -/
/-- If `M` and `M'` are each other's inverse matrices, they provide an equivalence between `n → A`
and `m → A` corresponding to `M.vec_mul` and `M'.vec_mul`. -/
@[simps]
def Matrix.toLinearEquivRight'OfInv [Fintype n] [DecidableEq n] {M : Matrix m n R}
    {M' : Matrix n m R} (hMM' : M ⬝ M' = 1) (hM'M : M' ⬝ M = 1) : (n → R) ≃ₗ[R] m → R :=
  {
    LinearMap.toMatrixRight'.symm
      M' with
    toFun := M'.toLinearMapRight'
    invFun := M.toLinearMapRight'
    left_inv := fun x => by
      rw [← Matrix.toLinearMapRight'_mul_apply, hM'M, Matrix.toLinearMapRight'_one, id_apply]
    right_inv := fun x => by
      rw [← Matrix.toLinearMapRight'_mul_apply, hMM', Matrix.toLinearMapRight'_one, id_apply] }
#align matrix.to_linear_equiv_right'_of_inv Matrix.toLinearEquivRight'OfInv

end ToMatrixRight

/-!
From this point on, we only work with commutative rings,
and fail to distinguish between `Rᵐᵒᵖ` and `R`.
This should eventually be remedied.
-/


section ToMatrix'

variable {R : Type _} [CommSemiring R]

variable {k l m n : Type _}

#print Matrix.mulVecLin /-
/-- `matrix.mul_vec M` is a linear map. -/
def Matrix.mulVecLin [Fintype n] (M : Matrix m n R) : (n → R) →ₗ[R] m → R
    where
  toFun := M.mulVec
  map_add' v w := funext fun i => dotProduct_add _ _ _
  map_smul' c v := funext fun i => dotProduct_smul _ _ _
#align matrix.mul_vec_lin Matrix.mulVecLin
-/

/- warning: matrix.mul_vec_lin_apply -> Matrix.mulVecLin_apply is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {m : Type.{u2}} {n : Type.{u3}} [_inst_2 : Fintype.{u3} n] (M : Matrix.{u2, u3, u1} m n R) (v : n -> R), Eq.{max (succ u2) (succ u1)} (m -> R) (coeFn.{max (succ (max u3 u1)) (succ (max u2 u1)), max (succ (max u3 u1)) (succ (max u2 u1))} (LinearMap.{u1, u1, max u3 u1, max u2 u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (n -> R) (m -> R) (Pi.addCommMonoid.{u3, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.addCommMonoid.{u2, u1} m (fun (ᾰ : m) => R) (fun (i : m) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.Function.module.{u3, u1, u1} n R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (Pi.Function.module.{u2, u1, u1} m R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (fun (_x : LinearMap.{u1, u1, max u3 u1, max u2 u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (n -> R) (m -> R) (Pi.addCommMonoid.{u3, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.addCommMonoid.{u2, u1} m (fun (ᾰ : m) => R) (fun (i : m) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.Function.module.{u3, u1, u1} n R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (Pi.Function.module.{u2, u1, u1} m R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) => (n -> R) -> m -> R) (LinearMap.hasCoeToFun.{u1, u1, max u3 u1, max u2 u1} R R (n -> R) (m -> R) (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (Pi.addCommMonoid.{u3, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.addCommMonoid.{u2, u1} m (fun (ᾰ : m) => R) (fun (i : m) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.Function.module.{u3, u1, u1} n R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (Pi.Function.module.{u2, u1, u1} m R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Matrix.mulVecLin.{u1, u2, u3} R _inst_1 m n _inst_2 M) v) (Matrix.mulVec.{u1, u2, u3} m n R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) _inst_2 M v)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {m : Type.{u2}} {n : Type.{u3}} [_inst_2 : Fintype.{u3} n] (M : Matrix.{u2, u3, u1} m n R) (v : n -> R), Eq.{max (succ u1) (succ u2)} ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : n -> R) => m -> R) v) (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u3), max (succ u1) (succ u3), max (succ u1) (succ u2)} (LinearMap.{u1, u1, max u1 u3, max u1 u2} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (n -> R) (m -> R) (Pi.addCommMonoid.{u3, u1} n (fun (a._@.Mathlib.LinearAlgebra.Matrix.ToLin._hyg.1177 : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.addCommMonoid.{u2, u1} m (fun (a._@.Mathlib.LinearAlgebra.Matrix.ToLin._hyg.1180 : m) => R) (fun (i : m) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.module.{u3, u1, u1} n (fun (a._@.Mathlib.LinearAlgebra.Matrix.ToLin._hyg.1177 : n) => R) R (CommSemiring.toSemiring.{u1} R _inst_1) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (fun (i : n) => Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (Pi.module.{u2, u1, u1} m (fun (a._@.Mathlib.LinearAlgebra.Matrix.ToLin._hyg.1180 : m) => R) R (CommSemiring.toSemiring.{u1} R _inst_1) (fun (i : m) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (fun (i : m) => Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (n -> R) (fun (_x : n -> R) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : n -> R) => m -> R) _x) (LinearMap.instFunLikeLinearMap.{u1, u1, max u1 u3, max u1 u2} R R (n -> R) (m -> R) (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (Pi.addCommMonoid.{u3, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.addCommMonoid.{u2, u1} m (fun (ᾰ : m) => R) (fun (i : m) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.module.{u3, u1, u1} n (fun (a._@.Mathlib.LinearAlgebra.Matrix.ToLin._hyg.1177 : n) => R) R (CommSemiring.toSemiring.{u1} R _inst_1) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (fun (i : n) => Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (Pi.module.{u2, u1, u1} m (fun (a._@.Mathlib.LinearAlgebra.Matrix.ToLin._hyg.1180 : m) => R) R (CommSemiring.toSemiring.{u1} R _inst_1) (fun (i : m) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (fun (i : m) => Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Matrix.mulVecLin.{u1, u2, u3} R _inst_1 m n _inst_2 M) v) (Matrix.mulVec.{u1, u2, u3} m n R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) _inst_2 M v)
Case conversion may be inaccurate. Consider using '#align matrix.mul_vec_lin_apply Matrix.mulVecLin_applyₓ'. -/
@[simp]
theorem Matrix.mulVecLin_apply [Fintype n] (M : Matrix m n R) (v : n → R) :
    M.mulVecLin v = M.mulVec v :=
  rfl
#align matrix.mul_vec_lin_apply Matrix.mulVecLin_apply

/- warning: matrix.mul_vec_lin_zero -> Matrix.mulVecLin_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.mul_vec_lin_zero Matrix.mulVecLin_zeroₓ'. -/
@[simp]
theorem Matrix.mulVecLin_zero [Fintype n] : Matrix.mulVecLin (0 : Matrix m n R) = 0 :=
  LinearMap.ext zero_mulVec
#align matrix.mul_vec_lin_zero Matrix.mulVecLin_zero

/- warning: matrix.mul_vec_lin_add -> Matrix.mulVecLin_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.mul_vec_lin_add Matrix.mulVecLin_addₓ'. -/
@[simp]
theorem Matrix.mulVecLin_add [Fintype n] (M N : Matrix m n R) :
    (M + N).mulVecLin = M.mulVecLin + N.mulVecLin :=
  LinearMap.ext fun _ => add_mulVec _ _ _
#align matrix.mul_vec_lin_add Matrix.mulVecLin_add

/- warning: matrix.mul_vec_lin_submatrix -> Matrix.mulVecLin_submatrix is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.mul_vec_lin_submatrix Matrix.mulVecLin_submatrixₓ'. -/
theorem Matrix.mulVecLin_submatrix [Fintype n] [Fintype l] (f₁ : m → k) (e₂ : n ≃ l)
    (M : Matrix k l R) :
    (M.submatrix f₁ e₂).mulVecLin = funLeft R R f₁ ∘ₗ M.mulVecLin ∘ₗ funLeft _ _ e₂.symm :=
  LinearMap.ext fun x => submatrix_mulVec_equiv _ _ _ _
#align matrix.mul_vec_lin_submatrix Matrix.mulVecLin_submatrix

/- warning: matrix.mul_vec_lin_reindex -> Matrix.mulVecLin_reindex is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.mul_vec_lin_reindex Matrix.mulVecLin_reindexₓ'. -/
/-- A variant of `matrix.mul_vec_lin_submatrix` that keeps around `linear_equiv`s. -/
theorem Matrix.mulVecLin_reindex [Fintype n] [Fintype l] (e₁ : k ≃ m) (e₂ : l ≃ n)
    (M : Matrix k l R) :
    (reindex e₁ e₂ M).mulVecLin =
      ↑(LinearEquiv.funCongrLeft R R e₁.symm) ∘ₗ
        M.mulVecLin ∘ₗ ↑(LinearEquiv.funCongrLeft R R e₂) :=
  Matrix.mulVecLin_submatrix _ _ _
#align matrix.mul_vec_lin_reindex Matrix.mulVecLin_reindex

variable [Fintype n]

/- warning: matrix.mul_vec_lin_one -> Matrix.mulVecLin_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {n : Type.{u2}} [_inst_2 : Fintype.{u2} n] [_inst_3 : DecidableEq.{succ u2} n], Eq.{succ (max u2 u1)} (LinearMap.{u1, u1, max u2 u1, max u2 u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (n -> R) (n -> R) (Pi.addCommMonoid.{u2, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.addCommMonoid.{u2, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.Function.module.{u2, u1, u1} n R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (Pi.Function.module.{u2, u1, u1} n R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Matrix.mulVecLin.{u1, u2, u2} R _inst_1 n n _inst_2 (OfNat.ofNat.{max u2 u1} (Matrix.{u2, u2, u1} n n R) 1 (OfNat.mk.{max u2 u1} (Matrix.{u2, u2, u1} n n R) 1 (One.one.{max u2 u1} (Matrix.{u2, u2, u1} n n R) (Matrix.hasOne.{u1, u2} n R (fun (a : n) (b : n) => _inst_3 a b) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))))))) (LinearMap.id.{u1, max u2 u1} R (n -> R) (CommSemiring.toSemiring.{u1} R _inst_1) (Pi.addCommMonoid.{u2, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.Function.module.{u2, u1, u1} n R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {n : Type.{u2}} [_inst_2 : Fintype.{u2} n] [_inst_3 : DecidableEq.{succ u2} n], Eq.{max (succ u1) (succ u2)} (LinearMap.{u1, u1, max u1 u2, max u1 u2} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (n -> R) (n -> R) (Pi.addCommMonoid.{u2, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.addCommMonoid.{u2, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.module.{u2, u1, u1} n (fun (a._@.Mathlib.LinearAlgebra.Matrix.ToLin._hyg.1177 : n) => R) R (CommSemiring.toSemiring.{u1} R _inst_1) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (fun (i : n) => Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (Pi.module.{u2, u1, u1} n (fun (a._@.Mathlib.LinearAlgebra.Matrix.ToLin._hyg.1180 : n) => R) R (CommSemiring.toSemiring.{u1} R _inst_1) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (fun (i : n) => Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Matrix.mulVecLin.{u1, u2, u2} R _inst_1 n n _inst_2 (OfNat.ofNat.{max u1 u2} (Matrix.{u2, u2, u1} n n R) 1 (One.toOfNat1.{max u1 u2} (Matrix.{u2, u2, u1} n n R) (Matrix.one.{u1, u2} n R (fun (a : n) (b : n) => _inst_3 a b) (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R _inst_1)) (Semiring.toOne.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (LinearMap.id.{u1, max u1 u2} R (n -> R) (CommSemiring.toSemiring.{u1} R _inst_1) (Pi.addCommMonoid.{u2, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.module.{u2, u1, u1} n (fun (a._@.Mathlib.LinearAlgebra.Matrix.ToLin._hyg.1177 : n) => R) R (CommSemiring.toSemiring.{u1} R _inst_1) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (fun (i : n) => Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align matrix.mul_vec_lin_one Matrix.mulVecLin_oneₓ'. -/
@[simp]
theorem Matrix.mulVecLin_one [DecidableEq n] : Matrix.mulVecLin (1 : Matrix n n R) = id := by ext;
  simp [LinearMap.one_apply, std_basis_apply]
#align matrix.mul_vec_lin_one Matrix.mulVecLin_one

/- warning: matrix.mul_vec_lin_mul -> Matrix.mulVecLin_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.mul_vec_lin_mul Matrix.mulVecLin_mulₓ'. -/
@[simp]
theorem Matrix.mulVecLin_mul [Fintype m] (M : Matrix l m R) (N : Matrix m n R) :
    Matrix.mulVecLin (M ⬝ N) = (Matrix.mulVecLin M).comp (Matrix.mulVecLin N) :=
  LinearMap.ext fun x => (mulVec_mulVec _ _ _).symm
#align matrix.mul_vec_lin_mul Matrix.mulVecLin_mul

/- warning: matrix.ker_mul_vec_lin_eq_bot_iff -> Matrix.ker_mulVecLin_eq_bot_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.ker_mul_vec_lin_eq_bot_iff Matrix.ker_mulVecLin_eq_bot_iffₓ'. -/
theorem Matrix.ker_mulVecLin_eq_bot_iff {M : Matrix n n R} :
    M.mulVecLin.ker = ⊥ ↔ ∀ v, M.mulVec v = 0 → v = 0 := by
  simp only [Submodule.eq_bot_iff, LinearMap.mem_ker, Matrix.mulVecLin_apply]
#align matrix.ker_mul_vec_lin_eq_bot_iff Matrix.ker_mulVecLin_eq_bot_iff

/- warning: matrix.mul_vec_std_basis -> Matrix.mulVec_stdBasis is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.mul_vec_std_basis Matrix.mulVec_stdBasisₓ'. -/
theorem Matrix.mulVec_stdBasis [DecidableEq n] (M : Matrix m n R) (i j) :
    M.mulVec (stdBasis R (fun _ => R) j 1) i = M i j :=
  (congr_fun (Matrix.mulVec_single _ _ (1 : R)) i).trans <| mul_one _
#align matrix.mul_vec_std_basis Matrix.mulVec_stdBasis

/- warning: matrix.mul_vec_std_basis_apply -> Matrix.mulVec_stdBasis_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.mul_vec_std_basis_apply Matrix.mulVec_stdBasis_applyₓ'. -/
@[simp]
theorem Matrix.mulVec_stdBasis_apply [DecidableEq n] (M : Matrix m n R) (j) :
    M.mulVec (stdBasis R (fun _ => R) j 1) = Mᵀ j :=
  funext fun i => Matrix.mulVec_stdBasis M i j
#align matrix.mul_vec_std_basis_apply Matrix.mulVec_stdBasis_apply

/- warning: matrix.range_mul_vec_lin -> Matrix.range_mulVecLin is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.range_mul_vec_lin Matrix.range_mulVecLinₓ'. -/
theorem Matrix.range_mulVecLin (M : Matrix m n R) : M.mulVecLin.range = span R (range Mᵀ) :=
  by
  letI := Classical.decEq n
  simp_rw [range_eq_map, ← supr_range_std_basis, Submodule.map_iSup, range_eq_map, ←
    Ideal.span_singleton_one, Ideal.span, Submodule.map_span, image_image, image_singleton,
    Matrix.mulVecLin_apply, M.mul_vec_std_basis_apply, supr_span, range_eq_Union]
#align matrix.range_mul_vec_lin Matrix.range_mulVecLin

variable [DecidableEq n]

#print LinearMap.toMatrix' /-
/-- Linear maps `(n → R) →ₗ[R] (m → R)` are linearly equivalent to `matrix m n R`. -/
def LinearMap.toMatrix' : ((n → R) →ₗ[R] m → R) ≃ₗ[R] Matrix m n R
    where
  toFun f := of fun i j => f (stdBasis R (fun _ => R) j 1) i
  invFun := Matrix.mulVecLin
  right_inv M := by ext (i j); simp only [Matrix.mulVec_stdBasis, Matrix.mulVecLin_apply, of_apply]
  left_inv f := by
    apply (Pi.basisFun R n).ext
    intro j; ext i
    simp only [Pi.basisFun_apply, Matrix.mulVec_stdBasis, Matrix.mulVecLin_apply, of_apply]
  map_add' f g := by ext (i j); simp only [Pi.add_apply, LinearMap.add_apply, of_apply]
  map_smul' c f := by ext (i j);
    simp only [Pi.smul_apply, LinearMap.smul_apply, RingHom.id_apply, of_apply]
#align linear_map.to_matrix' LinearMap.toMatrix'
-/

#print Matrix.toLin' /-
/-- A `matrix m n R` is linearly equivalent to a linear map `(n → R) →ₗ[R] (m → R)`.

Note that the forward-direction does not require `decidable_eq` and is `matrix.vec_mul_lin`. -/
def Matrix.toLin' : Matrix m n R ≃ₗ[R] (n → R) →ₗ[R] m → R :=
  LinearMap.toMatrix'.symm
#align matrix.to_lin' Matrix.toLin'
-/

/- warning: matrix.to_lin'_apply' -> Matrix.toLin'_apply' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_lin'_apply' Matrix.toLin'_apply'ₓ'. -/
theorem Matrix.toLin'_apply' (M : Matrix m n R) : Matrix.toLin' M = M.mulVecLin :=
  rfl
#align matrix.to_lin'_apply' Matrix.toLin'_apply'

/- warning: linear_map.to_matrix'_symm -> LinearMap.toMatrix'_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix'_symm LinearMap.toMatrix'_symmₓ'. -/
@[simp]
theorem LinearMap.toMatrix'_symm :
    (LinearMap.toMatrix'.symm : Matrix m n R ≃ₗ[R] _) = Matrix.toLin' :=
  rfl
#align linear_map.to_matrix'_symm LinearMap.toMatrix'_symm

/- warning: matrix.to_lin'_symm -> Matrix.toLin'_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_lin'_symm Matrix.toLin'_symmₓ'. -/
@[simp]
theorem Matrix.toLin'_symm :
    (Matrix.toLin'.symm : ((n → R) →ₗ[R] m → R) ≃ₗ[R] _) = LinearMap.toMatrix' :=
  rfl
#align matrix.to_lin'_symm Matrix.toLin'_symm

/- warning: linear_map.to_matrix'_to_lin' -> LinearMap.toMatrix'_toLin' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix'_to_lin' LinearMap.toMatrix'_toLin'ₓ'. -/
@[simp]
theorem LinearMap.toMatrix'_toLin' (M : Matrix m n R) : LinearMap.toMatrix' (Matrix.toLin' M) = M :=
  LinearMap.toMatrix'.apply_symm_apply M
#align linear_map.to_matrix'_to_lin' LinearMap.toMatrix'_toLin'

/- warning: matrix.to_lin'_to_matrix' -> Matrix.toLin'_toMatrix' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_lin'_to_matrix' Matrix.toLin'_toMatrix'ₓ'. -/
@[simp]
theorem Matrix.toLin'_toMatrix' (f : (n → R) →ₗ[R] m → R) :
    Matrix.toLin' (LinearMap.toMatrix' f) = f :=
  Matrix.toLin'.apply_symm_apply f
#align matrix.to_lin'_to_matrix' Matrix.toLin'_toMatrix'

/- warning: linear_map.to_matrix'_apply -> LinearMap.toMatrix'_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix'_apply LinearMap.toMatrix'_applyₓ'. -/
@[simp]
theorem LinearMap.toMatrix'_apply (f : (n → R) →ₗ[R] m → R) (i j) :
    LinearMap.toMatrix' f i j = f (fun j' => if j' = j then 1 else 0) i :=
  by
  simp only [LinearMap.toMatrix', LinearEquiv.coe_mk, of_apply]
  congr
  ext j'
  split_ifs with h
  · rw [h, std_basis_same]
  apply std_basis_ne _ _ _ _ h
#align linear_map.to_matrix'_apply LinearMap.toMatrix'_apply

/- warning: matrix.to_lin'_apply -> Matrix.toLin'_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_lin'_apply Matrix.toLin'_applyₓ'. -/
@[simp]
theorem Matrix.toLin'_apply (M : Matrix m n R) (v : n → R) : Matrix.toLin' M v = M.mulVec v :=
  rfl
#align matrix.to_lin'_apply Matrix.toLin'_apply

/- warning: matrix.to_lin'_one -> Matrix.toLin'_one is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_lin'_one Matrix.toLin'_oneₓ'. -/
@[simp]
theorem Matrix.toLin'_one : Matrix.toLin' (1 : Matrix n n R) = id :=
  Matrix.mulVecLin_one
#align matrix.to_lin'_one Matrix.toLin'_one

/- warning: linear_map.to_matrix'_id -> LinearMap.toMatrix'_id is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix'_id LinearMap.toMatrix'_idₓ'. -/
@[simp]
theorem LinearMap.toMatrix'_id : LinearMap.toMatrix' (LinearMap.id : (n → R) →ₗ[R] n → R) = 1 := by
  ext; rw [Matrix.one_apply, LinearMap.toMatrix'_apply, id_apply]
#align linear_map.to_matrix'_id LinearMap.toMatrix'_id

/- warning: matrix.to_lin'_mul -> Matrix.toLin'_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_lin'_mul Matrix.toLin'_mulₓ'. -/
@[simp]
theorem Matrix.toLin'_mul [Fintype m] [DecidableEq m] (M : Matrix l m R) (N : Matrix m n R) :
    Matrix.toLin' (M ⬝ N) = (Matrix.toLin' M).comp (Matrix.toLin' N) :=
  Matrix.mulVecLin_mul _ _
#align matrix.to_lin'_mul Matrix.toLin'_mul

/- warning: matrix.to_lin'_submatrix -> Matrix.toLin'_submatrix is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_lin'_submatrix Matrix.toLin'_submatrixₓ'. -/
@[simp]
theorem Matrix.toLin'_submatrix [Fintype l] [DecidableEq l] (f₁ : m → k) (e₂ : n ≃ l)
    (M : Matrix k l R) :
    (M.submatrix f₁ e₂).toLin' = funLeft R R f₁ ∘ₗ M.toLin' ∘ₗ funLeft _ _ e₂.symm :=
  Matrix.mulVecLin_submatrix _ _ _
#align matrix.to_lin'_submatrix Matrix.toLin'_submatrix

/- warning: matrix.to_lin'_reindex -> Matrix.toLin'_reindex is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_lin'_reindex Matrix.toLin'_reindexₓ'. -/
/-- A variant of `matrix.to_lin'_submatrix` that keeps around `linear_equiv`s. -/
theorem Matrix.toLin'_reindex [Fintype l] [DecidableEq l] (e₁ : k ≃ m) (e₂ : l ≃ n)
    (M : Matrix k l R) :
    (reindex e₁ e₂ M).toLin' =
      ↑(LinearEquiv.funCongrLeft R R e₁.symm) ∘ₗ M.toLin' ∘ₗ ↑(LinearEquiv.funCongrLeft R R e₂) :=
  Matrix.mulVecLin_reindex _ _ _
#align matrix.to_lin'_reindex Matrix.toLin'_reindex

/- warning: matrix.to_lin'_mul_apply -> Matrix.toLin'_mul_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_lin'_mul_apply Matrix.toLin'_mul_applyₓ'. -/
/-- Shortcut lemma for `matrix.to_lin'_mul` and `linear_map.comp_apply` -/
theorem Matrix.toLin'_mul_apply [Fintype m] [DecidableEq m] (M : Matrix l m R) (N : Matrix m n R)
    (x) : Matrix.toLin' (M ⬝ N) x = Matrix.toLin' M (Matrix.toLin' N x) := by
  rw [Matrix.toLin'_mul, LinearMap.comp_apply]
#align matrix.to_lin'_mul_apply Matrix.toLin'_mul_apply

/- warning: linear_map.to_matrix'_comp -> LinearMap.toMatrix'_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix'_comp LinearMap.toMatrix'_compₓ'. -/
theorem LinearMap.toMatrix'_comp [Fintype l] [DecidableEq l] (f : (n → R) →ₗ[R] m → R)
    (g : (l → R) →ₗ[R] n → R) : (f.comp g).toMatrix' = f.toMatrix' ⬝ g.toMatrix' :=
  by
  suffices f.comp g = (f.toMatrix' ⬝ g.toMatrix').toLin' by rw [this, LinearMap.toMatrix'_toLin']
  rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
#align linear_map.to_matrix'_comp LinearMap.toMatrix'_comp

/- warning: linear_map.to_matrix'_mul -> LinearMap.toMatrix'_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix'_mul LinearMap.toMatrix'_mulₓ'. -/
theorem LinearMap.toMatrix'_mul [Fintype m] [DecidableEq m] (f g : (m → R) →ₗ[R] m → R) :
    (f * g).toMatrix' = f.toMatrix' ⬝ g.toMatrix' :=
  LinearMap.toMatrix'_comp f g
#align linear_map.to_matrix'_mul LinearMap.toMatrix'_mul

/- warning: linear_map.to_matrix'_algebra_map -> LinearMap.toMatrix'_algebraMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix'_algebra_map LinearMap.toMatrix'_algebraMapₓ'. -/
@[simp]
theorem LinearMap.toMatrix'_algebraMap (x : R) :
    LinearMap.toMatrix' (algebraMap R (Module.End R (n → R)) x) = scalar n x := by
  simp [Module.algebraMap_end_eq_smul_id]
#align linear_map.to_matrix'_algebra_map LinearMap.toMatrix'_algebraMap

/- warning: matrix.ker_to_lin'_eq_bot_iff -> Matrix.ker_toLin'_eq_bot_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.ker_to_lin'_eq_bot_iff Matrix.ker_toLin'_eq_bot_iffₓ'. -/
theorem Matrix.ker_toLin'_eq_bot_iff {M : Matrix n n R} :
    M.toLin'.ker = ⊥ ↔ ∀ v, M.mulVec v = 0 → v = 0 :=
  Matrix.ker_mulVecLin_eq_bot_iff
#align matrix.ker_to_lin'_eq_bot_iff Matrix.ker_toLin'_eq_bot_iff

/- warning: matrix.range_to_lin' -> Matrix.range_toLin' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.range_to_lin' Matrix.range_toLin'ₓ'. -/
theorem Matrix.range_toLin' (M : Matrix m n R) : M.toLin'.range = span R (range Mᵀ) :=
  Matrix.range_mulVecLin _
#align matrix.range_to_lin' Matrix.range_toLin'

/- warning: matrix.to_lin'_of_inv -> Matrix.toLin'OfInv is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {m : Type.{u2}} {n : Type.{u3}} [_inst_2 : Fintype.{u3} n] [_inst_3 : DecidableEq.{succ u3} n] [_inst_4 : Fintype.{u2} m] [_inst_5 : DecidableEq.{succ u2} m] {M : Matrix.{u2, u3, u1} m n R} {M' : Matrix.{u3, u2, u1} n m R}, (Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} m m R) (Matrix.mul.{u1, u2, u3, u2} m n m R _inst_2 (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) M M') (OfNat.ofNat.{max u2 u1} (Matrix.{u2, u2, u1} m m R) 1 (OfNat.mk.{max u2 u1} (Matrix.{u2, u2, u1} m m R) 1 (One.one.{max u2 u1} (Matrix.{u2, u2, u1} m m R) (Matrix.hasOne.{u1, u2} m R (fun (a : m) (b : m) => _inst_5 a b) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))))))) -> (Eq.{succ (max u3 u1)} (Matrix.{u3, u3, u1} n n R) (Matrix.mul.{u1, u3, u2, u3} n m n R _inst_4 (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) M' M) (OfNat.ofNat.{max u3 u1} (Matrix.{u3, u3, u1} n n R) 1 (OfNat.mk.{max u3 u1} (Matrix.{u3, u3, u1} n n R) 1 (One.one.{max u3 u1} (Matrix.{u3, u3, u1} n n R) (Matrix.hasOne.{u1, u3} n R (fun (a : n) (b : n) => _inst_3 a b) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))))))) -> (LinearEquiv.{u1, u1, max u2 u1, max u3 u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (Matrix.toLin'OfInv._proof_1.{u1} R _inst_1) (Matrix.toLin'OfInv._proof_2.{u1} R _inst_1) (m -> R) (n -> R) (Pi.addCommMonoid.{u2, u1} m (fun (ᾰ : m) => R) (fun (i : m) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.addCommMonoid.{u3, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.Function.module.{u2, u1, u1} m R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (Pi.Function.module.{u3, u1, u1} n R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {m : Type.{u2}} {n : Type.{u3}} [_inst_2 : Fintype.{u3} n] [_inst_3 : DecidableEq.{succ u3} n] [_inst_4 : Fintype.{u2} m] [_inst_5 : DecidableEq.{succ u2} m] {M : Matrix.{u2, u3, u1} m n R} {M' : Matrix.{u3, u2, u1} n m R}, (Eq.{max (succ u1) (succ u2)} (Matrix.{u2, u2, u1} m m R) (Matrix.mul.{u1, u2, u3, u2} m n m R _inst_2 (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) M M') (OfNat.ofNat.{max u1 u2} (Matrix.{u2, u2, u1} m m R) 1 (One.toOfNat1.{max u1 u2} (Matrix.{u2, u2, u1} m m R) (Matrix.one.{u1, u2} m R (fun (a : m) (b : m) => _inst_5 a b) (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R _inst_1)) (Semiring.toOne.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) -> (Eq.{max (succ u1) (succ u3)} (Matrix.{u3, u3, u1} n n R) (Matrix.mul.{u1, u3, u2, u3} n m n R _inst_4 (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) M' M) (OfNat.ofNat.{max u1 u3} (Matrix.{u3, u3, u1} n n R) 1 (One.toOfNat1.{max u1 u3} (Matrix.{u3, u3, u1} n n R) (Matrix.one.{u1, u3} n R (fun (a : n) (b : n) => _inst_3 a b) (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R _inst_1)) (Semiring.toOne.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) -> (LinearEquiv.{u1, u1, max u1 u2, max u1 u3} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (RingHomInvPair.ids.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (m -> R) (n -> R) (Pi.addCommMonoid.{u2, u1} m (fun (ᾰ : m) => R) (fun (i : m) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.addCommMonoid.{u3, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.module.{u2, u1, u1} m (fun (a._@.Mathlib.LinearAlgebra.Matrix.ToLin._hyg.3442 : m) => R) R (CommSemiring.toSemiring.{u1} R _inst_1) (fun (i : m) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (fun (i : m) => Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (Pi.module.{u3, u1, u1} n (fun (a._@.Mathlib.LinearAlgebra.Matrix.ToLin._hyg.3445 : n) => R) R (CommSemiring.toSemiring.{u1} R _inst_1) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (fun (i : n) => Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align matrix.to_lin'_of_inv Matrix.toLin'OfInvₓ'. -/
/-- If `M` and `M'` are each other's inverse matrices, they provide an equivalence between `m → A`
and `n → A` corresponding to `M.mul_vec` and `M'.mul_vec`. -/
@[simps]
def Matrix.toLin'OfInv [Fintype m] [DecidableEq m] {M : Matrix m n R} {M' : Matrix n m R}
    (hMM' : M ⬝ M' = 1) (hM'M : M' ⬝ M = 1) : (m → R) ≃ₗ[R] n → R :=
  { Matrix.toLin' M' with
    toFun := Matrix.toLin' M'
    invFun := M.toLin'
    left_inv := fun x => by rw [← Matrix.toLin'_mul_apply, hMM', Matrix.toLin'_one, id_apply]
    right_inv := fun x => by rw [← Matrix.toLin'_mul_apply, hM'M, Matrix.toLin'_one, id_apply] }
#align matrix.to_lin'_of_inv Matrix.toLin'OfInv

/- warning: linear_map.to_matrix_alg_equiv' -> LinearMap.toMatrixAlgEquiv' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {n : Type.{u2}} [_inst_2 : Fintype.{u2} n] [_inst_3 : DecidableEq.{succ u2} n], AlgEquiv.{u1, max u2 u1, max u2 u1} R (LinearMap.{u1, u1, max u2 u1, max u2 u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (n -> R) (n -> R) (Pi.addCommMonoid.{u2, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.addCommMonoid.{u2, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.Function.module.{u2, u1, u1} n R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (Pi.Function.module.{u2, u1, u1} n R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Matrix.{u2, u2, u1} n n R) _inst_1 (Module.End.semiring.{u1, max u2 u1} R (n -> R) (CommSemiring.toSemiring.{u1} R _inst_1) (Pi.addCommMonoid.{u2, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.Function.module.{u2, u1, u1} n R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Matrix.semiring.{u1, u2} n R (CommSemiring.toSemiring.{u1} R _inst_1) _inst_2 (fun (a : n) (b : n) => _inst_3 a b)) (Module.End.algebra.{u1, max u2 u1} R (n -> R) _inst_1 (Pi.addCommMonoid.{u2, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.Function.module.{u2, u1, u1} n R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Matrix.algebra.{u1, u2, u1} n R R _inst_2 (fun (a : n) (b : n) => _inst_3 a b) _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {n : Type.{u2}} [_inst_2 : Fintype.{u2} n] [_inst_3 : DecidableEq.{succ u2} n], AlgEquiv.{u1, max u1 u2, max u1 u2} R (LinearMap.{u1, u1, max u1 u2, max u1 u2} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (n -> R) (n -> R) (Pi.addCommMonoid.{u2, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.addCommMonoid.{u2, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.module.{u2, u1, u1} n (fun (a._@.Mathlib.LinearAlgebra.Matrix.ToLin._hyg.3578 : n) => R) R (CommSemiring.toSemiring.{u1} R _inst_1) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (fun (i : n) => Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (Pi.module.{u2, u1, u1} n (fun (a._@.Mathlib.LinearAlgebra.Matrix.ToLin._hyg.3578 : n) => R) R (CommSemiring.toSemiring.{u1} R _inst_1) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (fun (i : n) => Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Matrix.{u2, u2, u1} n n R) _inst_1 (Module.End.semiring.{u1, max u1 u2} R (n -> R) (CommSemiring.toSemiring.{u1} R _inst_1) (Pi.addCommMonoid.{u2, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.module.{u2, u1, u1} n (fun (a._@.Mathlib.LinearAlgebra.Matrix.ToLin._hyg.3578 : n) => R) R (CommSemiring.toSemiring.{u1} R _inst_1) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (fun (i : n) => Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Matrix.semiring.{u1, u2} n R (CommSemiring.toSemiring.{u1} R _inst_1) _inst_2 (fun (a : n) (b : n) => _inst_3 a b)) (Module.instAlgebraEndToSemiringSemiring.{u1, max u1 u2} R (n -> R) _inst_1 (Pi.addCommMonoid.{u2, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.module.{u2, u1, u1} n (fun (a._@.Mathlib.LinearAlgebra.Matrix.ToLin._hyg.3578 : n) => R) R (CommSemiring.toSemiring.{u1} R _inst_1) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (fun (i : n) => Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Matrix.instAlgebraMatrixSemiring.{u1, u2, u1} n R R _inst_2 (fun (a : n) (b : n) => _inst_3 a b) _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1))
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_alg_equiv' LinearMap.toMatrixAlgEquiv'ₓ'. -/
/-- Linear maps `(n → R) →ₗ[R] (n → R)` are algebra equivalent to `matrix n n R`. -/
def LinearMap.toMatrixAlgEquiv' : ((n → R) →ₗ[R] n → R) ≃ₐ[R] Matrix n n R :=
  AlgEquiv.ofLinearEquiv LinearMap.toMatrix' LinearMap.toMatrix'_mul LinearMap.toMatrix'_algebraMap
#align linear_map.to_matrix_alg_equiv' LinearMap.toMatrixAlgEquiv'

/- warning: matrix.to_lin_alg_equiv' -> Matrix.toLinAlgEquiv' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {n : Type.{u2}} [_inst_2 : Fintype.{u2} n] [_inst_3 : DecidableEq.{succ u2} n], AlgEquiv.{u1, max u2 u1, max u2 u1} R (Matrix.{u2, u2, u1} n n R) (LinearMap.{u1, u1, max u2 u1, max u2 u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (n -> R) (n -> R) (Pi.addCommMonoid.{u2, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.addCommMonoid.{u2, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.Function.module.{u2, u1, u1} n R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (Pi.Function.module.{u2, u1, u1} n R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) _inst_1 (Matrix.semiring.{u1, u2} n R (CommSemiring.toSemiring.{u1} R _inst_1) _inst_2 (fun (a : n) (b : n) => _inst_3 a b)) (Module.End.semiring.{u1, max u2 u1} R (n -> R) (CommSemiring.toSemiring.{u1} R _inst_1) (Pi.addCommMonoid.{u2, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.Function.module.{u2, u1, u1} n R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Matrix.algebra.{u1, u2, u1} n R R _inst_2 (fun (a : n) (b : n) => _inst_3 a b) _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1)) (Module.End.algebra.{u1, max u2 u1} R (n -> R) _inst_1 (Pi.addCommMonoid.{u2, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.Function.module.{u2, u1, u1} n R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {n : Type.{u2}} [_inst_2 : Fintype.{u2} n] [_inst_3 : DecidableEq.{succ u2} n], AlgEquiv.{u1, max u1 u2, max u1 u2} R (Matrix.{u2, u2, u1} n n R) (LinearMap.{u1, u1, max u1 u2, max u1 u2} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (n -> R) (n -> R) (Pi.addCommMonoid.{u2, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.addCommMonoid.{u2, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.module.{u2, u1, u1} n (fun (a._@.Mathlib.LinearAlgebra.Matrix.ToLin._hyg.3629 : n) => R) R (CommSemiring.toSemiring.{u1} R _inst_1) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (fun (i : n) => Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (Pi.module.{u2, u1, u1} n (fun (a._@.Mathlib.LinearAlgebra.Matrix.ToLin._hyg.3629 : n) => R) R (CommSemiring.toSemiring.{u1} R _inst_1) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (fun (i : n) => Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) _inst_1 (Matrix.semiring.{u1, u2} n R (CommSemiring.toSemiring.{u1} R _inst_1) _inst_2 (fun (a : n) (b : n) => _inst_3 a b)) (Module.End.semiring.{u1, max u1 u2} R (n -> R) (CommSemiring.toSemiring.{u1} R _inst_1) (Pi.addCommMonoid.{u2, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.module.{u2, u1, u1} n (fun (a._@.Mathlib.LinearAlgebra.Matrix.ToLin._hyg.3629 : n) => R) R (CommSemiring.toSemiring.{u1} R _inst_1) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (fun (i : n) => Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Matrix.instAlgebraMatrixSemiring.{u1, u2, u1} n R R _inst_2 (fun (a : n) (b : n) => _inst_3 a b) _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1)) (Module.instAlgebraEndToSemiringSemiring.{u1, max u1 u2} R (n -> R) _inst_1 (Pi.addCommMonoid.{u2, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Pi.module.{u2, u1, u1} n (fun (a._@.Mathlib.LinearAlgebra.Matrix.ToLin._hyg.3629 : n) => R) R (CommSemiring.toSemiring.{u1} R _inst_1) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (fun (i : n) => Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align matrix.to_lin_alg_equiv' Matrix.toLinAlgEquiv'ₓ'. -/
/-- A `matrix n n R` is algebra equivalent to a linear map `(n → R) →ₗ[R] (n → R)`. -/
def Matrix.toLinAlgEquiv' : Matrix n n R ≃ₐ[R] (n → R) →ₗ[R] n → R :=
  LinearMap.toMatrixAlgEquiv'.symm
#align matrix.to_lin_alg_equiv' Matrix.toLinAlgEquiv'

/- warning: linear_map.to_matrix_alg_equiv'_symm -> LinearMap.toMatrixAlgEquiv'_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_alg_equiv'_symm LinearMap.toMatrixAlgEquiv'_symmₓ'. -/
@[simp]
theorem LinearMap.toMatrixAlgEquiv'_symm :
    (LinearMap.toMatrixAlgEquiv'.symm : Matrix n n R ≃ₐ[R] _) = Matrix.toLinAlgEquiv' :=
  rfl
#align linear_map.to_matrix_alg_equiv'_symm LinearMap.toMatrixAlgEquiv'_symm

/- warning: matrix.to_lin_alg_equiv'_symm -> Matrix.toLinAlgEquiv'_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_lin_alg_equiv'_symm Matrix.toLinAlgEquiv'_symmₓ'. -/
@[simp]
theorem Matrix.toLinAlgEquiv'_symm :
    (Matrix.toLinAlgEquiv'.symm : ((n → R) →ₗ[R] n → R) ≃ₐ[R] _) = LinearMap.toMatrixAlgEquiv' :=
  rfl
#align matrix.to_lin_alg_equiv'_symm Matrix.toLinAlgEquiv'_symm

/- warning: linear_map.to_matrix_alg_equiv'_to_lin_alg_equiv' -> LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_alg_equiv'_to_lin_alg_equiv' LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv'ₓ'. -/
@[simp]
theorem LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv' (M : Matrix n n R) :
    LinearMap.toMatrixAlgEquiv' (Matrix.toLinAlgEquiv' M) = M :=
  LinearMap.toMatrixAlgEquiv'.apply_symm_apply M
#align linear_map.to_matrix_alg_equiv'_to_lin_alg_equiv' LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv'

/- warning: matrix.to_lin_alg_equiv'_to_matrix_alg_equiv' -> Matrix.toLinAlgEquiv'_toMatrixAlgEquiv' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_lin_alg_equiv'_to_matrix_alg_equiv' Matrix.toLinAlgEquiv'_toMatrixAlgEquiv'ₓ'. -/
@[simp]
theorem Matrix.toLinAlgEquiv'_toMatrixAlgEquiv' (f : (n → R) →ₗ[R] n → R) :
    Matrix.toLinAlgEquiv' (LinearMap.toMatrixAlgEquiv' f) = f :=
  Matrix.toLinAlgEquiv'.apply_symm_apply f
#align matrix.to_lin_alg_equiv'_to_matrix_alg_equiv' Matrix.toLinAlgEquiv'_toMatrixAlgEquiv'

/- warning: linear_map.to_matrix_alg_equiv'_apply -> LinearMap.toMatrixAlgEquiv'_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_alg_equiv'_apply LinearMap.toMatrixAlgEquiv'_applyₓ'. -/
@[simp]
theorem LinearMap.toMatrixAlgEquiv'_apply (f : (n → R) →ₗ[R] n → R) (i j) :
    LinearMap.toMatrixAlgEquiv' f i j = f (fun j' => if j' = j then 1 else 0) i := by
  simp [LinearMap.toMatrixAlgEquiv']
#align linear_map.to_matrix_alg_equiv'_apply LinearMap.toMatrixAlgEquiv'_apply

/- warning: matrix.to_lin_alg_equiv'_apply -> Matrix.toLinAlgEquiv'_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_lin_alg_equiv'_apply Matrix.toLinAlgEquiv'_applyₓ'. -/
@[simp]
theorem Matrix.toLinAlgEquiv'_apply (M : Matrix n n R) (v : n → R) :
    Matrix.toLinAlgEquiv' M v = M.mulVec v :=
  rfl
#align matrix.to_lin_alg_equiv'_apply Matrix.toLinAlgEquiv'_apply

/- warning: matrix.to_lin_alg_equiv'_one -> Matrix.toLinAlgEquiv'_one is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_lin_alg_equiv'_one Matrix.toLinAlgEquiv'_oneₓ'. -/
@[simp]
theorem Matrix.toLinAlgEquiv'_one : Matrix.toLinAlgEquiv' (1 : Matrix n n R) = id :=
  Matrix.toLin'_one
#align matrix.to_lin_alg_equiv'_one Matrix.toLinAlgEquiv'_one

/- warning: linear_map.to_matrix_alg_equiv'_id -> LinearMap.toMatrixAlgEquiv'_id is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_alg_equiv'_id LinearMap.toMatrixAlgEquiv'_idₓ'. -/
@[simp]
theorem LinearMap.toMatrixAlgEquiv'_id :
    LinearMap.toMatrixAlgEquiv' (LinearMap.id : (n → R) →ₗ[R] n → R) = 1 :=
  LinearMap.toMatrix'_id
#align linear_map.to_matrix_alg_equiv'_id LinearMap.toMatrixAlgEquiv'_id

/- warning: matrix.to_lin_alg_equiv'_mul -> Matrix.toLinAlgEquiv'_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_lin_alg_equiv'_mul Matrix.toLinAlgEquiv'_mulₓ'. -/
@[simp]
theorem Matrix.toLinAlgEquiv'_mul (M N : Matrix n n R) :
    Matrix.toLinAlgEquiv' (M ⬝ N) = (Matrix.toLinAlgEquiv' M).comp (Matrix.toLinAlgEquiv' N) :=
  Matrix.toLin'_mul _ _
#align matrix.to_lin_alg_equiv'_mul Matrix.toLinAlgEquiv'_mul

/- warning: linear_map.to_matrix_alg_equiv'_comp -> LinearMap.toMatrixAlgEquiv'_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_alg_equiv'_comp LinearMap.toMatrixAlgEquiv'_compₓ'. -/
theorem LinearMap.toMatrixAlgEquiv'_comp (f g : (n → R) →ₗ[R] n → R) :
    (f.comp g).toMatrixAlgEquiv' = f.toMatrixAlgEquiv' ⬝ g.toMatrixAlgEquiv' :=
  LinearMap.toMatrix'_comp _ _
#align linear_map.to_matrix_alg_equiv'_comp LinearMap.toMatrixAlgEquiv'_comp

/- warning: linear_map.to_matrix_alg_equiv'_mul -> LinearMap.toMatrixAlgEquiv'_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_alg_equiv'_mul LinearMap.toMatrixAlgEquiv'_mulₓ'. -/
theorem LinearMap.toMatrixAlgEquiv'_mul (f g : (n → R) →ₗ[R] n → R) :
    (f * g).toMatrixAlgEquiv' = f.toMatrixAlgEquiv' ⬝ g.toMatrixAlgEquiv' :=
  LinearMap.toMatrixAlgEquiv'_comp f g
#align linear_map.to_matrix_alg_equiv'_mul LinearMap.toMatrixAlgEquiv'_mul

end ToMatrix'

section ToMatrix

variable {R : Type _} [CommSemiring R]

variable {l m n : Type _} [Fintype n] [Fintype m] [DecidableEq n]

variable {M₁ M₂ : Type _} [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]

variable (v₁ : Basis n R M₁) (v₂ : Basis m R M₂)

#print LinearMap.toMatrix /-
/-- Given bases of two modules `M₁` and `M₂` over a commutative ring `R`, we get a linear
equivalence between linear maps `M₁ →ₗ M₂` and matrices over `R` indexed by the bases. -/
def LinearMap.toMatrix : (M₁ →ₗ[R] M₂) ≃ₗ[R] Matrix m n R :=
  LinearEquiv.trans (LinearEquiv.arrowCongr v₁.equivFun v₂.equivFun) LinearMap.toMatrix'
#align linear_map.to_matrix LinearMap.toMatrix
-/

/- warning: linear_map.to_matrix_eq_to_matrix' -> LinearMap.toMatrix_eq_toMatrix' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_eq_to_matrix' LinearMap.toMatrix_eq_toMatrix'ₓ'. -/
/-- `linear_map.to_matrix'` is a particular case of `linear_map.to_matrix`, for the standard basis
`pi.basis_fun R n`. -/
theorem LinearMap.toMatrix_eq_toMatrix' :
    LinearMap.toMatrix (Pi.basisFun R n) (Pi.basisFun R n) = LinearMap.toMatrix' :=
  rfl
#align linear_map.to_matrix_eq_to_matrix' LinearMap.toMatrix_eq_toMatrix'

#print Matrix.toLin /-
/-- Given bases of two modules `M₁` and `M₂` over a commutative ring `R`, we get a linear
equivalence between matrices over `R` indexed by the bases and linear maps `M₁ →ₗ M₂`. -/
def Matrix.toLin : Matrix m n R ≃ₗ[R] M₁ →ₗ[R] M₂ :=
  (LinearMap.toMatrix v₁ v₂).symm
#align matrix.to_lin Matrix.toLin
-/

/- warning: matrix.to_lin_eq_to_lin' -> Matrix.toLin_eq_toLin' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_lin_eq_to_lin' Matrix.toLin_eq_toLin'ₓ'. -/
/-- `matrix.to_lin'` is a particular case of `matrix.to_lin`, for the standard basis
`pi.basis_fun R n`. -/
theorem Matrix.toLin_eq_toLin' : Matrix.toLin (Pi.basisFun R n) (Pi.basisFun R m) = Matrix.toLin' :=
  rfl
#align matrix.to_lin_eq_to_lin' Matrix.toLin_eq_toLin'

/- warning: linear_map.to_matrix_symm -> LinearMap.toMatrix_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_symm LinearMap.toMatrix_symmₓ'. -/
@[simp]
theorem LinearMap.toMatrix_symm : (LinearMap.toMatrix v₁ v₂).symm = Matrix.toLin v₁ v₂ :=
  rfl
#align linear_map.to_matrix_symm LinearMap.toMatrix_symm

/- warning: matrix.to_lin_symm -> Matrix.toLin_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_lin_symm Matrix.toLin_symmₓ'. -/
@[simp]
theorem Matrix.toLin_symm : (Matrix.toLin v₁ v₂).symm = LinearMap.toMatrix v₁ v₂ :=
  rfl
#align matrix.to_lin_symm Matrix.toLin_symm

/- warning: matrix.to_lin_to_matrix -> Matrix.toLin_toMatrix is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_lin_to_matrix Matrix.toLin_toMatrixₓ'. -/
@[simp]
theorem Matrix.toLin_toMatrix (f : M₁ →ₗ[R] M₂) :
    Matrix.toLin v₁ v₂ (LinearMap.toMatrix v₁ v₂ f) = f := by
  rw [← Matrix.toLin_symm, LinearEquiv.apply_symm_apply]
#align matrix.to_lin_to_matrix Matrix.toLin_toMatrix

/- warning: linear_map.to_matrix_to_lin -> LinearMap.toMatrix_toLin is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_to_lin LinearMap.toMatrix_toLinₓ'. -/
@[simp]
theorem LinearMap.toMatrix_toLin (M : Matrix m n R) :
    LinearMap.toMatrix v₁ v₂ (Matrix.toLin v₁ v₂ M) = M := by
  rw [← Matrix.toLin_symm, LinearEquiv.symm_apply_apply]
#align linear_map.to_matrix_to_lin LinearMap.toMatrix_toLin

/- warning: linear_map.to_matrix_apply -> LinearMap.toMatrix_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_apply LinearMap.toMatrix_applyₓ'. -/
theorem LinearMap.toMatrix_apply (f : M₁ →ₗ[R] M₂) (i : m) (j : n) :
    LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i :=
  by
  rw [LinearMap.toMatrix, LinearEquiv.trans_apply, LinearMap.toMatrix'_apply,
    LinearEquiv.arrowCongr_apply, Basis.equivFun_symm_apply, Finset.sum_eq_single j, if_pos rfl,
    one_smul, Basis.equivFun_apply]
  · intro j' _ hj'
    rw [if_neg hj', zero_smul]
  · intro hj
    have := Finset.mem_univ j
    contradiction
#align linear_map.to_matrix_apply LinearMap.toMatrix_apply

/- warning: linear_map.to_matrix_transpose_apply -> LinearMap.toMatrix_transpose_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_transpose_apply LinearMap.toMatrix_transpose_applyₓ'. -/
theorem LinearMap.toMatrix_transpose_apply (f : M₁ →ₗ[R] M₂) (j : n) :
    (LinearMap.toMatrix v₁ v₂ f)ᵀ j = v₂.repr (f (v₁ j)) :=
  funext fun i => f.toMatrix_apply _ _ i j
#align linear_map.to_matrix_transpose_apply LinearMap.toMatrix_transpose_apply

/- warning: linear_map.to_matrix_apply' -> LinearMap.toMatrix_apply' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_apply' LinearMap.toMatrix_apply'ₓ'. -/
theorem LinearMap.toMatrix_apply' (f : M₁ →ₗ[R] M₂) (i : m) (j : n) :
    LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i :=
  LinearMap.toMatrix_apply v₁ v₂ f i j
#align linear_map.to_matrix_apply' LinearMap.toMatrix_apply'

/- warning: linear_map.to_matrix_transpose_apply' -> LinearMap.toMatrix_transpose_apply' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_transpose_apply' LinearMap.toMatrix_transpose_apply'ₓ'. -/
theorem LinearMap.toMatrix_transpose_apply' (f : M₁ →ₗ[R] M₂) (j : n) :
    (LinearMap.toMatrix v₁ v₂ f)ᵀ j = v₂.repr (f (v₁ j)) :=
  LinearMap.toMatrix_transpose_apply v₁ v₂ f j
#align linear_map.to_matrix_transpose_apply' LinearMap.toMatrix_transpose_apply'

/- warning: matrix.to_lin_apply -> Matrix.toLin_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_lin_apply Matrix.toLin_applyₓ'. -/
theorem Matrix.toLin_apply (M : Matrix m n R) (v : M₁) :
    Matrix.toLin v₁ v₂ M v = ∑ j, M.mulVec (v₁.repr v) j • v₂ j :=
  show v₂.equivFun.symm (Matrix.toLin' M (v₁.repr v)) = _ by
    rw [Matrix.toLin'_apply, v₂.equiv_fun_symm_apply]
#align matrix.to_lin_apply Matrix.toLin_apply

/- warning: matrix.to_lin_self -> Matrix.toLin_self is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_lin_self Matrix.toLin_selfₓ'. -/
@[simp]
theorem Matrix.toLin_self (M : Matrix m n R) (i : n) :
    Matrix.toLin v₁ v₂ M (v₁ i) = ∑ j, M j i • v₂ j :=
  by
  rw [Matrix.toLin_apply, Finset.sum_congr rfl fun j hj => _]
  rw [Basis.repr_self, Matrix.mulVec, dot_product, Finset.sum_eq_single i, Finsupp.single_eq_same,
    mul_one]
  · intro i' _ i'_ne; rw [Finsupp.single_eq_of_ne i'_ne.symm, MulZeroClass.mul_zero]
  · intros
    have := Finset.mem_univ i
    contradiction
#align matrix.to_lin_self Matrix.toLin_self

/- warning: linear_map.to_matrix_id -> LinearMap.toMatrix_id is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_id LinearMap.toMatrix_idₓ'. -/
/-- This will be a special case of `linear_map.to_matrix_id_eq_basis_to_matrix`. -/
theorem LinearMap.toMatrix_id : LinearMap.toMatrix v₁ v₁ id = 1 :=
  by
  ext (i j)
  simp [LinearMap.toMatrix_apply, Matrix.one_apply, Finsupp.single_apply, eq_comm]
#align linear_map.to_matrix_id LinearMap.toMatrix_id

/- warning: linear_map.to_matrix_one -> LinearMap.toMatrix_one is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_one LinearMap.toMatrix_oneₓ'. -/
theorem LinearMap.toMatrix_one : LinearMap.toMatrix v₁ v₁ 1 = 1 :=
  LinearMap.toMatrix_id v₁
#align linear_map.to_matrix_one LinearMap.toMatrix_one

/- warning: matrix.to_lin_one -> Matrix.toLin_one is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_lin_one Matrix.toLin_oneₓ'. -/
@[simp]
theorem Matrix.toLin_one : Matrix.toLin v₁ v₁ 1 = id := by
  rw [← LinearMap.toMatrix_id v₁, Matrix.toLin_toMatrix]
#align matrix.to_lin_one Matrix.toLin_one

/- warning: linear_map.to_matrix_reindex_range -> LinearMap.toMatrix_reindexRange is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_reindex_range LinearMap.toMatrix_reindexRangeₓ'. -/
theorem LinearMap.toMatrix_reindexRange [DecidableEq M₁] [DecidableEq M₂] (f : M₁ →ₗ[R] M₂) (k : m)
    (i : n) :
    LinearMap.toMatrix v₁.reindexRange v₂.reindexRange f ⟨v₂ k, mem_range_self k⟩
        ⟨v₁ i, mem_range_self i⟩ =
      LinearMap.toMatrix v₁ v₂ f k i :=
  by simp_rw [LinearMap.toMatrix_apply, Basis.reindexRange_self, Basis.reindexRange_repr]
#align linear_map.to_matrix_reindex_range LinearMap.toMatrix_reindexRange

variable {M₃ : Type _} [AddCommMonoid M₃] [Module R M₃] (v₃ : Basis l R M₃)

/- warning: linear_map.to_matrix_comp -> LinearMap.toMatrix_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_comp LinearMap.toMatrix_compₓ'. -/
theorem LinearMap.toMatrix_comp [Fintype l] [DecidableEq m] (f : M₂ →ₗ[R] M₃) (g : M₁ →ₗ[R] M₂) :
    LinearMap.toMatrix v₁ v₃ (f.comp g) = LinearMap.toMatrix v₂ v₃ f ⬝ LinearMap.toMatrix v₁ v₂ g :=
  by
  simp_rw [LinearMap.toMatrix, LinearEquiv.trans_apply, LinearEquiv.arrowCongr_comp _ v₂.equiv_fun,
    LinearMap.toMatrix'_comp]
#align linear_map.to_matrix_comp LinearMap.toMatrix_comp

/- warning: linear_map.to_matrix_mul -> LinearMap.toMatrix_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_mul LinearMap.toMatrix_mulₓ'. -/
theorem LinearMap.toMatrix_mul (f g : M₁ →ₗ[R] M₁) :
    LinearMap.toMatrix v₁ v₁ (f * g) = LinearMap.toMatrix v₁ v₁ f ⬝ LinearMap.toMatrix v₁ v₁ g := by
  rw [show @Mul.mul (M₁ →ₗ[R] M₁) _ = LinearMap.comp from rfl, LinearMap.toMatrix_comp v₁ v₁ v₁ f g]
#align linear_map.to_matrix_mul LinearMap.toMatrix_mul

/- warning: linear_map.to_matrix_algebra_map -> LinearMap.toMatrix_algebraMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_algebra_map LinearMap.toMatrix_algebraMapₓ'. -/
@[simp]
theorem LinearMap.toMatrix_algebraMap (x : R) :
    LinearMap.toMatrix v₁ v₁ (algebraMap R (Module.End R M₁) x) = scalar n x := by
  simp [Module.algebraMap_end_eq_smul_id, LinearMap.toMatrix_id]
#align linear_map.to_matrix_algebra_map LinearMap.toMatrix_algebraMap

/- warning: linear_map.to_matrix_mul_vec_repr -> LinearMap.toMatrix_mulVec_repr is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_mul_vec_repr LinearMap.toMatrix_mulVec_reprₓ'. -/
theorem LinearMap.toMatrix_mulVec_repr (f : M₁ →ₗ[R] M₂) (x : M₁) :
    (LinearMap.toMatrix v₁ v₂ f).mulVec (v₁.repr x) = v₂.repr (f x) :=
  by
  ext i
  rw [← Matrix.toLin'_apply, LinearMap.toMatrix, LinearEquiv.trans_apply, Matrix.toLin'_toMatrix',
    LinearEquiv.arrowCongr_apply, v₂.equiv_fun_apply]
  congr
  exact v₁.equiv_fun.symm_apply_apply x
#align linear_map.to_matrix_mul_vec_repr LinearMap.toMatrix_mulVec_repr

/- warning: linear_map.to_matrix_basis_equiv -> LinearMap.toMatrix_basis_equiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_basis_equiv LinearMap.toMatrix_basis_equivₓ'. -/
@[simp]
theorem LinearMap.toMatrix_basis_equiv [Fintype l] [DecidableEq l] (b : Basis l R M₁)
    (b' : Basis l R M₂) : LinearMap.toMatrix b' b (b'.Equiv b (Equiv.refl l) : M₂ →ₗ[R] M₁) = 1 :=
  by
  ext (i j)
  simp [LinearMap.toMatrix_apply, Matrix.one_apply, Finsupp.single_apply, eq_comm]
#align linear_map.to_matrix_basis_equiv LinearMap.toMatrix_basis_equiv

/- warning: matrix.to_lin_mul -> Matrix.toLin_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_lin_mul Matrix.toLin_mulₓ'. -/
theorem Matrix.toLin_mul [Fintype l] [DecidableEq m] (A : Matrix l m R) (B : Matrix m n R) :
    Matrix.toLin v₁ v₃ (A ⬝ B) = (Matrix.toLin v₂ v₃ A).comp (Matrix.toLin v₁ v₂ B) :=
  by
  apply (LinearMap.toMatrix v₁ v₃).Injective
  haveI : DecidableEq l := fun _ _ => Classical.propDecidable _
  rw [LinearMap.toMatrix_comp v₁ v₂ v₃]
  repeat' rw [LinearMap.toMatrix_toLin]
#align matrix.to_lin_mul Matrix.toLin_mul

/- warning: matrix.to_lin_mul_apply -> Matrix.toLin_mul_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_lin_mul_apply Matrix.toLin_mul_applyₓ'. -/
/-- Shortcut lemma for `matrix.to_lin_mul` and `linear_map.comp_apply`. -/
theorem Matrix.toLin_mul_apply [Fintype l] [DecidableEq m] (A : Matrix l m R) (B : Matrix m n R)
    (x) : Matrix.toLin v₁ v₃ (A ⬝ B) x = (Matrix.toLin v₂ v₃ A) (Matrix.toLin v₁ v₂ B x) := by
  rw [Matrix.toLin_mul v₁ v₂, LinearMap.comp_apply]
#align matrix.to_lin_mul_apply Matrix.toLin_mul_apply

/- warning: matrix.to_lin_of_inv -> Matrix.toLinOfInv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_lin_of_inv Matrix.toLinOfInvₓ'. -/
/-- If `M` and `M` are each other's inverse matrices, `matrix.to_lin M` and `matrix.to_lin M'`
form a linear equivalence. -/
@[simps]
def Matrix.toLinOfInv [DecidableEq m] {M : Matrix m n R} {M' : Matrix n m R} (hMM' : M ⬝ M' = 1)
    (hM'M : M' ⬝ M = 1) : M₁ ≃ₗ[R] M₂ :=
  { Matrix.toLin v₁ v₂ M with
    toFun := Matrix.toLin v₁ v₂ M
    invFun := Matrix.toLin v₂ v₁ M'
    left_inv := fun x => by rw [← Matrix.toLin_mul_apply, hM'M, Matrix.toLin_one, id_apply]
    right_inv := fun x => by rw [← Matrix.toLin_mul_apply, hMM', Matrix.toLin_one, id_apply] }
#align matrix.to_lin_of_inv Matrix.toLinOfInv

/- warning: linear_map.to_matrix_alg_equiv -> LinearMap.toMatrixAlgEquiv is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {n : Type.{u2}} [_inst_2 : Fintype.{u2} n] [_inst_4 : DecidableEq.{succ u2} n] {M₁ : Type.{u3}} [_inst_5 : AddCommMonoid.{u3} M₁] [_inst_7 : Module.{u1, u3} R M₁ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_5], (Basis.{u2, u1, u3} n R M₁ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_5 _inst_7) -> (AlgEquiv.{u1, u3, max u2 u1} R (LinearMap.{u1, u1, u3, u3} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) M₁ M₁ _inst_5 _inst_5 _inst_7 _inst_7) (Matrix.{u2, u2, u1} n n R) _inst_1 (Module.End.semiring.{u1, u3} R M₁ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_5 _inst_7) (Matrix.semiring.{u1, u2} n R (CommSemiring.toSemiring.{u1} R _inst_1) _inst_2 (fun (a : n) (b : n) => _inst_4 a b)) (Module.End.algebra.{u1, u3} R M₁ _inst_1 _inst_5 _inst_7) (Matrix.algebra.{u1, u2, u1} n R R _inst_2 (fun (a : n) (b : n) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {n : Type.{u2}} [_inst_2 : Fintype.{u2} n] [_inst_4 : DecidableEq.{succ u2} n] {M₁ : Type.{u3}} [_inst_5 : AddCommMonoid.{u3} M₁] [_inst_7 : Module.{u1, u3} R M₁ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_5], (Basis.{u2, u1, u3} n R M₁ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_5 _inst_7) -> (AlgEquiv.{u1, u3, max u1 u2} R (LinearMap.{u1, u1, u3, u3} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) M₁ M₁ _inst_5 _inst_5 _inst_7 _inst_7) (Matrix.{u2, u2, u1} n n R) _inst_1 (Module.End.semiring.{u1, u3} R M₁ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_5 _inst_7) (Matrix.semiring.{u1, u2} n R (CommSemiring.toSemiring.{u1} R _inst_1) _inst_2 (fun (a : n) (b : n) => _inst_4 a b)) (Module.instAlgebraEndToSemiringSemiring.{u1, u3} R M₁ _inst_1 _inst_5 _inst_7) (Matrix.instAlgebraMatrixSemiring.{u1, u2, u1} n R R _inst_2 (fun (a : n) (b : n) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1)))
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_alg_equiv LinearMap.toMatrixAlgEquivₓ'. -/
/-- Given a basis of a module `M₁` over a commutative ring `R`, we get an algebra
equivalence between linear maps `M₁ →ₗ M₁` and square matrices over `R` indexed by the basis. -/
def LinearMap.toMatrixAlgEquiv : (M₁ →ₗ[R] M₁) ≃ₐ[R] Matrix n n R :=
  AlgEquiv.ofLinearEquiv (LinearMap.toMatrix v₁ v₁) (LinearMap.toMatrix_mul v₁)
    (LinearMap.toMatrix_algebraMap v₁)
#align linear_map.to_matrix_alg_equiv LinearMap.toMatrixAlgEquiv

/- warning: matrix.to_lin_alg_equiv -> Matrix.toLinAlgEquiv is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {n : Type.{u2}} [_inst_2 : Fintype.{u2} n] [_inst_4 : DecidableEq.{succ u2} n] {M₁ : Type.{u3}} [_inst_5 : AddCommMonoid.{u3} M₁] [_inst_7 : Module.{u1, u3} R M₁ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_5], (Basis.{u2, u1, u3} n R M₁ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_5 _inst_7) -> (AlgEquiv.{u1, max u2 u1, u3} R (Matrix.{u2, u2, u1} n n R) (LinearMap.{u1, u1, u3, u3} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) M₁ M₁ _inst_5 _inst_5 _inst_7 _inst_7) _inst_1 (Matrix.semiring.{u1, u2} n R (CommSemiring.toSemiring.{u1} R _inst_1) _inst_2 (fun (a : n) (b : n) => _inst_4 a b)) (Module.End.semiring.{u1, u3} R M₁ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_5 _inst_7) (Matrix.algebra.{u1, u2, u1} n R R _inst_2 (fun (a : n) (b : n) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1)) (Module.End.algebra.{u1, u3} R M₁ _inst_1 _inst_5 _inst_7))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {n : Type.{u2}} [_inst_2 : Fintype.{u2} n] [_inst_4 : DecidableEq.{succ u2} n] {M₁ : Type.{u3}} [_inst_5 : AddCommMonoid.{u3} M₁] [_inst_7 : Module.{u1, u3} R M₁ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_5], (Basis.{u2, u1, u3} n R M₁ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_5 _inst_7) -> (AlgEquiv.{u1, max u1 u2, u3} R (Matrix.{u2, u2, u1} n n R) (LinearMap.{u1, u1, u3, u3} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) M₁ M₁ _inst_5 _inst_5 _inst_7 _inst_7) _inst_1 (Matrix.semiring.{u1, u2} n R (CommSemiring.toSemiring.{u1} R _inst_1) _inst_2 (fun (a : n) (b : n) => _inst_4 a b)) (Module.End.semiring.{u1, u3} R M₁ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_5 _inst_7) (Matrix.instAlgebraMatrixSemiring.{u1, u2, u1} n R R _inst_2 (fun (a : n) (b : n) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1)) (Module.instAlgebraEndToSemiringSemiring.{u1, u3} R M₁ _inst_1 _inst_5 _inst_7))
Case conversion may be inaccurate. Consider using '#align matrix.to_lin_alg_equiv Matrix.toLinAlgEquivₓ'. -/
/-- Given a basis of a module `M₁` over a commutative ring `R`, we get an algebra
equivalence between square matrices over `R` indexed by the basis and linear maps `M₁ →ₗ M₁`. -/
def Matrix.toLinAlgEquiv : Matrix n n R ≃ₐ[R] M₁ →ₗ[R] M₁ :=
  (LinearMap.toMatrixAlgEquiv v₁).symm
#align matrix.to_lin_alg_equiv Matrix.toLinAlgEquiv

/- warning: linear_map.to_matrix_alg_equiv_symm -> LinearMap.toMatrixAlgEquiv_symm is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {n : Type.{u2}} [_inst_2 : Fintype.{u2} n] [_inst_4 : DecidableEq.{succ u2} n] {M₁ : Type.{u3}} [_inst_5 : AddCommMonoid.{u3} M₁] [_inst_7 : Module.{u1, u3} R M₁ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_5] (v₁ : Basis.{u2, u1, u3} n R M₁ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_5 _inst_7), Eq.{max (succ (max u2 u1)) (succ u3)} (AlgEquiv.{u1, max u2 u1, u3} R (Matrix.{u2, u2, u1} n n R) (LinearMap.{u1, u1, u3, u3} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) M₁ M₁ _inst_5 _inst_5 _inst_7 _inst_7) _inst_1 (Matrix.semiring.{u1, u2} n R (CommSemiring.toSemiring.{u1} R _inst_1) _inst_2 (fun (a : n) (b : n) => _inst_4 a b)) (Module.End.semiring.{u1, u3} R M₁ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_5 _inst_7) (Matrix.algebra.{u1, u2, u1} n R R _inst_2 (fun (a : n) (b : n) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1)) (Module.End.algebra.{u1, u3} R M₁ _inst_1 _inst_5 _inst_7)) (AlgEquiv.symm.{u1, u3, max u2 u1} R (LinearMap.{u1, u1, u3, u3} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) M₁ M₁ _inst_5 _inst_5 _inst_7 _inst_7) (Matrix.{u2, u2, u1} n n R) _inst_1 (Module.End.semiring.{u1, u3} R M₁ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_5 _inst_7) (Matrix.semiring.{u1, u2} n R (CommSemiring.toSemiring.{u1} R _inst_1) _inst_2 (fun (a : n) (b : n) => _inst_4 a b)) (Module.End.algebra.{u1, u3} R M₁ _inst_1 _inst_5 _inst_7) (Matrix.algebra.{u1, u2, u1} n R R _inst_2 (fun (a : n) (b : n) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1)) (LinearMap.toMatrixAlgEquiv.{u1, u2, u3} R _inst_1 n _inst_2 (fun (a : n) (b : n) => _inst_4 a b) M₁ _inst_5 _inst_7 v₁)) (Matrix.toLinAlgEquiv.{u1, u2, u3} R _inst_1 n _inst_2 (fun (a : n) (b : n) => _inst_4 a b) M₁ _inst_5 _inst_7 v₁)
but is expected to have type
  forall {R : Type.{u3}} [_inst_1 : CommSemiring.{u3} R] {n : Type.{u2}} [_inst_2 : Fintype.{u2} n] [_inst_4 : DecidableEq.{succ u2} n] {M₁ : Type.{u1}} [_inst_5 : AddCommMonoid.{u1} M₁] [_inst_7 : Module.{u3, u1} R M₁ (CommSemiring.toSemiring.{u3} R _inst_1) _inst_5] (v₁ : Basis.{u2, u3, u1} n R M₁ (CommSemiring.toSemiring.{u3} R _inst_1) _inst_5 _inst_7), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (AlgEquiv.{u3, max u3 u2, u1} R (Matrix.{u2, u2, u3} n n R) (LinearMap.{u3, u3, u1, u1} R R (CommSemiring.toSemiring.{u3} R _inst_1) (CommSemiring.toSemiring.{u3} R _inst_1) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1))) M₁ M₁ _inst_5 _inst_5 _inst_7 _inst_7) _inst_1 (Matrix.semiring.{u3, u2} n R (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 (fun (a : n) (b : n) => _inst_4 a b)) (Module.End.semiring.{u3, u1} R M₁ (CommSemiring.toSemiring.{u3} R _inst_1) _inst_5 _inst_7) (Matrix.instAlgebraMatrixSemiring.{u3, u2, u3} n R R _inst_2 (fun (a : n) (b : n) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u3} R _inst_1) (Algebra.id.{u3} R _inst_1)) (Module.instAlgebraEndToSemiringSemiring.{u3, u1} R M₁ _inst_1 _inst_5 _inst_7)) (AlgEquiv.symm.{u3, u1, max u3 u2} R (LinearMap.{u3, u3, u1, u1} R R (CommSemiring.toSemiring.{u3} R _inst_1) (CommSemiring.toSemiring.{u3} R _inst_1) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1))) M₁ M₁ _inst_5 _inst_5 _inst_7 _inst_7) (Matrix.{u2, u2, u3} n n R) _inst_1 (Module.End.semiring.{u3, u1} R M₁ (CommSemiring.toSemiring.{u3} R _inst_1) _inst_5 _inst_7) (Matrix.semiring.{u3, u2} n R (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 (fun (a : n) (b : n) => _inst_4 a b)) (Module.instAlgebraEndToSemiringSemiring.{u3, u1} R M₁ _inst_1 _inst_5 _inst_7) (Matrix.instAlgebraMatrixSemiring.{u3, u2, u3} n R R _inst_2 (fun (a : n) (b : n) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u3} R _inst_1) (Algebra.id.{u3} R _inst_1)) (LinearMap.toMatrixAlgEquiv.{u3, u2, u1} R _inst_1 n _inst_2 (fun (a : n) (b : n) => _inst_4 a b) M₁ _inst_5 _inst_7 v₁)) (Matrix.toLinAlgEquiv.{u3, u2, u1} R _inst_1 n _inst_2 (fun (a : n) (b : n) => _inst_4 a b) M₁ _inst_5 _inst_7 v₁)
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_alg_equiv_symm LinearMap.toMatrixAlgEquiv_symmₓ'. -/
@[simp]
theorem LinearMap.toMatrixAlgEquiv_symm :
    (LinearMap.toMatrixAlgEquiv v₁).symm = Matrix.toLinAlgEquiv v₁ :=
  rfl
#align linear_map.to_matrix_alg_equiv_symm LinearMap.toMatrixAlgEquiv_symm

/- warning: matrix.to_lin_alg_equiv_symm -> Matrix.toLinAlgEquiv_symm is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {n : Type.{u2}} [_inst_2 : Fintype.{u2} n] [_inst_4 : DecidableEq.{succ u2} n] {M₁ : Type.{u3}} [_inst_5 : AddCommMonoid.{u3} M₁] [_inst_7 : Module.{u1, u3} R M₁ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_5] (v₁ : Basis.{u2, u1, u3} n R M₁ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_5 _inst_7), Eq.{max (succ u3) (succ (max u2 u1))} (AlgEquiv.{u1, u3, max u2 u1} R (LinearMap.{u1, u1, u3, u3} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) M₁ M₁ _inst_5 _inst_5 _inst_7 _inst_7) (Matrix.{u2, u2, u1} n n R) _inst_1 (Module.End.semiring.{u1, u3} R M₁ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_5 _inst_7) (Matrix.semiring.{u1, u2} n R (CommSemiring.toSemiring.{u1} R _inst_1) _inst_2 (fun (a : n) (b : n) => _inst_4 a b)) (Module.End.algebra.{u1, u3} R M₁ _inst_1 _inst_5 _inst_7) (Matrix.algebra.{u1, u2, u1} n R R _inst_2 (fun (a : n) (b : n) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1))) (AlgEquiv.symm.{u1, max u2 u1, u3} R (Matrix.{u2, u2, u1} n n R) (LinearMap.{u1, u1, u3, u3} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) M₁ M₁ _inst_5 _inst_5 _inst_7 _inst_7) _inst_1 (Matrix.semiring.{u1, u2} n R (CommSemiring.toSemiring.{u1} R _inst_1) _inst_2 (fun (a : n) (b : n) => _inst_4 a b)) (Module.End.semiring.{u1, u3} R M₁ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_5 _inst_7) (Matrix.algebra.{u1, u2, u1} n R R _inst_2 (fun (a : n) (b : n) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1)) (Module.End.algebra.{u1, u3} R M₁ _inst_1 _inst_5 _inst_7) (Matrix.toLinAlgEquiv.{u1, u2, u3} R _inst_1 n _inst_2 (fun (a : n) (b : n) => _inst_4 a b) M₁ _inst_5 _inst_7 v₁)) (LinearMap.toMatrixAlgEquiv.{u1, u2, u3} R _inst_1 n _inst_2 (fun (a : n) (b : n) => _inst_4 a b) M₁ _inst_5 _inst_7 v₁)
but is expected to have type
  forall {R : Type.{u3}} [_inst_1 : CommSemiring.{u3} R] {n : Type.{u2}} [_inst_2 : Fintype.{u2} n] [_inst_4 : DecidableEq.{succ u2} n] {M₁ : Type.{u1}} [_inst_5 : AddCommMonoid.{u1} M₁] [_inst_7 : Module.{u3, u1} R M₁ (CommSemiring.toSemiring.{u3} R _inst_1) _inst_5] (v₁ : Basis.{u2, u3, u1} n R M₁ (CommSemiring.toSemiring.{u3} R _inst_1) _inst_5 _inst_7), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (AlgEquiv.{u3, u1, max u3 u2} R (LinearMap.{u3, u3, u1, u1} R R (CommSemiring.toSemiring.{u3} R _inst_1) (CommSemiring.toSemiring.{u3} R _inst_1) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1))) M₁ M₁ _inst_5 _inst_5 _inst_7 _inst_7) (Matrix.{u2, u2, u3} n n R) _inst_1 (Module.End.semiring.{u3, u1} R M₁ (CommSemiring.toSemiring.{u3} R _inst_1) _inst_5 _inst_7) (Matrix.semiring.{u3, u2} n R (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 (fun (a : n) (b : n) => _inst_4 a b)) (Module.instAlgebraEndToSemiringSemiring.{u3, u1} R M₁ _inst_1 _inst_5 _inst_7) (Matrix.instAlgebraMatrixSemiring.{u3, u2, u3} n R R _inst_2 (fun (a : n) (b : n) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u3} R _inst_1) (Algebra.id.{u3} R _inst_1))) (AlgEquiv.symm.{u3, max u3 u2, u1} R (Matrix.{u2, u2, u3} n n R) (LinearMap.{u3, u3, u1, u1} R R (CommSemiring.toSemiring.{u3} R _inst_1) (CommSemiring.toSemiring.{u3} R _inst_1) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1))) M₁ M₁ _inst_5 _inst_5 _inst_7 _inst_7) _inst_1 (Matrix.semiring.{u3, u2} n R (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 (fun (a : n) (b : n) => _inst_4 a b)) (Module.End.semiring.{u3, u1} R M₁ (CommSemiring.toSemiring.{u3} R _inst_1) _inst_5 _inst_7) (Matrix.instAlgebraMatrixSemiring.{u3, u2, u3} n R R _inst_2 (fun (a : n) (b : n) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u3} R _inst_1) (Algebra.id.{u3} R _inst_1)) (Module.instAlgebraEndToSemiringSemiring.{u3, u1} R M₁ _inst_1 _inst_5 _inst_7) (Matrix.toLinAlgEquiv.{u3, u2, u1} R _inst_1 n _inst_2 (fun (a : n) (b : n) => _inst_4 a b) M₁ _inst_5 _inst_7 v₁)) (LinearMap.toMatrixAlgEquiv.{u3, u2, u1} R _inst_1 n _inst_2 (fun (a : n) (b : n) => _inst_4 a b) M₁ _inst_5 _inst_7 v₁)
Case conversion may be inaccurate. Consider using '#align matrix.to_lin_alg_equiv_symm Matrix.toLinAlgEquiv_symmₓ'. -/
@[simp]
theorem Matrix.toLinAlgEquiv_symm :
    (Matrix.toLinAlgEquiv v₁).symm = LinearMap.toMatrixAlgEquiv v₁ :=
  rfl
#align matrix.to_lin_alg_equiv_symm Matrix.toLinAlgEquiv_symm

/- warning: matrix.to_lin_alg_equiv_to_matrix_alg_equiv -> Matrix.toLinAlgEquiv_toMatrixAlgEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_lin_alg_equiv_to_matrix_alg_equiv Matrix.toLinAlgEquiv_toMatrixAlgEquivₓ'. -/
@[simp]
theorem Matrix.toLinAlgEquiv_toMatrixAlgEquiv (f : M₁ →ₗ[R] M₁) :
    Matrix.toLinAlgEquiv v₁ (LinearMap.toMatrixAlgEquiv v₁ f) = f := by
  rw [← Matrix.toLinAlgEquiv_symm, AlgEquiv.apply_symm_apply]
#align matrix.to_lin_alg_equiv_to_matrix_alg_equiv Matrix.toLinAlgEquiv_toMatrixAlgEquiv

/- warning: linear_map.to_matrix_alg_equiv_to_lin_alg_equiv -> LinearMap.toMatrixAlgEquiv_toLinAlgEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_alg_equiv_to_lin_alg_equiv LinearMap.toMatrixAlgEquiv_toLinAlgEquivₓ'. -/
@[simp]
theorem LinearMap.toMatrixAlgEquiv_toLinAlgEquiv (M : Matrix n n R) :
    LinearMap.toMatrixAlgEquiv v₁ (Matrix.toLinAlgEquiv v₁ M) = M := by
  rw [← Matrix.toLinAlgEquiv_symm, AlgEquiv.symm_apply_apply]
#align linear_map.to_matrix_alg_equiv_to_lin_alg_equiv LinearMap.toMatrixAlgEquiv_toLinAlgEquiv

/- warning: linear_map.to_matrix_alg_equiv_apply -> LinearMap.toMatrixAlgEquiv_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_alg_equiv_apply LinearMap.toMatrixAlgEquiv_applyₓ'. -/
theorem LinearMap.toMatrixAlgEquiv_apply (f : M₁ →ₗ[R] M₁) (i j : n) :
    LinearMap.toMatrixAlgEquiv v₁ f i j = v₁.repr (f (v₁ j)) i := by
  simp [LinearMap.toMatrixAlgEquiv, LinearMap.toMatrix_apply]
#align linear_map.to_matrix_alg_equiv_apply LinearMap.toMatrixAlgEquiv_apply

/- warning: linear_map.to_matrix_alg_equiv_transpose_apply -> LinearMap.toMatrixAlgEquiv_transpose_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_alg_equiv_transpose_apply LinearMap.toMatrixAlgEquiv_transpose_applyₓ'. -/
theorem LinearMap.toMatrixAlgEquiv_transpose_apply (f : M₁ →ₗ[R] M₁) (j : n) :
    (LinearMap.toMatrixAlgEquiv v₁ f)ᵀ j = v₁.repr (f (v₁ j)) :=
  funext fun i => f.toMatrix_apply _ _ i j
#align linear_map.to_matrix_alg_equiv_transpose_apply LinearMap.toMatrixAlgEquiv_transpose_apply

/- warning: linear_map.to_matrix_alg_equiv_apply' -> LinearMap.toMatrixAlgEquiv_apply' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_alg_equiv_apply' LinearMap.toMatrixAlgEquiv_apply'ₓ'. -/
theorem LinearMap.toMatrixAlgEquiv_apply' (f : M₁ →ₗ[R] M₁) (i j : n) :
    LinearMap.toMatrixAlgEquiv v₁ f i j = v₁.repr (f (v₁ j)) i :=
  LinearMap.toMatrixAlgEquiv_apply v₁ f i j
#align linear_map.to_matrix_alg_equiv_apply' LinearMap.toMatrixAlgEquiv_apply'

/- warning: linear_map.to_matrix_alg_equiv_transpose_apply' -> LinearMap.toMatrixAlgEquiv_transpose_apply' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_alg_equiv_transpose_apply' LinearMap.toMatrixAlgEquiv_transpose_apply'ₓ'. -/
theorem LinearMap.toMatrixAlgEquiv_transpose_apply' (f : M₁ →ₗ[R] M₁) (j : n) :
    (LinearMap.toMatrixAlgEquiv v₁ f)ᵀ j = v₁.repr (f (v₁ j)) :=
  LinearMap.toMatrixAlgEquiv_transpose_apply v₁ f j
#align linear_map.to_matrix_alg_equiv_transpose_apply' LinearMap.toMatrixAlgEquiv_transpose_apply'

/- warning: matrix.to_lin_alg_equiv_apply -> Matrix.toLinAlgEquiv_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_lin_alg_equiv_apply Matrix.toLinAlgEquiv_applyₓ'. -/
theorem Matrix.toLinAlgEquiv_apply (M : Matrix n n R) (v : M₁) :
    Matrix.toLinAlgEquiv v₁ M v = ∑ j, M.mulVec (v₁.repr v) j • v₁ j :=
  show v₁.equivFun.symm (Matrix.toLinAlgEquiv' M (v₁.repr v)) = _ by
    rw [Matrix.toLinAlgEquiv'_apply, v₁.equiv_fun_symm_apply]
#align matrix.to_lin_alg_equiv_apply Matrix.toLinAlgEquiv_apply

/- warning: matrix.to_lin_alg_equiv_self -> Matrix.toLinAlgEquiv_self is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_lin_alg_equiv_self Matrix.toLinAlgEquiv_selfₓ'. -/
@[simp]
theorem Matrix.toLinAlgEquiv_self (M : Matrix n n R) (i : n) :
    Matrix.toLinAlgEquiv v₁ M (v₁ i) = ∑ j, M j i • v₁ j :=
  Matrix.toLin_self _ _ _ _
#align matrix.to_lin_alg_equiv_self Matrix.toLinAlgEquiv_self

/- warning: linear_map.to_matrix_alg_equiv_id -> LinearMap.toMatrixAlgEquiv_id is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_alg_equiv_id LinearMap.toMatrixAlgEquiv_idₓ'. -/
theorem LinearMap.toMatrixAlgEquiv_id : LinearMap.toMatrixAlgEquiv v₁ id = 1 := by
  simp_rw [LinearMap.toMatrixAlgEquiv, AlgEquiv.ofLinearEquiv_apply, LinearMap.toMatrix_id]
#align linear_map.to_matrix_alg_equiv_id LinearMap.toMatrixAlgEquiv_id

/- warning: matrix.to_lin_alg_equiv_one -> Matrix.toLinAlgEquiv_one is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_lin_alg_equiv_one Matrix.toLinAlgEquiv_oneₓ'. -/
@[simp]
theorem Matrix.toLinAlgEquiv_one : Matrix.toLinAlgEquiv v₁ 1 = id := by
  rw [← LinearMap.toMatrixAlgEquiv_id v₁, Matrix.toLinAlgEquiv_toMatrixAlgEquiv]
#align matrix.to_lin_alg_equiv_one Matrix.toLinAlgEquiv_one

/- warning: linear_map.to_matrix_alg_equiv_reindex_range -> LinearMap.toMatrixAlgEquiv_reindexRange is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_alg_equiv_reindex_range LinearMap.toMatrixAlgEquiv_reindexRangeₓ'. -/
theorem LinearMap.toMatrixAlgEquiv_reindexRange [DecidableEq M₁] (f : M₁ →ₗ[R] M₁) (k i : n) :
    LinearMap.toMatrixAlgEquiv v₁.reindexRange f ⟨v₁ k, mem_range_self k⟩ ⟨v₁ i, mem_range_self i⟩ =
      LinearMap.toMatrixAlgEquiv v₁ f k i :=
  by simp_rw [LinearMap.toMatrixAlgEquiv_apply, Basis.reindexRange_self, Basis.reindexRange_repr]
#align linear_map.to_matrix_alg_equiv_reindex_range LinearMap.toMatrixAlgEquiv_reindexRange

/- warning: linear_map.to_matrix_alg_equiv_comp -> LinearMap.toMatrixAlgEquiv_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_alg_equiv_comp LinearMap.toMatrixAlgEquiv_compₓ'. -/
theorem LinearMap.toMatrixAlgEquiv_comp (f g : M₁ →ₗ[R] M₁) :
    LinearMap.toMatrixAlgEquiv v₁ (f.comp g) =
      LinearMap.toMatrixAlgEquiv v₁ f ⬝ LinearMap.toMatrixAlgEquiv v₁ g :=
  by simp [LinearMap.toMatrixAlgEquiv, LinearMap.toMatrix_comp v₁ v₁ v₁ f g]
#align linear_map.to_matrix_alg_equiv_comp LinearMap.toMatrixAlgEquiv_comp

/- warning: linear_map.to_matrix_alg_equiv_mul -> LinearMap.toMatrixAlgEquiv_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_matrix_alg_equiv_mul LinearMap.toMatrixAlgEquiv_mulₓ'. -/
theorem LinearMap.toMatrixAlgEquiv_mul (f g : M₁ →ₗ[R] M₁) :
    LinearMap.toMatrixAlgEquiv v₁ (f * g) =
      LinearMap.toMatrixAlgEquiv v₁ f ⬝ LinearMap.toMatrixAlgEquiv v₁ g :=
  by
  rw [show @Mul.mul (M₁ →ₗ[R] M₁) _ = LinearMap.comp from rfl,
    LinearMap.toMatrixAlgEquiv_comp v₁ f g]
#align linear_map.to_matrix_alg_equiv_mul LinearMap.toMatrixAlgEquiv_mul

/- warning: matrix.to_lin_alg_equiv_mul -> Matrix.toLinAlgEquiv_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_lin_alg_equiv_mul Matrix.toLinAlgEquiv_mulₓ'. -/
theorem Matrix.toLinAlgEquiv_mul (A B : Matrix n n R) :
    Matrix.toLinAlgEquiv v₁ (A ⬝ B) =
      (Matrix.toLinAlgEquiv v₁ A).comp (Matrix.toLinAlgEquiv v₁ B) :=
  by convert Matrix.toLin_mul v₁ v₁ v₁ A B
#align matrix.to_lin_alg_equiv_mul Matrix.toLinAlgEquiv_mul

/- warning: matrix.to_lin_fin_two_prod_apply -> Matrix.toLin_finTwoProd_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_lin_fin_two_prod_apply Matrix.toLin_finTwoProd_applyₓ'. -/
@[simp]
theorem Matrix.toLin_finTwoProd_apply (a b c d : R) (x : R × R) :
    Matrix.toLin (Basis.finTwoProd R) (Basis.finTwoProd R) !![a, b; c, d] x =
      (a * x.fst + b * x.snd, c * x.fst + d * x.snd) :=
  by simp [Matrix.toLin_apply, Matrix.mulVec, Matrix.dotProduct]
#align matrix.to_lin_fin_two_prod_apply Matrix.toLin_finTwoProd_apply

/- warning: matrix.to_lin_fin_two_prod -> Matrix.toLin_finTwoProd is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.to_lin_fin_two_prod Matrix.toLin_finTwoProdₓ'. -/
theorem Matrix.toLin_finTwoProd (a b c d : R) :
    Matrix.toLin (Basis.finTwoProd R) (Basis.finTwoProd R) !![a, b; c, d] =
      (a • LinearMap.fst R R R + b • LinearMap.snd R R R).Prod
        (c • LinearMap.fst R R R + d • LinearMap.snd R R R) :=
  LinearMap.ext <| Matrix.toLin_finTwoProd_apply _ _ _ _
#align matrix.to_lin_fin_two_prod Matrix.toLin_finTwoProd

/- warning: to_matrix_distrib_mul_action_to_linear_map -> toMatrix_distrib_mul_action_toLinearMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align to_matrix_distrib_mul_action_to_linear_map toMatrix_distrib_mul_action_toLinearMapₓ'. -/
@[simp]
theorem toMatrix_distrib_mul_action_toLinearMap (x : R) :
    LinearMap.toMatrix v₁ v₁ (DistribMulAction.toLinearMap R M₁ x) = Matrix.diagonal fun _ => x :=
  by
  ext
  rw [LinearMap.toMatrix_apply, DistribMulAction.toLinearMap_apply, LinearEquiv.map_smul,
    Basis.repr_self, Finsupp.smul_single_one, Finsupp.single_eq_pi_single, Matrix.diagonal_apply,
    Pi.single_apply]
#align to_matrix_distrib_mul_action_to_linear_map toMatrix_distrib_mul_action_toLinearMap

end ToMatrix

namespace Algebra

section Lmul

variable {R S : Type _} [CommRing R] [Ring S] [Algebra R S]

variable {m : Type _} [Fintype m] [DecidableEq m] (b : Basis m R S)

/- warning: algebra.to_matrix_lmul' -> Algebra.toMatrix_lmul' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.to_matrix_lmul' Algebra.toMatrix_lmul'ₓ'. -/
theorem toMatrix_lmul' (x : S) (i j) :
    LinearMap.toMatrix b b (lmul R S x) i j = b.repr (x * b j) i := by
  simp only [LinearMap.toMatrix_apply', coe_lmul_eq_mul, LinearMap.mul_apply']
#align algebra.to_matrix_lmul' Algebra.toMatrix_lmul'

/- warning: algebra.to_matrix_lsmul -> Algebra.toMatrix_lsmul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.to_matrix_lsmul Algebra.toMatrix_lsmulₓ'. -/
@[simp]
theorem toMatrix_lsmul (x : R) :
    LinearMap.toMatrix b b (Algebra.lsmul R S x) = Matrix.diagonal fun _ => x :=
  toMatrix_distrib_mul_action_toLinearMap b x
#align algebra.to_matrix_lsmul Algebra.toMatrix_lsmul

/- warning: algebra.left_mul_matrix -> Algebra.leftMulMatrix is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Ring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S _inst_2)] {m : Type.{u3}} [_inst_4 : Fintype.{u3} m] [_inst_5 : DecidableEq.{succ u3} m], (Basis.{u3, u1, u2} m R S (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} S (NonUnitalNonAssocRing.toAddCommGroup.{u2} S (NonAssocRing.toNonUnitalNonAssocRing.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2)))) (Algebra.toModule.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S _inst_2) _inst_3)) -> (AlgHom.{u1, u2, max u3 u1} R S (Matrix.{u3, u3, u1} m m R) (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S _inst_2) (Matrix.semiring.{u1, u3} m R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) _inst_4 (fun (a : m) (b : m) => _inst_5 a b)) _inst_3 (Matrix.algebra.{u1, u3, u1} m R R _inst_4 (fun (a : m) (b : m) => _inst_5 a b) (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Algebra.id.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Ring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S _inst_2)] {m : Type.{u3}} [_inst_4 : Fintype.{u3} m] [_inst_5 : DecidableEq.{succ u3} m], (Basis.{u3, u1, u2} m R S (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} S (NonAssocRing.toNonUnitalNonAssocRing.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2)))) (Algebra.toModule.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S _inst_2) _inst_3)) -> (AlgHom.{u1, u2, max u1 u3} R S (Matrix.{u3, u3, u1} m m R) (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S _inst_2) (Matrix.semiring.{u1, u3} m R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) _inst_4 (fun (a : m) (b : m) => _inst_5 a b)) _inst_3 (Matrix.instAlgebraMatrixSemiring.{u1, u3, u1} m R R _inst_4 (fun (a : m) (b : m) => _inst_5 a b) (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (Algebra.id.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align algebra.left_mul_matrix Algebra.leftMulMatrixₓ'. -/
/-- `left_mul_matrix b x` is the matrix corresponding to the linear map `λ y, x * y`.

`left_mul_matrix_eq_repr_mul` gives a formula for the entries of `left_mul_matrix`.

This definition is useful for doing (more) explicit computations with `linear_map.mul_left`,
such as the trace form or norm map for algebras.
-/
noncomputable def leftMulMatrix : S →ₐ[R] Matrix m m R
    where
  toFun x := LinearMap.toMatrix b b (Algebra.lmul R S x)
  map_zero' := by rw [AlgHom.map_zero, LinearEquiv.map_zero]
  map_one' := by rw [AlgHom.map_one, LinearMap.toMatrix_one]
  map_add' x y := by rw [AlgHom.map_add, LinearEquiv.map_add]
  map_mul' x y := by rw [AlgHom.map_mul, LinearMap.toMatrix_mul, Matrix.mul_eq_mul]
  commutes' r := by ext;
    rw [lmul_algebra_map, to_matrix_lsmul, algebra_map_eq_diagonal, Pi.algebraMap_def,
      Algebra.id.map_eq_self]
#align algebra.left_mul_matrix Algebra.leftMulMatrix

/- warning: algebra.left_mul_matrix_apply -> Algebra.leftMulMatrix_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.left_mul_matrix_apply Algebra.leftMulMatrix_applyₓ'. -/
theorem leftMulMatrix_apply (x : S) : leftMulMatrix b x = LinearMap.toMatrix b b (lmul R S x) :=
  rfl
#align algebra.left_mul_matrix_apply Algebra.leftMulMatrix_apply

/- warning: algebra.left_mul_matrix_eq_repr_mul -> Algebra.leftMulMatrix_eq_repr_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.left_mul_matrix_eq_repr_mul Algebra.leftMulMatrix_eq_repr_mulₓ'. -/
theorem leftMulMatrix_eq_repr_mul (x : S) (i j) : leftMulMatrix b x i j = b.repr (x * b j) i :=
  by-- This is defeq to just `to_matrix_lmul' b x i j`,
  -- but the unfolding goes a lot faster with this explicit `rw`.
  rw [left_mul_matrix_apply, to_matrix_lmul' b x i j]
#align algebra.left_mul_matrix_eq_repr_mul Algebra.leftMulMatrix_eq_repr_mul

/- warning: algebra.left_mul_matrix_mul_vec_repr -> Algebra.leftMulMatrix_mulVec_repr is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.left_mul_matrix_mul_vec_repr Algebra.leftMulMatrix_mulVec_reprₓ'. -/
theorem leftMulMatrix_mulVec_repr (x y : S) :
    (leftMulMatrix b x).mulVec (b.repr y) = b.repr (x * y) :=
  (LinearMap.mulLeft R x).toMatrix_mulVec_repr b b y
#align algebra.left_mul_matrix_mul_vec_repr Algebra.leftMulMatrix_mulVec_repr

/- warning: algebra.to_matrix_lmul_eq -> Algebra.toMatrix_lmul_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.to_matrix_lmul_eq Algebra.toMatrix_lmul_eqₓ'. -/
@[simp]
theorem toMatrix_lmul_eq (x : S) :
    LinearMap.toMatrix b b (LinearMap.mulLeft R x) = leftMulMatrix b x :=
  rfl
#align algebra.to_matrix_lmul_eq Algebra.toMatrix_lmul_eq

/- warning: algebra.left_mul_matrix_injective -> Algebra.leftMulMatrix_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.left_mul_matrix_injective Algebra.leftMulMatrix_injectiveₓ'. -/
theorem leftMulMatrix_injective : Function.Injective (leftMulMatrix b) := fun x x' h =>
  calc
    x = Algebra.lmul R S x 1 := (mul_one x).symm
    _ = Algebra.lmul R S x' 1 := by rw [(LinearMap.toMatrix b b).Injective h]
    _ = x' := mul_one x'
    
#align algebra.left_mul_matrix_injective Algebra.leftMulMatrix_injective

end Lmul

section LmulTower

variable {R S T : Type _} [CommRing R] [CommRing S] [Ring T]

variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

variable {m n : Type _} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

variable (b : Basis m R S) (c : Basis n S T)

/- warning: algebra.smul_left_mul_matrix -> Algebra.smul_leftMulMatrix is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.smul_left_mul_matrix Algebra.smul_leftMulMatrixₓ'. -/
theorem smul_leftMulMatrix (x) (ik jk) :
    leftMulMatrix (b.smul c) x ik jk = leftMulMatrix b (leftMulMatrix c x ik.2 jk.2) ik.1 jk.1 := by
  simp only [left_mul_matrix_apply, LinearMap.toMatrix_apply, mul_comm, Basis.smul_apply,
    Basis.smul_repr, Finsupp.smul_apply, id.smul_eq_mul, LinearEquiv.map_smul, mul_smul_comm,
    coe_lmul_eq_mul, LinearMap.mul_apply']
#align algebra.smul_left_mul_matrix Algebra.smul_leftMulMatrix

/- warning: algebra.smul_left_mul_matrix_algebra_map -> Algebra.smul_leftMulMatrix_algebraMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.smul_left_mul_matrix_algebra_map Algebra.smul_leftMulMatrix_algebraMapₓ'. -/
theorem smul_leftMulMatrix_algebraMap (x : S) :
    leftMulMatrix (b.smul c) (algebraMap _ _ x) = blockDiagonal fun k => leftMulMatrix b x :=
  by
  ext (⟨i, k⟩⟨j, k'⟩)
  rw [smul_left_mul_matrix, AlgHom.commutes, block_diagonal_apply, algebra_map_matrix_apply]
  split_ifs with h <;> simp [h]
#align algebra.smul_left_mul_matrix_algebra_map Algebra.smul_leftMulMatrix_algebraMap

/- warning: algebra.smul_left_mul_matrix_algebra_map_eq -> Algebra.smul_leftMulMatrix_algebraMap_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.smul_left_mul_matrix_algebra_map_eq Algebra.smul_leftMulMatrix_algebraMap_eqₓ'. -/
theorem smul_leftMulMatrix_algebraMap_eq (x : S) (i j k) :
    leftMulMatrix (b.smul c) (algebraMap _ _ x) (i, k) (j, k) = leftMulMatrix b x i j := by
  rw [smul_left_mul_matrix_algebra_map, block_diagonal_apply_eq]
#align algebra.smul_left_mul_matrix_algebra_map_eq Algebra.smul_leftMulMatrix_algebraMap_eq

/- warning: algebra.smul_left_mul_matrix_algebra_map_ne -> Algebra.smul_leftMulMatrix_algebraMap_ne is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.smul_left_mul_matrix_algebra_map_ne Algebra.smul_leftMulMatrix_algebraMap_neₓ'. -/
theorem smul_leftMulMatrix_algebraMap_ne (x : S) (i j) {k k'} (h : k ≠ k') :
    leftMulMatrix (b.smul c) (algebraMap _ _ x) (i, k) (j, k') = 0 := by
  rw [smul_left_mul_matrix_algebra_map, block_diagonal_apply_ne _ _ _ h]
#align algebra.smul_left_mul_matrix_algebra_map_ne Algebra.smul_leftMulMatrix_algebraMap_ne

end LmulTower

end Algebra

section

variable {R : Type v} [CommRing R] {n : Type _} [DecidableEq n]

variable {M M₁ M₂ : Type _} [AddCommGroup M] [Module R M]

variable [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]

/- warning: alg_equiv_matrix' -> algEquivMatrix' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {n : Type.{u2}} [_inst_2 : DecidableEq.{succ u2} n] [_inst_9 : Fintype.{u2} n], AlgEquiv.{u1, max u2 u1, max u2 u1} R (Module.End.{u1, max u2 u1} R (n -> R) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Pi.addCommMonoid.{u2, u1} n (fun (ᾰ : n) => R) (fun (i : n) => AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (Pi.Function.module.{u2, u1, u1} n R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Matrix.{u2, u2, u1} n n R) (CommRing.toCommSemiring.{u1} R _inst_1) (Module.End.semiring.{u1, max u2 u1} R (n -> R) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Pi.addCommMonoid.{u2, u1} n (fun (ᾰ : n) => R) (fun (i : n) => AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (Pi.Function.module.{u2, u1, u1} n R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Matrix.semiring.{u1, u2} n R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) _inst_9 (fun (a : n) (b : n) => _inst_2 a b)) (Module.End.algebra.{u1, max u2 u1} R (n -> R) (CommRing.toCommSemiring.{u1} R _inst_1) (Pi.addCommMonoid.{u2, u1} n (fun (ᾰ : n) => R) (fun (i : n) => AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (Pi.Function.module.{u2, u1, u1} n R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Matrix.algebra.{u1, u2, u1} n R R _inst_9 (fun (a : n) (b : n) => _inst_2 a b) (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Algebra.id.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {n : Type.{u2}} [_inst_2 : DecidableEq.{succ u2} n] [_inst_9 : Fintype.{u2} n], AlgEquiv.{u1, max u1 u2, max u1 u2} R (Module.End.{u1, max u1 u2} R (n -> R) (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (Pi.addCommMonoid.{u2, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (Pi.module.{u2, u1, u1} n (fun (a._@.Mathlib.LinearAlgebra.Matrix.ToLin._hyg.11287 : n) => R) R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (fun (i : n) => Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) (Matrix.{u2, u2, u1} n n R) (CommRing.toCommSemiring.{u1} R _inst_1) (Module.End.semiring.{u1, max u1 u2} R (n -> R) (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (Pi.addCommMonoid.{u2, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (Pi.module.{u2, u1, u1} n (fun (a._@.Mathlib.LinearAlgebra.Matrix.ToLin._hyg.11287 : n) => R) R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (fun (i : n) => Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) (Matrix.semiring.{u1, u2} n R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) _inst_9 (fun (a : n) (b : n) => _inst_2 a b)) (Module.instAlgebraEndToSemiringSemiring.{u1, max u1 u2} R (n -> R) (CommRing.toCommSemiring.{u1} R _inst_1) (Pi.addCommMonoid.{u2, u1} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (Pi.module.{u2, u1, u1} n (fun (a._@.Mathlib.LinearAlgebra.Matrix.ToLin._hyg.11287 : n) => R) R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (fun (i : n) => Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) (Matrix.instAlgebraMatrixSemiring.{u1, u2, u1} n R R _inst_9 (fun (a : n) (b : n) => _inst_2 a b) (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (Algebra.id.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))
Case conversion may be inaccurate. Consider using '#align alg_equiv_matrix' algEquivMatrix'ₓ'. -/
/-- The natural equivalence between linear endomorphisms of finite free modules and square matrices
is compatible with the algebra structures. -/
def algEquivMatrix' [Fintype n] : Module.End R (n → R) ≃ₐ[R] Matrix n n R :=
  { LinearMap.toMatrix' with
    map_mul' := LinearMap.toMatrix'_comp
    map_add' := LinearMap.toMatrix'.map_add
    commutes' := fun r =>
      by
      change (r • (LinearMap.id : Module.End R _)).toMatrix' = r • 1
      rw [← LinearMap.toMatrix'_id]; rfl; infer_instance }
#align alg_equiv_matrix' algEquivMatrix'

/- warning: linear_equiv.alg_conj -> LinearEquiv.algConj is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {M₁ : Type.{u2}} {M₂ : Type.{u3}} [_inst_5 : AddCommGroup.{u2} M₁] [_inst_6 : Module.{u1, u2} R M₁ (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M₁ _inst_5)] [_inst_7 : AddCommGroup.{u3} M₂] [_inst_8 : Module.{u1, u3} R M₂ (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_7)], (LinearEquiv.{u1, u1, u2, u3} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (LinearEquiv.algConj._proof_1.{u1} R _inst_1) (LinearEquiv.algConj._proof_2.{u1} R _inst_1) M₁ M₂ (AddCommGroup.toAddCommMonoid.{u2} M₁ _inst_5) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_7) _inst_6 _inst_8) -> (AlgEquiv.{u1, u2, u3} R (Module.End.{u1, u2} R M₁ (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M₁ _inst_5) _inst_6) (Module.End.{u1, u3} R M₂ (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_7) _inst_8) (CommRing.toCommSemiring.{u1} R _inst_1) (Module.End.semiring.{u1, u2} R M₁ (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M₁ _inst_5) _inst_6) (Module.End.semiring.{u1, u3} R M₂ (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_7) _inst_8) (Module.End.algebra.{u1, u2} R M₁ (CommRing.toCommSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M₁ _inst_5) _inst_6) (Module.End.algebra.{u1, u3} R M₂ (CommRing.toCommSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_7) _inst_8))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {M₁ : Type.{u2}} {M₂ : Type.{u3}} [_inst_5 : AddCommGroup.{u2} M₁] [_inst_6 : Module.{u1, u2} R M₁ (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M₁ _inst_5)] [_inst_7 : AddCommGroup.{u3} M₂] [_inst_8 : Module.{u1, u3} R M₂ (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_7)], (LinearEquiv.{u1, u1, u2, u3} R R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) (RingHomInvPair.ids.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (RingHomInvPair.ids.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) M₁ M₂ (AddCommGroup.toAddCommMonoid.{u2} M₁ _inst_5) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_7) _inst_6 _inst_8) -> (AlgEquiv.{u1, u2, u3} R (Module.End.{u1, u2} R M₁ (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M₁ _inst_5) _inst_6) (Module.End.{u1, u3} R M₂ (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_7) _inst_8) (CommRing.toCommSemiring.{u1} R _inst_1) (Module.End.semiring.{u1, u2} R M₁ (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M₁ _inst_5) _inst_6) (Module.End.semiring.{u1, u3} R M₂ (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_7) _inst_8) (Module.instAlgebraEndToSemiringSemiring.{u1, u2} R M₁ (CommRing.toCommSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M₁ _inst_5) _inst_6) (Module.instAlgebraEndToSemiringSemiring.{u1, u3} R M₂ (CommRing.toCommSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M₂ _inst_7) _inst_8))
Case conversion may be inaccurate. Consider using '#align linear_equiv.alg_conj LinearEquiv.algConjₓ'. -/
/-- A linear equivalence of two modules induces an equivalence of algebras of their
endomorphisms. -/
def LinearEquiv.algConj (e : M₁ ≃ₗ[R] M₂) : Module.End R M₁ ≃ₐ[R] Module.End R M₂ :=
  { e.conj with
    map_mul' := fun f g => by apply e.arrow_congr_comp
    map_add' := e.conj.map_add
    commutes' := fun r => by
      change e.conj (r • LinearMap.id) = r • LinearMap.id
      rw [LinearEquiv.map_smul, LinearEquiv.conj_id] }
#align linear_equiv.alg_conj LinearEquiv.algConj

/- warning: alg_equiv_matrix -> algEquivMatrix is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {n : Type.{u2}} [_inst_2 : DecidableEq.{succ u2} n] {M : Type.{u3}} [_inst_3 : AddCommGroup.{u3} M] [_inst_4 : Module.{u1, u3} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3)] [_inst_9 : Fintype.{u2} n], (Basis.{u2, u1, u3} n R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_4) -> (AlgEquiv.{u1, u3, max u2 u1} R (Module.End.{u1, u3} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_4) (Matrix.{u2, u2, u1} n n R) (CommRing.toCommSemiring.{u1} R _inst_1) (Module.End.semiring.{u1, u3} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_4) (Matrix.semiring.{u1, u2} n R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) _inst_9 (fun (a : n) (b : n) => _inst_2 a b)) (Module.End.algebra.{u1, u3} R M (CommRing.toCommSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_4) (Matrix.algebra.{u1, u2, u1} n R R _inst_9 (fun (a : n) (b : n) => _inst_2 a b) (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Algebra.id.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {n : Type.{u2}} [_inst_2 : DecidableEq.{succ u2} n] {M : Type.{u3}} [_inst_3 : AddCommGroup.{u3} M] [_inst_4 : Module.{u1, u3} R M (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3)] [_inst_9 : Fintype.{u2} n], (Basis.{u2, u1, u3} n R M (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_4) -> (AlgEquiv.{u1, u3, max u1 u2} R (Module.End.{u1, u3} R M (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_4) (Matrix.{u2, u2, u1} n n R) (CommRing.toCommSemiring.{u1} R _inst_1) (Module.End.semiring.{u1, u3} R M (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_4) (Matrix.semiring.{u1, u2} n R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) _inst_9 (fun (a : n) (b : n) => _inst_2 a b)) (Module.instAlgebraEndToSemiringSemiring.{u1, u3} R M (CommRing.toCommSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_4) (Matrix.instAlgebraMatrixSemiring.{u1, u2, u1} n R R _inst_9 (fun (a : n) (b : n) => _inst_2 a b) (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (Algebra.id.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align alg_equiv_matrix algEquivMatrixₓ'. -/
/-- A basis of a module induces an equivalence of algebras from the endomorphisms of the module to
square matrices. -/
def algEquivMatrix [Fintype n] (h : Basis n R M) : Module.End R M ≃ₐ[R] Matrix n n R :=
  h.equivFun.algConj.trans algEquivMatrix'
#align alg_equiv_matrix algEquivMatrix

end

