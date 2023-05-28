/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen

! This file was ported from Lean 3 source module linear_algebra.matrix.reindex
! leanprover-community/mathlib commit 86d1873c01a723aba6788f0b9051ae3d23b4c1c3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Matrix.Determinant

/-!
# Changing the index type of a matrix

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file concerns the map `matrix.reindex`, mapping a `m` by `n` matrix
to an `m'` by `n'` matrix, as long as `m ≃ m'` and `n ≃ n'`.

## Main definitions

* `matrix.reindex_linear_equiv R A`: `matrix.reindex` is an `R`-linear equivalence between
  `A`-matrices.
* `matrix.reindex_alg_equiv R`: `matrix.reindex` is an `R`-algebra equivalence between `R`-matrices.

## Tags

matrix, reindex

-/


namespace Matrix

open Equiv

open Matrix

variable {l m n o : Type _} {l' m' n' o' : Type _} {m'' n'' : Type _}

variable (R A : Type _)

section AddCommMonoid

variable [Semiring R] [AddCommMonoid A] [Module R A]

#print Matrix.reindexLinearEquiv /-
/-- The natural map that reindexes a matrix's rows and columns with equivalent types,
`matrix.reindex`, is a linear equivalence. -/
def reindexLinearEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') : Matrix m n A ≃ₗ[R] Matrix m' n' A :=
  { reindex eₘ eₙ with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
#align matrix.reindex_linear_equiv Matrix.reindexLinearEquiv
-/

/- warning: matrix.reindex_linear_equiv_apply -> Matrix.reindexLinearEquiv_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.reindex_linear_equiv_apply Matrix.reindexLinearEquiv_applyₓ'. -/
@[simp]
theorem reindexLinearEquiv_apply (eₘ : m ≃ m') (eₙ : n ≃ n') (M : Matrix m n A) :
    reindexLinearEquiv R A eₘ eₙ M = reindex eₘ eₙ M :=
  rfl
#align matrix.reindex_linear_equiv_apply Matrix.reindexLinearEquiv_apply

/- warning: matrix.reindex_linear_equiv_symm -> Matrix.reindexLinearEquiv_symm is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {m' : Type.{u3}} {n' : Type.{u4}} (R : Type.{u5}) (A : Type.{u6}) [_inst_1 : Semiring.{u5} R] [_inst_2 : AddCommMonoid.{u6} A] [_inst_3 : Module.{u5, u6} R A _inst_1 _inst_2] (eₘ : Equiv.{succ u1, succ u3} m m') (eₙ : Equiv.{succ u2, succ u4} n n'), Eq.{max (succ (max u3 u4 u6)) (succ (max u1 u2 u6))} (LinearEquiv.{u5, u5, max u3 u4 u6, max u1 u2 u6} R R _inst_1 _inst_1 (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHomInvPair.ids.{u5} R _inst_1) (RingHomInvPair.ids.{u5} R _inst_1) (Matrix.{u3, u4, u6} m' n' A) (Matrix.{u1, u2, u6} m n A) (Matrix.addCommMonoid.{u6, u3, u4} m' n' A _inst_2) (Matrix.addCommMonoid.{u6, u1, u2} m n A _inst_2) (Matrix.module.{u6, u3, u4, u5} m' n' R A _inst_1 _inst_2 _inst_3) (Matrix.module.{u6, u1, u2, u5} m n R A _inst_1 _inst_2 _inst_3)) (LinearEquiv.symm.{u5, u5, max u1 u2 u6, max u3 u4 u6} R R (Matrix.{u1, u2, u6} m n A) (Matrix.{u3, u4, u6} m' n' A) _inst_1 _inst_1 (Matrix.addCommMonoid.{u6, u1, u2} m n A _inst_2) (Matrix.addCommMonoid.{u6, u3, u4} m' n' A _inst_2) (Matrix.module.{u6, u1, u2, u5} m n R A _inst_1 _inst_2 _inst_3) (Matrix.module.{u6, u3, u4, u5} m' n' R A _inst_1 _inst_2 _inst_3) (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHomInvPair.ids.{u5} R _inst_1) (RingHomInvPair.ids.{u5} R _inst_1) (Matrix.reindexLinearEquiv.{u1, u2, u3, u4, u5, u6} m n m' n' R A _inst_1 _inst_2 _inst_3 eₘ eₙ)) (Matrix.reindexLinearEquiv.{u3, u4, u1, u2, u5, u6} m' n' m n R A _inst_1 _inst_2 _inst_3 (Equiv.symm.{succ u1, succ u3} m m' eₘ) (Equiv.symm.{succ u2, succ u4} n n' eₙ))
but is expected to have type
  forall {m : Type.{u6}} {n : Type.{u4}} {m' : Type.{u5}} {n' : Type.{u3}} (R : Type.{u1}) (A : Type.{u2}) [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} A] [_inst_3 : Module.{u1, u2} R A _inst_1 _inst_2] (eₘ : Equiv.{succ u6, succ u5} m m') (eₙ : Equiv.{succ u4, succ u3} n n'), Eq.{max (max (max (max (succ u6) (succ u4)) (succ u5)) (succ u3)) (succ u2)} (LinearEquiv.{u1, u1, max (max u5 u3) u2, max (max u6 u4) u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) (Matrix.{u5, u3, u2} m' n' A) (Matrix.{u6, u4, u2} m n A) (Matrix.addCommMonoid.{u2, u5, u3} m' n' A _inst_2) (Matrix.addCommMonoid.{u2, u6, u4} m n A _inst_2) (Matrix.module.{u2, u5, u3, u1} m' n' R A _inst_1 _inst_2 _inst_3) (Matrix.module.{u2, u6, u4, u1} m n R A _inst_1 _inst_2 _inst_3)) (LinearEquiv.symm.{u1, u1, max (max u6 u4) u2, max (max u5 u3) u2} R R (Matrix.{u6, u4, u2} m n A) (Matrix.{u5, u3, u2} m' n' A) _inst_1 _inst_1 (Matrix.addCommMonoid.{u2, u6, u4} m n A _inst_2) (Matrix.addCommMonoid.{u2, u5, u3} m' n' A _inst_2) (Matrix.module.{u2, u6, u4, u1} m n R A _inst_1 _inst_2 _inst_3) (Matrix.module.{u2, u5, u3, u1} m' n' R A _inst_1 _inst_2 _inst_3) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) (Matrix.reindexLinearEquiv.{u6, u4, u5, u3, u1, u2} m n m' n' R A _inst_1 _inst_2 _inst_3 eₘ eₙ)) (Matrix.reindexLinearEquiv.{u5, u3, u6, u4, u1, u2} m' n' m n R A _inst_1 _inst_2 _inst_3 (Equiv.symm.{succ u6, succ u5} m m' eₘ) (Equiv.symm.{succ u4, succ u3} n n' eₙ))
Case conversion may be inaccurate. Consider using '#align matrix.reindex_linear_equiv_symm Matrix.reindexLinearEquiv_symmₓ'. -/
@[simp]
theorem reindexLinearEquiv_symm (eₘ : m ≃ m') (eₙ : n ≃ n') :
    (reindexLinearEquiv R A eₘ eₙ).symm = reindexLinearEquiv R A eₘ.symm eₙ.symm :=
  rfl
#align matrix.reindex_linear_equiv_symm Matrix.reindexLinearEquiv_symm

/- warning: matrix.reindex_linear_equiv_refl_refl -> Matrix.reindexLinearEquiv_refl_refl is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} (R : Type.{u3}) (A : Type.{u4}) [_inst_1 : Semiring.{u3} R] [_inst_2 : AddCommMonoid.{u4} A] [_inst_3 : Module.{u3, u4} R A _inst_1 _inst_2], Eq.{succ (max u1 u2 u4)} (LinearEquiv.{u3, u3, max u1 u2 u4, max u1 u2 u4} R R _inst_1 _inst_1 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHomInvPair.ids.{u3} R _inst_1) (RingHomInvPair.ids.{u3} R _inst_1) (Matrix.{u1, u2, u4} m n A) (Matrix.{u1, u2, u4} m n A) (Matrix.addCommMonoid.{u4, u1, u2} m n A _inst_2) (Matrix.addCommMonoid.{u4, u1, u2} m n A _inst_2) (Matrix.module.{u4, u1, u2, u3} m n R A _inst_1 _inst_2 _inst_3) (Matrix.module.{u4, u1, u2, u3} m n R A _inst_1 _inst_2 _inst_3)) (Matrix.reindexLinearEquiv.{u1, u2, u1, u2, u3, u4} m n m n R A _inst_1 _inst_2 _inst_3 (Equiv.refl.{succ u1} m) (Equiv.refl.{succ u2} n)) (LinearEquiv.refl.{u3, max u1 u2 u4} R (Matrix.{u1, u2, u4} m n A) _inst_1 (Matrix.addCommMonoid.{u4, u1, u2} m n A _inst_2) (Matrix.module.{u4, u1, u2, u3} m n R A _inst_1 _inst_2 _inst_3))
but is expected to have type
  forall {m : Type.{u4}} {n : Type.{u3}} (R : Type.{u1}) (A : Type.{u2}) [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} A] [_inst_3 : Module.{u1, u2} R A _inst_1 _inst_2], Eq.{max (max (succ u4) (succ u3)) (succ u2)} (LinearEquiv.{u1, u1, max (max u2 u3) u4, max (max u2 u3) u4} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) (Matrix.{u4, u3, u2} m n A) (Matrix.{u4, u3, u2} m n A) (Matrix.addCommMonoid.{u2, u4, u3} m n A _inst_2) (Matrix.addCommMonoid.{u2, u4, u3} m n A _inst_2) (Matrix.module.{u2, u4, u3, u1} m n R A _inst_1 _inst_2 _inst_3) (Matrix.module.{u2, u4, u3, u1} m n R A _inst_1 _inst_2 _inst_3)) (Matrix.reindexLinearEquiv.{u4, u3, u4, u3, u1, u2} m n m n R A _inst_1 _inst_2 _inst_3 (Equiv.refl.{succ u4} m) (Equiv.refl.{succ u3} n)) (LinearEquiv.refl.{u1, max (max u4 u3) u2} R (Matrix.{u4, u3, u2} m n A) _inst_1 (Matrix.addCommMonoid.{u2, u4, u3} m n A _inst_2) (Matrix.module.{u2, u4, u3, u1} m n R A _inst_1 _inst_2 _inst_3))
Case conversion may be inaccurate. Consider using '#align matrix.reindex_linear_equiv_refl_refl Matrix.reindexLinearEquiv_refl_reflₓ'. -/
@[simp]
theorem reindexLinearEquiv_refl_refl :
    reindexLinearEquiv R A (Equiv.refl m) (Equiv.refl n) = LinearEquiv.refl R _ :=
  LinearEquiv.ext fun _ => rfl
#align matrix.reindex_linear_equiv_refl_refl Matrix.reindexLinearEquiv_refl_refl

/- warning: matrix.reindex_linear_equiv_trans -> Matrix.reindexLinearEquiv_trans is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.reindex_linear_equiv_trans Matrix.reindexLinearEquiv_transₓ'. -/
theorem reindexLinearEquiv_trans (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'') (e₂' : n' ≃ n'') :
    (reindexLinearEquiv R A e₁ e₂).trans (reindexLinearEquiv R A e₁' e₂') =
      (reindexLinearEquiv R A (e₁.trans e₁') (e₂.trans e₂') : _ ≃ₗ[R] _) :=
  by ext; rfl
#align matrix.reindex_linear_equiv_trans Matrix.reindexLinearEquiv_trans

/- warning: matrix.reindex_linear_equiv_comp -> Matrix.reindexLinearEquiv_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.reindex_linear_equiv_comp Matrix.reindexLinearEquiv_compₓ'. -/
theorem reindexLinearEquiv_comp (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'') (e₂' : n' ≃ n'') :
    reindexLinearEquiv R A e₁' e₂' ∘ reindexLinearEquiv R A e₁ e₂ =
      reindexLinearEquiv R A (e₁.trans e₁') (e₂.trans e₂') :=
  by rw [← reindex_linear_equiv_trans]; rfl
#align matrix.reindex_linear_equiv_comp Matrix.reindexLinearEquiv_comp

/- warning: matrix.reindex_linear_equiv_comp_apply -> Matrix.reindexLinearEquiv_comp_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.reindex_linear_equiv_comp_apply Matrix.reindexLinearEquiv_comp_applyₓ'. -/
theorem reindexLinearEquiv_comp_apply (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'') (e₂' : n' ≃ n'')
    (M : Matrix m n A) :
    (reindexLinearEquiv R A e₁' e₂') (reindexLinearEquiv R A e₁ e₂ M) =
      reindexLinearEquiv R A (e₁.trans e₁') (e₂.trans e₂') M :=
  submatrix_submatrix _ _ _ _ _
#align matrix.reindex_linear_equiv_comp_apply Matrix.reindexLinearEquiv_comp_apply

/- warning: matrix.reindex_linear_equiv_one -> Matrix.reindexLinearEquiv_one is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.reindex_linear_equiv_one Matrix.reindexLinearEquiv_oneₓ'. -/
theorem reindexLinearEquiv_one [DecidableEq m] [DecidableEq m'] [One A] (e : m ≃ m') :
    reindexLinearEquiv R A e e (1 : Matrix m m A) = 1 :=
  submatrix_one_equiv e.symm
#align matrix.reindex_linear_equiv_one Matrix.reindexLinearEquiv_one

end AddCommMonoid

section Semiring

variable [Semiring R] [Semiring A] [Module R A]

/- warning: matrix.reindex_linear_equiv_mul -> Matrix.reindexLinearEquiv_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.reindex_linear_equiv_mul Matrix.reindexLinearEquiv_mulₓ'. -/
theorem reindexLinearEquiv_mul [Fintype n] [Fintype n'] (eₘ : m ≃ m') (eₙ : n ≃ n') (eₒ : o ≃ o')
    (M : Matrix m n A) (N : Matrix n o A) :
    reindexLinearEquiv R A eₘ eₙ M ⬝ reindexLinearEquiv R A eₙ eₒ N =
      reindexLinearEquiv R A eₘ eₒ (M ⬝ N) :=
  submatrix_mul_equiv M N _ _ _
#align matrix.reindex_linear_equiv_mul Matrix.reindexLinearEquiv_mul

/- warning: matrix.mul_reindex_linear_equiv_one -> Matrix.mul_reindexLinearEquiv_one is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.mul_reindex_linear_equiv_one Matrix.mul_reindexLinearEquiv_oneₓ'. -/
theorem mul_reindexLinearEquiv_one [Fintype n] [DecidableEq o] (e₁ : o ≃ n) (e₂ : o ≃ n')
    (M : Matrix m n A) :
    M.mul (reindexLinearEquiv R A e₁ e₂ 1) =
      reindexLinearEquiv R A (Equiv.refl m) (e₁.symm.trans e₂) M :=
  haveI := Fintype.ofEquiv _ e₁.symm
  mul_submatrix_one _ _ _
#align matrix.mul_reindex_linear_equiv_one Matrix.mul_reindexLinearEquiv_one

end Semiring

section Algebra

variable [CommSemiring R] [Fintype n] [Fintype m] [DecidableEq m] [DecidableEq n]

/- warning: matrix.reindex_alg_equiv -> Matrix.reindexAlgEquiv is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} (R : Type.{u3}) [_inst_1 : CommSemiring.{u3} R] [_inst_2 : Fintype.{u2} n] [_inst_3 : Fintype.{u1} m] [_inst_4 : DecidableEq.{succ u1} m] [_inst_5 : DecidableEq.{succ u2} n], (Equiv.{succ u1, succ u2} m n) -> (AlgEquiv.{u3, max u1 u3, max u2 u3} R (Matrix.{u1, u1, u3} m m R) (Matrix.{u2, u2, u3} n n R) _inst_1 (Matrix.semiring.{u3, u1} m R (CommSemiring.toSemiring.{u3} R _inst_1) _inst_3 (fun (a : m) (b : m) => _inst_4 a b)) (Matrix.semiring.{u3, u2} n R (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 (fun (a : n) (b : n) => _inst_5 a b)) (Matrix.algebra.{u3, u1, u3} m R R _inst_3 (fun (a : m) (b : m) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u3} R _inst_1) (Algebra.id.{u3} R _inst_1)) (Matrix.algebra.{u3, u2, u3} n R R _inst_2 (fun (a : n) (b : n) => _inst_5 a b) _inst_1 (CommSemiring.toSemiring.{u3} R _inst_1) (Algebra.id.{u3} R _inst_1)))
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} (R : Type.{u3}) [_inst_1 : CommSemiring.{u3} R] [_inst_2 : Fintype.{u2} n] [_inst_3 : Fintype.{u1} m] [_inst_4 : DecidableEq.{succ u1} m] [_inst_5 : DecidableEq.{succ u2} n], (Equiv.{succ u1, succ u2} m n) -> (AlgEquiv.{u3, max u3 u1, max u3 u2} R (Matrix.{u1, u1, u3} m m R) (Matrix.{u2, u2, u3} n n R) _inst_1 (Matrix.semiring.{u3, u1} m R (CommSemiring.toSemiring.{u3} R _inst_1) _inst_3 (fun (a : m) (b : m) => _inst_4 a b)) (Matrix.semiring.{u3, u2} n R (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 (fun (a : n) (b : n) => _inst_5 a b)) (Matrix.instAlgebraMatrixSemiring.{u3, u1, u3} m R R _inst_3 (fun (a : m) (b : m) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u3} R _inst_1) (Algebra.id.{u3} R _inst_1)) (Matrix.instAlgebraMatrixSemiring.{u3, u2, u3} n R R _inst_2 (fun (a : n) (b : n) => _inst_5 a b) _inst_1 (CommSemiring.toSemiring.{u3} R _inst_1) (Algebra.id.{u3} R _inst_1)))
Case conversion may be inaccurate. Consider using '#align matrix.reindex_alg_equiv Matrix.reindexAlgEquivₓ'. -/
/-- For square matrices with coefficients in commutative semirings, the natural map that reindexes
a matrix's rows and columns with equivalent types, `matrix.reindex`, is an equivalence of algebras.
-/
def reindexAlgEquiv (e : m ≃ n) : Matrix m m R ≃ₐ[R] Matrix n n R :=
  { reindexLinearEquiv R R e e with
    toFun := reindex e e
    map_mul' := fun a b => (reindexLinearEquiv_mul R R e e e a b).symm
    commutes' := fun r => by simp [algebraMap, Algebra.toRingHom, submatrix_smul] }
#align matrix.reindex_alg_equiv Matrix.reindexAlgEquiv

/- warning: matrix.reindex_alg_equiv_apply -> Matrix.reindexAlgEquiv_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.reindex_alg_equiv_apply Matrix.reindexAlgEquiv_applyₓ'. -/
@[simp]
theorem reindexAlgEquiv_apply (e : m ≃ n) (M : Matrix m m R) :
    reindexAlgEquiv R e M = reindex e e M :=
  rfl
#align matrix.reindex_alg_equiv_apply Matrix.reindexAlgEquiv_apply

/- warning: matrix.reindex_alg_equiv_symm -> Matrix.reindexAlgEquiv_symm is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} (R : Type.{u3}) [_inst_1 : CommSemiring.{u3} R] [_inst_2 : Fintype.{u2} n] [_inst_3 : Fintype.{u1} m] [_inst_4 : DecidableEq.{succ u1} m] [_inst_5 : DecidableEq.{succ u2} n] (e : Equiv.{succ u1, succ u2} m n), Eq.{max (succ (max u2 u3)) (succ (max u1 u3))} (AlgEquiv.{u3, max u2 u3, max u1 u3} R (Matrix.{u2, u2, u3} n n R) (Matrix.{u1, u1, u3} m m R) _inst_1 (Matrix.semiring.{u3, u2} n R (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 (fun (a : n) (b : n) => _inst_5 a b)) (Matrix.semiring.{u3, u1} m R (CommSemiring.toSemiring.{u3} R _inst_1) _inst_3 (fun (a : m) (b : m) => _inst_4 a b)) (Matrix.algebra.{u3, u2, u3} n R R _inst_2 (fun (a : n) (b : n) => _inst_5 a b) _inst_1 (CommSemiring.toSemiring.{u3} R _inst_1) (Algebra.id.{u3} R _inst_1)) (Matrix.algebra.{u3, u1, u3} m R R _inst_3 (fun (a : m) (b : m) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u3} R _inst_1) (Algebra.id.{u3} R _inst_1))) (AlgEquiv.symm.{u3, max u1 u3, max u2 u3} R (Matrix.{u1, u1, u3} m m R) (Matrix.{u2, u2, u3} n n R) _inst_1 (Matrix.semiring.{u3, u1} m R (CommSemiring.toSemiring.{u3} R _inst_1) _inst_3 (fun (a : m) (b : m) => _inst_4 a b)) (Matrix.semiring.{u3, u2} n R (CommSemiring.toSemiring.{u3} R _inst_1) _inst_2 (fun (a : n) (b : n) => _inst_5 a b)) (Matrix.algebra.{u3, u1, u3} m R R _inst_3 (fun (a : m) (b : m) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u3} R _inst_1) (Algebra.id.{u3} R _inst_1)) (Matrix.algebra.{u3, u2, u3} n R R _inst_2 (fun (a : n) (b : n) => _inst_5 a b) _inst_1 (CommSemiring.toSemiring.{u3} R _inst_1) (Algebra.id.{u3} R _inst_1)) (Matrix.reindexAlgEquiv.{u1, u2, u3} m n R _inst_1 _inst_2 _inst_3 (fun (a : m) (b : m) => _inst_4 a b) (fun (a : n) (b : n) => _inst_5 a b) e)) (Matrix.reindexAlgEquiv.{u2, u1, u3} n m R _inst_1 _inst_3 _inst_2 (fun (a : n) (b : n) => _inst_5 a b) (fun (a : m) (b : m) => _inst_4 a b) (Equiv.symm.{succ u1, succ u2} m n e))
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u2}} (R : Type.{u1}) [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Fintype.{u2} n] [_inst_3 : Fintype.{u3} m] [_inst_4 : DecidableEq.{succ u3} m] [_inst_5 : DecidableEq.{succ u2} n] (e : Equiv.{succ u3, succ u2} m n), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (AlgEquiv.{u1, max u2 u1, max u3 u1} R (Matrix.{u2, u2, u1} n n R) (Matrix.{u3, u3, u1} m m R) _inst_1 (Matrix.semiring.{u1, u2} n R (CommSemiring.toSemiring.{u1} R _inst_1) _inst_2 (fun (a : n) (b : n) => _inst_5 a b)) (Matrix.semiring.{u1, u3} m R (CommSemiring.toSemiring.{u1} R _inst_1) _inst_3 (fun (a : m) (b : m) => _inst_4 a b)) (Matrix.instAlgebraMatrixSemiring.{u1, u2, u1} n R R _inst_2 (fun (a : n) (b : n) => _inst_5 a b) _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1)) (Matrix.instAlgebraMatrixSemiring.{u1, u3, u1} m R R _inst_3 (fun (a : m) (b : m) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1))) (AlgEquiv.symm.{u1, max u3 u1, max u2 u1} R (Matrix.{u3, u3, u1} m m R) (Matrix.{u2, u2, u1} n n R) _inst_1 (Matrix.semiring.{u1, u3} m R (CommSemiring.toSemiring.{u1} R _inst_1) _inst_3 (fun (a : m) (b : m) => _inst_4 a b)) (Matrix.semiring.{u1, u2} n R (CommSemiring.toSemiring.{u1} R _inst_1) _inst_2 (fun (a : n) (b : n) => _inst_5 a b)) (Matrix.instAlgebraMatrixSemiring.{u1, u3, u1} m R R _inst_3 (fun (a : m) (b : m) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1)) (Matrix.instAlgebraMatrixSemiring.{u1, u2, u1} n R R _inst_2 (fun (a : n) (b : n) => _inst_5 a b) _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1)) (Matrix.reindexAlgEquiv.{u3, u2, u1} m n R _inst_1 _inst_2 _inst_3 (fun (a : m) (b : m) => _inst_4 a b) (fun (a : n) (b : n) => _inst_5 a b) e)) (Matrix.reindexAlgEquiv.{u2, u3, u1} n m R _inst_1 _inst_3 _inst_2 (fun (a : n) (b : n) => _inst_5 a b) (fun (a : m) (b : m) => _inst_4 a b) (Equiv.symm.{succ u3, succ u2} m n e))
Case conversion may be inaccurate. Consider using '#align matrix.reindex_alg_equiv_symm Matrix.reindexAlgEquiv_symmₓ'. -/
@[simp]
theorem reindexAlgEquiv_symm (e : m ≃ n) : (reindexAlgEquiv R e).symm = reindexAlgEquiv R e.symm :=
  rfl
#align matrix.reindex_alg_equiv_symm Matrix.reindexAlgEquiv_symm

/- warning: matrix.reindex_alg_equiv_refl -> Matrix.reindexAlgEquiv_refl is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} (R : Type.{u2}) [_inst_1 : CommSemiring.{u2} R] [_inst_3 : Fintype.{u1} m] [_inst_4 : DecidableEq.{succ u1} m], Eq.{succ (max u1 u2)} (AlgEquiv.{u2, max u1 u2, max u1 u2} R (Matrix.{u1, u1, u2} m m R) (Matrix.{u1, u1, u2} m m R) _inst_1 (Matrix.semiring.{u2, u1} m R (CommSemiring.toSemiring.{u2} R _inst_1) _inst_3 (fun (a : m) (b : m) => _inst_4 a b)) (Matrix.semiring.{u2, u1} m R (CommSemiring.toSemiring.{u2} R _inst_1) _inst_3 (fun (a : m) (b : m) => _inst_4 a b)) (Matrix.algebra.{u2, u1, u2} m R R _inst_3 (fun (a : m) (b : m) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u2} R _inst_1) (Algebra.id.{u2} R _inst_1)) (Matrix.algebra.{u2, u1, u2} m R R _inst_3 (fun (a : m) (b : m) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u2} R _inst_1) (Algebra.id.{u2} R _inst_1))) (Matrix.reindexAlgEquiv.{u1, u1, u2} m m R _inst_1 _inst_3 _inst_3 (fun (a : m) (b : m) => _inst_4 a b) (fun (a : m) (b : m) => _inst_4 a b) (Equiv.refl.{succ u1} m)) (AlgEquiv.refl.{u2, max u1 u2} R (Matrix.{u1, u1, u2} m m R) _inst_1 (Matrix.semiring.{u2, u1} m R (CommSemiring.toSemiring.{u2} R _inst_1) _inst_3 (fun (a : m) (b : m) => _inst_4 a b)) (Matrix.algebra.{u2, u1, u2} m R R _inst_3 (fun (a : m) (b : m) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u2} R _inst_1) (Algebra.id.{u2} R _inst_1)))
but is expected to have type
  forall {m : Type.{u2}} (R : Type.{u1}) [_inst_1 : CommSemiring.{u1} R] [_inst_3 : Fintype.{u2} m] [_inst_4 : DecidableEq.{succ u2} m], Eq.{max (succ u2) (succ u1)} (AlgEquiv.{u1, max u1 u2, max u1 u2} R (Matrix.{u2, u2, u1} m m R) (Matrix.{u2, u2, u1} m m R) _inst_1 (Matrix.semiring.{u1, u2} m R (CommSemiring.toSemiring.{u1} R _inst_1) _inst_3 (fun (a : m) (b : m) => _inst_4 a b)) (Matrix.semiring.{u1, u2} m R (CommSemiring.toSemiring.{u1} R _inst_1) _inst_3 (fun (a : m) (b : m) => _inst_4 a b)) (Matrix.instAlgebraMatrixSemiring.{u1, u2, u1} m R R _inst_3 (fun (a : m) (b : m) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1)) (Matrix.instAlgebraMatrixSemiring.{u1, u2, u1} m R R _inst_3 (fun (a : m) (b : m) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1))) (Matrix.reindexAlgEquiv.{u2, u2, u1} m m R _inst_1 _inst_3 _inst_3 (fun (a : m) (b : m) => _inst_4 a b) (fun (a : m) (b : m) => _inst_4 a b) (Equiv.refl.{succ u2} m)) (AlgEquiv.refl.{u1, max u2 u1} R (Matrix.{u2, u2, u1} m m R) _inst_1 (Matrix.semiring.{u1, u2} m R (CommSemiring.toSemiring.{u1} R _inst_1) _inst_3 (fun (a : m) (b : m) => _inst_4 a b)) (Matrix.instAlgebraMatrixSemiring.{u1, u2, u1} m R R _inst_3 (fun (a : m) (b : m) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1)))
Case conversion may be inaccurate. Consider using '#align matrix.reindex_alg_equiv_refl Matrix.reindexAlgEquiv_reflₓ'. -/
@[simp]
theorem reindexAlgEquiv_refl : reindexAlgEquiv R (Equiv.refl m) = AlgEquiv.refl :=
  AlgEquiv.ext fun _ => rfl
#align matrix.reindex_alg_equiv_refl Matrix.reindexAlgEquiv_refl

/- warning: matrix.reindex_alg_equiv_mul -> Matrix.reindexAlgEquiv_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.reindex_alg_equiv_mul Matrix.reindexAlgEquiv_mulₓ'. -/
theorem reindexAlgEquiv_mul (e : m ≃ n) (M : Matrix m m R) (N : Matrix m m R) :
    reindexAlgEquiv R e (M ⬝ N) = reindexAlgEquiv R e M ⬝ reindexAlgEquiv R e N :=
  (reindexAlgEquiv R e).map_mul M N
#align matrix.reindex_alg_equiv_mul Matrix.reindexAlgEquiv_mul

end Algebra

/- warning: matrix.det_reindex_linear_equiv_self -> Matrix.det_reindexLinearEquiv_self is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.det_reindex_linear_equiv_self Matrix.det_reindexLinearEquiv_selfₓ'. -/
/-- Reindexing both indices along the same equivalence preserves the determinant.

For the `simp` version of this lemma, see `det_submatrix_equiv_self`.
-/
theorem det_reindexLinearEquiv_self [CommRing R] [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (e : m ≃ n) (M : Matrix m m R) : det (reindexLinearEquiv R R e e M) = det M :=
  det_reindex_self e M
#align matrix.det_reindex_linear_equiv_self Matrix.det_reindexLinearEquiv_self

/- warning: matrix.det_reindex_alg_equiv -> Matrix.det_reindexAlgEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.det_reindex_alg_equiv Matrix.det_reindexAlgEquivₓ'. -/
/-- Reindexing both indices along the same equivalence preserves the determinant.

For the `simp` version of this lemma, see `det_submatrix_equiv_self`.
-/
theorem det_reindexAlgEquiv [CommRing R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) (A : Matrix m m R) : det (reindexAlgEquiv R e A) = det A :=
  det_reindex_self e A
#align matrix.det_reindex_alg_equiv Matrix.det_reindexAlgEquiv

end Matrix

