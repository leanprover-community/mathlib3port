/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Data.Polynomial.Degree.Definitions

#align_import ring_theory.polynomial.opposites from "leanprover-community/mathlib"@"932872382355f00112641d305ba0619305dc8642"

/-!  #  Interactions between `R[X]` and `Rᵐᵒᵖ[X]`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains the basic API for "pushing through" the isomorphism
`op_ring_equiv : R[X]ᵐᵒᵖ ≃+* Rᵐᵒᵖ[X]`.  It allows going back and forth between a polynomial ring
over a semiring and the polynomial ring over the opposite semiring. -/


open scoped Polynomial

open Polynomial MulOpposite

variable {R : Type _} [Semiring R] {p q : R[X]}

noncomputable section

namespace Polynomial

#print Polynomial.opRingEquiv /-
/-- Ring isomorphism between `R[X]ᵐᵒᵖ` and `Rᵐᵒᵖ[X]` sending each coefficient of a polynomial
to the corresponding element of the opposite ring. -/
def opRingEquiv (R : Type _) [Semiring R] : R[X]ᵐᵒᵖ ≃+* Rᵐᵒᵖ[X] :=
  ((toFinsuppIso R).op.trans AddMonoidAlgebra.opRingEquiv).trans (toFinsuppIso _).symm
#align polynomial.op_ring_equiv Polynomial.opRingEquiv
-/

/-!  Lemmas to get started, using `op_ring_equiv R` on the various expressions of
`finsupp.single`: `monomial`, `C a`, `X`, `C a * X ^ n`. -/


#print Polynomial.opRingEquiv_op_monomial /-
-- for maintenance purposes: `by simp [op_ring_equiv]` proves this lemma
@[simp]
theorem opRingEquiv_op_monomial (n : ℕ) (r : R) :
    opRingEquiv R (op (monomial n r : R[X])) = monomial n (op r) := by
  simp only [op_ring_equiv, RingEquiv.trans_apply, RingEquiv.op_apply_apply,
    RingEquiv.toAddEquiv_eq_coe, AddEquiv.mulOp_apply, AddEquiv.to_fun_eq_coe, AddEquiv.coe_trans,
    op_add_equiv_apply, RingEquiv.coe_toAddEquiv, op_add_equiv_symm_apply, Function.comp_apply,
    unop_op, to_finsupp_iso_apply, to_finsupp_monomial, AddMonoidAlgebra.opRingEquiv_single,
    to_finsupp_iso_symm_apply, of_finsupp_single]
#align polynomial.op_ring_equiv_op_monomial Polynomial.opRingEquiv_op_monomial
-/

#print Polynomial.opRingEquiv_op_C /-
@[simp]
theorem opRingEquiv_op_C (a : R) : opRingEquiv R (op (C a)) = C (op a) :=
  opRingEquiv_op_monomial 0 a
#align polynomial.op_ring_equiv_op_C Polynomial.opRingEquiv_op_C
-/

#print Polynomial.opRingEquiv_op_X /-
@[simp]
theorem opRingEquiv_op_X : opRingEquiv R (op (X : R[X])) = X :=
  opRingEquiv_op_monomial 1 1
#align polynomial.op_ring_equiv_op_X Polynomial.opRingEquiv_op_X
-/

#print Polynomial.opRingEquiv_op_C_mul_X_pow /-
theorem opRingEquiv_op_C_mul_X_pow (r : R) (n : ℕ) :
    opRingEquiv R (op (C r * X ^ n : R[X])) = C (op r) * X ^ n := by
  simp only [X_pow_mul, op_mul, op_pow, map_mul, map_pow, op_ring_equiv_op_X, op_ring_equiv_op_C]
#align polynomial.op_ring_equiv_op_C_mul_X_pow Polynomial.opRingEquiv_op_C_mul_X_pow
-/

/-!  Lemmas to get started, using `(op_ring_equiv R).symm` on the various expressions of
`finsupp.single`: `monomial`, `C a`, `X`, `C a * X ^ n`. -/


#print Polynomial.opRingEquiv_symm_monomial /-
@[simp]
theorem opRingEquiv_symm_monomial (n : ℕ) (r : Rᵐᵒᵖ) :
    (opRingEquiv R).symm (monomial n r) = op (monomial n (unop r)) :=
  (opRingEquiv R).Injective (by simp)
#align polynomial.op_ring_equiv_symm_monomial Polynomial.opRingEquiv_symm_monomial
-/

#print Polynomial.opRingEquiv_symm_C /-
@[simp]
theorem opRingEquiv_symm_C (a : Rᵐᵒᵖ) : (opRingEquiv R).symm (C a) = op (C (unop a)) :=
  opRingEquiv_symm_monomial 0 a
#align polynomial.op_ring_equiv_symm_C Polynomial.opRingEquiv_symm_C
-/

#print Polynomial.opRingEquiv_symm_X /-
@[simp]
theorem opRingEquiv_symm_X : (opRingEquiv R).symm (X : Rᵐᵒᵖ[X]) = op X :=
  opRingEquiv_symm_monomial 1 1
#align polynomial.op_ring_equiv_symm_X Polynomial.opRingEquiv_symm_X
-/

#print Polynomial.opRingEquiv_symm_C_mul_X_pow /-
theorem opRingEquiv_symm_C_mul_X_pow (r : Rᵐᵒᵖ) (n : ℕ) :
    (opRingEquiv R).symm (C r * X ^ n : Rᵐᵒᵖ[X]) = op (C (unop r) * X ^ n) := by
  rw [C_mul_X_pow_eq_monomial, op_ring_equiv_symm_monomial, ← C_mul_X_pow_eq_monomial]
#align polynomial.op_ring_equiv_symm_C_mul_X_pow Polynomial.opRingEquiv_symm_C_mul_X_pow
-/

/-!  Lemmas about more global properties of polynomials and opposites. -/


#print Polynomial.coeff_opRingEquiv /-
@[simp]
theorem coeff_opRingEquiv (p : R[X]ᵐᵒᵖ) (n : ℕ) :
    (opRingEquiv R p).coeff n = op ((unop p).coeff n) :=
  by
  induction p using MulOpposite.rec'
  cases p
  rfl
#align polynomial.coeff_op_ring_equiv Polynomial.coeff_opRingEquiv
-/

#print Polynomial.support_opRingEquiv /-
@[simp]
theorem support_opRingEquiv (p : R[X]ᵐᵒᵖ) : (opRingEquiv R p).support = (unop p).support :=
  by
  induction p using MulOpposite.rec'
  cases p
  exact Finsupp.support_mapRange_of_injective _ _ op_injective
#align polynomial.support_op_ring_equiv Polynomial.support_opRingEquiv
-/

#print Polynomial.natDegree_opRingEquiv /-
@[simp]
theorem natDegree_opRingEquiv (p : R[X]ᵐᵒᵖ) : (opRingEquiv R p).natDegree = (unop p).natDegree :=
  by
  by_cases p0 : p = 0
  · simp only [p0, _root_.map_zero, nat_degree_zero, unop_zero]
  ·
    simp only [p0, nat_degree_eq_support_max', Ne.def, AddEquivClass.map_eq_zero_iff, not_false_iff,
      support_op_ring_equiv, unop_eq_zero_iff]
#align polynomial.nat_degree_op_ring_equiv Polynomial.natDegree_opRingEquiv
-/

#print Polynomial.leadingCoeff_opRingEquiv /-
@[simp]
theorem leadingCoeff_opRingEquiv (p : R[X]ᵐᵒᵖ) :
    (opRingEquiv R p).leadingCoeff = op (unop p).leadingCoeff := by
  rw [leading_coeff, coeff_op_ring_equiv, nat_degree_op_ring_equiv, leading_coeff]
#align polynomial.leading_coeff_op_ring_equiv Polynomial.leadingCoeff_opRingEquiv
-/

end Polynomial

