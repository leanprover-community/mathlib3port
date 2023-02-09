/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky

! This file was ported from Lean 3 source module linear_algebra.matrix.polynomial
! leanprover-community/mathlib commit 0ebfdb71919ac6ca5d7fbc61a082fa2519556818
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Polynomial.BigOperators
import Mathbin.Data.Polynomial.Degree.Lemmas
import Mathbin.LinearAlgebra.Matrix.Determinant

/-!
# Matrices of polynomials and polynomials of matrices

In this file, we prove results about matrices over a polynomial ring.
In particular, we give results about the polynomial given by
`det (t * I + A)`.

## References

  * "The trace Cayley-Hamilton theorem" by Darij Grinberg, Section 5.3

## Tags

matrix determinant, polynomial
-/


open Matrix BigOperators Polynomial

variable {n α : Type _} [DecidableEq n] [Fintype n] [CommRing α]

open Polynomial Matrix Equiv.Perm

namespace Polynomial

theorem natDegree_det_x_add_c_le (A B : Matrix n n α) :
    natDegree (det ((x : α[X]) • A.map c + B.map c)) ≤ Fintype.card n :=
  by
  rw [det_apply]
  refine' (natDegree_sum_le _ _).trans _
  refine' Multiset.max_nat_le_of_forall_le _ _ _
  simp only [forall_apply_eq_imp_iff', true_and_iff, Function.comp_apply, Multiset.map_map,
    Multiset.mem_map, exists_imp, Finset.mem_univ_val]
  intro g
  calc
    natDegree (sign g • ∏ i : n, (x • A.map c + B.map c) (g i) i) ≤
        natDegree (∏ i : n, (x • A.map c + B.map c) (g i) i) :=
      by
      cases' Int.units_eq_one_or (sign g) with sg sg
      · rw [sg, one_smul]
      · rw [sg, Units.neg_smul, one_smul, natDegree_neg]
    _ ≤ ∑ i : n, natDegree (((x : α[X]) • A.map c + B.map c) (g i) i) :=
      natDegree_prod_le (Finset.univ : Finset n) fun i : n => (x • A.map c + B.map c) (g i) i
    _ ≤ finset.univ.card • 1 := Finset.sum_le_card_nsmul _ _ 1 fun (i : n) _ => _
    _ ≤ Fintype.card n := by simpa
    
  calc
    natDegree (((x : α[X]) • A.map c + B.map c) (g i) i) =
        natDegree ((x : α[X]) * c (A (g i) i) + c (B (g i) i)) :=
      by simp
    _ ≤ max (natDegree ((x : α[X]) * c (A (g i) i))) (natDegree (c (B (g i) i))) :=
      natDegree_add_le _ _
    _ = natDegree ((x : α[X]) * c (A (g i) i)) := max_eq_left ((natDegree_c _).le.trans (zero_le _))
    _ ≤ natDegree (x : α[X]) := natDegree_mul_c_le _ _
    _ ≤ 1 := natDegree_x_le
    
#align polynomial.nat_degree_det_X_add_C_le Polynomial.natDegree_det_x_add_c_le

theorem coeff_det_x_add_c_zero (A B : Matrix n n α) :
    coeff (det ((x : α[X]) • A.map c + B.map c)) 0 = det B :=
  by
  rw [det_apply, finset_sum_coeff, det_apply]
  refine' Finset.sum_congr rfl _
  intro g hg
  convert coeff_smul (sign g) _ 0
  rw [coeff_zero_prod]
  refine' Finset.prod_congr rfl _
  simp
#align polynomial.coeff_det_X_add_C_zero Polynomial.coeff_det_x_add_c_zero

theorem coeff_det_x_add_c_card (A B : Matrix n n α) :
    coeff (det ((x : α[X]) • A.map c + B.map c)) (Fintype.card n) = det A :=
  by
  rw [det_apply, det_apply, finset_sum_coeff]
  refine' Finset.sum_congr rfl _
  simp only [Algebra.id.smul_eq_mul, Finset.mem_univ, RingHom.mapMatrix_apply, forall_true_left,
    map_apply, Pi.smul_apply]
  intro g
  convert coeff_smul (sign g) _ _
  rw [← mul_one (Fintype.card n)]
  convert (coeff_prod_of_natDegree_le _ _ _ _).symm
  · ext
    simp [coeff_c]
  · intro p hp
    refine' (natDegree_add_le _ _).trans _
    simpa only [Pi.smul_apply, map_apply, Algebra.id.smul_eq_mul, x_mul_c, natDegree_c, max_eq_left,
      zero_le'] using (natDegree_c_mul_le _ _).trans natDegree_x_le
#align polynomial.coeff_det_X_add_C_card Polynomial.coeff_det_x_add_c_card

theorem leadingCoeff_det_x_one_add_c (A : Matrix n n α) :
    leadingCoeff (det ((x : α[X]) • (1 : Matrix n n α[X]) + A.map c)) = 1 :=
  by
  cases subsingleton_or_nontrivial α
  · simp
  rw [← @det_one n, ← coeff_det_x_add_c_card _ A, leadingCoeff]
  simp only [Matrix.map_one, c_eq_zero, RingHom.map_one]
  cases' (natDegree_det_x_add_c_le 1 A).eq_or_lt with h h
  · simp only [RingHom.map_one, Matrix.map_one, c_eq_zero] at h
    rw [h]
  · -- contradiction. we have a hypothesis that the degree is less than |n|
    -- but we know that coeff _ n = 1
    have H := coeff_eq_zero_of_natDegree_lt h
    rw [coeff_det_x_add_c_card] at H
    simpa using H
#align polynomial.leading_coeff_det_X_one_add_C Polynomial.leadingCoeff_det_x_one_add_c

end Polynomial

