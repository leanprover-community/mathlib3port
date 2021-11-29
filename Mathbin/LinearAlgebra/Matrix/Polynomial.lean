import Mathbin.Algebra.Polynomial.BigOperators 
import Mathbin.Data.Polynomial.Degree.Lemmas 
import Mathbin.Data.Polynomial.Eval 
import Mathbin.Data.Polynomial.Monic 
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


open_locale Matrix BigOperators

variable{n α : Type _}[DecidableEq n][Fintype n][CommRingₓ α]

open Polynomial Matrix Equiv.Perm

namespace Polynomial

-- error in LinearAlgebra.Matrix.Polynomial: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem nat_degree_det_X_add_C_le
(A
 B : matrix n n α) : «expr ≤ »(nat_degree (det «expr + »(«expr • »((X : polynomial α), A.map C), B.map C)), fintype.card n) :=
begin
  rw [expr det_apply] [],
  refine [expr (nat_degree_sum_le _ _).trans _],
  refine [expr multiset.max_nat_le_of_forall_le _ _ _],
  simp [] [] ["only"] ["[", expr forall_apply_eq_imp_iff', ",", expr true_and, ",", expr function.comp_app, ",", expr multiset.map_map, ",", expr multiset.mem_map, ",", expr exists_imp_distrib, ",", expr finset.mem_univ_val, "]"] [] [],
  intro [ident g],
  calc
    «expr ≤ »(nat_degree «expr • »(sign g, «expr∏ , »((i : n), «expr + »(«expr • »(X, A.map C), B.map C) (g i) i)), nat_degree «expr∏ , »((i : n), «expr + »(«expr • »(X, A.map C), B.map C) (g i) i)) : by { cases [expr int.units_eq_one_or (sign g)] ["with", ident sg, ident sg],
      { rw ["[", expr sg, ",", expr one_smul, "]"] [] },
      { rw ["[", expr sg, ",", expr units.neg_smul, ",", expr one_smul, ",", expr nat_degree_neg, "]"] [] } }
    «expr ≤ »(..., «expr∑ , »((i : n), nat_degree («expr + »(«expr • »((X : polynomial α), A.map C), B.map C) (g i) i))) : nat_degree_prod_le (finset.univ : finset n) (λ
     i : n, «expr + »(«expr • »(X, A.map C), B.map C) (g i) i)
    «expr ≤ »(..., «expr • »(finset.univ.card, 1)) : finset.sum_le_of_forall_le _ _ 1 (λ (i : n) (_), _)
    «expr ≤ »(..., fintype.card n) : by simpa [] [] [] [] [] [],
  calc
    «expr = »(nat_degree («expr + »(«expr • »((X : polynomial α), A.map C), B.map C) (g i) i), nat_degree «expr + »(«expr * »((X : polynomial α), C (A (g i) i)), C (B (g i) i))) : by simp [] [] [] [] [] []
    «expr ≤ »(..., max (nat_degree «expr * »((X : polynomial α), C (A (g i) i))) (nat_degree (C (B (g i) i)))) : nat_degree_add_le _ _
    «expr = »(..., nat_degree «expr * »((X : polynomial α), C (A (g i) i))) : max_eq_left ((nat_degree_C _).le.trans (zero_le _))
    «expr ≤ »(..., nat_degree (X : polynomial α)) : nat_degree_mul_C_le _ _
    «expr ≤ »(..., 1) : nat_degree_X_le
end

theorem coeff_det_X_add_C_zero (A B : Matrix n n α) : coeff (det (((X : Polynomial α) • A.map C)+B.map C)) 0 = det B :=
  by 
    rw [det_apply, finset_sum_coeff, det_apply]
    refine' Finset.sum_congr rfl _ 
    intro g hg 
    convert coeff_smul (sign g) _ 0
    rw [coeff_zero_prod]
    refine' Finset.prod_congr rfl _ 
    simp 

theorem coeff_det_X_add_C_card (A B : Matrix n n α) :
  coeff (det (((X : Polynomial α) • A.map C)+B.map C)) (Fintype.card n) = det A :=
  by 
    rw [det_apply, det_apply, finset_sum_coeff]
    refine' Finset.sum_congr rfl _ 
    simp only [Algebra.id.smul_eq_mul, Finset.mem_univ, RingHom.map_matrix_apply, forall_true_left, map_apply,
      Pi.smul_apply]
    intro g 
    convert coeff_smul (sign g) _ _ 
    rw [←mul_oneₓ (Fintype.card n)]
    convert (coeff_prod_of_nat_degree_le _ _ _ _).symm
    ·
      ext 
      simp [coeff_C]
    ·
      intro p hp 
      refine' (nat_degree_add_le _ _).trans _ 
      simpa using (nat_degree_mul_C_le _ _).trans nat_degree_X_le

-- error in LinearAlgebra.Matrix.Polynomial: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem leading_coeff_det_X_one_add_C
(A : matrix n n α) : «expr = »(leading_coeff (det «expr + »(«expr • »((X : polynomial α), (1 : matrix n n (polynomial α))), A.map C)), 1) :=
begin
  casesI [expr subsingleton_or_nontrivial α] [],
  { simp [] [] [] [] [] [] },
  rw ["[", "<-", expr @det_one n, ",", "<-", expr coeff_det_X_add_C_card _ A, ",", expr leading_coeff, "]"] [],
  simp [] [] ["only"] ["[", expr matrix.map_one, ",", expr C_eq_zero, ",", expr ring_hom.map_one, "]"] [] [],
  cases [expr (nat_degree_det_X_add_C_le 1 A).eq_or_lt] ["with", ident h, ident h],
  { simp [] [] ["only"] ["[", expr ring_hom.map_one, ",", expr matrix.map_one, ",", expr C_eq_zero, "]"] [] ["at", ident h],
    rw [expr h] [] },
  { have [ident H] [] [":=", expr coeff_eq_zero_of_nat_degree_lt h],
    rw [expr coeff_det_X_add_C_card] ["at", ident H],
    simpa [] [] [] [] [] ["using", expr H] }
end

end Polynomial

