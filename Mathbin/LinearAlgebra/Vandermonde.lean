import Mathbin.Algebra.BigOperators.Fin 
import Mathbin.Algebra.GeomSum 
import Mathbin.GroupTheory.Perm.Fin 
import Mathbin.LinearAlgebra.Matrix.Determinant 
import Mathbin.Tactic.RingExp

/-!
# Vandermonde matrix

This file defines the `vandermonde` matrix and gives its determinant.

## Main definitions

 - `vandermonde v`: a square matrix with the `i, j`th entry equal to `v i ^ j`.

## Main results

 - `det_vandermonde`: `det (vandermonde v)` is the product of `v i - v j`, where
   `(i, j)` ranges over the unordered pairs.
-/


variable{R : Type _}[CommRingₓ R]

open_locale BigOperators

open_locale Matrix

open Equiv

namespace Matrix

/-- `vandermonde v` is the square matrix with `i`th row equal to `1, v i, v i ^ 2, v i ^ 3, ...`.
-/
def vandermonde {n : ℕ} (v : Finₓ n → R) : Matrix (Finₓ n) (Finₓ n) R :=
  fun i j => v i^(j : ℕ)

@[simp]
theorem vandermonde_apply {n : ℕ} (v : Finₓ n → R) i j : vandermonde v i j = (v i^(j : ℕ)) :=
  rfl

@[simp]
theorem vandermonde_cons {n : ℕ} (v0 : R) (v : Finₓ n → R) :
  vandermonde (Finₓ.cons v0 v : Finₓ n.succ → R) =
    Finₓ.cons (fun j => v0^(j : ℕ)) fun i => Finₓ.cons 1 fun j => v i*vandermonde v i j :=
  by 
    ext i j 
    refine'
      Finₓ.cases
        (by 
          simp )
        (fun i => _) i 
    refine'
      Finₓ.cases
        (by 
          simp )
        (fun j => _) j 
    simp [pow_succₓ]

theorem vandermonde_succ {n : ℕ} (v : Finₓ n.succ → R) :
  vandermonde v =
    Finₓ.cons (fun j => v 0^(j : ℕ)) fun i => Finₓ.cons 1 fun j => v i.succ*vandermonde (Finₓ.tail v) i j :=
  by 
    convLHS => rw [←Finₓ.cons_self_tail v, vandermonde_cons]
    simp only [Finₓ.tail]

theorem vandermonde_mul_vandermonde_transpose {n : ℕ} (v w : Finₓ n → R) i j :
  (vandermonde v ⬝ (vandermonde w)ᵀ) i j = ∑k : Finₓ n, (v i*w j)^(k : ℕ) :=
  by 
    simp only [vandermonde_apply, Matrix.mul_apply, Matrix.transpose_apply, mul_powₓ]

theorem vandermonde_transpose_mul_vandermonde {n : ℕ} (v : Finₓ n → R) i j :
  ((vandermonde v)ᵀ ⬝ vandermonde v) i j = ∑k : Finₓ n, v k^(i+j : ℕ) :=
  by 
    simp only [vandermonde_apply, Matrix.mul_apply, Matrix.transpose_apply, pow_addₓ]

-- error in LinearAlgebra.Vandermonde: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem det_vandermonde
{n : exprℕ()}
(v : fin n → R) : «expr = »(det (vandermonde v), «expr∏ , »((i : fin n), «expr∏ in , »((j), finset.univ.filter (λ
    j, «expr < »(i, j)), «expr - »(v j, v i)))) :=
begin
  unfold [ident vandermonde] [],
  induction [expr n] [] ["with", ident n, ident ih] [],
  { exact [expr det_eq_one_of_card_eq_zero (fintype.card_fin 0)] },
  calc
    «expr = »(det (λ
      i
      j : fin n.succ, «expr ^ »(v i, (j : exprℕ()))), det (λ
      i
      j : fin n.succ, @fin.cons _ (λ
       _, R) «expr ^ »(v 0, (j : exprℕ())) (λ
       i, «expr - »(«expr ^ »(v (fin.succ i), (j : exprℕ())), «expr ^ »(v 0, (j : exprℕ())))) i)) : det_eq_of_forall_row_eq_smul_add_const (fin.cons 0 1) 0 (fin.cons_zero _ _) _
    «expr = »(..., det (λ
      i
      j : fin n, @fin.cons _ (λ
       _, R) «expr ^ »(v 0, (j.succ : exprℕ())) (λ
       i : fin n, «expr - »(«expr ^ »(v (fin.succ i), (j.succ : exprℕ())), «expr ^ »(v 0, (j.succ : exprℕ())))) (fin.succ_above 0 i))) : by simp_rw ["[", expr det_succ_column_zero, ",", expr fin.sum_univ_succ, ",", expr fin.cons_zero, ",", expr minor, ",", expr fin.cons_succ, ",", expr fin.coe_zero, ",", expr pow_zero, ",", expr one_mul, ",", expr sub_self, ",", expr mul_zero, ",", expr zero_mul, ",", expr finset.sum_const_zero, ",", expr add_zero, "]"] []
    «expr = »(..., det (λ
      i
      j : fin n, «expr * »(«expr - »(v (fin.succ i), v 0), «expr∑ in , »((k), finset.range («expr + »(j, 1) : exprℕ()), «expr * »(«expr ^ »(v i.succ, k), «expr ^ »(v 0, («expr - »(j, k) : exprℕ()))))))) : by { congr,
      ext [] [ident i, ident j] [],
      rw ["[", expr fin.succ_above_zero, ",", expr fin.cons_succ, ",", expr fin.coe_succ, ",", expr mul_comm, "]"] [],
      exact [expr (geom_sum₂_mul (v i.succ) (v 0) («expr + »(j, 1) : exprℕ())).symm] }
    «expr = »(..., «expr * »(«expr∏ , »((i : fin n), «expr - »(v (fin.succ i), v 0)), det (λ
       i
       j : fin n, «expr∑ in , »((k), finset.range («expr + »(j, 1) : exprℕ()), «expr * »(«expr ^ »(v i.succ, k), «expr ^ »(v 0, («expr - »(j, k) : exprℕ()))))))) : det_mul_column (λ
     i, «expr - »(v (fin.succ i), v 0)) _
    «expr = »(..., «expr * »(«expr∏ , »((i : fin n), «expr - »(v (fin.succ i), v 0)), det (λ
       i j : fin n, «expr ^ »(v (fin.succ i), (j : exprℕ()))))) : congr_arg (((«expr * »)) _) _
    «expr = »(..., «expr∏ , »((i : fin n.succ), «expr∏ in , »((j), finset.univ.filter (λ
        j, «expr < »(i, j)), «expr - »(v j, v i)))) : by { simp_rw ["[", expr ih «expr ∘ »(v, fin.succ), ",", expr fin.prod_univ_succ, ",", expr fin.prod_filter_zero_lt, ",", expr fin.prod_filter_succ_lt, "]"] [] },
  { intros [ident i, ident j],
    rw [expr fin.cons_zero] [],
    refine [expr fin.cases _ (λ i, _) i],
    { simp [] [] [] [] [] [] },
    rw ["[", expr fin.cons_succ, ",", expr fin.cons_succ, ",", expr pi.one_apply, "]"] [],
    ring [] },
  { cases [expr n] [],
    { simp [] [] ["only"] ["[", expr det_eq_one_of_card_eq_zero (fintype.card_fin 0), "]"] [] [] },
    apply [expr det_eq_of_forall_col_eq_smul_add_pred (λ i, v 0)],
    { intro [ident j],
      simp [] [] [] [] [] [] },
    { intros [ident i, ident j],
      simp [] [] ["only"] ["[", expr smul_eq_mul, ",", expr pi.add_apply, ",", expr fin.coe_succ, ",", expr fin.coe_cast_succ, ",", expr pi.smul_apply, "]"] [] [],
      rw ["[", expr finset.sum_range_succ, ",", expr add_comm, ",", expr tsub_self, ",", expr pow_zero, ",", expr mul_one, ",", expr finset.mul_sum, "]"] [],
      congr' [1] [],
      refine [expr finset.sum_congr rfl (λ i' hi', _)],
      rw ["[", expr mul_left_comm (v 0), ",", expr nat.succ_sub, ",", expr pow_succ, "]"] [],
      exact [expr nat.lt_succ_iff.mp (finset.mem_range.mp hi')] } }
end

end Matrix

