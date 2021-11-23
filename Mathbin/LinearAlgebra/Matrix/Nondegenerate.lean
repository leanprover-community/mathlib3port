import Mathbin.Data.Matrix.Basic 
import Mathbin.LinearAlgebra.Matrix.Determinant 
import Mathbin.LinearAlgebra.Matrix.Adjugate

/-!
# Matrices associated with non-degenerate bilinear forms

## Main definitions

* `matrix.nondegenerate A`: the proposition that when interpreted as a bilinear form, the matrix `A`
  is nondegenerate.

-/


namespace Matrix

variable{m R A : Type _}[Fintype m][CommRingₓ R]

/-- A matrix `M` is nondegenerate if for all `v ≠ 0`, there is a `w ≠ 0` with `w ⬝ M ⬝ v ≠ 0`. -/
def nondegenerate (M : Matrix m m R) :=
  ∀ v, (∀ w, Matrix.dotProduct v (mul_vec M w) = 0) → v = 0

/-- If `M` is nondegenerate and `w ⬝ M ⬝ v = 0` for all `w`, then `v = 0`. -/
theorem nondegenerate.eq_zero_of_ortho {M : Matrix m m R} (hM : nondegenerate M) {v : m → R}
  (hv : ∀ w, Matrix.dotProduct v (mul_vec M w) = 0) : v = 0 :=
  hM v hv

/-- If `M` is nondegenerate and `v ≠ 0`, then there is some `w` such that `w ⬝ M ⬝ v ≠ 0`. -/
theorem nondegenerate.exists_not_ortho_of_ne_zero {M : Matrix m m R} (hM : nondegenerate M) {v : m → R} (hv : v ≠ 0) :
  ∃ w, Matrix.dotProduct v (mul_vec M w) ≠ 0 :=
  not_forall.mp (mt hM.eq_zero_of_ortho hv)

variable[CommRingₓ A][IsDomain A]

-- error in LinearAlgebra.Matrix.Nondegenerate: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `M` has a nonzero determinant, then `M` as a bilinear form on `n → A` is nondegenerate.

See also `bilin_form.nondegenerate_of_det_ne_zero'` and `bilin_form.nondegenerate_of_det_ne_zero`.
-/
theorem nondegenerate_of_det_ne_zero [decidable_eq m] {M : matrix m m A} (hM : «expr ≠ »(M.det, 0)) : nondegenerate M :=
begin
  intros [ident v, ident hv],
  ext [] [ident i] [],
  specialize [expr hv (M.cramer (pi.single i 1))],
  refine [expr (mul_eq_zero.mp _).resolve_right hM],
  convert [] [expr hv] [],
  simp [] [] ["only"] ["[", expr mul_vec_cramer M (pi.single i 1), ",", expr dot_product, ",", expr pi.smul_apply, ",", expr smul_eq_mul, "]"] [] [],
  rw ["[", expr finset.sum_eq_single i, ",", expr pi.single_eq_same, ",", expr mul_one, "]"] [],
  { intros [ident j, "_", ident hj],
    simp [] [] [] ["[", expr hj, "]"] [] [] },
  { intros [],
    have [] [] [":=", expr finset.mem_univ i],
    contradiction }
end

theorem eq_zero_of_vec_mul_eq_zero [DecidableEq m] {M : Matrix m m A} (hM : M.det ≠ 0) {v : m → A}
  (hv : M.vec_mul v = 0) : v = 0 :=
  (nondegenerate_of_det_ne_zero hM).eq_zero_of_ortho
    fun w =>
      by 
        rw [dot_product_mul_vec, hv, zero_dot_product]

theorem eq_zero_of_mul_vec_eq_zero [DecidableEq m] {M : Matrix m m A} (hM : M.det ≠ 0) {v : m → A}
  (hv : M.mul_vec v = 0) : v = 0 :=
  eq_zero_of_vec_mul_eq_zero
    (by 
      rwa [det_transpose])
    ((vec_mul_transpose M v).trans hv)

end Matrix

