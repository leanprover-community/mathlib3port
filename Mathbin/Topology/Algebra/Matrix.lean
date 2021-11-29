import Mathbin.LinearAlgebra.Determinant 
import Mathbin.Topology.Algebra.Ring

/-!
# Topological properties of matrices

This file is a place to collect topological results about matrices.

## Main definitions:

 * `continuous_det`: the determinant is continuous over a topological ring.
-/


open Matrix

variable {ι k : Type _} [TopologicalSpace k]

instance : TopologicalSpace (Matrix ι ι k) :=
  Pi.topologicalSpace

variable [Fintype ι] [DecidableEq ι] [CommRingₓ k] [TopologicalRing k]

-- error in Topology.Algebra.Matrix: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem continuous_det : continuous (det : matrix ι ι k → k) :=
begin
  suffices [] [":", expr ∀ n : exprℕ(), continuous (λ A : matrix (fin n) (fin n) k, matrix.det A)],
  { have [ident h] [":", expr «expr = »((det : matrix ι ι k → k), «expr ∘ »(det, reindex (fintype.equiv_fin ι) (fintype.equiv_fin ι)))] [],
    { ext [] [] [],
      simp [] [] [] [] [] [] },
    rw [expr h] [],
    apply [expr (this (fintype.card ι)).comp],
    exact [expr continuous_pi (λ i, continuous_pi (λ j, continuous_apply_apply _ _))] },
  intros [ident n],
  induction [expr n] [] ["with", ident n, ident ih] [],
  { simp_rw [expr coe_det_is_empty] [],
    exact [expr continuous_const] },
  simp_rw [expr det_succ_column_zero] [],
  refine [expr continuous_finset_sum _ (λ l _, _)],
  refine [expr (continuous_const.mul (continuous_apply_apply _ _)).mul (ih.comp _)],
  exact [expr continuous_pi (λ i, continuous_pi (λ j, continuous_apply_apply _ _))]
end

