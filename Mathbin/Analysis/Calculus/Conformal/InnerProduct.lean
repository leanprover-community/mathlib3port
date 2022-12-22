/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang

! This file was ported from Lean 3 source module analysis.calculus.conformal.inner_product
! leanprover-community/mathlib commit 9116dd6709f303dcf781632e15fdef382b0fc579
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Calculus.Conformal.NormedSpace
import Mathbin.Analysis.InnerProductSpace.ConformalLinearMap

/-!
# Conformal maps between inner product spaces

A function between inner product spaces is which has a derivative at `x`
is conformal at `x` iff the derivative preserves inner products up to a scalar multiple.
-/


noncomputable section

variable {E F : Type _} [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]

open RealInnerProductSpace

/-- A real differentiable map `f` is conformal at point `x` if and only if its
    differential `fderiv ℝ f x` at that point scales every inner product by a positive scalar. -/
theorem conformal_at_iff' {f : E → F} {x : E} :
    ConformalAt f x ↔ ∃ c : ℝ, 0 < c ∧ ∀ u v : E, ⟪fderiv ℝ f x u, fderiv ℝ f x v⟫ = c * ⟪u, v⟫ :=
  by rw [conformal_at_iff_is_conformal_map_fderiv, is_conformal_map_iff]
#align conformal_at_iff' conformal_at_iff'

/-- A real differentiable map `f` is conformal at point `x` if and only if its
    differential `f'` at that point scales every inner product by a positive scalar. -/
theorem conformal_at_iff {f : E → F} {x : E} {f' : E →L[ℝ] F} (h : HasFderivAt f f' x) :
    ConformalAt f x ↔ ∃ c : ℝ, 0 < c ∧ ∀ u v : E, ⟪f' u, f' v⟫ = c * ⟪u, v⟫ := by
  simp only [conformal_at_iff', h.fderiv]
#align conformal_at_iff conformal_at_iff

/-- The conformal factor of a conformal map at some point `x`. Some authors refer to this function
    as the characteristic function of the conformal map. -/
def conformalFactorAt {f : E → F} {x : E} (h : ConformalAt f x) : ℝ :=
  Classical.choose (conformal_at_iff'.mp h)
#align conformal_factor_at conformalFactorAt

theorem conformal_factor_at_pos {f : E → F} {x : E} (h : ConformalAt f x) :
    0 < conformalFactorAt h :=
  (Classical.choose_spec <| conformal_at_iff'.mp h).1
#align conformal_factor_at_pos conformal_factor_at_pos

theorem conformal_factor_at_inner_eq_mul_inner' {f : E → F} {x : E} (h : ConformalAt f x)
    (u v : E) : ⟪(fderiv ℝ f x) u, (fderiv ℝ f x) v⟫ = (conformalFactorAt h : ℝ) * ⟪u, v⟫ :=
  (Classical.choose_spec <| conformal_at_iff'.mp h).2 u v
#align conformal_factor_at_inner_eq_mul_inner' conformal_factor_at_inner_eq_mul_inner'

theorem conformal_factor_at_inner_eq_mul_inner {f : E → F} {x : E} {f' : E →L[ℝ] F}
    (h : HasFderivAt f f' x) (H : ConformalAt f x) (u v : E) :
    ⟪f' u, f' v⟫ = (conformalFactorAt H : ℝ) * ⟪u, v⟫ :=
  H.DifferentiableAt.HasFderivAt.unique h ▸ conformal_factor_at_inner_eq_mul_inner' H u v
#align conformal_factor_at_inner_eq_mul_inner conformal_factor_at_inner_eq_mul_inner

