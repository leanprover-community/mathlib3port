/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang

! This file was ported from Lean 3 source module analysis.calculus.conformal.inner_product
! leanprover-community/mathlib commit 0b7c740e25651db0ba63648fbae9f9d6f941e31b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Calculus.Conformal.NormedSpace
import Mathbin.Analysis.InnerProductSpace.ConformalLinearMap

/-!
# Conformal maps between inner product spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A function between inner product spaces is which has a derivative at `x`
is conformal at `x` iff the derivative preserves inner products up to a scalar multiple.
-/


noncomputable section

variable {E F : Type _}

variable [NormedAddCommGroup E] [NormedAddCommGroup F]

variable [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]

open RealInnerProductSpace

/- warning: conformal_at_iff' -> conformalAt_iff' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align conformal_at_iff' conformalAt_iff'ₓ'. -/
/-- A real differentiable map `f` is conformal at point `x` if and only if its
    differential `fderiv ℝ f x` at that point scales every inner product by a positive scalar. -/
theorem conformalAt_iff' {f : E → F} {x : E} :
    ConformalAt f x ↔ ∃ c : ℝ, 0 < c ∧ ∀ u v : E, ⟪fderiv ℝ f x u, fderiv ℝ f x v⟫ = c * ⟪u, v⟫ :=
  by rw [conformalAt_iff_isConformalMap_fderiv, isConformalMap_iff]
#align conformal_at_iff' conformalAt_iff'

/- warning: conformal_at_iff -> conformalAt_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align conformal_at_iff conformalAt_iffₓ'. -/
/-- A real differentiable map `f` is conformal at point `x` if and only if its
    differential `f'` at that point scales every inner product by a positive scalar. -/
theorem conformalAt_iff {f : E → F} {x : E} {f' : E →L[ℝ] F} (h : HasFDerivAt f f' x) :
    ConformalAt f x ↔ ∃ c : ℝ, 0 < c ∧ ∀ u v : E, ⟪f' u, f' v⟫ = c * ⟪u, v⟫ := by
  simp only [conformalAt_iff', h.fderiv]
#align conformal_at_iff conformalAt_iff

#print conformalFactorAt /-
/-- The conformal factor of a conformal map at some point `x`. Some authors refer to this function
    as the characteristic function of the conformal map. -/
def conformalFactorAt {f : E → F} {x : E} (h : ConformalAt f x) : ℝ :=
  Classical.choose (conformalAt_iff'.mp h)
#align conformal_factor_at conformalFactorAt
-/

/- warning: conformal_factor_at_pos -> conformalFactorAt_pos is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} {F : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} E] [_inst_2 : NormedAddCommGroup.{u2} F] [_inst_3 : InnerProductSpace.{0, u1} Real E Real.isROrC _inst_1] [_inst_4 : InnerProductSpace.{0, u2} Real F Real.isROrC _inst_2] {f : E -> F} {x : E} (h : ConformalAt.{u1, u2} E F _inst_1 _inst_2 (InnerProductSpace.toNormedSpace.{0, u1} Real E Real.isROrC _inst_1 _inst_3) (InnerProductSpace.toNormedSpace.{0, u2} Real F Real.isROrC _inst_2 _inst_4) f x), LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (conformalFactorAt.{u1, u2} E F _inst_1 _inst_2 _inst_3 _inst_4 f x h)
but is expected to have type
  forall {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} E] [_inst_2 : NormedAddCommGroup.{u1} F] [_inst_3 : InnerProductSpace.{0, u2} Real E Real.isROrC _inst_1] [_inst_4 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_2] {f : E -> F} {x : E} (h : ConformalAt.{u2, u1} E F _inst_1 _inst_2 (InnerProductSpace.toNormedSpace.{0, u2} Real E Real.isROrC _inst_1 _inst_3) (InnerProductSpace.toNormedSpace.{0, u1} Real F Real.isROrC _inst_2 _inst_4) f x), LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (conformalFactorAt.{u2, u1} E F _inst_1 _inst_2 _inst_3 _inst_4 f x h)
Case conversion may be inaccurate. Consider using '#align conformal_factor_at_pos conformalFactorAt_posₓ'. -/
theorem conformalFactorAt_pos {f : E → F} {x : E} (h : ConformalAt f x) : 0 < conformalFactorAt h :=
  (Classical.choose_spec <| conformalAt_iff'.mp h).1
#align conformal_factor_at_pos conformalFactorAt_pos

/- warning: conformal_factor_at_inner_eq_mul_inner' -> conformalFactorAt_inner_eq_mul_inner' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align conformal_factor_at_inner_eq_mul_inner' conformalFactorAt_inner_eq_mul_inner'ₓ'. -/
theorem conformalFactorAt_inner_eq_mul_inner' {f : E → F} {x : E} (h : ConformalAt f x) (u v : E) :
    ⟪(fderiv ℝ f x) u, (fderiv ℝ f x) v⟫ = (conformalFactorAt h : ℝ) * ⟪u, v⟫ :=
  (Classical.choose_spec <| conformalAt_iff'.mp h).2 u v
#align conformal_factor_at_inner_eq_mul_inner' conformalFactorAt_inner_eq_mul_inner'

/- warning: conformal_factor_at_inner_eq_mul_inner -> conformalFactorAt_inner_eq_mul_inner is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align conformal_factor_at_inner_eq_mul_inner conformalFactorAt_inner_eq_mul_innerₓ'. -/
theorem conformalFactorAt_inner_eq_mul_inner {f : E → F} {x : E} {f' : E →L[ℝ] F}
    (h : HasFDerivAt f f' x) (H : ConformalAt f x) (u v : E) :
    ⟪f' u, f' v⟫ = (conformalFactorAt H : ℝ) * ⟪u, v⟫ :=
  H.DifferentiableAt.HasFDerivAt.unique h ▸ conformalFactorAt_inner_eq_mul_inner' H u v
#align conformal_factor_at_inner_eq_mul_inner conformalFactorAt_inner_eq_mul_inner

