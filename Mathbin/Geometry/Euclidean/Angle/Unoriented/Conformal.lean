/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang

! This file was ported from Lean 3 source module geometry.euclidean.angle.unoriented.conformal
! leanprover-community/mathlib commit b363547b3113d350d053abdf2884e9850a56b205
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Calculus.Conformal.NormedSpace
import Mathbin.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# Angles and conformal maps

This file proves that conformal maps preserve angles.

-/


namespace InnerProductGeometry

variable {V : Type _} [InnerProductSpace ℝ V]

theorem IsConformalMap.preserves_angle {E F : Type _} [InnerProductSpace ℝ E]
    [InnerProductSpace ℝ F] {f' : E →L[ℝ] F} (h : IsConformalMap f') (u v : E) :
    angle (f' u) (f' v) = angle u v :=
  by
  obtain ⟨c, hc, li, rfl⟩ := h
  exact (angle_smul_smul hc _ _).trans (li.angle_map _ _)
#align inner_product_geometry.is_conformal_map.preserves_angle InnerProductGeometry.IsConformalMap.preserves_angle

/-- If a real differentiable map `f` is conformal at a point `x`,
    then it preserves the angles at that point. -/
theorem ConformalAt.preserves_angle {E F : Type _} [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]
    {f : E → F} {x : E} {f' : E →L[ℝ] F} (h : HasFderivAt f f' x) (H : ConformalAt f x) (u v : E) :
    angle (f' u) (f' v) = angle u v :=
  let ⟨f₁, h₁, c⟩ := H
  h₁.unique h ▸ IsConformalMap.preserves_angle c u v
#align inner_product_geometry.conformal_at.preserves_angle InnerProductGeometry.ConformalAt.preserves_angle

end InnerProductGeometry

