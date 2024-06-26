/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Analysis.Complex.UpperHalfPlane.Topology
import Geometry.Manifold.ContMDiffMFDeriv

#align_import analysis.complex.upper_half_plane.manifold from "leanprover-community/mathlib"@"728ef9dbb281241906f25cbeb30f90d83e0bb451"

/-!
# Manifold structure on the upper half plane.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define the complex manifold structure on the upper half-plane.
-/


open scoped UpperHalfPlane Manifold

namespace UpperHalfPlane

noncomputable instance : ChartedSpace ℂ ℍ :=
  UpperHalfPlane.openEmbedding_coe.singletonChartedSpace

instance : SmoothManifoldWithCorners 𝓘(ℂ) ℍ :=
  UpperHalfPlane.openEmbedding_coe.singleton_smoothManifoldWithCorners 𝓘(ℂ)

#print UpperHalfPlane.smooth_coe /-
/-- The inclusion map `ℍ → ℂ` is a smooth map of manifolds. -/
theorem smooth_coe : Smooth 𝓘(ℂ) 𝓘(ℂ) (coe : ℍ → ℂ) := fun x => contMDiffAt_extChartAt
#align upper_half_plane.smooth_coe UpperHalfPlane.smooth_coe
-/

#print UpperHalfPlane.mdifferentiable_coe /-
/-- The inclusion map `ℍ → ℂ` is a differentiable map of manifolds. -/
theorem mdifferentiable_coe : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (coe : ℍ → ℂ) :=
  smooth_coe.MDifferentiable
#align upper_half_plane.mdifferentiable_coe UpperHalfPlane.mdifferentiable_coe
-/

end UpperHalfPlane

