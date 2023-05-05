/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module analysis.complex.upper_half_plane.topology
! leanprover-community/mathlib commit f0c8bf9245297a541f468be517f1bde6195105e9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Complex.UpperHalfPlane.Basic
import Mathbin.Analysis.Convex.Contractible
import Mathbin.Analysis.Convex.Normed
import Mathbin.Analysis.Convex.Complex
import Mathbin.Analysis.Complex.ReImTopology
import Mathbin.Topology.Homotopy.Contractible
import Mathbin.Geometry.Manifold.ContMdiffMfderiv

/-!
# Topology on the upper half plane

In this file we introduce a `topological_space` structure on the upper half plane and provide
various instances.
-/


noncomputable section

open Set Filter Function TopologicalSpace Complex

open Filter Topology UpperHalfPlane Manifold

namespace UpperHalfPlane

instance : TopologicalSpace ℍ :=
  Subtype.topologicalSpace

theorem openEmbedding_coe : OpenEmbedding (coe : ℍ → ℂ) :=
  IsOpen.openEmbedding_subtype_val <| isOpen_lt continuous_const Complex.continuous_im
#align upper_half_plane.open_embedding_coe UpperHalfPlane.openEmbedding_coe

theorem embedding_coe : Embedding (coe : ℍ → ℂ) :=
  embedding_subtype_val
#align upper_half_plane.embedding_coe UpperHalfPlane.embedding_coe

theorem continuous_coe : Continuous (coe : ℍ → ℂ) :=
  embedding_coe.Continuous
#align upper_half_plane.continuous_coe UpperHalfPlane.continuous_coe

theorem continuous_re : Continuous re :=
  Complex.continuous_re.comp continuous_coe
#align upper_half_plane.continuous_re UpperHalfPlane.continuous_re

theorem continuous_im : Continuous im :=
  Complex.continuous_im.comp continuous_coe
#align upper_half_plane.continuous_im UpperHalfPlane.continuous_im

instance : TopologicalSpace.SecondCountableTopology ℍ :=
  TopologicalSpace.Subtype.secondCountableTopology _ _

instance : T3Space ℍ :=
  Subtype.t3Space

instance : NormalSpace ℍ :=
  normalSpaceOfT3SecondCountable ℍ

instance : ContractibleSpace ℍ :=
  (convex_halfspace_im_gt 0).ContractibleSpace ⟨I, one_pos.trans_eq I_im.symm⟩

instance : LocPathConnectedSpace ℍ :=
  locPathConnected_of_isOpen <| isOpen_lt continuous_const Complex.continuous_im

instance : NoncompactSpace ℍ := by
  refine' ⟨fun h => _⟩
  have : IsCompact (Complex.im ⁻¹' Ioi 0) := isCompact_iff_isCompact_univ.2 h
  replace := this.is_closed.closure_eq
  rw [closure_preimage_im, closure_Ioi, Set.ext_iff] at this
  exact absurd ((this 0).1 left_mem_Ici) (lt_irrefl _)

instance : LocallyCompactSpace ℍ :=
  openEmbedding_coe.LocallyCompactSpace

instance UpperHalfPlane.chartedSpace : ChartedSpace ℂ ℍ :=
  UpperHalfPlane.openEmbedding_coe.singletonChartedSpace
#align upper_half_plane.upper_half_plane.charted_space UpperHalfPlane.UpperHalfPlane.chartedSpace

instance UpperHalfPlane.smoothManifoldWithCorners : SmoothManifoldWithCorners 𝓘(ℂ) ℍ :=
  UpperHalfPlane.openEmbedding_coe.singleton_smoothManifoldWithCorners 𝓘(ℂ)
#align upper_half_plane.upper_half_plane.smooth_manifold_with_corners UpperHalfPlane.UpperHalfPlane.smoothManifoldWithCorners

/-- The inclusion map `ℍ → ℂ` is a smooth map of manifolds. -/
theorem smooth_coe : Smooth 𝓘(ℂ) 𝓘(ℂ) (coe : ℍ → ℂ) := fun x => contMdiffAt_extChartAt
#align upper_half_plane.smooth_coe UpperHalfPlane.smooth_coe

/-- The inclusion map `ℍ → ℂ` is a differentiable map of manifolds. -/
theorem mdifferentiable_coe : Mdifferentiable 𝓘(ℂ) 𝓘(ℂ) (coe : ℍ → ℂ) :=
  smooth_coe.Mdifferentiable
#align upper_half_plane.mdifferentiable_coe UpperHalfPlane.mdifferentiable_coe

end UpperHalfPlane

