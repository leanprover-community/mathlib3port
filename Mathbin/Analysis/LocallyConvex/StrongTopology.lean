/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker

! This file was ported from Lean 3 source module analysis.locally_convex.strong_topology
! leanprover-community/mathlib commit b8627dbac120a9ad6267a75575ae1e070d5bff5b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.Module.StrongTopology
import Mathbin.Topology.Algebra.Module.LocallyConvex

/-!
# Local convexity of the strong topology

In this file we prove that the strong topology on `E →L[ℝ] F` is locally convex provided that `F` is
locally convex.

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Todo

* Characterization in terms of seminorms

## Tags

locally convex, bounded convergence
-/


open Topology UniformConvergence

variable {E F : Type _}

namespace ContinuousLinearMap

section General

variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace F] [TopologicalAddGroup F] [ContinuousConstSMul ℝ F] [LocallyConvexSpace ℝ F]

theorem strongTopology.locallyConvexSpace (𝔖 : Set (Set E)) (h𝔖₁ : 𝔖.Nonempty)
    (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖) :
    @LocallyConvexSpace ℝ (E →L[ℝ] F) _ _ _ (strongTopology (RingHom.id ℝ) F 𝔖) :=
  by
  letI : TopologicalSpace (E →L[ℝ] F) := strong_topology (RingHom.id ℝ) F 𝔖
  haveI : TopologicalAddGroup (E →L[ℝ] F) := strong_topology.topological_add_group _ _ _
  refine'
    LocallyConvexSpace.ofBasisZero _ _ _ _
      (strong_topology.has_basis_nhds_zero_of_basis _ _ _ h𝔖₁ h𝔖₂
        (LocallyConvexSpace.convex_basis_zero ℝ F))
      _
  rintro ⟨S, V⟩ ⟨hS, hVmem, hVconvex⟩ f hf g hg a b ha hb hab x hx
  exact hVconvex (hf x hx) (hg x hx) ha hb hab
#align continuous_linear_map.strong_topology.locally_convex_space ContinuousLinearMap.strongTopology.locallyConvexSpace

end General

section BoundedSets

variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace F] [TopologicalAddGroup F] [ContinuousConstSMul ℝ F] [LocallyConvexSpace ℝ F]

instance : LocallyConvexSpace ℝ (E →L[ℝ] F) :=
  strongTopology.locallyConvexSpace _ ⟨∅, Bornology.isVonNBounded_empty ℝ E⟩
    (directedOn_of_sup_mem fun _ _ => Bornology.IsVonNBounded.union)

end BoundedSets

end ContinuousLinearMap

