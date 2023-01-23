/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot

! This file was ported from Lean 3 source module topology.algebra.uniform_filter_basis
! leanprover-community/mathlib commit 1f0096e6caa61e9c849ec2adbd227e960e9dff58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.FilterBasis
import Mathbin.Topology.Algebra.UniformGroup

/-!
# Uniform properties of neighborhood bases in topological algebra

This files contains properties of filter bases on algebraic structures that also require the theory
of uniform spaces.

The only result so far is a characterization of Cauchy filters in topological groups.

-/


open uniformity Filter

open Filter

namespace AddGroupFilterBasis

variable {G : Type _} [AddCommGroup G] (B : AddGroupFilterBasis G)

/-- The uniform space structure associated to an abelian group filter basis via the associated
topological abelian group structure. -/
protected def uniformSpace : UniformSpace G :=
  @TopologicalAddGroup.toUniformSpace G _ B.topology B.is_topological_add_group
#align add_group_filter_basis.uniform_space AddGroupFilterBasis.uniformSpace

/-- The uniform space structure associated to an abelian group filter basis via the associated
topological abelian group structure is compatible with its group structure. -/
protected theorem uniformAddGroup : @UniformAddGroup G B.UniformSpace _ :=
  @topological_add_commGroup_is_uniform G _ B.topology B.is_topological_add_group
#align add_group_filter_basis.uniform_add_group AddGroupFilterBasis.uniformAddGroup

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (x y «expr ∈ » M) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (x y «expr ∈ » M) -/
theorem cauchy_iff {F : Filter G} :
    @Cauchy G B.UniformSpace F ↔
      F.ne_bot ∧ ∀ U ∈ B, ∃ M ∈ F, ∀ (x) (_ : x ∈ M) (y) (_ : y ∈ M), y - x ∈ U :=
  by
  letI := B.uniform_space
  haveI := B.uniform_add_group
  suffices F ×ᶠ F ≤ 𝓤 G ↔ ∀ U ∈ B, ∃ M ∈ F, ∀ (x) (_ : x ∈ M) (y) (_ : y ∈ M), y - x ∈ U by
    constructor <;> rintro ⟨h', h⟩ <;> refine' ⟨h', _⟩ <;> [rwa [← this], rwa [this]]
  rw [uniformity_eq_comap_nhds_zero G, ← map_le_iff_le_comap]
  change tendsto _ _ _ ↔ _
  simp [(basis_sets F).prod_self.tendsto_iff B.nhds_zero_has_basis, @forall_swap (_ ∈ _) G]
#align add_group_filter_basis.cauchy_iff AddGroupFilterBasis.cauchy_iff

end AddGroupFilterBasis

