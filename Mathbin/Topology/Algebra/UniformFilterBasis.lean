/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Topology.Algebra.FilterBasis
import Topology.Algebra.UniformGroup

#align_import topology.algebra.uniform_filter_basis from "leanprover-community/mathlib"@"19cb3751e5e9b3d97adb51023949c50c13b5fdfd"

/-!
# Uniform properties of neighborhood bases in topological algebra

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This files contains properties of filter bases on algebraic structures that also require the theory
of uniform spaces.

The only result so far is a characterization of Cauchy filters in topological groups.

-/


open scoped uniformity Filter

open Filter

namespace AddGroupFilterBasis

variable {G : Type _} [AddCommGroup G] (B : AddGroupFilterBasis G)

#print AddGroupFilterBasis.uniformSpace /-
/-- The uniform space structure associated to an abelian group filter basis via the associated
topological abelian group structure. -/
protected def uniformSpace : UniformSpace G :=
  @TopologicalAddGroup.toUniformSpace G _ B.topology B.isTopologicalAddGroup
#align add_group_filter_basis.uniform_space AddGroupFilterBasis.uniformSpace
-/

#print AddGroupFilterBasis.uniformAddGroup /-
/-- The uniform space structure associated to an abelian group filter basis via the associated
topological abelian group structure is compatible with its group structure. -/
protected theorem uniformAddGroup : @UniformAddGroup G B.UniformSpace _ :=
  @comm_topologicalAddGroup_is_uniform G _ B.topology B.isTopologicalAddGroup
#align add_group_filter_basis.uniform_add_group AddGroupFilterBasis.uniformAddGroup
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:642:2: warning: expanding binder collection (x y «expr ∈ » M) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:642:2: warning: expanding binder collection (x y «expr ∈ » M) -/
#print AddGroupFilterBasis.cauchy_iff /-
theorem cauchy_iff {F : Filter G} :
    @Cauchy G B.UniformSpace F ↔
      F.ne_bot ∧ ∀ U ∈ B, ∃ M ∈ F, ∀ (x) (_ : x ∈ M) (y) (_ : y ∈ M), y - x ∈ U :=
  by
  letI := B.uniform_space
  haveI := B.uniform_add_group
  suffices F ×ᶠ F ≤ 𝓤 G ↔ ∀ U ∈ B, ∃ M ∈ F, ∀ (x) (_ : x ∈ M) (y) (_ : y ∈ M), y - x ∈ U by
    constructor <;> rintro ⟨h', h⟩ <;> refine' ⟨h', _⟩ <;> [rwa [← this]; rwa [this]]
  rw [uniformity_eq_comap_nhds_zero G, ← map_le_iff_le_comap]
  change tendsto _ _ _ ↔ _
  simp [(basis_sets F).prod_self.tendsto_iffₓ B.nhds_zero_has_basis, @forall_swap (_ ∈ _) G]
#align add_group_filter_basis.cauchy_iff AddGroupFilterBasis.cauchy_iff
-/

end AddGroupFilterBasis

