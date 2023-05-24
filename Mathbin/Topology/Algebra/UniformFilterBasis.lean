/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot

! This file was ported from Lean 3 source module topology.algebra.uniform_filter_basis
! leanprover-community/mathlib commit 19cb3751e5e9b3d97adb51023949c50c13b5fdfd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.FilterBasis
import Mathbin.Topology.Algebra.UniformGroup

/-!
# Uniform properties of neighborhood bases in topological algebra

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This files contains properties of filter bases on algebraic structures that also require the theory
of uniform spaces.

The only result so far is a characterization of Cauchy filters in topological groups.

-/


open uniformity Filter

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

/- warning: add_group_filter_basis.cauchy_iff -> AddGroupFilterBasis.cauchy_iff is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : AddCommGroup.{u1} G] (B : AddGroupFilterBasis.{u1} G (AddCommGroup.toAddGroup.{u1} G _inst_1)) {F : Filter.{u1} G}, Iff (Cauchy.{u1} G (AddGroupFilterBasis.uniformSpace.{u1} G _inst_1 B) F) (And (Filter.NeBot.{u1} G F) (forall (U : Set.{u1} G), (Membership.Mem.{u1, u1} (Set.{u1} G) (AddGroupFilterBasis.{u1} G (AddCommGroup.toAddGroup.{u1} G _inst_1)) (AddGroupFilterBasis.hasMem.{u1} G (AddCommGroup.toAddGroup.{u1} G _inst_1)) U B) -> (Exists.{succ u1} (Set.{u1} G) (fun (M : Set.{u1} G) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (Filter.hasMem.{u1} G) M F) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (Filter.hasMem.{u1} G) M F) => forall (x : G), (Membership.Mem.{u1, u1} G (Set.{u1} G) (Set.hasMem.{u1} G) x M) -> (forall (y : G), (Membership.Mem.{u1, u1} G (Set.{u1} G) (Set.hasMem.{u1} G) y M) -> (Membership.Mem.{u1, u1} G (Set.{u1} G) (Set.hasMem.{u1} G) (HSub.hSub.{u1, u1, u1} G G G (instHSub.{u1} G (SubNegMonoid.toHasSub.{u1} G (AddGroup.toSubNegMonoid.{u1} G (AddCommGroup.toAddGroup.{u1} G _inst_1)))) y x) U)))))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : AddCommGroup.{u1} G] (B : AddGroupFilterBasis.{u1} G (AddCommGroup.toAddGroup.{u1} G _inst_1)) {F : Filter.{u1} G}, Iff (Cauchy.{u1} G (AddGroupFilterBasis.uniformSpace.{u1} G _inst_1 B) F) (And (Filter.NeBot.{u1} G F) (forall (U : Set.{u1} G), (Membership.mem.{u1, u1} (Set.{u1} G) (AddGroupFilterBasis.{u1} G (AddCommGroup.toAddGroup.{u1} G _inst_1)) (AddGroupFilterBasis.instMembershipSetAddGroupFilterBasis.{u1} G (AddCommGroup.toAddGroup.{u1} G _inst_1)) U B) -> (Exists.{succ u1} (Set.{u1} G) (fun (M : Set.{u1} G) => And (Membership.mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (instMembershipSetFilter.{u1} G) M F) (forall (x : G), (Membership.mem.{u1, u1} G (Set.{u1} G) (Set.instMembershipSet.{u1} G) x M) -> (forall (y : G), (Membership.mem.{u1, u1} G (Set.{u1} G) (Set.instMembershipSet.{u1} G) y M) -> (Membership.mem.{u1, u1} G (Set.{u1} G) (Set.instMembershipSet.{u1} G) (HSub.hSub.{u1, u1, u1} G G G (instHSub.{u1} G (SubNegMonoid.toSub.{u1} G (AddGroup.toSubNegMonoid.{u1} G (AddCommGroup.toAddGroup.{u1} G _inst_1)))) y x) U)))))))
Case conversion may be inaccurate. Consider using '#align add_group_filter_basis.cauchy_iff AddGroupFilterBasis.cauchy_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » M) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » M) -/
theorem cauchy_iff {F : Filter G} :
    @Cauchy G B.UniformSpace F ↔
      F.ne_bot ∧ ∀ U ∈ B, ∃ M ∈ F, ∀ (x) (_ : x ∈ M) (y) (_ : y ∈ M), y - x ∈ U :=
  by
  letI := B.uniform_space
  haveI := B.uniform_add_group
  suffices F ×ᶠ F ≤ 𝓤 G ↔ ∀ U ∈ B, ∃ M ∈ F, ∀ (x) (_ : x ∈ M) (y) (_ : y ∈ M), y - x ∈ U by
    constructor <;> rintro ⟨h', h⟩ <;> refine' ⟨h', _⟩ <;> [rwa [← this];rwa [this]]
  rw [uniformity_eq_comap_nhds_zero G, ← map_le_iff_le_comap]
  change tendsto _ _ _ ↔ _
  simp [(basis_sets F).prod_self.tendsto_iffₓ B.nhds_zero_has_basis, @forall_swap (_ ∈ _) G]
#align add_group_filter_basis.cauchy_iff AddGroupFilterBasis.cauchy_iff

end AddGroupFilterBasis

