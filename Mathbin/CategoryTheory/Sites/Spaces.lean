/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.sites.spaces
! leanprover-community/mathlib commit b6fa3beb29f035598cf0434d919694c5e98091eb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Sites.Grothendieck
import Mathbin.CategoryTheory.Sites.Pretopology
import Mathbin.CategoryTheory.Limits.Lattice
import Mathbin.Topology.Sets.Opens

/-!
# Grothendieck topology on a topological space

Define the Grothendieck topology and the pretopology associated to a topological space, and show
that the pretopology induces the topology.

The covering (pre)sieves on `X` are those for which the union of domains contains `X`.

## Tags

site, Grothendieck topology, space

## References

* [nLab, *Grothendieck topology*](https://ncatlab.org/nlab/show/Grothendieck+topology)
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]

## Implementation notes

We define the two separately, rather than defining the Grothendieck topology as that generated
by the pretopology for the purpose of having nice definitional properties for the sieves.
-/


universe u

namespace Opens

variable (T : Type u) [TopologicalSpace T]

open CategoryTheory TopologicalSpace CategoryTheory.Limits

/- warning: opens.grothendieck_topology -> Opens.grothendieckTopology is a dubious translation:
lean 3 declaration is
  forall (T : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} T], CategoryTheory.GrothendieckTopology.{u1, u1} (TopologicalSpace.Opens.{u1} T _inst_1) (Preorder.smallCategory.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (SetLike.partialOrder.{u1, u1} (TopologicalSpace.Opens.{u1} T _inst_1) T (TopologicalSpace.Opens.setLike.{u1} T _inst_1))))
but is expected to have type
  forall (T : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} T], CategoryTheory.GrothendieckTopology.{u1, u1} (TopologicalSpace.Opens.{u1} T _inst_1) (Preorder.smallCategory.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} T _inst_1)))))
Case conversion may be inaccurate. Consider using '#align opens.grothendieck_topology Opens.grothendieckTopologyₓ'. -/
/-- The Grothendieck topology associated to a topological space. -/
def grothendieckTopology : GrothendieckTopology (Opens T)
    where
  sieves X S := ∀ x ∈ X, ∃ (U : _)(f : U ⟶ X), S f ∧ x ∈ U
  top_mem' X x hx := ⟨_, 𝟙 _, trivial, hx⟩
  pullback_stable' X Y S f hf y hy :=
    by
    rcases hf y (f.le hy) with ⟨U, g, hg, hU⟩
    refine' ⟨U ⊓ Y, hom_of_le inf_le_right, _, hU, hy⟩
    apply S.downward_closed hg (hom_of_le inf_le_left)
  transitive' X S hS R hR x hx :=
    by
    rcases hS x hx with ⟨U, f, hf, hU⟩
    rcases hR hf _ hU with ⟨V, g, hg, hV⟩
    exact ⟨_, g ≫ f, hg, hV⟩
#align opens.grothendieck_topology Opens.grothendieckTopology

/- warning: opens.pretopology -> Opens.pretopology is a dubious translation:
lean 3 declaration is
  forall (T : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} T], CategoryTheory.Pretopology.{u1, u1} (TopologicalSpace.Opens.{u1} T _inst_1) (Preorder.smallCategory.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (SetLike.partialOrder.{u1, u1} (TopologicalSpace.Opens.{u1} T _inst_1) T (TopologicalSpace.Opens.setLike.{u1} T _inst_1)))) (Opens.pretopology._proof_1.{u1} T _inst_1)
but is expected to have type
  forall (T : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} T], CategoryTheory.Pretopology.{u1, u1} (TopologicalSpace.Opens.{u1} T _inst_1) (Preorder.smallCategory.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} T _inst_1))))) (CategoryTheory.Limits.hasPullbacks_of_hasWidePullbacks.{u1, u1, u1} (TopologicalSpace.Opens.{u1} T _inst_1) (Preorder.smallCategory.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} T _inst_1))))) (fun (J : Type.{u1}) => CategoryTheory.Limits.hasLimitsOfShapeOfHasLimits.{u1, u1, u1, u1} (TopologicalSpace.Opens.{u1} T _inst_1) (Preorder.smallCategory.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} T _inst_1))))) (CategoryTheory.Limits.WidePullbackShape.{u1} J) (CategoryTheory.Limits.WidePullbackShape.category.{u1} J) (CategoryTheory.Limits.CompleteLattice.hasLimits_of_completeLattice.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} T _inst_1))))
Case conversion may be inaccurate. Consider using '#align opens.pretopology Opens.pretopologyₓ'. -/
/-- The Grothendieck pretopology associated to a topological space. -/
def pretopology : Pretopology (Opens T)
    where
  coverings X R := ∀ x ∈ X, ∃ (U : _)(f : U ⟶ X), R f ∧ x ∈ U
  has_isos X Y f i x hx := ⟨_, _, presieve.singleton_self _, (inv f).le hx⟩
  pullbacks X Y f S hS x hx :=
    by
    rcases hS _ (f.le hx) with ⟨U, g, hg, hU⟩
    refine' ⟨_, _, presieve.pullback_arrows.mk _ _ hg, _⟩
    have : U ⊓ Y ≤ pullback g f
    refine' le_of_hom (pullback.lift (hom_of_le inf_le_left) (hom_of_le inf_le_right) rfl)
    apply this ⟨hU, hx⟩
  Transitive X S Ti hS hTi x hx :=
    by
    rcases hS x hx with ⟨U, f, hf, hU⟩
    rcases hTi f hf x hU with ⟨V, g, hg, hV⟩
    exact ⟨_, _, ⟨_, g, f, hf, hg, rfl⟩, hV⟩
#align opens.pretopology Opens.pretopology

/- warning: opens.pretopology_of_grothendieck -> Opens.pretopology_ofGrothendieck is a dubious translation:
lean 3 declaration is
  forall (T : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} T], Eq.{succ u1} (CategoryTheory.Pretopology.{u1, u1} (TopologicalSpace.Opens.{u1} T _inst_1) (Preorder.smallCategory.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (SetLike.partialOrder.{u1, u1} (TopologicalSpace.Opens.{u1} T _inst_1) T (TopologicalSpace.Opens.setLike.{u1} T _inst_1)))) (Opens.pretopology._proof_1.{u1} T _inst_1)) (CategoryTheory.Pretopology.ofGrothendieck.{u1, u1} (TopologicalSpace.Opens.{u1} T _inst_1) (Preorder.smallCategory.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (SetLike.partialOrder.{u1, u1} (TopologicalSpace.Opens.{u1} T _inst_1) T (TopologicalSpace.Opens.setLike.{u1} T _inst_1)))) (Opens.pretopology._proof_1.{u1} T _inst_1) (Opens.grothendieckTopology.{u1} T _inst_1)) (Opens.pretopology.{u1} T _inst_1)
but is expected to have type
  forall (T : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} T], Eq.{succ u1} (CategoryTheory.Pretopology.{u1, u1} (TopologicalSpace.Opens.{u1} T _inst_1) (Preorder.smallCategory.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} T _inst_1))))) (CategoryTheory.Limits.hasPullbacks_of_hasWidePullbacks.{u1, u1, u1} (TopologicalSpace.Opens.{u1} T _inst_1) (Preorder.smallCategory.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} T _inst_1))))) (fun (J : Type.{u1}) => CategoryTheory.Limits.hasLimitsOfShapeOfHasLimits.{u1, u1, u1, u1} (TopologicalSpace.Opens.{u1} T _inst_1) (Preorder.smallCategory.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} T _inst_1))))) (CategoryTheory.Limits.WidePullbackShape.{u1} J) (CategoryTheory.Limits.WidePullbackShape.category.{u1} J) (CategoryTheory.Limits.CompleteLattice.hasLimits_of_completeLattice.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} T _inst_1))))) (CategoryTheory.Pretopology.ofGrothendieck.{u1, u1} (TopologicalSpace.Opens.{u1} T _inst_1) (Preorder.smallCategory.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} T _inst_1))))) (CategoryTheory.Limits.hasPullbacks_of_hasWidePullbacks.{u1, u1, u1} (TopologicalSpace.Opens.{u1} T _inst_1) (Preorder.smallCategory.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} T _inst_1))))) (fun (J : Type.{u1}) => CategoryTheory.Limits.hasLimitsOfShapeOfHasLimits.{u1, u1, u1, u1} (TopologicalSpace.Opens.{u1} T _inst_1) (Preorder.smallCategory.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} T _inst_1))))) (CategoryTheory.Limits.WidePullbackShape.{u1} J) (CategoryTheory.Limits.WidePullbackShape.category.{u1} J) (CategoryTheory.Limits.CompleteLattice.hasLimits_of_completeLattice.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} T _inst_1)))) (Opens.grothendieckTopology.{u1} T _inst_1)) (Opens.pretopology.{u1} T _inst_1)
Case conversion may be inaccurate. Consider using '#align opens.pretopology_of_grothendieck Opens.pretopology_ofGrothendieckₓ'. -/
/-- The pretopology associated to a space is the largest pretopology that
    generates the Grothendieck topology associated to the space. -/
@[simp]
theorem pretopology_ofGrothendieck :
    Pretopology.ofGrothendieck _ (Opens.grothendieckTopology T) = Opens.pretopology T :=
  by
  apply le_antisymm
  · intro X R hR x hx
    rcases hR x hx with ⟨U, f, ⟨V, g₁, g₂, hg₂, _⟩, hU⟩
    exact ⟨V, g₂, hg₂, g₁.le hU⟩
  · intro X R hR x hx
    rcases hR x hx with ⟨U, f, hf, hU⟩
    exact ⟨U, f, sieve.le_generate R U hf, hU⟩
#align opens.pretopology_of_grothendieck Opens.pretopology_ofGrothendieck

/- warning: opens.pretopology_to_grothendieck -> Opens.pretopology_toGrothendieck is a dubious translation:
lean 3 declaration is
  forall (T : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} T], Eq.{succ u1} (CategoryTheory.GrothendieckTopology.{u1, u1} (TopologicalSpace.Opens.{u1} T _inst_1) (Preorder.smallCategory.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (SetLike.partialOrder.{u1, u1} (TopologicalSpace.Opens.{u1} T _inst_1) T (TopologicalSpace.Opens.setLike.{u1} T _inst_1))))) (CategoryTheory.Pretopology.toGrothendieck.{u1, u1} (TopologicalSpace.Opens.{u1} T _inst_1) (Preorder.smallCategory.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (SetLike.partialOrder.{u1, u1} (TopologicalSpace.Opens.{u1} T _inst_1) T (TopologicalSpace.Opens.setLike.{u1} T _inst_1)))) (Opens.pretopology._proof_1.{u1} T _inst_1) (Opens.pretopology.{u1} T _inst_1)) (Opens.grothendieckTopology.{u1} T _inst_1)
but is expected to have type
  forall (T : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} T], Eq.{succ u1} (CategoryTheory.GrothendieckTopology.{u1, u1} (TopologicalSpace.Opens.{u1} T _inst_1) (Preorder.smallCategory.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} T _inst_1)))))) (CategoryTheory.Pretopology.toGrothendieck.{u1, u1} (TopologicalSpace.Opens.{u1} T _inst_1) (Preorder.smallCategory.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} T _inst_1))))) (CategoryTheory.Limits.hasPullbacks_of_hasWidePullbacks.{u1, u1, u1} (TopologicalSpace.Opens.{u1} T _inst_1) (Preorder.smallCategory.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} T _inst_1))))) (fun (J : Type.{u1}) => CategoryTheory.Limits.hasLimitsOfShapeOfHasLimits.{u1, u1, u1, u1} (TopologicalSpace.Opens.{u1} T _inst_1) (Preorder.smallCategory.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} T _inst_1))))) (CategoryTheory.Limits.WidePullbackShape.{u1} J) (CategoryTheory.Limits.WidePullbackShape.category.{u1} J) (CategoryTheory.Limits.CompleteLattice.hasLimits_of_completeLattice.{u1} (TopologicalSpace.Opens.{u1} T _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} T _inst_1)))) (Opens.pretopology.{u1} T _inst_1)) (Opens.grothendieckTopology.{u1} T _inst_1)
Case conversion may be inaccurate. Consider using '#align opens.pretopology_to_grothendieck Opens.pretopology_toGrothendieckₓ'. -/
/-- The pretopology associated to a space induces the Grothendieck topology associated to the space.
-/
@[simp]
theorem pretopology_toGrothendieck :
    Pretopology.toGrothendieck _ (Opens.pretopology T) = Opens.grothendieckTopology T :=
  by
  rw [← pretopology_of_grothendieck]
  apply (pretopology.gi (opens T)).l_u_eq
#align opens.pretopology_to_grothendieck Opens.pretopology_toGrothendieck

end Opens

