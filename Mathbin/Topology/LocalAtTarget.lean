/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module topology.local_at_target
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Sets.Opens

/-!
# Properties of maps that are local at the target.

We show that the following properties of continuous maps are local at the target :
- `inducing`
- `embedding`
- `open_embedding`
- `closed_embedding`

-/


open TopologicalSpace Set Filter

open Topology Filter

variable {α β : Type _} [TopologicalSpace α] [TopologicalSpace β] {f : α → β}

variable {s : Set β} {ι : Type _} {U : ι → Opens β} (hU : supᵢ U = ⊤)

#print Set.restrictPreimage_inducing /-
theorem Set.restrictPreimage_inducing (s : Set β) (h : Inducing f) :
    Inducing (s.restrictPreimage f) :=
  by
  simp_rw [inducing_coe.inducing_iff, inducing_iff_nhds, restrict_preimage, maps_to.coe_restrict,
    restrict_eq, ← @Filter.comap_comap _ _ _ _ coe f] at h⊢
  intro a
  rw [← h, ← inducing_coe.nhds_eq_comap]
#align set.restrict_preimage_inducing Set.restrictPreimage_inducing
-/

alias Set.restrictPreimage_inducing ← Inducing.restrictPreimage
#align inducing.restrict_preimage Inducing.restrictPreimage

#print Set.restrictPreimage_embedding /-
theorem Set.restrictPreimage_embedding (s : Set β) (h : Embedding f) :
    Embedding (s.restrictPreimage f) :=
  ⟨h.1.restrictPreimage s, h.2.restrictPreimage s⟩
#align set.restrict_preimage_embedding Set.restrictPreimage_embedding
-/

alias Set.restrictPreimage_embedding ← Embedding.restrictPreimage
#align embedding.restrict_preimage Embedding.restrictPreimage

#print Set.restrictPreimage_openEmbedding /-
theorem Set.restrictPreimage_openEmbedding (s : Set β) (h : OpenEmbedding f) :
    OpenEmbedding (s.restrictPreimage f) :=
  ⟨h.1.restrictPreimage s,
    (s.range_restrictPreimage f).symm ▸ continuous_subtype_val.isOpen_preimage _ h.2⟩
#align set.restrict_preimage_open_embedding Set.restrictPreimage_openEmbedding
-/

alias Set.restrictPreimage_openEmbedding ← OpenEmbedding.restrictPreimage
#align open_embedding.restrict_preimage OpenEmbedding.restrictPreimage

#print Set.restrictPreimage_closedEmbedding /-
theorem Set.restrictPreimage_closedEmbedding (s : Set β) (h : ClosedEmbedding f) :
    ClosedEmbedding (s.restrictPreimage f) :=
  ⟨h.1.restrictPreimage s,
    (s.range_restrictPreimage f).symm ▸ inducing_subtype_val.isClosed_preimage _ h.2⟩
#align set.restrict_preimage_closed_embedding Set.restrictPreimage_closedEmbedding
-/

alias Set.restrictPreimage_closedEmbedding ← ClosedEmbedding.restrictPreimage
#align closed_embedding.restrict_preimage ClosedEmbedding.restrictPreimage

#print Set.restrictPreimage_isClosedMap /-
theorem Set.restrictPreimage_isClosedMap (s : Set β) (H : IsClosedMap f) :
    IsClosedMap (s.restrictPreimage f) :=
  by
  rintro t ⟨u, hu, e⟩
  refine' ⟨⟨_, (H _ (IsOpen.isClosed_compl hu)).1, _⟩⟩
  rw [← (congr_arg HasCompl.compl e).trans (compl_compl t)]
  simp only [Set.preimage_compl, compl_inj_iff]
  ext ⟨x, hx⟩
  suffices (∃ y, y ∉ u ∧ f y = x) ↔ ∃ y, f y ∈ s ∧ y ∉ u ∧ f y = x by
    simpa [Set.restrictPreimage, ← Subtype.coe_inj]
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, c.symm ▸ hx, b, c⟩, fun ⟨a, _, b, c⟩ => ⟨a, b, c⟩⟩
#align set.restrict_preimage_is_closed_map Set.restrictPreimage_isClosedMap
-/

include hU

/- warning: is_open_iff_inter_of_supr_eq_top -> isOpen_iff_inter_of_supᵢ_eq_top is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} β] {ι : Type.{u2}} {U : ι -> (TopologicalSpace.Opens.{u1} β _inst_2)}, (Eq.{succ u1} (TopologicalSpace.Opens.{u1} β _inst_2) (supᵢ.{u1, succ u2} (TopologicalSpace.Opens.{u1} β _inst_2) (ConditionallyCompleteLattice.toHasSup.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u1} β _inst_2))) ι U) (Top.top.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (CompleteLattice.toHasTop.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u1} β _inst_2)))) -> (forall (s : Set.{u1} β), Iff (IsOpen.{u1} β _inst_2 s) (forall (i : ι), IsOpen.{u1} β _inst_2 (Inter.inter.{u1} (Set.{u1} β) (Set.hasInter.{u1} β) s ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Opens.{u1} β _inst_2) (Set.{u1} β) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} β _inst_2) (Set.{u1} β) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} β _inst_2) (Set.{u1} β) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Opens.{u1} β _inst_2) β (TopologicalSpace.Opens.setLike.{u1} β _inst_2)))) (U i)))))
but is expected to have type
  forall {β : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} β] {ι : Type.{u2}} {U : ι -> (TopologicalSpace.Opens.{u1} β _inst_2)}, (Eq.{succ u1} (TopologicalSpace.Opens.{u1} β _inst_2) (supᵢ.{u1, succ u2} (TopologicalSpace.Opens.{u1} β _inst_2) (ConditionallyCompleteLattice.toSupSet.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2))) ι U) (Top.top.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (CompleteLattice.toTop.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2)))) -> (forall (s : Set.{u1} β), Iff (IsOpen.{u1} β _inst_2 s) (forall (i : ι), IsOpen.{u1} β _inst_2 (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) s (SetLike.coe.{u1, u1} (TopologicalSpace.Opens.{u1} β _inst_2) β (TopologicalSpace.Opens.instSetLikeOpens.{u1} β _inst_2) (U i)))))
Case conversion may be inaccurate. Consider using '#align is_open_iff_inter_of_supr_eq_top isOpen_iff_inter_of_supᵢ_eq_topₓ'. -/
theorem isOpen_iff_inter_of_supᵢ_eq_top (s : Set β) : IsOpen s ↔ ∀ i, IsOpen (s ∩ U i) :=
  by
  constructor
  · exact fun H i => H.inter (U i).2
  · intro H
    have : (⋃ i, (U i : Set β)) = Set.univ :=
      by
      convert congr_arg coe hU
      simp
    rw [← s.inter_univ, ← this, Set.inter_unionᵢ]
    exact isOpen_unionᵢ H
#align is_open_iff_inter_of_supr_eq_top isOpen_iff_inter_of_supᵢ_eq_top

/- warning: is_open_iff_coe_preimage_of_supr_eq_top -> isOpen_iff_coe_preimage_of_supᵢ_eq_top is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} β] {ι : Type.{u2}} {U : ι -> (TopologicalSpace.Opens.{u1} β _inst_2)}, (Eq.{succ u1} (TopologicalSpace.Opens.{u1} β _inst_2) (supᵢ.{u1, succ u2} (TopologicalSpace.Opens.{u1} β _inst_2) (ConditionallyCompleteLattice.toHasSup.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u1} β _inst_2))) ι U) (Top.top.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (CompleteLattice.toHasTop.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u1} β _inst_2)))) -> (forall (s : Set.{u1} β), Iff (IsOpen.{u1} β _inst_2 s) (forall (i : ι), IsOpen.{u1} (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} β _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} β _inst_2) β (TopologicalSpace.Opens.setLike.{u1} β _inst_2)) (U i)) (Subtype.topologicalSpace.{u1} β (fun (x : β) => Membership.Mem.{u1, u1} β (TopologicalSpace.Opens.{u1} β _inst_2) (SetLike.hasMem.{u1, u1} (TopologicalSpace.Opens.{u1} β _inst_2) β (TopologicalSpace.Opens.setLike.{u1} β _inst_2)) x (U i)) _inst_2) (Set.preimage.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} β _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} β _inst_2) β (TopologicalSpace.Opens.setLike.{u1} β _inst_2)) (U i)) β ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} β _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} β _inst_2) β (TopologicalSpace.Opens.setLike.{u1} β _inst_2)) (U i)) β (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} β _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} β _inst_2) β (TopologicalSpace.Opens.setLike.{u1} β _inst_2)) (U i)) β (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} β _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} β _inst_2) β (TopologicalSpace.Opens.setLike.{u1} β _inst_2)) (U i)) β (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} β _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} β _inst_2) β (TopologicalSpace.Opens.setLike.{u1} β _inst_2)) (U i)) β (coeSubtype.{succ u1} β (fun (x : β) => Membership.Mem.{u1, u1} β (TopologicalSpace.Opens.{u1} β _inst_2) (SetLike.hasMem.{u1, u1} (TopologicalSpace.Opens.{u1} β _inst_2) β (TopologicalSpace.Opens.setLike.{u1} β _inst_2)) x (U i))))))) s)))
but is expected to have type
  forall {β : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} β] {ι : Type.{u2}} {U : ι -> (TopologicalSpace.Opens.{u1} β _inst_2)}, (Eq.{succ u1} (TopologicalSpace.Opens.{u1} β _inst_2) (supᵢ.{u1, succ u2} (TopologicalSpace.Opens.{u1} β _inst_2) (ConditionallyCompleteLattice.toSupSet.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2))) ι U) (Top.top.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (CompleteLattice.toTop.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2)))) -> (forall (s : Set.{u1} β), Iff (IsOpen.{u1} β _inst_2 s) (forall (i : ι), IsOpen.{u1} (Subtype.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (TopologicalSpace.Opens.{u1} β _inst_2) (SetLike.instMembership.{u1, u1} (TopologicalSpace.Opens.{u1} β _inst_2) β (TopologicalSpace.Opens.instSetLikeOpens.{u1} β _inst_2)) x (U i))) (instTopologicalSpaceSubtype.{u1} β (fun (x : β) => Membership.mem.{u1, u1} β (TopologicalSpace.Opens.{u1} β _inst_2) (SetLike.instMembership.{u1, u1} (TopologicalSpace.Opens.{u1} β _inst_2) β (TopologicalSpace.Opens.instSetLikeOpens.{u1} β _inst_2)) x (U i)) _inst_2) (Set.preimage.{u1, u1} (Subtype.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (TopologicalSpace.Opens.{u1} β _inst_2) (SetLike.instMembership.{u1, u1} (TopologicalSpace.Opens.{u1} β _inst_2) β (TopologicalSpace.Opens.instSetLikeOpens.{u1} β _inst_2)) x (U i))) β (Subtype.val.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (SetLike.coe.{u1, u1} (TopologicalSpace.Opens.{u1} β _inst_2) β (TopologicalSpace.Opens.instSetLikeOpens.{u1} β _inst_2) (U i)))) s)))
Case conversion may be inaccurate. Consider using '#align is_open_iff_coe_preimage_of_supr_eq_top isOpen_iff_coe_preimage_of_supᵢ_eq_topₓ'. -/
theorem isOpen_iff_coe_preimage_of_supᵢ_eq_top (s : Set β) :
    IsOpen s ↔ ∀ i, IsOpen (coe ⁻¹' s : Set (U i)) :=
  by
  simp_rw [(U _).2.openEmbedding_subtype_val.open_iff_image_open, Set.image_preimage_eq_inter_range,
    Subtype.range_coe]
  apply isOpen_iff_inter_of_supᵢ_eq_top
  assumption
#align is_open_iff_coe_preimage_of_supr_eq_top isOpen_iff_coe_preimage_of_supᵢ_eq_top

/- warning: is_closed_iff_coe_preimage_of_supr_eq_top -> isClosed_iff_coe_preimage_of_supᵢ_eq_top is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} β] {ι : Type.{u2}} {U : ι -> (TopologicalSpace.Opens.{u1} β _inst_2)}, (Eq.{succ u1} (TopologicalSpace.Opens.{u1} β _inst_2) (supᵢ.{u1, succ u2} (TopologicalSpace.Opens.{u1} β _inst_2) (ConditionallyCompleteLattice.toHasSup.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u1} β _inst_2))) ι U) (Top.top.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (CompleteLattice.toHasTop.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u1} β _inst_2)))) -> (forall (s : Set.{u1} β), Iff (IsClosed.{u1} β _inst_2 s) (forall (i : ι), IsClosed.{u1} (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} β _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} β _inst_2) β (TopologicalSpace.Opens.setLike.{u1} β _inst_2)) (U i)) (Subtype.topologicalSpace.{u1} β (fun (x : β) => Membership.Mem.{u1, u1} β (TopologicalSpace.Opens.{u1} β _inst_2) (SetLike.hasMem.{u1, u1} (TopologicalSpace.Opens.{u1} β _inst_2) β (TopologicalSpace.Opens.setLike.{u1} β _inst_2)) x (U i)) _inst_2) (Set.preimage.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} β _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} β _inst_2) β (TopologicalSpace.Opens.setLike.{u1} β _inst_2)) (U i)) β ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} β _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} β _inst_2) β (TopologicalSpace.Opens.setLike.{u1} β _inst_2)) (U i)) β (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} β _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} β _inst_2) β (TopologicalSpace.Opens.setLike.{u1} β _inst_2)) (U i)) β (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} β _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} β _inst_2) β (TopologicalSpace.Opens.setLike.{u1} β _inst_2)) (U i)) β (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} β _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} β _inst_2) β (TopologicalSpace.Opens.setLike.{u1} β _inst_2)) (U i)) β (coeSubtype.{succ u1} β (fun (x : β) => Membership.Mem.{u1, u1} β (TopologicalSpace.Opens.{u1} β _inst_2) (SetLike.hasMem.{u1, u1} (TopologicalSpace.Opens.{u1} β _inst_2) β (TopologicalSpace.Opens.setLike.{u1} β _inst_2)) x (U i))))))) s)))
but is expected to have type
  forall {β : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} β] {ι : Type.{u2}} {U : ι -> (TopologicalSpace.Opens.{u1} β _inst_2)}, (Eq.{succ u1} (TopologicalSpace.Opens.{u1} β _inst_2) (supᵢ.{u1, succ u2} (TopologicalSpace.Opens.{u1} β _inst_2) (ConditionallyCompleteLattice.toSupSet.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2))) ι U) (Top.top.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (CompleteLattice.toTop.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2)))) -> (forall (s : Set.{u1} β), Iff (IsClosed.{u1} β _inst_2 s) (forall (i : ι), IsClosed.{u1} (Subtype.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (TopologicalSpace.Opens.{u1} β _inst_2) (SetLike.instMembership.{u1, u1} (TopologicalSpace.Opens.{u1} β _inst_2) β (TopologicalSpace.Opens.instSetLikeOpens.{u1} β _inst_2)) x (U i))) (instTopologicalSpaceSubtype.{u1} β (fun (x : β) => Membership.mem.{u1, u1} β (TopologicalSpace.Opens.{u1} β _inst_2) (SetLike.instMembership.{u1, u1} (TopologicalSpace.Opens.{u1} β _inst_2) β (TopologicalSpace.Opens.instSetLikeOpens.{u1} β _inst_2)) x (U i)) _inst_2) (Set.preimage.{u1, u1} (Subtype.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (TopologicalSpace.Opens.{u1} β _inst_2) (SetLike.instMembership.{u1, u1} (TopologicalSpace.Opens.{u1} β _inst_2) β (TopologicalSpace.Opens.instSetLikeOpens.{u1} β _inst_2)) x (U i))) β (Subtype.val.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (SetLike.coe.{u1, u1} (TopologicalSpace.Opens.{u1} β _inst_2) β (TopologicalSpace.Opens.instSetLikeOpens.{u1} β _inst_2) (U i)))) s)))
Case conversion may be inaccurate. Consider using '#align is_closed_iff_coe_preimage_of_supr_eq_top isClosed_iff_coe_preimage_of_supᵢ_eq_topₓ'. -/
theorem isClosed_iff_coe_preimage_of_supᵢ_eq_top (s : Set β) :
    IsClosed s ↔ ∀ i, IsClosed (coe ⁻¹' s : Set (U i)) := by
  simpa using isOpen_iff_coe_preimage_of_supᵢ_eq_top hU (sᶜ)
#align is_closed_iff_coe_preimage_of_supr_eq_top isClosed_iff_coe_preimage_of_supᵢ_eq_top

/- warning: is_closed_map_iff_is_closed_map_of_supr_eq_top -> isClosedMap_iff_isClosedMap_of_supᵢ_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {ι : Type.{u3}} {U : ι -> (TopologicalSpace.Opens.{u2} β _inst_2)}, (Eq.{succ u2} (TopologicalSpace.Opens.{u2} β _inst_2) (supᵢ.{u2, succ u3} (TopologicalSpace.Opens.{u2} β _inst_2) (ConditionallyCompleteLattice.toHasSup.{u2} (TopologicalSpace.Opens.{u2} β _inst_2) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.Opens.{u2} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u2} β _inst_2))) ι U) (Top.top.{u2} (TopologicalSpace.Opens.{u2} β _inst_2) (CompleteLattice.toHasTop.{u2} (TopologicalSpace.Opens.{u2} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u2} β _inst_2)))) -> (Iff (IsClosedMap.{u1, u2} α β _inst_1 _inst_2 f) (forall (i : ι), IsClosedMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.preimage.{u1, u2} α β f (TopologicalSpace.Opens.carrier.{u2} β _inst_2 (U i)))) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (TopologicalSpace.Opens.carrier.{u2} β _inst_2 (U i))) (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.preimage.{u1, u2} α β f (TopologicalSpace.Opens.carrier.{u2} β _inst_2 (U i)))) _inst_1) (Subtype.topologicalSpace.{u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (TopologicalSpace.Opens.carrier.{u2} β _inst_2 (U i))) _inst_2) (Set.restrictPreimage.{u1, u2} α β (TopologicalSpace.Opens.carrier.{u2} β _inst_2 (U i)) f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {ι : Type.{u3}} {U : ι -> (TopologicalSpace.Opens.{u1} β _inst_2)}, (Eq.{succ u1} (TopologicalSpace.Opens.{u1} β _inst_2) (supᵢ.{u1, succ u3} (TopologicalSpace.Opens.{u1} β _inst_2) (ConditionallyCompleteLattice.toSupSet.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2))) ι U) (Top.top.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (CompleteLattice.toTop.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2)))) -> (Iff (IsClosedMap.{u2, u1} α β _inst_1 _inst_2 f) (forall (i : ι), IsClosedMap.{u2, u1} (Set.Elem.{u2} α (Set.preimage.{u2, u1} α β f (TopologicalSpace.Opens.carrier.{u1} β _inst_2 (U i)))) (Set.Elem.{u1} β (TopologicalSpace.Opens.carrier.{u1} β _inst_2 (U i))) (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Set.preimage.{u2, u1} α β f (TopologicalSpace.Opens.carrier.{u1} β _inst_2 (U i)))) _inst_1) (instTopologicalSpaceSubtype.{u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (TopologicalSpace.Opens.carrier.{u1} β _inst_2 (U i))) _inst_2) (Set.restrictPreimage.{u2, u1} α β (TopologicalSpace.Opens.carrier.{u1} β _inst_2 (U i)) f)))
Case conversion may be inaccurate. Consider using '#align is_closed_map_iff_is_closed_map_of_supr_eq_top isClosedMap_iff_isClosedMap_of_supᵢ_eq_topₓ'. -/
theorem isClosedMap_iff_isClosedMap_of_supᵢ_eq_top :
    IsClosedMap f ↔ ∀ i, IsClosedMap ((U i).1.restrictPreimage f) :=
  by
  refine' ⟨fun h i => Set.restrictPreimage_isClosedMap _ h, _⟩
  rintro H s hs
  rw [isClosed_iff_coe_preimage_of_supᵢ_eq_top hU]
  intro i
  convert H i _ ⟨⟨_, hs.1, eq_compl_comm.mpr rfl⟩⟩
  ext ⟨x, hx⟩
  suffices (∃ y, y ∈ s ∧ f y = x) ↔ ∃ y, f y ∈ U i ∧ y ∈ s ∧ f y = x by
    simpa [Set.restrictPreimage, ← Subtype.coe_inj]
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, c.symm ▸ hx, b, c⟩, fun ⟨a, _, b, c⟩ => ⟨a, b, c⟩⟩
#align is_closed_map_iff_is_closed_map_of_supr_eq_top isClosedMap_iff_isClosedMap_of_supᵢ_eq_top

/- warning: inducing_iff_inducing_of_supr_eq_top -> inducing_iff_inducing_of_supᵢ_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {ι : Type.{u3}} {U : ι -> (TopologicalSpace.Opens.{u2} β _inst_2)}, (Eq.{succ u2} (TopologicalSpace.Opens.{u2} β _inst_2) (supᵢ.{u2, succ u3} (TopologicalSpace.Opens.{u2} β _inst_2) (ConditionallyCompleteLattice.toHasSup.{u2} (TopologicalSpace.Opens.{u2} β _inst_2) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.Opens.{u2} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u2} β _inst_2))) ι U) (Top.top.{u2} (TopologicalSpace.Opens.{u2} β _inst_2) (CompleteLattice.toHasTop.{u2} (TopologicalSpace.Opens.{u2} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u2} β _inst_2)))) -> (Continuous.{u1, u2} α β _inst_1 _inst_2 f) -> (Iff (Inducing.{u1, u2} α β _inst_1 _inst_2 f) (forall (i : ι), Inducing.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.preimage.{u1, u2} α β f (TopologicalSpace.Opens.carrier.{u2} β _inst_2 (U i)))) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (TopologicalSpace.Opens.carrier.{u2} β _inst_2 (U i))) (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.preimage.{u1, u2} α β f (TopologicalSpace.Opens.carrier.{u2} β _inst_2 (U i)))) _inst_1) (Subtype.topologicalSpace.{u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (TopologicalSpace.Opens.carrier.{u2} β _inst_2 (U i))) _inst_2) (Set.restrictPreimage.{u1, u2} α β (TopologicalSpace.Opens.carrier.{u2} β _inst_2 (U i)) f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {ι : Type.{u3}} {U : ι -> (TopologicalSpace.Opens.{u1} β _inst_2)}, (Eq.{succ u1} (TopologicalSpace.Opens.{u1} β _inst_2) (supᵢ.{u1, succ u3} (TopologicalSpace.Opens.{u1} β _inst_2) (ConditionallyCompleteLattice.toSupSet.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2))) ι U) (Top.top.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (CompleteLattice.toTop.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2)))) -> (Continuous.{u2, u1} α β _inst_1 _inst_2 f) -> (Iff (Inducing.{u2, u1} α β _inst_1 _inst_2 f) (forall (i : ι), Inducing.{u2, u1} (Set.Elem.{u2} α (Set.preimage.{u2, u1} α β f (TopologicalSpace.Opens.carrier.{u1} β _inst_2 (U i)))) (Set.Elem.{u1} β (TopologicalSpace.Opens.carrier.{u1} β _inst_2 (U i))) (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Set.preimage.{u2, u1} α β f (TopologicalSpace.Opens.carrier.{u1} β _inst_2 (U i)))) _inst_1) (instTopologicalSpaceSubtype.{u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (TopologicalSpace.Opens.carrier.{u1} β _inst_2 (U i))) _inst_2) (Set.restrictPreimage.{u2, u1} α β (TopologicalSpace.Opens.carrier.{u1} β _inst_2 (U i)) f)))
Case conversion may be inaccurate. Consider using '#align inducing_iff_inducing_of_supr_eq_top inducing_iff_inducing_of_supᵢ_eq_topₓ'. -/
theorem inducing_iff_inducing_of_supᵢ_eq_top (h : Continuous f) :
    Inducing f ↔ ∀ i, Inducing ((U i).1.restrictPreimage f) :=
  by
  simp_rw [inducing_coe.inducing_iff, inducing_iff_nhds, restrict_preimage, maps_to.coe_restrict,
    restrict_eq, ← @Filter.comap_comap _ _ _ _ coe f]
  constructor
  · intro H i x
    rw [← H, ← inducing_coe.nhds_eq_comap]
  · intro H x
    obtain ⟨i, hi⟩ :=
      opens.mem_supr.mp
        (show f x ∈ supᵢ U by
          rw [hU]
          triv)
    erw [← OpenEmbedding.map_nhds_eq (h.1 _ (U i).2).openEmbedding_subtype_val ⟨x, hi⟩]
    rw [(H i) ⟨x, hi⟩, Filter.subtype_coe_map_comap, Function.comp_apply, Subtype.coe_mk,
      inf_eq_left, Filter.le_principal_iff]
    exact Filter.preimage_mem_comap ((U i).2.mem_nhds hi)
#align inducing_iff_inducing_of_supr_eq_top inducing_iff_inducing_of_supᵢ_eq_top

/- warning: embedding_iff_embedding_of_supr_eq_top -> embedding_iff_embedding_of_supᵢ_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {ι : Type.{u3}} {U : ι -> (TopologicalSpace.Opens.{u2} β _inst_2)}, (Eq.{succ u2} (TopologicalSpace.Opens.{u2} β _inst_2) (supᵢ.{u2, succ u3} (TopologicalSpace.Opens.{u2} β _inst_2) (ConditionallyCompleteLattice.toHasSup.{u2} (TopologicalSpace.Opens.{u2} β _inst_2) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.Opens.{u2} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u2} β _inst_2))) ι U) (Top.top.{u2} (TopologicalSpace.Opens.{u2} β _inst_2) (CompleteLattice.toHasTop.{u2} (TopologicalSpace.Opens.{u2} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u2} β _inst_2)))) -> (Continuous.{u1, u2} α β _inst_1 _inst_2 f) -> (Iff (Embedding.{u1, u2} α β _inst_1 _inst_2 f) (forall (i : ι), Embedding.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.preimage.{u1, u2} α β f (TopologicalSpace.Opens.carrier.{u2} β _inst_2 (U i)))) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (TopologicalSpace.Opens.carrier.{u2} β _inst_2 (U i))) (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.preimage.{u1, u2} α β f (TopologicalSpace.Opens.carrier.{u2} β _inst_2 (U i)))) _inst_1) (Subtype.topologicalSpace.{u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (TopologicalSpace.Opens.carrier.{u2} β _inst_2 (U i))) _inst_2) (Set.restrictPreimage.{u1, u2} α β (TopologicalSpace.Opens.carrier.{u2} β _inst_2 (U i)) f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {ι : Type.{u3}} {U : ι -> (TopologicalSpace.Opens.{u1} β _inst_2)}, (Eq.{succ u1} (TopologicalSpace.Opens.{u1} β _inst_2) (supᵢ.{u1, succ u3} (TopologicalSpace.Opens.{u1} β _inst_2) (ConditionallyCompleteLattice.toSupSet.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2))) ι U) (Top.top.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (CompleteLattice.toTop.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2)))) -> (Continuous.{u2, u1} α β _inst_1 _inst_2 f) -> (Iff (Embedding.{u2, u1} α β _inst_1 _inst_2 f) (forall (i : ι), Embedding.{u2, u1} (Set.Elem.{u2} α (Set.preimage.{u2, u1} α β f (TopologicalSpace.Opens.carrier.{u1} β _inst_2 (U i)))) (Set.Elem.{u1} β (TopologicalSpace.Opens.carrier.{u1} β _inst_2 (U i))) (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Set.preimage.{u2, u1} α β f (TopologicalSpace.Opens.carrier.{u1} β _inst_2 (U i)))) _inst_1) (instTopologicalSpaceSubtype.{u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (TopologicalSpace.Opens.carrier.{u1} β _inst_2 (U i))) _inst_2) (Set.restrictPreimage.{u2, u1} α β (TopologicalSpace.Opens.carrier.{u1} β _inst_2 (U i)) f)))
Case conversion may be inaccurate. Consider using '#align embedding_iff_embedding_of_supr_eq_top embedding_iff_embedding_of_supᵢ_eq_topₓ'. -/
theorem embedding_iff_embedding_of_supᵢ_eq_top (h : Continuous f) :
    Embedding f ↔ ∀ i, Embedding ((U i).1.restrictPreimage f) :=
  by
  simp_rw [embedding_iff]
  rw [forall_and]
  apply and_congr
  · apply inducing_iff_inducing_of_supᵢ_eq_top <;> assumption
  · apply Set.injective_iff_injective_of_unionᵢ_eq_univ
    convert congr_arg coe hU
    simp
#align embedding_iff_embedding_of_supr_eq_top embedding_iff_embedding_of_supᵢ_eq_top

/- warning: open_embedding_iff_open_embedding_of_supr_eq_top -> openEmbedding_iff_openEmbedding_of_supᵢ_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {ι : Type.{u3}} {U : ι -> (TopologicalSpace.Opens.{u2} β _inst_2)}, (Eq.{succ u2} (TopologicalSpace.Opens.{u2} β _inst_2) (supᵢ.{u2, succ u3} (TopologicalSpace.Opens.{u2} β _inst_2) (ConditionallyCompleteLattice.toHasSup.{u2} (TopologicalSpace.Opens.{u2} β _inst_2) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.Opens.{u2} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u2} β _inst_2))) ι U) (Top.top.{u2} (TopologicalSpace.Opens.{u2} β _inst_2) (CompleteLattice.toHasTop.{u2} (TopologicalSpace.Opens.{u2} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u2} β _inst_2)))) -> (Continuous.{u1, u2} α β _inst_1 _inst_2 f) -> (Iff (OpenEmbedding.{u1, u2} α β _inst_1 _inst_2 f) (forall (i : ι), OpenEmbedding.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.preimage.{u1, u2} α β f (TopologicalSpace.Opens.carrier.{u2} β _inst_2 (U i)))) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (TopologicalSpace.Opens.carrier.{u2} β _inst_2 (U i))) (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.preimage.{u1, u2} α β f (TopologicalSpace.Opens.carrier.{u2} β _inst_2 (U i)))) _inst_1) (Subtype.topologicalSpace.{u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (TopologicalSpace.Opens.carrier.{u2} β _inst_2 (U i))) _inst_2) (Set.restrictPreimage.{u1, u2} α β (TopologicalSpace.Opens.carrier.{u2} β _inst_2 (U i)) f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {ι : Type.{u3}} {U : ι -> (TopologicalSpace.Opens.{u1} β _inst_2)}, (Eq.{succ u1} (TopologicalSpace.Opens.{u1} β _inst_2) (supᵢ.{u1, succ u3} (TopologicalSpace.Opens.{u1} β _inst_2) (ConditionallyCompleteLattice.toSupSet.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2))) ι U) (Top.top.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (CompleteLattice.toTop.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2)))) -> (Continuous.{u2, u1} α β _inst_1 _inst_2 f) -> (Iff (OpenEmbedding.{u2, u1} α β _inst_1 _inst_2 f) (forall (i : ι), OpenEmbedding.{u2, u1} (Set.Elem.{u2} α (Set.preimage.{u2, u1} α β f (TopologicalSpace.Opens.carrier.{u1} β _inst_2 (U i)))) (Set.Elem.{u1} β (TopologicalSpace.Opens.carrier.{u1} β _inst_2 (U i))) (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Set.preimage.{u2, u1} α β f (TopologicalSpace.Opens.carrier.{u1} β _inst_2 (U i)))) _inst_1) (instTopologicalSpaceSubtype.{u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (TopologicalSpace.Opens.carrier.{u1} β _inst_2 (U i))) _inst_2) (Set.restrictPreimage.{u2, u1} α β (TopologicalSpace.Opens.carrier.{u1} β _inst_2 (U i)) f)))
Case conversion may be inaccurate. Consider using '#align open_embedding_iff_open_embedding_of_supr_eq_top openEmbedding_iff_openEmbedding_of_supᵢ_eq_topₓ'. -/
theorem openEmbedding_iff_openEmbedding_of_supᵢ_eq_top (h : Continuous f) :
    OpenEmbedding f ↔ ∀ i, OpenEmbedding ((U i).1.restrictPreimage f) :=
  by
  simp_rw [openEmbedding_iff]
  rw [forall_and]
  apply and_congr
  · apply embedding_iff_embedding_of_supᵢ_eq_top <;> assumption
  · simp_rw [Set.range_restrictPreimage]
    apply isOpen_iff_coe_preimage_of_supᵢ_eq_top hU
#align open_embedding_iff_open_embedding_of_supr_eq_top openEmbedding_iff_openEmbedding_of_supᵢ_eq_top

/- warning: closed_embedding_iff_closed_embedding_of_supr_eq_top -> closedEmbedding_iff_closedEmbedding_of_supᵢ_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {ι : Type.{u3}} {U : ι -> (TopologicalSpace.Opens.{u2} β _inst_2)}, (Eq.{succ u2} (TopologicalSpace.Opens.{u2} β _inst_2) (supᵢ.{u2, succ u3} (TopologicalSpace.Opens.{u2} β _inst_2) (ConditionallyCompleteLattice.toHasSup.{u2} (TopologicalSpace.Opens.{u2} β _inst_2) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.Opens.{u2} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u2} β _inst_2))) ι U) (Top.top.{u2} (TopologicalSpace.Opens.{u2} β _inst_2) (CompleteLattice.toHasTop.{u2} (TopologicalSpace.Opens.{u2} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u2} β _inst_2)))) -> (Continuous.{u1, u2} α β _inst_1 _inst_2 f) -> (Iff (ClosedEmbedding.{u1, u2} α β _inst_1 _inst_2 f) (forall (i : ι), ClosedEmbedding.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.preimage.{u1, u2} α β f (TopologicalSpace.Opens.carrier.{u2} β _inst_2 (U i)))) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (TopologicalSpace.Opens.carrier.{u2} β _inst_2 (U i))) (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.preimage.{u1, u2} α β f (TopologicalSpace.Opens.carrier.{u2} β _inst_2 (U i)))) _inst_1) (Subtype.topologicalSpace.{u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (TopologicalSpace.Opens.carrier.{u2} β _inst_2 (U i))) _inst_2) (Set.restrictPreimage.{u1, u2} α β (TopologicalSpace.Opens.carrier.{u2} β _inst_2 (U i)) f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {ι : Type.{u3}} {U : ι -> (TopologicalSpace.Opens.{u1} β _inst_2)}, (Eq.{succ u1} (TopologicalSpace.Opens.{u1} β _inst_2) (supᵢ.{u1, succ u3} (TopologicalSpace.Opens.{u1} β _inst_2) (ConditionallyCompleteLattice.toSupSet.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2))) ι U) (Top.top.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (CompleteLattice.toTop.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2)))) -> (Continuous.{u2, u1} α β _inst_1 _inst_2 f) -> (Iff (ClosedEmbedding.{u2, u1} α β _inst_1 _inst_2 f) (forall (i : ι), ClosedEmbedding.{u2, u1} (Set.Elem.{u2} α (Set.preimage.{u2, u1} α β f (TopologicalSpace.Opens.carrier.{u1} β _inst_2 (U i)))) (Set.Elem.{u1} β (TopologicalSpace.Opens.carrier.{u1} β _inst_2 (U i))) (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Set.preimage.{u2, u1} α β f (TopologicalSpace.Opens.carrier.{u1} β _inst_2 (U i)))) _inst_1) (instTopologicalSpaceSubtype.{u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (TopologicalSpace.Opens.carrier.{u1} β _inst_2 (U i))) _inst_2) (Set.restrictPreimage.{u2, u1} α β (TopologicalSpace.Opens.carrier.{u1} β _inst_2 (U i)) f)))
Case conversion may be inaccurate. Consider using '#align closed_embedding_iff_closed_embedding_of_supr_eq_top closedEmbedding_iff_closedEmbedding_of_supᵢ_eq_topₓ'. -/
theorem closedEmbedding_iff_closedEmbedding_of_supᵢ_eq_top (h : Continuous f) :
    ClosedEmbedding f ↔ ∀ i, ClosedEmbedding ((U i).1.restrictPreimage f) :=
  by
  simp_rw [closedEmbedding_iff]
  rw [forall_and]
  apply and_congr
  · apply embedding_iff_embedding_of_supᵢ_eq_top <;> assumption
  · simp_rw [Set.range_restrictPreimage]
    apply isClosed_iff_coe_preimage_of_supᵢ_eq_top hU
#align closed_embedding_iff_closed_embedding_of_supr_eq_top closedEmbedding_iff_closedEmbedding_of_supᵢ_eq_top

