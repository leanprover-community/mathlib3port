/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth

! This file was ported from Lean 3 source module order.complete_lattice_intervals
! leanprover-community/mathlib commit 509de852e1de55e1efa8eacfa11df0823f26f226
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.ConditionallyCompleteLattice.Basic
import Mathbin.Data.Set.Intervals.OrdConnected

/-! # Subtypes of conditionally complete linear orders

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we give conditions on a subset of a conditionally complete linear order, to ensure that
the subtype is itself conditionally complete.

We check that an `ord_connected` set satisfies these conditions.

## TODO

Add appropriate instances for all `set.Ixx`. This requires a refactor that will allow different
default values for `Sup` and `Inf`.
-/


open Classical

open Set

variable {α : Type _} (s : Set α)

section SupSet

variable [SupSet α]

#print subsetSupSet /-
/-- `has_Sup` structure on a nonempty subset `s` of an object with `has_Sup`. This definition is
non-canonical (it uses `default s`); it should be used only as here, as an auxiliary instance in the
construction of the `conditionally_complete_linear_order` structure. -/
noncomputable def subsetSupSet [Inhabited s] : SupSet s
    where sup t :=
    if ht : supₛ (coe '' t : Set α) ∈ s then ⟨supₛ (coe '' t : Set α), ht⟩ else default
#align subset_has_Sup subsetSupSet
-/

attribute [local instance] subsetSupSet

#print subset_supₛ_def /-
@[simp]
theorem subset_supₛ_def [Inhabited s] :
    @supₛ s _ = fun t =>
      if ht : supₛ (coe '' t : Set α) ∈ s then ⟨supₛ (coe '' t : Set α), ht⟩ else default :=
  rfl
#align subset_Sup_def subset_supₛ_def
-/

#print subset_supₛ_of_within /-
theorem subset_supₛ_of_within [Inhabited s] {t : Set s} (h : supₛ (coe '' t : Set α) ∈ s) :
    supₛ (coe '' t : Set α) = (@supₛ s _ t : α) := by simp [dif_pos h]
#align subset_Sup_of_within subset_supₛ_of_within
-/

end SupSet

section InfSet

variable [InfSet α]

#print subsetInfSet /-
/-- `has_Inf` structure on a nonempty subset `s` of an object with `has_Inf`. This definition is
non-canonical (it uses `default s`); it should be used only as here, as an auxiliary instance in the
construction of the `conditionally_complete_linear_order` structure. -/
noncomputable def subsetInfSet [Inhabited s] : InfSet s
    where inf t :=
    if ht : infₛ (coe '' t : Set α) ∈ s then ⟨infₛ (coe '' t : Set α), ht⟩ else default
#align subset_has_Inf subsetInfSet
-/

attribute [local instance] subsetInfSet

#print subset_infₛ_def /-
@[simp]
theorem subset_infₛ_def [Inhabited s] :
    @infₛ s _ = fun t =>
      if ht : infₛ (coe '' t : Set α) ∈ s then ⟨infₛ (coe '' t : Set α), ht⟩ else default :=
  rfl
#align subset_Inf_def subset_infₛ_def
-/

#print subset_infₛ_of_within /-
theorem subset_infₛ_of_within [Inhabited s] {t : Set s} (h : infₛ (coe '' t : Set α) ∈ s) :
    infₛ (coe '' t : Set α) = (@infₛ s _ t : α) := by simp [dif_pos h]
#align subset_Inf_of_within subset_infₛ_of_within
-/

end InfSet

variable [ConditionallyCompleteLinearOrder α]

attribute [local instance] subsetSupSet

attribute [local instance] subsetInfSet

/- warning: subset_conditionally_complete_linear_order -> subsetConditionallyCompleteLinearOrder is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] [_inst_2 : Inhabited.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)], (forall {t : Set.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)}, (Set.Nonempty.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) t) -> (BddAbove.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (Subtype.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))) (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) t) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) (Set.image.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)))))) t)) s)) -> (forall {t : Set.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)}, (Set.Nonempty.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) t) -> (BddBelow.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (Subtype.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))) (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) t) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) (Set.image.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)))))) t)) s)) -> (ConditionallyCompleteLinearOrder.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] [_inst_2 : Inhabited.{succ u1} (Set.Elem.{u1} α s)], (forall {t : Set.{u1} (Set.Elem.{u1} α s)}, (Set.Nonempty.{u1} (Set.Elem.{u1} α s) t) -> (BddAbove.{u1} (Set.Elem.{u1} α s) (Subtype.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))) (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) t) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) (Set.image.{u1, u1} (Set.Elem.{u1} α s) α (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) t)) s)) -> (forall {t : Set.{u1} (Set.Elem.{u1} α s)}, (Set.Nonempty.{u1} (Set.Elem.{u1} α s) t) -> (BddBelow.{u1} (Set.Elem.{u1} α s) (Subtype.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))) (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) t) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) (Set.image.{u1, u1} (Set.Elem.{u1} α s) α (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) t)) s)) -> (ConditionallyCompleteLinearOrder.{u1} (Set.Elem.{u1} α s))
Case conversion may be inaccurate. Consider using '#align subset_conditionally_complete_linear_order subsetConditionallyCompleteLinearOrderₓ'. -/
/-- For a nonempty subset of a conditionally complete linear order to be a conditionally complete
linear order, it suffices that it contain the `Sup` of all its nonempty bounded-above subsets, and
the `Inf` of all its nonempty bounded-below subsets.
See note [reducible non-instances]. -/
@[reducible]
noncomputable def subsetConditionallyCompleteLinearOrder [Inhabited s]
    (h_Sup : ∀ {t : Set s} (ht : t.Nonempty) (h_bdd : BddAbove t), supₛ (coe '' t : Set α) ∈ s)
    (h_Inf : ∀ {t : Set s} (ht : t.Nonempty) (h_bdd : BddBelow t), infₛ (coe '' t : Set α) ∈ s) :
    ConditionallyCompleteLinearOrder s :=
  {-- The following would be a more natural way to finish, but gives a "deep recursion" error:
      -- simpa [subset_Sup_of_within (h_Sup t)] using
      --   (strict_mono_coe s).monotone.le_cSup_image hct h_bdd,
      subsetSupSet
      s,
    subsetInfSet s, DistribLattice.toLattice s,
    (inferInstance :
      LinearOrder
        s) with
    le_cSup := by
      rintro t c h_bdd hct
      have := (Subtype.mono_coe s).le_cSup_image hct h_bdd
      rwa [subset_supₛ_of_within s (h_Sup ⟨c, hct⟩ h_bdd)] at this
    cSup_le := by
      rintro t B ht hB
      have := (Subtype.mono_coe s).cSup_image_le ht hB
      rwa [subset_supₛ_of_within s (h_Sup ht ⟨B, hB⟩)] at this
    le_cInf := by
      intro t B ht hB
      have := (Subtype.mono_coe s).le_cInf_image ht hB
      rwa [subset_infₛ_of_within s (h_Inf ht ⟨B, hB⟩)] at this
    cInf_le := by
      rintro t c h_bdd hct
      have := (Subtype.mono_coe s).cInf_image_le hct h_bdd
      rwa [subset_infₛ_of_within s (h_Inf ⟨c, hct⟩ h_bdd)] at this }
#align subset_conditionally_complete_linear_order subsetConditionallyCompleteLinearOrder

section OrdConnected

/- warning: Sup_within_of_ord_connected -> supₛ_within_of_ordConnected is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} [hs : Set.OrdConnected.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))) s] {{t : Set.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)}}, (Set.Nonempty.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) t) -> (BddAbove.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (Subtype.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))) (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) t) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) (Set.image.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)))))) t)) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} [hs : Set.OrdConnected.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))) s] {{t : Set.{u1} (Set.Elem.{u1} α s)}}, (Set.Nonempty.{u1} (Set.Elem.{u1} α s) t) -> (BddAbove.{u1} (Set.Elem.{u1} α s) (Subtype.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))) (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) t) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) (Set.image.{u1, u1} (Set.Elem.{u1} α s) α (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) t)) s)
Case conversion may be inaccurate. Consider using '#align Sup_within_of_ord_connected supₛ_within_of_ordConnectedₓ'. -/
/-- The `Sup` function on a nonempty `ord_connected` set `s` in a conditionally complete linear
order takes values within `s`, for all nonempty bounded-above subsets of `s`. -/
theorem supₛ_within_of_ordConnected {s : Set α} [hs : OrdConnected s] ⦃t : Set s⦄ (ht : t.Nonempty)
    (h_bdd : BddAbove t) : supₛ (coe '' t : Set α) ∈ s :=
  by
  obtain ⟨c, hct⟩ : ∃ c, c ∈ t := ht
  obtain ⟨B, hB⟩ : ∃ B, B ∈ upperBounds t := h_bdd
  refine' hs.out c.2 B.2 ⟨_, _⟩
  · exact (Subtype.mono_coe s).le_cSup_image hct ⟨B, hB⟩
  · exact (Subtype.mono_coe s).cSup_image_le ⟨c, hct⟩ hB
#align Sup_within_of_ord_connected supₛ_within_of_ordConnected

/- warning: Inf_within_of_ord_connected -> infₛ_within_of_ordConnected is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} [hs : Set.OrdConnected.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))) s] {{t : Set.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)}}, (Set.Nonempty.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) t) -> (BddBelow.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (Subtype.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))) (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) t) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) (Set.image.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)))))) t)) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} [hs : Set.OrdConnected.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))) s] {{t : Set.{u1} (Set.Elem.{u1} α s)}}, (Set.Nonempty.{u1} (Set.Elem.{u1} α s) t) -> (BddBelow.{u1} (Set.Elem.{u1} α s) (Subtype.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))) (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) t) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) (Set.image.{u1, u1} (Set.Elem.{u1} α s) α (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) t)) s)
Case conversion may be inaccurate. Consider using '#align Inf_within_of_ord_connected infₛ_within_of_ordConnectedₓ'. -/
/-- The `Inf` function on a nonempty `ord_connected` set `s` in a conditionally complete linear
order takes values within `s`, for all nonempty bounded-below subsets of `s`. -/
theorem infₛ_within_of_ordConnected {s : Set α} [hs : OrdConnected s] ⦃t : Set s⦄ (ht : t.Nonempty)
    (h_bdd : BddBelow t) : infₛ (coe '' t : Set α) ∈ s :=
  by
  obtain ⟨c, hct⟩ : ∃ c, c ∈ t := ht
  obtain ⟨B, hB⟩ : ∃ B, B ∈ lowerBounds t := h_bdd
  refine' hs.out B.2 c.2 ⟨_, _⟩
  · exact (Subtype.mono_coe s).le_cInf_image ⟨c, hct⟩ hB
  · exact (Subtype.mono_coe s).cInf_image_le hct ⟨B, hB⟩
#align Inf_within_of_ord_connected infₛ_within_of_ordConnected

#print ordConnectedSubsetConditionallyCompleteLinearOrder /-
/-- A nonempty `ord_connected` set in a conditionally complete linear order is naturally a
conditionally complete linear order. -/
noncomputable instance ordConnectedSubsetConditionallyCompleteLinearOrder [Inhabited s]
    [OrdConnected s] : ConditionallyCompleteLinearOrder s :=
  subsetConditionallyCompleteLinearOrder s supₛ_within_of_ordConnected infₛ_within_of_ordConnected
#align
  ord_connected_subset_conditionally_complete_linear_order ordConnectedSubsetConditionallyCompleteLinearOrder
-/

end OrdConnected

