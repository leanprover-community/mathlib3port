/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module order.conditionally_complete_lattice.finset
! leanprover-community/mathlib commit 28aa996fc6fb4317f0083c4e6daf79878d81be33
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.ConditionallyCompleteLattice.Basic
import Mathbin.Data.Set.Finite

/-!
# Conditionally complete lattices and finite sets.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/


open Set

variable {α β γ : Type _}

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] {s t : Set α} {a b : α}

/- warning: finset.nonempty.sup'_eq_cSup_image -> Finset.Nonempty.sup'_eq_cSup_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Finset.{u2} β} (hs : Finset.Nonempty.{u2} β s) (f : β -> α), Eq.{succ u1} α (Finset.sup'.{u1, u2} α β (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)) s hs f) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (Set.image.{u2, u1} β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) s)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Finset.{u2} β} (hs : Finset.Nonempty.{u2} β s) (f : β -> α), Eq.{succ u1} α (Finset.sup'.{u1, u2} α β (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)) s hs f) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Set.image.{u2, u1} β α f (Finset.toSet.{u2} β s)))
Case conversion may be inaccurate. Consider using '#align finset.nonempty.sup'_eq_cSup_image Finset.Nonempty.sup'_eq_cSup_imageₓ'. -/
theorem Finset.Nonempty.sup'_eq_cSup_image {s : Finset β} (hs : s.Nonempty) (f : β → α) :
    s.sup' hs f = supₛ (f '' s) :=
  eq_of_forall_ge_iff fun a => by
    simp [csupₛ_le_iff (s.finite_to_set.image f).BddAbove (hs.to_set.image f)]
#align finset.nonempty.sup'_eq_cSup_image Finset.Nonempty.sup'_eq_cSup_image

/- warning: finset.nonempty.sup'_id_eq_cSup -> Finset.Nonempty.sup'_id_eq_cSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Finset.{u1} α} (hs : Finset.Nonempty.{u1} α s), Eq.{succ u1} α (Finset.sup'.{u1, u1} α α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)) s hs (id.{succ u1} α)) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Finset.{u1} α} (hs : Finset.Nonempty.{u1} α s), Eq.{succ u1} α (Finset.sup'.{u1, u1} α α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)) s hs (id.{succ u1} α)) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Finset.toSet.{u1} α s))
Case conversion may be inaccurate. Consider using '#align finset.nonempty.sup'_id_eq_cSup Finset.Nonempty.sup'_id_eq_cSupₓ'. -/
theorem Finset.Nonempty.sup'_id_eq_cSup {s : Finset α} (hs : s.Nonempty) : s.sup' hs id = supₛ s :=
  by rw [hs.sup'_eq_cSup_image, image_id]
#align finset.nonempty.sup'_id_eq_cSup Finset.Nonempty.sup'_id_eq_cSup

end ConditionallyCompleteLattice

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] {s t : Set α} {a b : α}

/- warning: finset.nonempty.cSup_eq_max' -> Finset.Nonempty.cSup_eq_max' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Finset.{u1} α} (h : Finset.Nonempty.{u1} α s), Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) (Finset.max'.{u1} α (ConditionallyCompleteLinearOrder.toLinearOrder.{u1} α _inst_1) s h)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Finset.{u1} α} (h : Finset.Nonempty.{u1} α s), Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) (Finset.toSet.{u1} α s)) (Finset.max'.{u1} α (instLinearOrder.{u1} α _inst_1) s h)
Case conversion may be inaccurate. Consider using '#align finset.nonempty.cSup_eq_max' Finset.Nonempty.cSup_eq_max'ₓ'. -/
theorem Finset.Nonempty.cSup_eq_max' {s : Finset α} (h : s.Nonempty) : supₛ ↑s = s.max' h :=
  eq_of_forall_ge_iff fun a => (csupₛ_le_iff s.BddAbove h.to_set).trans (s.max'_le_iff h).symm
#align finset.nonempty.cSup_eq_max' Finset.Nonempty.cSup_eq_max'

/- warning: finset.nonempty.cInf_eq_min' -> Finset.Nonempty.cInf_eq_min' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Finset.{u1} α} (h : Finset.Nonempty.{u1} α s), Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) (Finset.min'.{u1} α (ConditionallyCompleteLinearOrder.toLinearOrder.{u1} α _inst_1) s h)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Finset.{u1} α} (h : Finset.Nonempty.{u1} α s), Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) (Finset.toSet.{u1} α s)) (Finset.min'.{u1} α (instLinearOrder.{u1} α _inst_1) s h)
Case conversion may be inaccurate. Consider using '#align finset.nonempty.cInf_eq_min' Finset.Nonempty.cInf_eq_min'ₓ'. -/
theorem Finset.Nonempty.cInf_eq_min' {s : Finset α} (h : s.Nonempty) : infₛ ↑s = s.min' h :=
  @Finset.Nonempty.cSup_eq_max' αᵒᵈ _ s h
#align finset.nonempty.cInf_eq_min' Finset.Nonempty.cInf_eq_min'

/- warning: finset.nonempty.cSup_mem -> Finset.Nonempty.cSup_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Finset.{u1} α}, (Finset.Nonempty.{u1} α s) -> (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Finset.{u1} α}, (Finset.Nonempty.{u1} α s) -> (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) (Finset.toSet.{u1} α s)) s)
Case conversion may be inaccurate. Consider using '#align finset.nonempty.cSup_mem Finset.Nonempty.cSup_memₓ'. -/
theorem Finset.Nonempty.cSup_mem {s : Finset α} (h : s.Nonempty) : supₛ (s : Set α) ∈ s :=
  by
  rw [h.cSup_eq_max']
  exact s.max'_mem _
#align finset.nonempty.cSup_mem Finset.Nonempty.cSup_mem

/- warning: finset.nonempty.cInf_mem -> Finset.Nonempty.cInf_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Finset.{u1} α}, (Finset.Nonempty.{u1} α s) -> (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Finset.{u1} α}, (Finset.Nonempty.{u1} α s) -> (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) (Finset.toSet.{u1} α s)) s)
Case conversion may be inaccurate. Consider using '#align finset.nonempty.cInf_mem Finset.Nonempty.cInf_memₓ'. -/
theorem Finset.Nonempty.cInf_mem {s : Finset α} (h : s.Nonempty) : infₛ (s : Set α) ∈ s :=
  @Finset.Nonempty.cSup_mem αᵒᵈ _ _ h
#align finset.nonempty.cInf_mem Finset.Nonempty.cInf_mem

/- warning: set.nonempty.cSup_mem -> Set.Nonempty.cSup_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Set.Finite.{u1} α s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Set.Finite.{u1} α s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s) s)
Case conversion may be inaccurate. Consider using '#align set.nonempty.cSup_mem Set.Nonempty.cSup_memₓ'. -/
theorem Set.Nonempty.cSup_mem (h : s.Nonempty) (hs : s.Finite) : supₛ s ∈ s :=
  by
  lift s to Finset α using hs
  exact Finset.Nonempty.cSup_mem h
#align set.nonempty.cSup_mem Set.Nonempty.cSup_mem

/- warning: set.nonempty.cInf_mem -> Set.Nonempty.cInf_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Set.Finite.{u1} α s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Set.Finite.{u1} α s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s) s)
Case conversion may be inaccurate. Consider using '#align set.nonempty.cInf_mem Set.Nonempty.cInf_memₓ'. -/
theorem Set.Nonempty.cInf_mem (h : s.Nonempty) (hs : s.Finite) : infₛ s ∈ s :=
  @Set.Nonempty.cSup_mem αᵒᵈ _ _ h hs
#align set.nonempty.cInf_mem Set.Nonempty.cInf_mem

/- warning: set.finite.cSup_lt_iff -> Set.Finite.cSup_lt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} {a : α}, (Set.Finite.{u1} α s) -> (Set.Nonempty.{u1} α s) -> (Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s) a) (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) x a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} {a : α}, (Set.Finite.{u1} α s) -> (Set.Nonempty.{u1} α s) -> (Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s) a) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) x a)))
Case conversion may be inaccurate. Consider using '#align set.finite.cSup_lt_iff Set.Finite.cSup_lt_iffₓ'. -/
theorem Set.Finite.cSup_lt_iff (hs : s.Finite) (h : s.Nonempty) : supₛ s < a ↔ ∀ x ∈ s, x < a :=
  ⟨fun h x hx => (le_csupₛ hs.BddAbove hx).trans_lt h, fun H => H _ <| h.cSup_mem hs⟩
#align set.finite.cSup_lt_iff Set.Finite.cSup_lt_iff

/- warning: set.finite.lt_cInf_iff -> Set.Finite.lt_cInf_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} {a : α}, (Set.Finite.{u1} α s) -> (Set.Nonempty.{u1} α s) -> (Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) a (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) a x)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} {a : α}, (Set.Finite.{u1} α s) -> (Set.Nonempty.{u1} α s) -> (Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) a (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) a x)))
Case conversion may be inaccurate. Consider using '#align set.finite.lt_cInf_iff Set.Finite.lt_cInf_iffₓ'. -/
theorem Set.Finite.lt_cInf_iff (hs : s.Finite) (h : s.Nonempty) : a < infₛ s ↔ ∀ x ∈ s, a < x :=
  @Set.Finite.cSup_lt_iff αᵒᵈ _ _ _ hs h
#align set.finite.lt_cInf_iff Set.Finite.lt_cInf_iff

end ConditionallyCompleteLinearOrder

/-!
### Relation between `Sup` / `Inf` and `finset.sup'` / `finset.inf'`

Like the `Sup` of a `conditionally_complete_lattice`, `finset.sup'` also requires the set to be
non-empty. As a result, we can translate between the two.
-/


namespace Finset

/- warning: finset.sup'_eq_cSup_image -> Finset.sup'_eq_csupₛ_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u2} β] (s : Finset.{u1} α) (H : Finset.Nonempty.{u1} α s) (f : α -> β), Eq.{succ u2} β (Finset.sup'.{u2, u1} β α (Lattice.toSemilatticeSup.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_1)) s H f) (SupSet.supₛ.{u2} β (ConditionallyCompleteLattice.toHasSup.{u2} β _inst_1) (Set.image.{u1, u2} α β f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u2} β] (s : Finset.{u1} α) (H : Finset.Nonempty.{u1} α s) (f : α -> β), Eq.{succ u2} β (Finset.sup'.{u2, u1} β α (Lattice.toSemilatticeSup.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_1)) s H f) (SupSet.supₛ.{u2} β (ConditionallyCompleteLattice.toSupSet.{u2} β _inst_1) (Set.image.{u1, u2} α β f (Finset.toSet.{u1} α s)))
Case conversion may be inaccurate. Consider using '#align finset.sup'_eq_cSup_image Finset.sup'_eq_csupₛ_imageₓ'. -/
theorem sup'_eq_csupₛ_image [ConditionallyCompleteLattice β] (s : Finset α) (H) (f : α → β) :
    s.sup' H f = supₛ (f '' s) := by
  apply le_antisymm
  · refine' Finset.sup'_le _ _ fun a ha => _
    refine' le_csupₛ ⟨s.sup' H f, _⟩ ⟨a, ha, rfl⟩
    rintro i ⟨j, hj, rfl⟩
    exact Finset.le_sup' _ hj
  · apply csupₛ_le ((coe_nonempty.mpr H).image _)
    rintro _ ⟨a, ha, rfl⟩
    exact Finset.le_sup' _ ha
#align finset.sup'_eq_cSup_image Finset.sup'_eq_csupₛ_image

/- warning: finset.inf'_eq_cInf_image -> Finset.inf'_eq_cinfₛ_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u2} β] (s : Finset.{u1} α) (H : Finset.Nonempty.{u1} α s) (f : α -> β), Eq.{succ u2} β (Finset.inf'.{u2, u1} β α (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_1)) s H f) (InfSet.infₛ.{u2} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_1) (Set.image.{u1, u2} α β f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u2} β] (s : Finset.{u1} α) (H : Finset.Nonempty.{u1} α s) (f : α -> β), Eq.{succ u2} β (Finset.inf'.{u2, u1} β α (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_1)) s H f) (InfSet.infₛ.{u2} β (ConditionallyCompleteLattice.toInfSet.{u2} β _inst_1) (Set.image.{u1, u2} α β f (Finset.toSet.{u1} α s)))
Case conversion may be inaccurate. Consider using '#align finset.inf'_eq_cInf_image Finset.inf'_eq_cinfₛ_imageₓ'. -/
theorem inf'_eq_cinfₛ_image [ConditionallyCompleteLattice β] (s : Finset α) (H) (f : α → β) :
    s.inf' H f = infₛ (f '' s) :=
  @sup'_eq_csupₛ_image _ βᵒᵈ _ _ H _
#align finset.inf'_eq_cInf_image Finset.inf'_eq_cinfₛ_image

/- warning: finset.sup'_id_eq_cSup -> Finset.sup'_id_eq_csupₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] (s : Finset.{u1} α) (H : Finset.Nonempty.{u1} α s), Eq.{succ u1} α (Finset.sup'.{u1, u1} α α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)) s H (id.{succ u1} α)) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] (s : Finset.{u1} α) (H : Finset.Nonempty.{u1} α s), Eq.{succ u1} α (Finset.sup'.{u1, u1} α α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)) s H (id.{succ u1} α)) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Finset.toSet.{u1} α s))
Case conversion may be inaccurate. Consider using '#align finset.sup'_id_eq_cSup Finset.sup'_id_eq_csupₛₓ'. -/
theorem sup'_id_eq_csupₛ [ConditionallyCompleteLattice α] (s : Finset α) (H) :
    s.sup' H id = supₛ s := by rw [sup'_eq_cSup_image s H, Set.image_id]
#align finset.sup'_id_eq_cSup Finset.sup'_id_eq_csupₛ

/- warning: finset.inf'_id_eq_cInf -> Finset.inf'_id_eq_cinfₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] (s : Finset.{u1} α) (H : Finset.Nonempty.{u1} α s), Eq.{succ u1} α (Finset.inf'.{u1, u1} α α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)) s H (id.{succ u1} α)) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] (s : Finset.{u1} α) (H : Finset.Nonempty.{u1} α s), Eq.{succ u1} α (Finset.inf'.{u1, u1} α α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)) s H (id.{succ u1} α)) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) (Finset.toSet.{u1} α s))
Case conversion may be inaccurate. Consider using '#align finset.inf'_id_eq_cInf Finset.inf'_id_eq_cinfₛₓ'. -/
theorem inf'_id_eq_cinfₛ [ConditionallyCompleteLattice α] (s : Finset α) (H) :
    s.inf' H id = infₛ s :=
  @sup'_id_eq_csupₛ αᵒᵈ _ _ H
#align finset.inf'_id_eq_cInf Finset.inf'_id_eq_cinfₛ

end Finset

