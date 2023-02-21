/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.finset.pairwise
! leanprover-community/mathlib commit bd9851ca476957ea4549eb19b40e7b5ade9428cc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Lattice

/-!
# Relations holding pairwise on finite sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove a few results about the interaction of `set.pairwise_disjoint` and `finset`,
as well as the interaction of `list.pairwise disjoint` and the condition of
`disjoint` on `list.to_finset`, in `set` form.
-/


open Finset

variable {α ι ι' : Type _}

instance [DecidableEq α] {r : α → α → Prop} [DecidableRel r] {s : Finset α} :
    Decidable ((s : Set α).Pairwise r) :=
  decidable_of_iff' (∀ a ∈ s, ∀ b ∈ s, a ≠ b → r a b) Iff.rfl

/- warning: finset.pairwise_disjoint_range_singleton -> Finset.pairwiseDisjoint_range_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Set.PairwiseDisjoint.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) (Set.range.{u1, succ u1} (Finset.{u1} α) α (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α))) (id.{succ u1} (Finset.{u1} α))
but is expected to have type
  forall {α : Type.{u1}}, Set.PairwiseDisjoint.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (Set.range.{u1, succ u1} (Finset.{u1} α) α (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α))) (id.{succ u1} (Finset.{u1} α))
Case conversion may be inaccurate. Consider using '#align finset.pairwise_disjoint_range_singleton Finset.pairwiseDisjoint_range_singletonₓ'. -/
theorem Finset.pairwiseDisjoint_range_singleton :
    (Set.range (singleton : α → Finset α)).PairwiseDisjoint id :=
  by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h
  exact disjoint_singleton.2 (ne_of_apply_ne _ h)
#align finset.pairwise_disjoint_range_singleton Finset.pairwiseDisjoint_range_singleton

namespace Set

/- warning: set.pairwise_disjoint.elim_finset -> Set.PairwiseDisjoint.elim_finset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {s : Set.{u2} ι} {f : ι -> (Finset.{u1} α)}, (Set.PairwiseDisjoint.{u1, u2} (Finset.{u1} α) ι (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s f) -> (forall {i : ι} {j : ι}, (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) -> (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) j s) -> (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (f i)) -> (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (f j)) -> (Eq.{succ u2} ι i j)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} {s : Set.{u2} ι} {f : ι -> (Finset.{u1} α)}, (Set.PairwiseDisjoint.{u1, u2} (Finset.{u1} α) ι (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s f) -> (forall {i : ι} {j : ι}, (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) -> (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) j s) -> (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a (f i)) -> (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a (f j)) -> (Eq.{succ u2} ι i j)))
Case conversion may be inaccurate. Consider using '#align set.pairwise_disjoint.elim_finset Set.PairwiseDisjoint.elim_finsetₓ'. -/
theorem PairwiseDisjoint.elim_finset {s : Set ι} {f : ι → Finset α} (hs : s.PairwiseDisjoint f)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (a : α) (hai : a ∈ f i) (haj : a ∈ f j) : i = j :=
  hs.elim hi hj (Finset.not_disjoint_iff.2 ⟨a, hai, haj⟩)
#align set.pairwise_disjoint.elim_finset Set.PairwiseDisjoint.elim_finset

#print Set.PairwiseDisjoint.image_finset_of_le /-
theorem PairwiseDisjoint.image_finset_of_le [DecidableEq ι] [SemilatticeInf α] [OrderBot α]
    {s : Finset ι} {f : ι → α} (hs : (s : Set ι).PairwiseDisjoint f) {g : ι → ι}
    (hf : ∀ a, f (g a) ≤ f a) : (s.image g : Set ι).PairwiseDisjoint f :=
  by
  rw [coe_image]
  exact hs.image_of_le hf
#align set.pairwise_disjoint.image_finset_of_le Set.PairwiseDisjoint.image_finset_of_le
-/

variable [Lattice α] [OrderBot α]

#print Set.PairwiseDisjoint.bunionᵢ_finset /-
/-- Bind operation for `set.pairwise_disjoint`. In a complete lattice, you can use
`set.pairwise_disjoint.bUnion`. -/
theorem PairwiseDisjoint.bunionᵢ_finset {s : Set ι'} {g : ι' → Finset ι} {f : ι → α}
    (hs : s.PairwiseDisjoint fun i' : ι' => (g i').sup f)
    (hg : ∀ i ∈ s, (g i : Set ι).PairwiseDisjoint f) : (⋃ i ∈ s, ↑(g i)).PairwiseDisjoint f :=
  by
  rintro a ha b hb hab
  simp_rw [Set.mem_unionᵢ] at ha hb
  obtain ⟨c, hc, ha⟩ := ha
  obtain ⟨d, hd, hb⟩ := hb
  obtain hcd | hcd := eq_or_ne (g c) (g d)
  · exact hg d hd (by rwa [hcd] at ha) hb hab
  · exact (hs hc hd (ne_of_apply_ne _ hcd)).mono (Finset.le_sup ha) (Finset.le_sup hb)
#align set.pairwise_disjoint.bUnion_finset Set.PairwiseDisjoint.bunionᵢ_finset
-/

end Set

namespace List

variable {β : Type _} [DecidableEq α] {r : α → α → Prop} {l : List α}

#print List.pairwise_of_coe_toFinset_pairwise /-
theorem pairwise_of_coe_toFinset_pairwise (hl : (l.toFinset : Set α).Pairwise r) (hn : l.Nodup) :
    l.Pairwise r := by
  rw [coe_to_finset] at hl
  exact hn.pairwise_of_set_pairwise hl
#align list.pairwise_of_coe_to_finset_pairwise List.pairwise_of_coe_toFinset_pairwise
-/

#print List.pairwise_iff_coe_toFinset_pairwise /-
theorem pairwise_iff_coe_toFinset_pairwise (hn : l.Nodup) (hs : Symmetric r) :
    (l.toFinset : Set α).Pairwise r ↔ l.Pairwise r :=
  by
  rw [coe_to_finset, hn.pairwise_coe]
  exact ⟨hs⟩
#align list.pairwise_iff_coe_to_finset_pairwise List.pairwise_iff_coe_toFinset_pairwise
-/

/- warning: list.pairwise_disjoint_of_coe_to_finset_pairwise_disjoint -> List.pairwise_disjoint_of_coe_toFinset_pairwiseDisjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_2 : SemilatticeInf.{u1} α] [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_2)))] [_inst_4 : DecidableEq.{succ u2} ι] {l : List.{u2} ι} {f : ι -> α}, (Set.PairwiseDisjoint.{u1, u2} α ι (SemilatticeInf.toPartialOrder.{u1} α _inst_2) _inst_3 ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} ι) (Set.{u2} ι) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} ι) (Set.{u2} ι) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} ι) (Set.{u2} ι) (Finset.Set.hasCoeT.{u2} ι))) (List.toFinset.{u2} ι (fun (a : ι) (b : ι) => _inst_4 a b) l)) f) -> (List.Nodup.{u2} ι l) -> (List.Pairwise.{u2} ι (Function.onFun.{succ u2, succ u1, 1} ι α Prop (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_2) _inst_3) f) l)
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_2 : SemilatticeInf.{u2} α] [_inst_3 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_2)))] [_inst_4 : DecidableEq.{succ u1} ι] {l : List.{u1} ι} {f : ι -> α}, (Set.PairwiseDisjoint.{u2, u1} α ι (SemilatticeInf.toPartialOrder.{u2} α _inst_2) _inst_3 (Finset.toSet.{u1} ι (List.toFinset.{u1} ι (fun (a : ι) (b : ι) => _inst_4 a b) l)) f) -> (List.Nodup.{u1} ι l) -> (List.Pairwise.{u1} ι (Function.onFun.{succ u1, succ u2, 1} ι α Prop (Disjoint.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_2) _inst_3) f) l)
Case conversion may be inaccurate. Consider using '#align list.pairwise_disjoint_of_coe_to_finset_pairwise_disjoint List.pairwise_disjoint_of_coe_toFinset_pairwiseDisjointₓ'. -/
theorem pairwise_disjoint_of_coe_toFinset_pairwiseDisjoint {α ι} [SemilatticeInf α] [OrderBot α]
    [DecidableEq ι] {l : List ι} {f : ι → α} (hl : (l.toFinset : Set ι).PairwiseDisjoint f)
    (hn : l.Nodup) : l.Pairwise (Disjoint on f) :=
  pairwise_of_coe_toFinset_pairwise hl hn
#align list.pairwise_disjoint_of_coe_to_finset_pairwise_disjoint List.pairwise_disjoint_of_coe_toFinset_pairwiseDisjoint

/- warning: list.pairwise_disjoint_iff_coe_to_finset_pairwise_disjoint -> List.pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_2 : SemilatticeInf.{u1} α] [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_2)))] [_inst_4 : DecidableEq.{succ u2} ι] {l : List.{u2} ι} {f : ι -> α}, (List.Nodup.{u2} ι l) -> (Iff (Set.PairwiseDisjoint.{u1, u2} α ι (SemilatticeInf.toPartialOrder.{u1} α _inst_2) _inst_3 ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} ι) (Set.{u2} ι) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} ι) (Set.{u2} ι) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} ι) (Set.{u2} ι) (Finset.Set.hasCoeT.{u2} ι))) (List.toFinset.{u2} ι (fun (a : ι) (b : ι) => _inst_4 a b) l)) f) (List.Pairwise.{u2} ι (Function.onFun.{succ u2, succ u1, 1} ι α Prop (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_2) _inst_3) f) l))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_2 : SemilatticeInf.{u2} α] [_inst_3 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_2)))] [_inst_4 : DecidableEq.{succ u1} ι] {l : List.{u1} ι} {f : ι -> α}, (List.Nodup.{u1} ι l) -> (Iff (Set.PairwiseDisjoint.{u2, u1} α ι (SemilatticeInf.toPartialOrder.{u2} α _inst_2) _inst_3 (Finset.toSet.{u1} ι (List.toFinset.{u1} ι (fun (a : ι) (b : ι) => _inst_4 a b) l)) f) (List.Pairwise.{u1} ι (Function.onFun.{succ u1, succ u2, 1} ι α Prop (Disjoint.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_2) _inst_3) f) l))
Case conversion may be inaccurate. Consider using '#align list.pairwise_disjoint_iff_coe_to_finset_pairwise_disjoint List.pairwiseDisjoint_iff_coe_toFinset_pairwise_disjointₓ'. -/
theorem pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint {α ι} [SemilatticeInf α] [OrderBot α]
    [DecidableEq ι] {l : List ι} {f : ι → α} (hn : l.Nodup) :
    (l.toFinset : Set ι).PairwiseDisjoint f ↔ l.Pairwise (Disjoint on f) :=
  pairwise_iff_coe_toFinset_pairwise hn (symmetric_disjoint.comap f)
#align list.pairwise_disjoint_iff_coe_to_finset_pairwise_disjoint List.pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint

end List

