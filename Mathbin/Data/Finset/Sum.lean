/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.finset.sum
! leanprover-community/mathlib commit 2705404e701abc6b3127da906f40bae062a169c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Multiset.Sum
import Mathbin.Data.Finset.Card

/-!
# Disjoint sum of finsets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the disjoint sum of two finsets as `finset (α ⊕ β)`. Beware not to confuse with
the `finset.sum` operation which computes the additive sum.

## Main declarations

* `finset.disj_sum`: `s.disj_sum t` is the disjoint sum of `s` and `t`.
-/


open Function Multiset Sum

namespace Finset

variable {α β : Type _} (s : Finset α) (t : Finset β)

#print Finset.disjSum /-
/-- Disjoint sum of finsets. -/
def disjSum : Finset (Sum α β) :=
  ⟨s.1.disjSum t.1, s.2.disjSum t.2⟩
#align finset.disj_sum Finset.disjSum
-/

/- warning: finset.val_disj_sum -> Finset.val_disjSum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Finset.{u1} α) (t : Finset.{u2} β), Eq.{succ (max u1 u2)} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.val.{max u1 u2} (Sum.{u1, u2} α β) (Finset.disjSum.{u1, u2} α β s t)) (Multiset.disjSum.{u1, u2} α β (Finset.val.{u1} α s) (Finset.val.{u2} β t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Finset.{u2} α) (t : Finset.{u1} β), Eq.{max (succ u2) (succ u1)} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) (Finset.val.{max u2 u1} (Sum.{u2, u1} α β) (Finset.disjSum.{u2, u1} α β s t)) (Multiset.disjSum.{u2, u1} α β (Finset.val.{u2} α s) (Finset.val.{u1} β t))
Case conversion may be inaccurate. Consider using '#align finset.val_disj_sum Finset.val_disjSumₓ'. -/
@[simp]
theorem val_disjSum : (s.disjSum t).1 = s.1.disjSum t.1 :=
  rfl
#align finset.val_disj_sum Finset.val_disjSum

/- warning: finset.empty_disj_sum -> Finset.empty_disjSum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (t : Finset.{u2} β), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.disjSum.{u1, u2} α β (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α)) t) (Finset.map.{u2, max u1 u2} β (Sum.{u1, u2} α β) (Function.Embedding.inr.{u1, u2} α β) t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (t : Finset.{u1} β), Eq.{max (succ u2) (succ u1)} (Finset.{max u1 u2} (Sum.{u2, u1} α β)) (Finset.disjSum.{u2, u1} α β (EmptyCollection.emptyCollection.{u2} (Finset.{u2} α) (Finset.instEmptyCollectionFinset.{u2} α)) t) (Finset.map.{u1, max u1 u2} β (Sum.{u2, u1} α β) (Function.Embedding.inr.{u2, u1} α β) t)
Case conversion may be inaccurate. Consider using '#align finset.empty_disj_sum Finset.empty_disjSumₓ'. -/
@[simp]
theorem empty_disjSum : (∅ : Finset α).disjSum t = t.map Embedding.inr :=
  val_inj.1 <| Multiset.zero_disjSum _
#align finset.empty_disj_sum Finset.empty_disjSum

/- warning: finset.disj_sum_empty -> Finset.disjSum_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Finset.{u1} α), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.disjSum.{u1, u2} α β s (EmptyCollection.emptyCollection.{u2} (Finset.{u2} β) (Finset.hasEmptyc.{u2} β))) (Finset.map.{u1, max u1 u2} α (Sum.{u1, u2} α β) (Function.Embedding.inl.{u1, u2} α β) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Finset.{u2} α), Eq.{max (succ u2) (succ u1)} (Finset.{max u1 u2} (Sum.{u2, u1} α β)) (Finset.disjSum.{u2, u1} α β s (EmptyCollection.emptyCollection.{u1} (Finset.{u1} β) (Finset.instEmptyCollectionFinset.{u1} β))) (Finset.map.{u2, max u1 u2} α (Sum.{u2, u1} α β) (Function.Embedding.inl.{u2, u1} α β) s)
Case conversion may be inaccurate. Consider using '#align finset.disj_sum_empty Finset.disjSum_emptyₓ'. -/
@[simp]
theorem disjSum_empty : s.disjSum (∅ : Finset β) = s.map Embedding.inl :=
  val_inj.1 <| Multiset.disjSum_zero _
#align finset.disj_sum_empty Finset.disjSum_empty

/- warning: finset.card_disj_sum -> Finset.card_disjSum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Finset.{u1} α) (t : Finset.{u2} β), Eq.{1} Nat (Finset.card.{max u1 u2} (Sum.{u1, u2} α β) (Finset.disjSum.{u1, u2} α β s t)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Finset.card.{u1} α s) (Finset.card.{u2} β t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Finset.{u2} α) (t : Finset.{u1} β), Eq.{1} Nat (Finset.card.{max u2 u1} (Sum.{u2, u1} α β) (Finset.disjSum.{u2, u1} α β s t)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Finset.card.{u2} α s) (Finset.card.{u1} β t))
Case conversion may be inaccurate. Consider using '#align finset.card_disj_sum Finset.card_disjSumₓ'. -/
@[simp]
theorem card_disjSum : (s.disjSum t).card = s.card + t.card :=
  Multiset.card_disjSum _ _
#align finset.card_disj_sum Finset.card_disjSum

/- warning: finset.disjoint_map_inl_map_inr -> Finset.disjoint_map_inl_map_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Finset.{u1} α) (t : Finset.{u2} β), Disjoint.{max u1 u2} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.partialOrder.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.orderBot.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.map.{u1, max u1 u2} α (Sum.{u1, u2} α β) (Function.Embedding.inl.{u1, u2} α β) s) (Finset.map.{u2, max u1 u2} β (Sum.{u1, u2} α β) (Function.Embedding.inr.{u1, u2} α β) t)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Finset.{u1} α) (t : Finset.{u2} β), Disjoint.{max u2 u1} (Finset.{max u2 u1} (Sum.{u1, u2} α β)) (Finset.partialOrder.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.map.{u1, max u2 u1} α (Sum.{u1, u2} α β) (Function.Embedding.inl.{u1, u2} α β) s) (Finset.map.{u2, max u1 u2} β (Sum.{u1, u2} α β) (Function.Embedding.inr.{u1, u2} α β) t)
Case conversion may be inaccurate. Consider using '#align finset.disjoint_map_inl_map_inr Finset.disjoint_map_inl_map_inrₓ'. -/
theorem disjoint_map_inl_map_inr : Disjoint (s.map Embedding.inl) (t.map Embedding.inr) :=
  by
  simp_rw [disjoint_left, mem_map]
  rintro x ⟨a, _, rfl⟩ ⟨b, _, ⟨⟩⟩
#align finset.disjoint_map_inl_map_inr Finset.disjoint_map_inl_map_inr

/- warning: finset.map_inl_disj_union_map_inr -> Finset.map_inl_disjUnion_map_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Finset.{u1} α) (t : Finset.{u2} β), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.disjUnion.{max u1 u2} (Sum.{u1, u2} α β) (Finset.map.{u1, max u1 u2} α (Sum.{u1, u2} α β) (Function.Embedding.inl.{u1, u2} α β) s) (Finset.map.{u2, max u1 u2} β (Sum.{u1, u2} α β) (Function.Embedding.inr.{u1, u2} α β) t) (Finset.disjoint_map_inl_map_inr.{u1, u2} α β s t)) (Finset.disjSum.{u1, u2} α β s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Finset.{u2} α) (t : Finset.{u1} β), Eq.{max (succ u2) (succ u1)} (Finset.{max u2 u1} (Sum.{u2, u1} α β)) (Finset.disjUnion.{max u2 u1} (Sum.{u2, u1} α β) (Finset.map.{u2, max u1 u2} α (Sum.{u2, u1} α β) (Function.Embedding.inl.{u2, u1} α β) s) (Finset.map.{u1, max u2 u1} β (Sum.{u2, u1} α β) (Function.Embedding.inr.{u2, u1} α β) t) (Finset.disjoint_map_inl_map_inr.{u2, u1} α β s t)) (Finset.disjSum.{u2, u1} α β s t)
Case conversion may be inaccurate. Consider using '#align finset.map_inl_disj_union_map_inr Finset.map_inl_disjUnion_map_inrₓ'. -/
@[simp]
theorem map_inl_disjUnion_map_inr :
    (s.map Embedding.inl).disjUnion (t.map Embedding.inr) (disjoint_map_inl_map_inr _ _) =
      s.disjSum t :=
  rfl
#align finset.map_inl_disj_union_map_inr Finset.map_inl_disjUnion_map_inr

variable {s t} {s₁ s₂ : Finset α} {t₁ t₂ : Finset β} {a : α} {b : β} {x : Sum α β}

/- warning: finset.mem_disj_sum -> Finset.mem_disjSum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {t : Finset.{u2} β} {x : Sum.{u1, u2} α β}, Iff (Membership.Mem.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.hasMem.{max u1 u2} (Sum.{u1, u2} α β)) x (Finset.disjSum.{u1, u2} α β s t)) (Or (Exists.{succ u1} α (fun (a : α) => And (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (Eq.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β) (Sum.inl.{u1, u2} α β a) x))) (Exists.{succ u2} β (fun (b : β) => And (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b t) (Eq.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β) (Sum.inr.{u1, u2} α β b) x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Finset.{u2} α} {t : Finset.{u1} β} {x : Sum.{u2, u1} α β}, Iff (Membership.mem.{max u2 u1, max u2 u1} (Sum.{u2, u1} α β) (Finset.{max u1 u2} (Sum.{u2, u1} α β)) (Finset.instMembershipFinset.{max u2 u1} (Sum.{u2, u1} α β)) x (Finset.disjSum.{u2, u1} α β s t)) (Or (Exists.{succ u2} α (fun (a : α) => And (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) (Eq.{max (succ u2) (succ u1)} (Sum.{u2, u1} α β) (Sum.inl.{u2, u1} α β a) x))) (Exists.{succ u1} β (fun (b : β) => And (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b t) (Eq.{max (succ u2) (succ u1)} (Sum.{u2, u1} α β) (Sum.inr.{u2, u1} α β b) x))))
Case conversion may be inaccurate. Consider using '#align finset.mem_disj_sum Finset.mem_disjSumₓ'. -/
theorem mem_disjSum : x ∈ s.disjSum t ↔ (∃ a, a ∈ s ∧ inl a = x) ∨ ∃ b, b ∈ t ∧ inr b = x :=
  Multiset.mem_disjSum
#align finset.mem_disj_sum Finset.mem_disjSum

#print Finset.inl_mem_disjSum /-
@[simp]
theorem inl_mem_disjSum : inl a ∈ s.disjSum t ↔ a ∈ s :=
  inl_mem_disjSum
#align finset.inl_mem_disj_sum Finset.inl_mem_disjSum
-/

#print Finset.inr_mem_disjSum /-
@[simp]
theorem inr_mem_disjSum : inr b ∈ s.disjSum t ↔ b ∈ t :=
  inr_mem_disjSum
#align finset.inr_mem_disj_sum Finset.inr_mem_disjSum
-/

/- warning: finset.disj_sum_mono -> Finset.disjSum_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s₁ : Finset.{u1} α} {s₂ : Finset.{u1} α} {t₁ : Finset.{u2} β} {t₂ : Finset.{u2} β}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s₁ s₂) -> (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) t₁ t₂) -> (HasSubset.Subset.{max u1 u2} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.hasSubset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.disjSum.{u1, u2} α β s₁ t₁) (Finset.disjSum.{u1, u2} α β s₂ t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α} {t₁ : Finset.{u1} β} {t₂ : Finset.{u1} β}, (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) s₁ s₂) -> (HasSubset.Subset.{u1} (Finset.{u1} β) (Finset.instHasSubsetFinset.{u1} β) t₁ t₂) -> (HasSubset.Subset.{max u2 u1} (Finset.{max u1 u2} (Sum.{u2, u1} α β)) (Finset.instHasSubsetFinset.{max u2 u1} (Sum.{u2, u1} α β)) (Finset.disjSum.{u2, u1} α β s₁ t₁) (Finset.disjSum.{u2, u1} α β s₂ t₂))
Case conversion may be inaccurate. Consider using '#align finset.disj_sum_mono Finset.disjSum_monoₓ'. -/
theorem disjSum_mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : s₁.disjSum t₁ ⊆ s₂.disjSum t₂ :=
  val_le_iff.1 <| disjSum_mono (val_le_iff.2 hs) (val_le_iff.2 ht)
#align finset.disj_sum_mono Finset.disjSum_mono

#print Finset.disjSum_mono_left /-
theorem disjSum_mono_left (t : Finset β) : Monotone fun s : Finset α => s.disjSum t :=
  fun s₁ s₂ hs => disjSum_mono hs Subset.rfl
#align finset.disj_sum_mono_left Finset.disjSum_mono_left
-/

/- warning: finset.disj_sum_mono_right -> Finset.disjSum_mono_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Finset.{u1} α), Monotone.{u2, max u1 u2} (Finset.{u2} β) (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (PartialOrder.toPreorder.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β)) (PartialOrder.toPreorder.{max u1 u2} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.partialOrder.{max u1 u2} (Sum.{u1, u2} α β))) (Finset.disjSum.{u1, u2} α β s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Finset.{u2} α), Monotone.{u1, max u2 u1} (Finset.{u1} β) (Finset.{max u1 u2} (Sum.{u2, u1} α β)) (PartialOrder.toPreorder.{u1} (Finset.{u1} β) (Finset.partialOrder.{u1} β)) (PartialOrder.toPreorder.{max u2 u1} (Finset.{max u1 u2} (Sum.{u2, u1} α β)) (Finset.partialOrder.{max u2 u1} (Sum.{u2, u1} α β))) (Finset.disjSum.{u2, u1} α β s)
Case conversion may be inaccurate. Consider using '#align finset.disj_sum_mono_right Finset.disjSum_mono_rightₓ'. -/
theorem disjSum_mono_right (s : Finset α) : Monotone (s.disjSum : Finset β → Finset (Sum α β)) :=
  fun t₁ t₂ => disjSum_mono Subset.rfl
#align finset.disj_sum_mono_right Finset.disjSum_mono_right

/- warning: finset.disj_sum_ssubset_disj_sum_of_ssubset_of_subset -> Finset.disjSum_ssubset_disjSum_of_ssubset_of_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s₁ : Finset.{u1} α} {s₂ : Finset.{u1} α} {t₁ : Finset.{u2} β} {t₂ : Finset.{u2} β}, (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.hasSsubset.{u1} α) s₁ s₂) -> (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) t₁ t₂) -> (HasSSubset.SSubset.{max u1 u2} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.hasSsubset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.disjSum.{u1, u2} α β s₁ t₁) (Finset.disjSum.{u1, u2} α β s₂ t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α} {t₁ : Finset.{u1} β} {t₂ : Finset.{u1} β}, (HasSSubset.SSubset.{u2} (Finset.{u2} α) (Finset.instHasSSubsetFinset.{u2} α) s₁ s₂) -> (HasSubset.Subset.{u1} (Finset.{u1} β) (Finset.instHasSubsetFinset.{u1} β) t₁ t₂) -> (HasSSubset.SSubset.{max u2 u1} (Finset.{max u1 u2} (Sum.{u2, u1} α β)) (Finset.instHasSSubsetFinset.{max u2 u1} (Sum.{u2, u1} α β)) (Finset.disjSum.{u2, u1} α β s₁ t₁) (Finset.disjSum.{u2, u1} α β s₂ t₂))
Case conversion may be inaccurate. Consider using '#align finset.disj_sum_ssubset_disj_sum_of_ssubset_of_subset Finset.disjSum_ssubset_disjSum_of_ssubset_of_subsetₓ'. -/
theorem disjSum_ssubset_disjSum_of_ssubset_of_subset (hs : s₁ ⊂ s₂) (ht : t₁ ⊆ t₂) :
    s₁.disjSum t₁ ⊂ s₂.disjSum t₂ :=
  val_lt_iff.1 <| disjSum_lt_disjSum_of_lt_of_le (val_lt_iff.2 hs) (val_le_iff.2 ht)
#align finset.disj_sum_ssubset_disj_sum_of_ssubset_of_subset Finset.disjSum_ssubset_disjSum_of_ssubset_of_subset

/- warning: finset.disj_sum_ssubset_disj_sum_of_subset_of_ssubset -> Finset.disjSum_ssubset_disjSum_of_subset_of_ssubset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s₁ : Finset.{u1} α} {s₂ : Finset.{u1} α} {t₁ : Finset.{u2} β} {t₂ : Finset.{u2} β}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s₁ s₂) -> (HasSSubset.SSubset.{u2} (Finset.{u2} β) (Finset.hasSsubset.{u2} β) t₁ t₂) -> (HasSSubset.SSubset.{max u1 u2} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.hasSsubset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.disjSum.{u1, u2} α β s₁ t₁) (Finset.disjSum.{u1, u2} α β s₂ t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α} {t₁ : Finset.{u1} β} {t₂ : Finset.{u1} β}, (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) s₁ s₂) -> (HasSSubset.SSubset.{u1} (Finset.{u1} β) (Finset.instHasSSubsetFinset.{u1} β) t₁ t₂) -> (HasSSubset.SSubset.{max u2 u1} (Finset.{max u1 u2} (Sum.{u2, u1} α β)) (Finset.instHasSSubsetFinset.{max u2 u1} (Sum.{u2, u1} α β)) (Finset.disjSum.{u2, u1} α β s₁ t₁) (Finset.disjSum.{u2, u1} α β s₂ t₂))
Case conversion may be inaccurate. Consider using '#align finset.disj_sum_ssubset_disj_sum_of_subset_of_ssubset Finset.disjSum_ssubset_disjSum_of_subset_of_ssubsetₓ'. -/
theorem disjSum_ssubset_disjSum_of_subset_of_ssubset (hs : s₁ ⊆ s₂) (ht : t₁ ⊂ t₂) :
    s₁.disjSum t₁ ⊂ s₂.disjSum t₂ :=
  val_lt_iff.1 <| disjSum_lt_disjSum_of_le_of_lt (val_le_iff.2 hs) (val_lt_iff.2 ht)
#align finset.disj_sum_ssubset_disj_sum_of_subset_of_ssubset Finset.disjSum_ssubset_disjSum_of_subset_of_ssubset

#print Finset.disjSum_strictMono_left /-
theorem disjSum_strictMono_left (t : Finset β) : StrictMono fun s : Finset α => s.disjSum t :=
  fun s₁ s₂ hs => disjSum_ssubset_disjSum_of_ssubset_of_subset hs Subset.rfl
#align finset.disj_sum_strict_mono_left Finset.disjSum_strictMono_left
-/

/- warning: finset.disj_sum_strict_mono_right -> Finset.disj_sum_strictMono_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Finset.{u1} α), StrictMono.{u2, max u1 u2} (Finset.{u2} β) (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (PartialOrder.toPreorder.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β)) (PartialOrder.toPreorder.{max u1 u2} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.partialOrder.{max u1 u2} (Sum.{u1, u2} α β))) (Finset.disjSum.{u1, u2} α β s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Finset.{u2} α), StrictMono.{u1, max u2 u1} (Finset.{u1} β) (Finset.{max u1 u2} (Sum.{u2, u1} α β)) (PartialOrder.toPreorder.{u1} (Finset.{u1} β) (Finset.partialOrder.{u1} β)) (PartialOrder.toPreorder.{max u2 u1} (Finset.{max u1 u2} (Sum.{u2, u1} α β)) (Finset.partialOrder.{max u2 u1} (Sum.{u2, u1} α β))) (Finset.disjSum.{u2, u1} α β s)
Case conversion may be inaccurate. Consider using '#align finset.disj_sum_strict_mono_right Finset.disj_sum_strictMono_rightₓ'. -/
theorem disj_sum_strictMono_right (s : Finset α) :
    StrictMono (s.disjSum : Finset β → Finset (Sum α β)) := fun s₁ s₂ =>
  disjSum_ssubset_disjSum_of_subset_of_ssubset Subset.rfl
#align finset.disj_sum_strict_mono_right Finset.disj_sum_strictMono_right

end Finset

