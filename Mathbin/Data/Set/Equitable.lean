/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta

! This file was ported from Lean 3 source module data.set.equitable
! leanprover-community/mathlib commit 2705404e701abc6b3127da906f40bae062a169c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Order
import Mathbin.Data.Nat.Basic

/-!
# Equitable functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines equitable functions.

A function `f` is equitable on a set `s` if `f a₁ ≤ f a₂ + 1` for all `a₁, a₂ ∈ s`. This is mostly
useful when the codomain of `f` is `ℕ` or `ℤ` (or more generally a successor order).

## TODO

`ℕ` can be replaced by any `succ_order` + `conditionally_complete_monoid`, but we don't have the
latter yet.
-/


open BigOperators

variable {α β : Type _}

namespace Set

#print Set.EquitableOn /-
/-- A set is equitable if no element value is more than one bigger than another. -/
def EquitableOn [LE β] [Add β] [One β] (s : Set α) (f : α → β) : Prop :=
  ∀ ⦃a₁ a₂⦄, a₁ ∈ s → a₂ ∈ s → f a₁ ≤ f a₂ + 1
#align set.equitable_on Set.EquitableOn
-/

#print Set.equitableOn_empty /-
@[simp]
theorem equitableOn_empty [LE β] [Add β] [One β] (f : α → β) : EquitableOn ∅ f := fun a _ ha =>
  (Set.not_mem_empty _ ha).elim
#align set.equitable_on_empty Set.equitableOn_empty
-/

#print Set.equitableOn_iff_exists_le_le_add_one /-
theorem equitableOn_iff_exists_le_le_add_one {s : Set α} {f : α → ℕ} :
    s.EquitableOn f ↔ ∃ b, ∀ a ∈ s, b ≤ f a ∧ f a ≤ b + 1 :=
  by
  refine' ⟨_, fun ⟨b, hb⟩ x y hx hy => (hb x hx).2.trans (add_le_add_right (hb y hy).1 _)⟩
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · simp
  intro hs
  by_cases h : ∀ y ∈ s, f x ≤ f y
  · exact ⟨f x, fun y hy => ⟨h _ hy, hs hy hx⟩⟩
  push_neg  at h
  obtain ⟨w, hw, hwx⟩ := h
  refine' ⟨f w, fun y hy => ⟨Nat.le_of_succ_le_succ _, hs hy hw⟩⟩
  rw [(Nat.succ_le_of_lt hwx).antisymm (hs hx hw)]
  exact hs hx hy
#align set.equitable_on_iff_exists_le_le_add_one Set.equitableOn_iff_exists_le_le_add_one
-/

#print Set.equitableOn_iff_exists_image_subset_icc /-
theorem equitableOn_iff_exists_image_subset_icc {s : Set α} {f : α → ℕ} :
    s.EquitableOn f ↔ ∃ b, f '' s ⊆ Icc b (b + 1) := by
  simpa only [image_subset_iff] using equitable_on_iff_exists_le_le_add_one
#align set.equitable_on_iff_exists_image_subset_Icc Set.equitableOn_iff_exists_image_subset_icc
-/

#print Set.equitableOn_iff_exists_eq_eq_add_one /-
theorem equitableOn_iff_exists_eq_eq_add_one {s : Set α} {f : α → ℕ} :
    s.EquitableOn f ↔ ∃ b, ∀ a ∈ s, f a = b ∨ f a = b + 1 := by
  simp_rw [equitable_on_iff_exists_le_le_add_one, Nat.le_and_le_add_one_iff]
#align set.equitable_on_iff_exists_eq_eq_add_one Set.equitableOn_iff_exists_eq_eq_add_one
-/

section OrderedSemiring

variable [OrderedSemiring β]

/- warning: set.subsingleton.equitable_on -> Set.Subsingleton.equitableOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : OrderedSemiring.{u2} β] {s : Set.{u1} α}, (Set.Subsingleton.{u1} α s) -> (forall (f : α -> β), Set.EquitableOn.{u1, u2} α β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (OrderedAddCommMonoid.toPartialOrder.{u2} β (OrderedSemiring.toOrderedAddCommMonoid.{u2} β _inst_1)))) (Distrib.toHasAdd.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β (OrderedSemiring.toSemiring.{u2} β _inst_1))))) (AddMonoidWithOne.toOne.{u2} β (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} β (NonAssocSemiring.toAddCommMonoidWithOne.{u2} β (Semiring.toNonAssocSemiring.{u2} β (OrderedSemiring.toSemiring.{u2} β _inst_1))))) s f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : OrderedSemiring.{u1} β] {s : Set.{u2} α}, (Set.Subsingleton.{u2} α s) -> (forall (f : α -> β), Set.EquitableOn.{u2, u1} α β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (OrderedSemiring.toPartialOrder.{u1} β _inst_1))) (Distrib.toAdd.{u1} β (NonUnitalNonAssocSemiring.toDistrib.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β (OrderedSemiring.toSemiring.{u1} β _inst_1))))) (Semiring.toOne.{u1} β (OrderedSemiring.toSemiring.{u1} β _inst_1)) s f)
Case conversion may be inaccurate. Consider using '#align set.subsingleton.equitable_on Set.Subsingleton.equitableOnₓ'. -/
theorem Subsingleton.equitableOn {s : Set α} (hs : s.Subsingleton) (f : α → β) : s.EquitableOn f :=
  fun i j hi hj => by
  rw [hs hi hj]
  exact le_add_of_nonneg_right zero_le_one
#align set.subsingleton.equitable_on Set.Subsingleton.equitableOn

/- warning: set.equitable_on_singleton -> Set.equitableOn_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : OrderedSemiring.{u2} β] (a : α) (f : α -> β), Set.EquitableOn.{u1, u2} α β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (OrderedAddCommMonoid.toPartialOrder.{u2} β (OrderedSemiring.toOrderedAddCommMonoid.{u2} β _inst_1)))) (Distrib.toHasAdd.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β (OrderedSemiring.toSemiring.{u2} β _inst_1))))) (AddMonoidWithOne.toOne.{u2} β (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} β (NonAssocSemiring.toAddCommMonoidWithOne.{u2} β (Semiring.toNonAssocSemiring.{u2} β (OrderedSemiring.toSemiring.{u2} β _inst_1))))) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : OrderedSemiring.{u1} β] (a : α) (f : α -> β), Set.EquitableOn.{u2, u1} α β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (OrderedSemiring.toPartialOrder.{u1} β _inst_1))) (Distrib.toAdd.{u1} β (NonUnitalNonAssocSemiring.toDistrib.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β (OrderedSemiring.toSemiring.{u1} β _inst_1))))) (Semiring.toOne.{u1} β (OrderedSemiring.toSemiring.{u1} β _inst_1)) (Singleton.singleton.{u2, u2} α (Set.{u2} α) (Set.instSingletonSet.{u2} α) a) f
Case conversion may be inaccurate. Consider using '#align set.equitable_on_singleton Set.equitableOn_singletonₓ'. -/
theorem equitableOn_singleton (a : α) (f : α → β) : Set.EquitableOn {a} f :=
  Set.subsingleton_singleton.EquitableOn f
#align set.equitable_on_singleton Set.equitableOn_singleton

end OrderedSemiring

end Set

open Set

namespace Finset

variable {s : Finset α} {f : α → ℕ} {a : α}

#print Finset.equitableOn_iff_le_le_add_one /-
theorem equitableOn_iff_le_le_add_one :
    EquitableOn (s : Set α) f ↔
      ∀ a ∈ s, (∑ i in s, f i) / s.card ≤ f a ∧ f a ≤ (∑ i in s, f i) / s.card + 1 :=
  by
  rw [Set.equitableOn_iff_exists_le_le_add_one]
  refine' ⟨_, fun h => ⟨_, h⟩⟩
  rintro ⟨b, hb⟩
  by_cases h : ∀ a ∈ s, f a = b + 1
  · intro a ha
    rw [h _ ha, sum_const_nat h, Nat.mul_div_cancel_left _ (card_pos.2 ⟨a, ha⟩)]
    exact ⟨le_rfl, Nat.le_succ _⟩
  push_neg  at h
  obtain ⟨x, hx₁, hx₂⟩ := h
  suffices h : b = (∑ i in s, f i) / s.card
  · simp_rw [← h]
    apply hb
  symm
  refine'
    Nat.div_eq_of_lt_le (le_trans (by simp [mul_comm]) (sum_le_sum fun a ha => (hb a ha).1))
      ((sum_lt_sum (fun a ha => (hb a ha).2) ⟨_, hx₁, (hb _ hx₁).2.lt_of_ne hx₂⟩).trans_le _)
  rw [mul_comm, sum_const_nat]
  exact fun _ _ => rfl
#align finset.equitable_on_iff_le_le_add_one Finset.equitableOn_iff_le_le_add_one
-/

#print Finset.EquitableOn.le /-
theorem EquitableOn.le (h : EquitableOn (s : Set α) f) (ha : a ∈ s) :
    (∑ i in s, f i) / s.card ≤ f a :=
  (equitableOn_iff_le_le_add_one.1 h a ha).1
#align finset.equitable_on.le Finset.EquitableOn.le
-/

#print Finset.EquitableOn.le_add_one /-
theorem EquitableOn.le_add_one (h : EquitableOn (s : Set α) f) (ha : a ∈ s) :
    f a ≤ (∑ i in s, f i) / s.card + 1 :=
  (equitableOn_iff_le_le_add_one.1 h a ha).2
#align finset.equitable_on.le_add_one Finset.EquitableOn.le_add_one
-/

#print Finset.equitableOn_iff /-
theorem equitableOn_iff :
    EquitableOn (s : Set α) f ↔
      ∀ a ∈ s, f a = (∑ i in s, f i) / s.card ∨ f a = (∑ i in s, f i) / s.card + 1 :=
  by simp_rw [equitable_on_iff_le_le_add_one, Nat.le_and_le_add_one_iff]
#align finset.equitable_on_iff Finset.equitableOn_iff
-/

end Finset

