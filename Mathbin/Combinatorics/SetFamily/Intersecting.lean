/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module combinatorics.set_family.intersecting
! leanprover-community/mathlib commit 48085f140e684306f9e7da907cd5932056d1aded
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Card
import Mathbin.Order.UpperLower.Basic

/-!
# Intersecting families

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines intersecting families and proves their basic properties.

## Main declarations

* `set.intersecting`: Predicate for a set of elements in a generalized boolean algebra to be an
  intersecting family.
* `set.intersecting.card_le`: An intersecting family can only take up to half the elements, because
  `a` and `aᶜ` cannot simultaneously be in it.
* `set.intersecting.is_max_iff_card_eq`: Any maximal intersecting family takes up half the elements.

## References

* [D. J. Kleitman, *Families of non-disjoint subsets*][kleitman1966]
-/


open Finset

variable {α : Type _}

namespace Set

section SemilatticeInf

variable [SemilatticeInf α] [OrderBot α] {s t : Set α} {a b c : α}

#print Set.Intersecting /-
/-- A set family is intersecting if every pair of elements is non-disjoint. -/
def Intersecting (s : Set α) : Prop :=
  ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → ¬Disjoint a b
#align set.intersecting Set.Intersecting
-/

#print Set.Intersecting.mono /-
@[mono]
theorem Intersecting.mono (h : t ⊆ s) (hs : s.Intersecting) : t.Intersecting := fun a ha b hb =>
  hs (h ha) (h hb)
#align set.intersecting.mono Set.Intersecting.mono
-/

/- warning: set.intersecting.not_bot_mem -> Set.Intersecting.not_bot_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Set.{u1} α}, (Set.Intersecting.{u1} α _inst_1 _inst_2 s) -> (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2)) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Set.{u1} α}, (Set.Intersecting.{u1} α _inst_1 _inst_2 s) -> (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2)) s))
Case conversion may be inaccurate. Consider using '#align set.intersecting.not_bot_mem Set.Intersecting.not_bot_memₓ'. -/
theorem Intersecting.not_bot_mem (hs : s.Intersecting) : ⊥ ∉ s := fun h => hs h h disjoint_bot_left
#align set.intersecting.not_bot_mem Set.Intersecting.not_bot_mem

/- warning: set.intersecting.ne_bot -> Set.Intersecting.ne_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Set.{u1} α} {a : α}, (Set.Intersecting.{u1} α _inst_1 _inst_2 s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (Ne.{succ u1} α a (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Set.{u1} α} {a : α}, (Set.Intersecting.{u1} α _inst_1 _inst_2 s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (Ne.{succ u1} α a (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2)))
Case conversion may be inaccurate. Consider using '#align set.intersecting.ne_bot Set.Intersecting.ne_botₓ'. -/
theorem Intersecting.ne_bot (hs : s.Intersecting) (ha : a ∈ s) : a ≠ ⊥ :=
  ne_of_mem_of_not_mem ha hs.not_bot_mem
#align set.intersecting.ne_bot Set.Intersecting.ne_bot

#print Set.intersecting_empty /-
theorem intersecting_empty : (∅ : Set α).Intersecting := fun _ => False.elim
#align set.intersecting_empty Set.intersecting_empty
-/

/- warning: set.intersecting_singleton -> Set.intersecting_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {a : α}, Iff (Set.Intersecting.{u1} α _inst_1 _inst_2 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)) (Ne.{succ u1} α a (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {a : α}, Iff (Set.Intersecting.{u1} α _inst_1 _inst_2 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a)) (Ne.{succ u1} α a (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2)))
Case conversion may be inaccurate. Consider using '#align set.intersecting_singleton Set.intersecting_singletonₓ'. -/
@[simp]
theorem intersecting_singleton : ({a} : Set α).Intersecting ↔ a ≠ ⊥ := by simp [intersecting]
#align set.intersecting_singleton Set.intersecting_singleton

/- warning: set.intersecting.insert -> Set.Intersecting.insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Set.{u1} α} {a : α}, (Set.Intersecting.{u1} α _inst_1 _inst_2 s) -> (Ne.{succ u1} α a (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2))) -> (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (Not (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1) _inst_2 a b))) -> (Set.Intersecting.{u1} α _inst_1 _inst_2 (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Set.{u1} α} {a : α}, (Set.Intersecting.{u1} α _inst_1 _inst_2 s) -> (Ne.{succ u1} α a (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2))) -> (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (Not (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1) _inst_2 a b))) -> (Set.Intersecting.{u1} α _inst_1 _inst_2 (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s))
Case conversion may be inaccurate. Consider using '#align set.intersecting.insert Set.Intersecting.insertₓ'. -/
theorem Intersecting.insert (hs : s.Intersecting) (ha : a ≠ ⊥) (h : ∀ b ∈ s, ¬Disjoint a b) :
    (insert a s).Intersecting := by
  rintro b (rfl | hb) c (rfl | hc)
  · rwa [disjoint_self]
  · exact h _ hc
  · exact fun H => h _ hb H.symm
  · exact hs hb hc
#align set.intersecting.insert Set.Intersecting.insert

/- warning: set.intersecting_insert -> Set.intersecting_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Set.{u1} α} {a : α}, Iff (Set.Intersecting.{u1} α _inst_1 _inst_2 (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)) (And (Set.Intersecting.{u1} α _inst_1 _inst_2 s) (And (Ne.{succ u1} α a (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2))) (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (Not (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1) _inst_2 a b)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Set.{u1} α} {a : α}, Iff (Set.Intersecting.{u1} α _inst_1 _inst_2 (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s)) (And (Set.Intersecting.{u1} α _inst_1 _inst_2 s) (And (Ne.{succ u1} α a (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2))) (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (Not (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1) _inst_2 a b)))))
Case conversion may be inaccurate. Consider using '#align set.intersecting_insert Set.intersecting_insertₓ'. -/
theorem intersecting_insert :
    (insert a s).Intersecting ↔ s.Intersecting ∧ a ≠ ⊥ ∧ ∀ b ∈ s, ¬Disjoint a b :=
  ⟨fun h =>
    ⟨h.mono <| subset_insert _ _, h.ne_bot <| mem_insert _ _, fun b hb =>
      h (mem_insert _ _) <| mem_insert_of_mem _ hb⟩,
    fun h => h.1.insert h.2.1 h.2.2⟩
#align set.intersecting_insert Set.intersecting_insert

/- warning: set.intersecting_iff_pairwise_not_disjoint -> Set.intersecting_iff_pairwise_not_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Set.{u1} α}, Iff (Set.Intersecting.{u1} α _inst_1 _inst_2 s) (And (Set.Pairwise.{u1} α s (fun (a : α) (b : α) => Not (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1) _inst_2 a b))) (Ne.{succ u1} (Set.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Set.{u1} α}, Iff (Set.Intersecting.{u1} α _inst_1 _inst_2 s) (And (Set.Pairwise.{u1} α s (fun (a : α) (b : α) => Not (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1) _inst_2 a b))) (Ne.{succ u1} (Set.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2)))))
Case conversion may be inaccurate. Consider using '#align set.intersecting_iff_pairwise_not_disjoint Set.intersecting_iff_pairwise_not_disjointₓ'. -/
theorem intersecting_iff_pairwise_not_disjoint :
    s.Intersecting ↔ (s.Pairwise fun a b => ¬Disjoint a b) ∧ s ≠ {⊥} :=
  by
  refine' ⟨fun h => ⟨fun a ha b hb _ => h ha hb, _⟩, fun h a ha b hb hab => _⟩
  · rintro rfl
    exact intersecting_singleton.1 h rfl
  · have := h.1.Eq ha hb (Classical.not_not.2 hab)
    rw [this, disjoint_self] at hab
    rw [hab] at hb
    exact
      h.2
        (eq_singleton_iff_unique_mem.2
          ⟨hb, fun c hc => not_ne_iff.1 fun H => h.1 hb hc H.symm disjoint_bot_left⟩)
#align set.intersecting_iff_pairwise_not_disjoint Set.intersecting_iff_pairwise_not_disjoint

/- warning: set.subsingleton.intersecting -> Set.Subsingleton.intersecting is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Set.{u1} α}, (Set.Subsingleton.{u1} α s) -> (Iff (Set.Intersecting.{u1} α _inst_1 _inst_2 s) (Ne.{succ u1} (Set.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Set.{u1} α}, (Set.Subsingleton.{u1} α s) -> (Iff (Set.Intersecting.{u1} α _inst_1 _inst_2 s) (Ne.{succ u1} (Set.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2)))))
Case conversion may be inaccurate. Consider using '#align set.subsingleton.intersecting Set.Subsingleton.intersectingₓ'. -/
protected theorem Subsingleton.intersecting (hs : s.Subsingleton) : s.Intersecting ↔ s ≠ {⊥} :=
  intersecting_iff_pairwise_not_disjoint.trans <| and_iff_right <| hs.Pairwise _
#align set.subsingleton.intersecting Set.Subsingleton.intersecting

#print Set.intersecting_iff_eq_empty_of_subsingleton /-
theorem intersecting_iff_eq_empty_of_subsingleton [Subsingleton α] (s : Set α) :
    s.Intersecting ↔ s = ∅ :=
  by
  refine'
    subsingleton_of_subsingleton.intersecting.trans
      ⟨not_imp_comm.2 fun h => subsingleton_of_subsingleton.eq_singleton_of_mem _, _⟩
  · obtain ⟨a, ha⟩ := nonempty_iff_ne_empty.2 h
    rwa [Subsingleton.elim ⊥ a]
  · rintro rfl
    exact (Set.singleton_nonempty _).ne_empty.symm
#align set.intersecting_iff_eq_empty_of_subsingleton Set.intersecting_iff_eq_empty_of_subsingleton
-/

#print Set.Intersecting.isUpperSet /-
/-- Maximal intersecting families are upper sets. -/
protected theorem Intersecting.isUpperSet (hs : s.Intersecting)
    (h : ∀ t : Set α, t.Intersecting → s ⊆ t → s = t) : IsUpperSet s := by
  classical
    rintro a b hab ha
    rw [h (insert b s) _ (subset_insert _ _)]
    · exact mem_insert _ _
    exact
      hs.insert (mt (eq_bot_mono hab) <| hs.ne_bot ha) fun c hc hbc => hs ha hc <| hbc.mono_left hab
#align set.intersecting.is_upper_set Set.Intersecting.isUpperSet
-/

#print Set.Intersecting.isUpperSet' /-
/-- Maximal intersecting families are upper sets. Finset version. -/
theorem Intersecting.isUpperSet' {s : Finset α} (hs : (s : Set α).Intersecting)
    (h : ∀ t : Finset α, (t : Set α).Intersecting → s ⊆ t → s = t) : IsUpperSet (s : Set α) := by
  classical
    rintro a b hab ha
    rw [h (insert b s) _ (Finset.subset_insert _ _)]
    · exact mem_insert_self _ _
    rw [coe_insert]
    exact
      hs.insert (mt (eq_bot_mono hab) <| hs.ne_bot ha) fun c hc hbc => hs ha hc <| hbc.mono_left hab
#align set.intersecting.is_upper_set' Set.Intersecting.isUpperSet'
-/

end SemilatticeInf

/- warning: set.intersecting.exists_mem_set -> Set.Intersecting.exists_mem_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝒜 : Set.{u1} (Set.{u1} α)}, (Set.Intersecting.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (CompleteLattice.toLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) 𝒜) -> (forall {s : Set.{u1} α} {t : Set.{u1} α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s 𝒜) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) t 𝒜) -> (Exists.{succ u1} α (fun (a : α) => And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a t))))
but is expected to have type
  forall {α : Type.{u1}} {𝒜 : Set.{u1} (Set.{u1} α)}, (Set.Intersecting.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (CompleteLattice.toLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (CompleteLattice.toLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) 𝒜) -> (forall {s : Set.{u1} α} {t : Set.{u1} α}, (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s 𝒜) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) t 𝒜) -> (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a t))))
Case conversion may be inaccurate. Consider using '#align set.intersecting.exists_mem_set Set.Intersecting.exists_mem_setₓ'. -/
theorem Intersecting.exists_mem_set {𝒜 : Set (Set α)} (h𝒜 : 𝒜.Intersecting) {s t : Set α}
    (hs : s ∈ 𝒜) (ht : t ∈ 𝒜) : ∃ a, a ∈ s ∧ a ∈ t :=
  not_disjoint_iff.1 <| h𝒜 hs ht
#align set.intersecting.exists_mem_set Set.Intersecting.exists_mem_set

/- warning: set.intersecting.exists_mem_finset -> Set.Intersecting.exists_mem_finset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {𝒜 : Set.{u1} (Finset.{u1} α)}, (Set.Intersecting.{u1} (Finset.{u1} α) (Lattice.toSemilatticeInf.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) (Finset.orderBot.{u1} α) 𝒜) -> (forall {s : Finset.{u1} α} {t : Finset.{u1} α}, (Membership.Mem.{u1, u1} (Finset.{u1} α) (Set.{u1} (Finset.{u1} α)) (Set.hasMem.{u1} (Finset.{u1} α)) s 𝒜) -> (Membership.Mem.{u1, u1} (Finset.{u1} α) (Set.{u1} (Finset.{u1} α)) (Set.hasMem.{u1} (Finset.{u1} α)) t 𝒜) -> (Exists.{succ u1} α (fun (a : α) => And (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a t))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {𝒜 : Set.{u1} (Finset.{u1} α)}, (Set.Intersecting.{u1} (Finset.{u1} α) (Lattice.toSemilatticeInf.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) 𝒜) -> (forall {s : Finset.{u1} α} {t : Finset.{u1} α}, (Membership.mem.{u1, u1} (Finset.{u1} α) (Set.{u1} (Finset.{u1} α)) (Set.instMembershipSet.{u1} (Finset.{u1} α)) s 𝒜) -> (Membership.mem.{u1, u1} (Finset.{u1} α) (Set.{u1} (Finset.{u1} α)) (Set.instMembershipSet.{u1} (Finset.{u1} α)) t 𝒜) -> (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a t))))
Case conversion may be inaccurate. Consider using '#align set.intersecting.exists_mem_finset Set.Intersecting.exists_mem_finsetₓ'. -/
theorem Intersecting.exists_mem_finset [DecidableEq α] {𝒜 : Set (Finset α)} (h𝒜 : 𝒜.Intersecting)
    {s t : Finset α} (hs : s ∈ 𝒜) (ht : t ∈ 𝒜) : ∃ a, a ∈ s ∧ a ∈ t :=
  not_disjoint_iff.1 <| disjoint_coe.Not.2 <| h𝒜 hs ht
#align set.intersecting.exists_mem_finset Set.Intersecting.exists_mem_finset

variable [BooleanAlgebra α]

#print Set.Intersecting.not_compl_mem /-
theorem Intersecting.not_compl_mem {s : Set α} (hs : s.Intersecting) {a : α} (ha : a ∈ s) :
    aᶜ ∉ s := fun h => hs ha h disjoint_compl_right
#align set.intersecting.not_compl_mem Set.Intersecting.not_compl_mem
-/

#print Set.Intersecting.not_mem /-
theorem Intersecting.not_mem {s : Set α} (hs : s.Intersecting) {a : α} (ha : aᶜ ∈ s) : a ∉ s :=
  fun h => hs ha h disjoint_compl_left
#align set.intersecting.not_mem Set.Intersecting.not_mem
-/

/- warning: set.intersecting.disjoint_map_compl -> Set.Intersecting.disjoint_map_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] {s : Finset.{u1} α}, (Set.Intersecting.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) -> (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s (Finset.map.{u1, u1} α α (Function.Embedding.mk.{succ u1, succ u1} α α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1)) (compl_injective.{u1} α _inst_1)) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] {s : Finset.{u1} α}, (Set.Intersecting.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))))) (BooleanAlgebra.toBoundedOrder.{u1} α _inst_1)) (Finset.toSet.{u1} α s)) -> (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s (Finset.map.{u1, u1} α α (Function.Embedding.mk.{succ u1, succ u1} α α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1)) (compl_injective.{u1} α _inst_1)) s))
Case conversion may be inaccurate. Consider using '#align set.intersecting.disjoint_map_compl Set.Intersecting.disjoint_map_complₓ'. -/
theorem Intersecting.disjoint_map_compl {s : Finset α} (hs : (s : Set α).Intersecting) :
    Disjoint s (s.map ⟨compl, compl_injective⟩) :=
  by
  rw [Finset.disjoint_left]
  rintro x hx hxc
  obtain ⟨x, hx', rfl⟩ := mem_map.mp hxc
  exact hs.not_compl_mem hx' hx
#align set.intersecting.disjoint_map_compl Set.Intersecting.disjoint_map_compl

#print Set.Intersecting.card_le /-
theorem Intersecting.card_le [Fintype α] {s : Finset α} (hs : (s : Set α).Intersecting) :
    2 * s.card ≤ Fintype.card α := by
  classical
    refine' (s.disj_union _ hs.disjoint_map_compl).card_le_univ.trans_eq' _
    rw [two_mul, card_disj_union, card_map]
#align set.intersecting.card_le Set.Intersecting.card_le
-/

variable [Nontrivial α] [Fintype α] {s : Finset α}

#print Set.Intersecting.is_max_iff_card_eq /-
-- Note, this lemma is false when `α` has exactly one element and boring when `α` is empty.
theorem Intersecting.is_max_iff_card_eq (hs : (s : Set α).Intersecting) :
    (∀ t : Finset α, (t : Set α).Intersecting → s ⊆ t → s = t) ↔ 2 * s.card = Fintype.card α := by
  classical
    refine'
      ⟨fun h => _, fun h t ht hst =>
        Finset.eq_of_subset_of_card_le hst <|
          le_of_mul_le_mul_left (ht.card_le.trans_eq h.symm) two_pos⟩
    suffices s.disj_union (s.map ⟨compl, compl_injective⟩) hs.disjoint_map_compl = Finset.univ by
      rw [Fintype.card, ← this, two_mul, card_disj_union, card_map]
    rw [← coe_eq_univ, disj_union_eq_union, coe_union, coe_map, Function.Embedding.coeFn_mk,
      image_eq_preimage_of_inverse compl_compl compl_compl]
    refine' eq_univ_of_forall fun a => _
    simp_rw [mem_union, mem_preimage]
    by_contra' ha
    refine' s.ne_insert_of_not_mem _ ha.1 (h _ _ <| s.subset_insert _)
    rw [coe_insert]
    refine' hs.insert _ fun b hb hab => ha.2 <| (hs.is_upper_set' h) hab.le_compl_left hb
    rintro rfl
    have :=
      h {⊤}
        (by
          rw [coe_singleton]
          exact intersecting_singleton.2 top_ne_bot)
    rw [compl_bot] at ha
    rw [coe_eq_empty.1 ((hs.is_upper_set' h).not_top_mem.1 ha.2)] at this
    exact Finset.singleton_ne_empty _ (this <| empty_subset _).symm
#align set.intersecting.is_max_iff_card_eq Set.Intersecting.is_max_iff_card_eq
-/

#print Set.Intersecting.exists_card_eq /-
theorem Intersecting.exists_card_eq (hs : (s : Set α).Intersecting) :
    ∃ t, s ⊆ t ∧ 2 * t.card = Fintype.card α ∧ (t : Set α).Intersecting :=
  by
  have := hs.card_le
  rw [mul_comm, ← Nat.le_div_iff_mul_le' two_pos] at this
  revert hs
  refine' s.strong_downward_induction_on _ this
  rintro s ih hcard hs
  by_cases ∀ t : Finset α, (t : Set α).Intersecting → s ⊆ t → s = t
  · exact ⟨s, subset.rfl, hs.is_max_iff_card_eq.1 h, hs⟩
  push_neg  at h
  obtain ⟨t, ht, hst⟩ := h
  refine' (ih _ (_root_.ssubset_iff_subset_ne.2 hst) ht).imp fun u => And.imp_left hst.1.trans
  rw [Nat.le_div_iff_mul_le' two_pos, mul_comm]
  exact ht.card_le
#align set.intersecting.exists_card_eq Set.Intersecting.exists_card_eq
-/

end Set

