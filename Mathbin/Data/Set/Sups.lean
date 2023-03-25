/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.set.sups
! leanprover-community/mathlib commit 97eab48559068f3d6313da387714ef25768fb730
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.NAry
import Mathbin.Order.UpperLower.Basic

/-!
# Set family operations

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines a few binary operations on `set α` for use in set family combinatorics.

## Main declarations

* `s ⊻ t`: Set of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t`.
* `s ⊼ t`: Set of elements of the form `a ⊓ b` where `a ∈ s`, `b ∈ t`.

## Notation

We define the following notation in locale `set_family`:
* `s ⊻ t`
* `s ⊼ t`

## References

[B. Bollobás, *Combinatorics*][bollobas1986]
-/


open Function

variable {α : Type _}

#print HasSups /-
/-- Notation typeclass for pointwise supremum `⊻`. -/
class HasSups (α : Type _) where
  sups : α → α → α
#align has_sups HasSups
-/

#print HasInfs /-
/-- Notation typeclass for pointwise infimum `⊼`. -/
class HasInfs (α : Type _) where
  infs : α → α → α
#align has_infs HasInfs
-/

-- mathport name: «expr ⊻ »
infixl:74
  " ⊻ " =>-- This notation is meant to have higher precedence than `⊔` and `⊓`, but still within the realm of
  -- other binary operations
  HasSups.sups

-- mathport name: «expr ⊼ »
infixl:75 " ⊼ " => HasInfs.infs

namespace Set

section Sups

variable [SemilatticeSup α] (s s₁ s₂ t t₁ t₂ u v : Set α)

#print Set.hasSups /-
/-- `s ⊻ t` is the set of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t`. -/
protected def hasSups : HasSups (Set α) :=
  ⟨image2 (· ⊔ ·)⟩
#align set.has_sups Set.hasSups
-/

scoped[SetFamily] attribute [instance] Set.hasSups

variable {s s₁ s₂ t t₁ t₂ u} {a b c : α}

/- warning: set.mem_sups -> Set.mem_sups is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {c : α}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) c (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s t)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => Exists.{succ u1} α (fun (b : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b t) => Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) a b) c)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {c : α}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) c (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s t)) (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (Exists.{succ u1} α (fun (b : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b t) (Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_1) a b) c)))))
Case conversion may be inaccurate. Consider using '#align set.mem_sups Set.mem_supsₓ'. -/
@[simp]
theorem mem_sups : c ∈ s ⊻ t ↔ ∃ a ∈ s, ∃ b ∈ t, a ⊔ b = c := by simp [(· ⊻ ·)]
#align set.mem_sups Set.mem_sups

/- warning: set.sup_mem_sups -> Set.sup_mem_sups is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {a : α} {b : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b t) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) a b) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {a : α} {b : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b t) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_1) a b) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s t))
Case conversion may be inaccurate. Consider using '#align set.sup_mem_sups Set.sup_mem_supsₓ'. -/
theorem sup_mem_sups : a ∈ s → b ∈ t → a ⊔ b ∈ s ⊻ t :=
  mem_image2_of_mem
#align set.sup_mem_sups Set.sup_mem_sups

#print Set.sups_subset /-
theorem sups_subset : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ ⊻ t₁ ⊆ s₂ ⊻ t₂ :=
  image2_subset
#align set.sups_subset Set.sups_subset
-/

#print Set.sups_subset_left /-
theorem sups_subset_left : t₁ ⊆ t₂ → s ⊻ t₁ ⊆ s ⊻ t₂ :=
  image2_subset_left
#align set.sups_subset_left Set.sups_subset_left
-/

#print Set.sups_subset_right /-
theorem sups_subset_right : s₁ ⊆ s₂ → s₁ ⊻ t ⊆ s₂ ⊻ t :=
  image2_subset_right
#align set.sups_subset_right Set.sups_subset_right
-/

/- warning: set.image_subset_sups_left -> Set.image_subset_sups_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {b : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.image.{u1, u1} α α (fun (a : α) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) a b) s) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {b : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Set.image.{u1, u1} α α (fun (a : α) => Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_1) a b) s) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s t))
Case conversion may be inaccurate. Consider using '#align set.image_subset_sups_left Set.image_subset_sups_leftₓ'. -/
theorem image_subset_sups_left : b ∈ t → (fun a => a ⊔ b) '' s ⊆ s ⊻ t :=
  image_subset_image2_left
#align set.image_subset_sups_left Set.image_subset_sups_left

/- warning: set.image_subset_sups_right -> Set.image_subset_sups_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {a : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.image.{u1, u1} α α (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) a) t) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {a : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Set.image.{u1, u1} α α ((fun (x._@.Mathlib.Data.Set.Sups._hyg.1635 : α) (x._@.Mathlib.Data.Set.Sups._hyg.1637 : α) => Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_1) x._@.Mathlib.Data.Set.Sups._hyg.1635 x._@.Mathlib.Data.Set.Sups._hyg.1637) a) t) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s t))
Case conversion may be inaccurate. Consider using '#align set.image_subset_sups_right Set.image_subset_sups_rightₓ'. -/
theorem image_subset_sups_right : a ∈ s → (· ⊔ ·) a '' t ⊆ s ⊻ t :=
  image_subset_image2_right
#align set.image_subset_sups_right Set.image_subset_sups_right

/- warning: set.forall_sups_iff -> Set.forall_sups_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {p : α -> Prop}, Iff (forall (c : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) c (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s t)) -> (p c)) (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b t) -> (p (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) a b))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {p : α -> Prop}, Iff (forall (c : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) c (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s t)) -> (p c)) (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b t) -> (p (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_1) a b))))
Case conversion may be inaccurate. Consider using '#align set.forall_sups_iff Set.forall_sups_iffₓ'. -/
theorem forall_sups_iff {p : α → Prop} : (∀ c ∈ s ⊻ t, p c) ↔ ∀ a ∈ s, ∀ b ∈ t, p (a ⊔ b) :=
  forall_image2_iff
#align set.forall_sups_iff Set.forall_sups_iff

/- warning: set.sups_subset_iff -> Set.sups_subset_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s t) u) (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b t) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) a b) u)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s t) u) (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b t) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_1) a b) u)))
Case conversion may be inaccurate. Consider using '#align set.sups_subset_iff Set.sups_subset_iffₓ'. -/
@[simp]
theorem sups_subset_iff : s ⊻ t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a ⊔ b ∈ u :=
  image2_subset_iff
#align set.sups_subset_iff Set.sups_subset_iff

#print Set.sups_nonempty /-
@[simp]
theorem sups_nonempty : (s ⊻ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image2_nonempty_iff
#align set.sups_nonempty Set.sups_nonempty
-/

#print Set.Nonempty.sups /-
protected theorem Nonempty.sups : s.Nonempty → t.Nonempty → (s ⊻ t).Nonempty :=
  Nonempty.image2
#align set.nonempty.sups Set.Nonempty.sups
-/

#print Set.Nonempty.of_sups_left /-
theorem Nonempty.of_sups_left : (s ⊻ t).Nonempty → s.Nonempty :=
  Nonempty.of_image2_left
#align set.nonempty.of_sups_left Set.Nonempty.of_sups_left
-/

#print Set.Nonempty.of_sups_right /-
theorem Nonempty.of_sups_right : (s ⊻ t).Nonempty → t.Nonempty :=
  Nonempty.of_image2_right
#align set.nonempty.of_sups_right Set.Nonempty.of_sups_right
-/

#print Set.empty_sups /-
@[simp]
theorem empty_sups : ∅ ⊻ t = ∅ :=
  image2_empty_left
#align set.empty_sups Set.empty_sups
-/

#print Set.sups_empty /-
@[simp]
theorem sups_empty : s ⊻ ∅ = ∅ :=
  image2_empty_right
#align set.sups_empty Set.sups_empty
-/

#print Set.sups_eq_empty /-
@[simp]
theorem sups_eq_empty : s ⊻ t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image2_eq_empty_iff
#align set.sups_eq_empty Set.sups_eq_empty
-/

/- warning: set.singleton_sups -> Set.singleton_sups is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] {t : Set.{u1} α} {a : α}, Eq.{succ u1} (Set.{u1} α) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a) t) (Set.image.{u1, u1} α α (fun (b : α) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) a b) t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] {t : Set.{u1} α} {a : α}, Eq.{succ u1} (Set.{u1} α) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a) t) (Set.image.{u1, u1} α α (fun (b : α) => Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_1) a b) t)
Case conversion may be inaccurate. Consider using '#align set.singleton_sups Set.singleton_supsₓ'. -/
@[simp]
theorem singleton_sups : {a} ⊻ t = t.image fun b => a ⊔ b :=
  image2_singleton_left
#align set.singleton_sups Set.singleton_sups

/- warning: set.sups_singleton -> Set.sups_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] {s : Set.{u1} α} {b : α}, Eq.{succ u1} (Set.{u1} α) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) b)) (Set.image.{u1, u1} α α (fun (a : α) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) a b) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] {s : Set.{u1} α} {b : α}, Eq.{succ u1} (Set.{u1} α) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) b)) (Set.image.{u1, u1} α α (fun (a : α) => Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_1) a b) s)
Case conversion may be inaccurate. Consider using '#align set.sups_singleton Set.sups_singletonₓ'. -/
@[simp]
theorem sups_singleton : s ⊻ {b} = s.image fun a => a ⊔ b :=
  image2_singleton_right
#align set.sups_singleton Set.sups_singleton

/- warning: set.singleton_sups_singleton -> Set.singleton_sups_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] {a : α} {b : α}, Eq.{succ u1} (Set.{u1} α) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) b)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] {a : α} {b : α}, Eq.{succ u1} (Set.{u1} α) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) b)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_1) a b))
Case conversion may be inaccurate. Consider using '#align set.singleton_sups_singleton Set.singleton_sups_singletonₓ'. -/
theorem singleton_sups_singleton : ({a} ⊻ {b} : Set α) = {a ⊔ b} :=
  image2_singleton
#align set.singleton_sups_singleton Set.singleton_sups_singleton

/- warning: set.sups_union_left -> Set.sups_union_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂) t) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s₁ t) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s₂ t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₁ s₂) t) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s₁ t) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s₂ t))
Case conversion may be inaccurate. Consider using '#align set.sups_union_left Set.sups_union_leftₓ'. -/
theorem sups_union_left : (s₁ ∪ s₂) ⊻ t = s₁ ⊻ t ∪ s₂ ⊻ t :=
  image2_union_left
#align set.sups_union_left Set.sups_union_left

/- warning: set.sups_union_right -> Set.sups_union_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] {s : Set.{u1} α} {t₁ : Set.{u1} α} {t₂ : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t₁ t₂)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s t₁) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s t₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] {s : Set.{u1} α} {t₁ : Set.{u1} α} {t₂ : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) t₁ t₂)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s t₁) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s t₂))
Case conversion may be inaccurate. Consider using '#align set.sups_union_right Set.sups_union_rightₓ'. -/
theorem sups_union_right : s ⊻ (t₁ ∪ t₂) = s ⊻ t₁ ∪ s ⊻ t₂ :=
  image2_union_right
#align set.sups_union_right Set.sups_union_right

/- warning: set.sups_inter_subset_left -> Set.sups_inter_subset_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ s₂) t) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s₁ t) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s₂ t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s₁ s₂) t) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s₁ t) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s₂ t))
Case conversion may be inaccurate. Consider using '#align set.sups_inter_subset_left Set.sups_inter_subset_leftₓ'. -/
theorem sups_inter_subset_left : (s₁ ∩ s₂) ⊻ t ⊆ s₁ ⊻ t ∩ s₂ ⊻ t :=
  image2_inter_subset_left
#align set.sups_inter_subset_left Set.sups_inter_subset_left

/- warning: set.sups_inter_subset_right -> Set.sups_inter_subset_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] {s : Set.{u1} α} {t₁ : Set.{u1} α} {t₂ : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t₁ t₂)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s t₁) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s t₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] {s : Set.{u1} α} {t₁ : Set.{u1} α} {t₂ : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t₁ t₂)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s t₁) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s t₂))
Case conversion may be inaccurate. Consider using '#align set.sups_inter_subset_right Set.sups_inter_subset_rightₓ'. -/
theorem sups_inter_subset_right : s ⊻ (t₁ ∩ t₂) ⊆ s ⊻ t₁ ∩ s ⊻ t₂ :=
  image2_inter_subset_right
#align set.sups_inter_subset_right Set.sups_inter_subset_right

variable (s t u v)

/- warning: set.Union_image_sup_left -> Set.unionᵢ_image_sup_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, succ u1} α α (fun (a : α) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => Set.image.{u1, u1} α α (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) a) t))) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, succ u1} α α (fun (a : α) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => Set.image.{u1, u1} α α ((fun (x._@.Mathlib.Data.Set.Sups._hyg.2587 : α) (x._@.Mathlib.Data.Set.Sups._hyg.2589 : α) => Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_1) x._@.Mathlib.Data.Set.Sups._hyg.2587 x._@.Mathlib.Data.Set.Sups._hyg.2589) a) t))) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s t)
Case conversion may be inaccurate. Consider using '#align set.Union_image_sup_left Set.unionᵢ_image_sup_leftₓ'. -/
theorem unionᵢ_image_sup_left : (⋃ a ∈ s, (· ⊔ ·) a '' t) = s ⊻ t :=
  unionᵢ_image_left _
#align set.Union_image_sup_left Set.unionᵢ_image_sup_left

/- warning: set.Union_image_sup_right -> Set.unionᵢ_image_sup_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, succ u1} α α (fun (b : α) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b t) => Set.image.{u1, u1} α α (fun (_x : α) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) _x b) s))) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, succ u1} α α (fun (b : α) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b t) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b t) => Set.image.{u1, u1} α α (fun (_x : α) => Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_1) _x b) s))) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s t)
Case conversion may be inaccurate. Consider using '#align set.Union_image_sup_right Set.unionᵢ_image_sup_rightₓ'. -/
theorem unionᵢ_image_sup_right : (⋃ b ∈ t, (· ⊔ b) '' s) = s ⊻ t :=
  unionᵢ_image_right _
#align set.Union_image_sup_right Set.unionᵢ_image_sup_right

/- warning: set.image_sup_prod -> Set.image_sup_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.image.{u1, u1} (Prod.{u1, u1} α α) α (Function.uncurry.{u1, u1, u1} α α α (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1))) (Set.prod.{u1, u1} α α s t)) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.image2.{u1, u1, u1} α α α (fun (x : α) (x_1 : α) => Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_1) x x_1) s t) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s t)
Case conversion may be inaccurate. Consider using '#align set.image_sup_prod Set.image_sup_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem image_sup_prod (s t : Set α) : (s ×ˢ t).image (uncurry (· ⊔ ·)) = s ⊻ t :=
  image_uncurry_prod _ _ _
#align set.image_sup_prod Set.image_sup_prod

#print Set.sups_assoc /-
theorem sups_assoc : s ⊻ t ⊻ u = s ⊻ (t ⊻ u) :=
  image2_assoc fun _ _ _ => sup_assoc
#align set.sups_assoc Set.sups_assoc
-/

#print Set.sups_comm /-
theorem sups_comm : s ⊻ t = t ⊻ s :=
  image2_comm fun _ _ => sup_comm
#align set.sups_comm Set.sups_comm
-/

#print Set.sups_left_comm /-
theorem sups_left_comm : s ⊻ (t ⊻ u) = t ⊻ (s ⊻ u) :=
  image2_left_comm sup_left_comm
#align set.sups_left_comm Set.sups_left_comm
-/

#print Set.sups_right_comm /-
theorem sups_right_comm : s ⊻ t ⊻ u = s ⊻ u ⊻ t :=
  image2_right_comm sup_right_comm
#align set.sups_right_comm Set.sups_right_comm
-/

#print Set.sups_sups_sups_comm /-
theorem sups_sups_sups_comm : s ⊻ t ⊻ (u ⊻ v) = s ⊻ u ⊻ (t ⊻ v) :=
  image2_image2_image2_comm sup_sup_sup_comm
#align set.sups_sups_sups_comm Set.sups_sups_sups_comm
-/

end Sups

section Infs

variable [SemilatticeInf α] (s s₁ s₂ t t₁ t₂ u v : Set α)

#print Set.hasInfs /-
/-- `s ⊼ t` is the set of elements of the form `a ⊓ b` where `a ∈ s`, `b ∈ t`. -/
protected def hasInfs : HasInfs (Set α) :=
  ⟨image2 (· ⊓ ·)⟩
#align set.has_infs Set.hasInfs
-/

scoped[SetFamily] attribute [instance] Set.hasInfs

variable {s s₁ s₂ t t₁ t₂ u} {a b c : α}

/- warning: set.mem_infs -> Set.mem_infs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {c : α}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) c (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s t)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => Exists.{succ u1} α (fun (b : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b t) => Eq.{succ u1} α (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) a b) c)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {c : α}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) c (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s t)) (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (Exists.{succ u1} α (fun (b : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b t) (Eq.{succ u1} α (Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_1) a b) c)))))
Case conversion may be inaccurate. Consider using '#align set.mem_infs Set.mem_infsₓ'. -/
@[simp]
theorem mem_infs : c ∈ s ⊼ t ↔ ∃ a ∈ s, ∃ b ∈ t, a ⊓ b = c := by simp [(· ⊼ ·)]
#align set.mem_infs Set.mem_infs

/- warning: set.inf_mem_infs -> Set.inf_mem_infs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {a : α} {b : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b t) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) a b) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {a : α} {b : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b t) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_1) a b) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s t))
Case conversion may be inaccurate. Consider using '#align set.inf_mem_infs Set.inf_mem_infsₓ'. -/
theorem inf_mem_infs : a ∈ s → b ∈ t → a ⊓ b ∈ s ⊼ t :=
  mem_image2_of_mem
#align set.inf_mem_infs Set.inf_mem_infs

#print Set.infs_subset /-
theorem infs_subset : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ ⊼ t₁ ⊆ s₂ ⊼ t₂ :=
  image2_subset
#align set.infs_subset Set.infs_subset
-/

#print Set.infs_subset_left /-
theorem infs_subset_left : t₁ ⊆ t₂ → s ⊼ t₁ ⊆ s ⊼ t₂ :=
  image2_subset_left
#align set.infs_subset_left Set.infs_subset_left
-/

#print Set.infs_subset_right /-
theorem infs_subset_right : s₁ ⊆ s₂ → s₁ ⊼ t ⊆ s₂ ⊼ t :=
  image2_subset_right
#align set.infs_subset_right Set.infs_subset_right
-/

/- warning: set.image_subset_infs_left -> Set.image_subset_infs_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {b : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.image.{u1, u1} α α (fun (a : α) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) a b) s) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {b : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Set.image.{u1, u1} α α (fun (a : α) => Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_1) a b) s) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s t))
Case conversion may be inaccurate. Consider using '#align set.image_subset_infs_left Set.image_subset_infs_leftₓ'. -/
theorem image_subset_infs_left : b ∈ t → (fun a => a ⊓ b) '' s ⊆ s ⊼ t :=
  image_subset_image2_left
#align set.image_subset_infs_left Set.image_subset_infs_left

/- warning: set.image_subset_infs_right -> Set.image_subset_infs_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {a : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.image.{u1, u1} α α (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) a) t) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {a : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Set.image.{u1, u1} α α ((fun (x._@.Mathlib.Data.Set.Sups._hyg.3583 : α) (x._@.Mathlib.Data.Set.Sups._hyg.3585 : α) => Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_1) x._@.Mathlib.Data.Set.Sups._hyg.3583 x._@.Mathlib.Data.Set.Sups._hyg.3585) a) t) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s t))
Case conversion may be inaccurate. Consider using '#align set.image_subset_infs_right Set.image_subset_infs_rightₓ'. -/
theorem image_subset_infs_right : a ∈ s → (· ⊓ ·) a '' t ⊆ s ⊼ t :=
  image_subset_image2_right
#align set.image_subset_infs_right Set.image_subset_infs_right

/- warning: set.forall_infs_iff -> Set.forall_infs_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {p : α -> Prop}, Iff (forall (c : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) c (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s t)) -> (p c)) (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b t) -> (p (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) a b))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {p : α -> Prop}, Iff (forall (c : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) c (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s t)) -> (p c)) (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b t) -> (p (Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_1) a b))))
Case conversion may be inaccurate. Consider using '#align set.forall_infs_iff Set.forall_infs_iffₓ'. -/
theorem forall_infs_iff {p : α → Prop} : (∀ c ∈ s ⊼ t, p c) ↔ ∀ a ∈ s, ∀ b ∈ t, p (a ⊓ b) :=
  forall_image2_iff
#align set.forall_infs_iff Set.forall_infs_iff

/- warning: set.infs_subset_iff -> Set.infs_subset_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s t) u) (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b t) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) a b) u)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s t) u) (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b t) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_1) a b) u)))
Case conversion may be inaccurate. Consider using '#align set.infs_subset_iff Set.infs_subset_iffₓ'. -/
@[simp]
theorem infs_subset_iff : s ⊼ t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a ⊓ b ∈ u :=
  image2_subset_iff
#align set.infs_subset_iff Set.infs_subset_iff

#print Set.infs_nonempty /-
@[simp]
theorem infs_nonempty : (s ⊼ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image2_nonempty_iff
#align set.infs_nonempty Set.infs_nonempty
-/

#print Set.Nonempty.infs /-
protected theorem Nonempty.infs : s.Nonempty → t.Nonempty → (s ⊼ t).Nonempty :=
  Nonempty.image2
#align set.nonempty.infs Set.Nonempty.infs
-/

#print Set.Nonempty.of_infs_left /-
theorem Nonempty.of_infs_left : (s ⊼ t).Nonempty → s.Nonempty :=
  Nonempty.of_image2_left
#align set.nonempty.of_infs_left Set.Nonempty.of_infs_left
-/

#print Set.Nonempty.of_infs_right /-
theorem Nonempty.of_infs_right : (s ⊼ t).Nonempty → t.Nonempty :=
  Nonempty.of_image2_right
#align set.nonempty.of_infs_right Set.Nonempty.of_infs_right
-/

#print Set.empty_infs /-
@[simp]
theorem empty_infs : ∅ ⊼ t = ∅ :=
  image2_empty_left
#align set.empty_infs Set.empty_infs
-/

#print Set.infs_empty /-
@[simp]
theorem infs_empty : s ⊼ ∅ = ∅ :=
  image2_empty_right
#align set.infs_empty Set.infs_empty
-/

#print Set.infs_eq_empty /-
@[simp]
theorem infs_eq_empty : s ⊼ t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image2_eq_empty_iff
#align set.infs_eq_empty Set.infs_eq_empty
-/

/- warning: set.singleton_infs -> Set.singleton_infs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] {t : Set.{u1} α} {a : α}, Eq.{succ u1} (Set.{u1} α) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a) t) (Set.image.{u1, u1} α α (fun (b : α) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) a b) t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] {t : Set.{u1} α} {a : α}, Eq.{succ u1} (Set.{u1} α) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a) t) (Set.image.{u1, u1} α α (fun (b : α) => Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_1) a b) t)
Case conversion may be inaccurate. Consider using '#align set.singleton_infs Set.singleton_infsₓ'. -/
@[simp]
theorem singleton_infs : {a} ⊼ t = t.image fun b => a ⊓ b :=
  image2_singleton_left
#align set.singleton_infs Set.singleton_infs

/- warning: set.infs_singleton -> Set.infs_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] {s : Set.{u1} α} {b : α}, Eq.{succ u1} (Set.{u1} α) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) b)) (Set.image.{u1, u1} α α (fun (a : α) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) a b) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] {s : Set.{u1} α} {b : α}, Eq.{succ u1} (Set.{u1} α) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) b)) (Set.image.{u1, u1} α α (fun (a : α) => Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_1) a b) s)
Case conversion may be inaccurate. Consider using '#align set.infs_singleton Set.infs_singletonₓ'. -/
@[simp]
theorem infs_singleton : s ⊼ {b} = s.image fun a => a ⊓ b :=
  image2_singleton_right
#align set.infs_singleton Set.infs_singleton

/- warning: set.singleton_infs_singleton -> Set.singleton_infs_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] {a : α} {b : α}, Eq.{succ u1} (Set.{u1} α) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) b)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] {a : α} {b : α}, Eq.{succ u1} (Set.{u1} α) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) b)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) (Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_1) a b))
Case conversion may be inaccurate. Consider using '#align set.singleton_infs_singleton Set.singleton_infs_singletonₓ'. -/
theorem singleton_infs_singleton : ({a} ⊼ {b} : Set α) = {a ⊓ b} :=
  image2_singleton
#align set.singleton_infs_singleton Set.singleton_infs_singleton

/- warning: set.infs_union_left -> Set.infs_union_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂) t) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s₁ t) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s₂ t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₁ s₂) t) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s₁ t) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s₂ t))
Case conversion may be inaccurate. Consider using '#align set.infs_union_left Set.infs_union_leftₓ'. -/
theorem infs_union_left : (s₁ ∪ s₂) ⊼ t = s₁ ⊼ t ∪ s₂ ⊼ t :=
  image2_union_left
#align set.infs_union_left Set.infs_union_left

/- warning: set.infs_union_right -> Set.infs_union_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] {s : Set.{u1} α} {t₁ : Set.{u1} α} {t₂ : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t₁ t₂)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s t₁) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s t₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] {s : Set.{u1} α} {t₁ : Set.{u1} α} {t₂ : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) t₁ t₂)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s t₁) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s t₂))
Case conversion may be inaccurate. Consider using '#align set.infs_union_right Set.infs_union_rightₓ'. -/
theorem infs_union_right : s ⊼ (t₁ ∪ t₂) = s ⊼ t₁ ∪ s ⊼ t₂ :=
  image2_union_right
#align set.infs_union_right Set.infs_union_right

/- warning: set.infs_inter_subset_left -> Set.infs_inter_subset_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ s₂) t) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s₁ t) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s₂ t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s₁ s₂) t) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s₁ t) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s₂ t))
Case conversion may be inaccurate. Consider using '#align set.infs_inter_subset_left Set.infs_inter_subset_leftₓ'. -/
theorem infs_inter_subset_left : (s₁ ∩ s₂) ⊼ t ⊆ s₁ ⊼ t ∩ s₂ ⊼ t :=
  image2_inter_subset_left
#align set.infs_inter_subset_left Set.infs_inter_subset_left

/- warning: set.infs_inter_subset_right -> Set.infs_inter_subset_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] {s : Set.{u1} α} {t₁ : Set.{u1} α} {t₂ : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t₁ t₂)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s t₁) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s t₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] {s : Set.{u1} α} {t₁ : Set.{u1} α} {t₂ : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t₁ t₂)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s t₁) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s t₂))
Case conversion may be inaccurate. Consider using '#align set.infs_inter_subset_right Set.infs_inter_subset_rightₓ'. -/
theorem infs_inter_subset_right : s ⊼ (t₁ ∩ t₂) ⊆ s ⊼ t₁ ∩ s ⊼ t₂ :=
  image2_inter_subset_right
#align set.infs_inter_subset_right Set.infs_inter_subset_right

variable (s t u v)

/- warning: set.Union_image_inf_left -> Set.unionᵢ_image_inf_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, succ u1} α α (fun (a : α) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => Set.image.{u1, u1} α α (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) a) t))) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, succ u1} α α (fun (a : α) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => Set.image.{u1, u1} α α ((fun (x._@.Mathlib.Data.Set.Sups._hyg.4535 : α) (x._@.Mathlib.Data.Set.Sups._hyg.4537 : α) => Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_1) x._@.Mathlib.Data.Set.Sups._hyg.4535 x._@.Mathlib.Data.Set.Sups._hyg.4537) a) t))) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s t)
Case conversion may be inaccurate. Consider using '#align set.Union_image_inf_left Set.unionᵢ_image_inf_leftₓ'. -/
theorem unionᵢ_image_inf_left : (⋃ a ∈ s, (· ⊓ ·) a '' t) = s ⊼ t :=
  unionᵢ_image_left _
#align set.Union_image_inf_left Set.unionᵢ_image_inf_left

/- warning: set.Union_image_inf_right -> Set.unionᵢ_image_inf_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, succ u1} α α (fun (b : α) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b t) => Set.image.{u1, u1} α α (fun (_x : α) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) _x b) s))) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, succ u1} α α (fun (b : α) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b t) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b t) => Set.image.{u1, u1} α α (fun (_x : α) => Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_1) _x b) s))) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s t)
Case conversion may be inaccurate. Consider using '#align set.Union_image_inf_right Set.unionᵢ_image_inf_rightₓ'. -/
theorem unionᵢ_image_inf_right : (⋃ b ∈ t, (· ⊓ b) '' s) = s ⊼ t :=
  unionᵢ_image_right _
#align set.Union_image_inf_right Set.unionᵢ_image_inf_right

/- warning: set.image_inf_prod -> Set.image_inf_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.image.{u1, u1} (Prod.{u1, u1} α α) α (Function.uncurry.{u1, u1, u1} α α α (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1))) (Set.prod.{u1, u1} α α s t)) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.image2.{u1, u1, u1} α α α (fun (x : α) (x_1 : α) => Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_1) x x_1) s t) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s t)
Case conversion may be inaccurate. Consider using '#align set.image_inf_prod Set.image_inf_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem image_inf_prod (s t : Set α) : (s ×ˢ t).image (uncurry (· ⊓ ·)) = s ⊼ t :=
  image_uncurry_prod _ _ _
#align set.image_inf_prod Set.image_inf_prod

#print Set.infs_assoc /-
theorem infs_assoc : s ⊼ t ⊼ u = s ⊼ (t ⊼ u) :=
  image2_assoc fun _ _ _ => inf_assoc
#align set.infs_assoc Set.infs_assoc
-/

#print Set.infs_comm /-
theorem infs_comm : s ⊼ t = t ⊼ s :=
  image2_comm fun _ _ => inf_comm
#align set.infs_comm Set.infs_comm
-/

#print Set.infs_left_comm /-
theorem infs_left_comm : s ⊼ (t ⊼ u) = t ⊼ (s ⊼ u) :=
  image2_left_comm inf_left_comm
#align set.infs_left_comm Set.infs_left_comm
-/

#print Set.infs_right_comm /-
theorem infs_right_comm : s ⊼ t ⊼ u = s ⊼ u ⊼ t :=
  image2_right_comm inf_right_comm
#align set.infs_right_comm Set.infs_right_comm
-/

#print Set.infs_infs_infs_comm /-
theorem infs_infs_infs_comm : s ⊼ t ⊼ (u ⊼ v) = s ⊼ u ⊼ (t ⊼ v) :=
  image2_image2_image2_comm inf_inf_inf_comm
#align set.infs_infs_infs_comm Set.infs_infs_infs_comm
-/

end Infs

open SetFamily

section DistribLattice

variable [DistribLattice α] (s t u : Set α)

#print Set.sups_infs_subset_left /-
theorem sups_infs_subset_left : s ⊻ t ⊼ u ⊆ (s ⊻ t) ⊼ (s ⊻ u) :=
  image2_distrib_subset_left fun _ _ _ => sup_inf_left
#align set.sups_infs_subset_left Set.sups_infs_subset_left
-/

#print Set.sups_infs_subset_right /-
theorem sups_infs_subset_right : t ⊼ u ⊻ s ⊆ (t ⊻ s) ⊼ (u ⊻ s) :=
  image2_distrib_subset_right fun _ _ _ => sup_inf_right
#align set.sups_infs_subset_right Set.sups_infs_subset_right
-/

#print Set.infs_sups_subset_left /-
theorem infs_sups_subset_left : s ⊼ (t ⊻ u) ⊆ s ⊼ t ⊻ s ⊼ u :=
  image2_distrib_subset_left fun _ _ _ => inf_sup_left
#align set.infs_sups_subset_left Set.infs_sups_subset_left
-/

#print Set.infs_sups_subset_right /-
theorem infs_sups_subset_right : (t ⊻ u) ⊼ s ⊆ t ⊼ s ⊻ u ⊼ s :=
  image2_distrib_subset_right fun _ _ _ => inf_sup_right
#align set.infs_sups_subset_right Set.infs_sups_subset_right
-/

end DistribLattice

end Set

open SetFamily

/- warning: upper_closure_sups -> upperClosure_sups is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) (upperClosure.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s t)) (Sup.sup.{u1} (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) (UpperSet.hasSup.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) (upperClosure.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)) s) (upperClosure.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) (upperClosure.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)) (HasSups.sups.{u1} (Set.{u1} α) (Set.hasSups.{u1} α _inst_1) s t)) (Sup.sup.{u1} (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) (UpperSet.instSupUpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) (upperClosure.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)) s) (upperClosure.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)) t))
Case conversion may be inaccurate. Consider using '#align upper_closure_sups upperClosure_supsₓ'. -/
@[simp]
theorem upperClosure_sups [SemilatticeSup α] (s t : Set α) :
    upperClosure (s ⊻ t) = upperClosure s ⊔ upperClosure t :=
  by
  ext a
  simp only [SetLike.mem_coe, mem_upperClosure, Set.mem_sups, exists_and_left, exists_prop,
    UpperSet.coe_sup, Set.mem_inter_iff]
  constructor
  · rintro ⟨_, ⟨b, hb, c, hc, rfl⟩, ha⟩
    exact ⟨⟨b, hb, le_sup_left.trans ha⟩, c, hc, le_sup_right.trans ha⟩
  · rintro ⟨⟨b, hb, hab⟩, c, hc, hac⟩
    exact ⟨_, ⟨b, hb, c, hc, rfl⟩, sup_le hab hac⟩
#align upper_closure_sups upperClosure_sups

/- warning: lower_closure_infs -> lowerClosure_infs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) (lowerClosure.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s t)) (Inf.inf.{u1} (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) (LowerSet.hasInf.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) (lowerClosure.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)) s) (lowerClosure.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) (lowerClosure.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)) (HasInfs.infs.{u1} (Set.{u1} α) (Set.hasInfs.{u1} α _inst_1) s t)) (Inf.inf.{u1} (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) (LowerSet.instInfLowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) (lowerClosure.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)) s) (lowerClosure.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)) t))
Case conversion may be inaccurate. Consider using '#align lower_closure_infs lowerClosure_infsₓ'. -/
@[simp]
theorem lowerClosure_infs [SemilatticeInf α] (s t : Set α) :
    lowerClosure (s ⊼ t) = lowerClosure s ⊓ lowerClosure t :=
  by
  ext a
  simp only [SetLike.mem_coe, mem_lowerClosure, Set.mem_infs, exists_and_left, exists_prop,
    LowerSet.coe_sup, Set.mem_inter_iff]
  constructor
  · rintro ⟨_, ⟨b, hb, c, hc, rfl⟩, ha⟩
    exact ⟨⟨b, hb, ha.trans inf_le_left⟩, c, hc, ha.trans inf_le_right⟩
  · rintro ⟨⟨b, hb, hab⟩, c, hc, hac⟩
    exact ⟨_, ⟨b, hb, c, hc, rfl⟩, le_inf hab hac⟩
#align lower_closure_infs lowerClosure_infs

