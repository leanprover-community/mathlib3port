/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.finset.sups
! leanprover-community/mathlib commit 20715f4ac6819ef2453d9e5106ecd086a5dc2a5e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.NAry
import Mathbin.Data.Set.Sups

/-!
# Set family operations

This file defines a few binary operations on `finset α` for use in set family combinatorics.

## Main declarations

* `s ⊻ t`: Finset of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t`.
* `s ⊼ t`: Finset of elements of the form `a ⊓ b` where `a ∈ s`, `b ∈ t`.
* `finset.disj_sups s t`: Finset of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t` and `a`
  and `b` are disjoint.

## Notation

We define the following notation in locale `finset_family`:
* `s ⊻ t`
* `s ⊼ t`
* `s ○ t` for `finset.disj_sups s t`

## References

[B. Bollobás, *Combinatorics*][bollobas1986]
-/


open Function

open SetFamily

variable {α : Type _} [DecidableEq α]

namespace Finset

section Sups

variable [SemilatticeSup α] (s s₁ s₂ t t₁ t₂ u v : Finset α)

#print Finset.hasSups /-
/-- `s ⊻ t` is the finset of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t`. -/
protected def hasSups : HasSups (Finset α) :=
  ⟨image₂ (· ⊔ ·)⟩
#align finset.has_sups Finset.hasSups
-/

scoped[FinsetFamily] attribute [instance] Finset.hasSups

variable {s t} {a b c : α}

/- warning: finset.mem_sups -> Finset.mem_sups is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {c : α}, Iff (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) c (HasSups.sups.{u1} (Finset.{u1} α) (Finset.hasSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Exists.{succ u1} α (fun (b : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) b t) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) b t) => Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_2) a b) c)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {c : α}, Iff (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) c (HasSups.sups.{u1} (Finset.{u1} α) (Finset.hasSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t)) (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) (Exists.{succ u1} α (fun (b : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) b t) (Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_2) a b) c)))))
Case conversion may be inaccurate. Consider using '#align finset.mem_sups Finset.mem_supsₓ'. -/
@[simp]
theorem mem_sups : c ∈ s ⊻ t ↔ ∃ a ∈ s, ∃ b ∈ t, a ⊔ b = c := by simp [(· ⊻ ·)]
#align finset.mem_sups Finset.mem_sups

variable (s t)

#print Finset.coe_sups /-
@[simp, norm_cast]
theorem coe_sups : (↑(s ⊻ t) : Set α) = s ⊻ t :=
  coe_image₂ _ _ _
#align finset.coe_sups Finset.coe_sups
-/

#print Finset.card_sups_le /-
theorem card_sups_le : (s ⊻ t).card ≤ s.card * t.card :=
  card_image₂_le _ _ _
#align finset.card_sups_le Finset.card_sups_le
-/

/- warning: finset.card_sups_iff -> Finset.card_sups_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Iff (Eq.{1} Nat (Finset.card.{u1} α (HasSups.sups.{u1} (Finset.{u1} α) (Finset.hasSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (Finset.card.{u1} α s) (Finset.card.{u1} α t))) (Set.InjOn.{u1, u1} (Prod.{u1, u1} α α) α (fun (x : Prod.{u1, u1} α α) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_2) (Prod.fst.{u1, u1} α α x) (Prod.snd.{u1, u1} α α x)) (Set.prod.{u1, u1} α α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Iff (Eq.{1} Nat (Finset.card.{u1} α (HasSups.sups.{u1} (Finset.{u1} α) (Finset.hasSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (Finset.card.{u1} α s) (Finset.card.{u1} α t))) (Set.InjOn.{u1, u1} (Prod.{u1, u1} α α) α (fun (x : Prod.{u1, u1} α α) => Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_2) (Prod.fst.{u1, u1} α α x) (Prod.snd.{u1, u1} α α x)) (Set.prod.{u1, u1} α α (Finset.toSet.{u1} α s) (Finset.toSet.{u1} α t)))
Case conversion may be inaccurate. Consider using '#align finset.card_sups_iff Finset.card_sups_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem card_sups_iff :
    (s ⊻ t).card = s.card * t.card ↔ (s ×ˢ t : Set (α × α)).InjOn fun x => x.1 ⊔ x.2 :=
  card_image₂_iff
#align finset.card_sups_iff Finset.card_sups_iff

variable {s s₁ s₂ t t₁ t₂ u}

/- warning: finset.sup_mem_sups -> Finset.sup_mem_sups is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {a : α} {b : α}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) b t) -> (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_2) a b) (HasSups.sups.{u1} (Finset.{u1} α) (Finset.hasSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {a : α} {b : α}, (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) b t) -> (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_2) a b) (HasSups.sups.{u1} (Finset.{u1} α) (Finset.hasSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t))
Case conversion may be inaccurate. Consider using '#align finset.sup_mem_sups Finset.sup_mem_supsₓ'. -/
theorem sup_mem_sups : a ∈ s → b ∈ t → a ⊔ b ∈ s ⊻ t :=
  mem_image₂_of_mem
#align finset.sup_mem_sups Finset.sup_mem_sups

#print Finset.sups_subset /-
theorem sups_subset : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ ⊻ t₁ ⊆ s₂ ⊻ t₂ :=
  image₂_subset
#align finset.sups_subset Finset.sups_subset
-/

#print Finset.sups_subset_left /-
theorem sups_subset_left : t₁ ⊆ t₂ → s ⊻ t₁ ⊆ s ⊻ t₂ :=
  image₂_subset_left
#align finset.sups_subset_left Finset.sups_subset_left
-/

#print Finset.sups_subset_right /-
theorem sups_subset_right : s₁ ⊆ s₂ → s₁ ⊻ t ⊆ s₂ ⊻ t :=
  image₂_subset_right
#align finset.sups_subset_right Finset.sups_subset_right
-/

/- warning: finset.image_subset_sups_left -> Finset.image_subset_sups_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {b : α}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) b t) -> (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_2) a b) s) (HasSups.sups.{u1} (Finset.{u1} α) (Finset.hasSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {b : α}, (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) b t) -> (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_2) a b) s) (HasSups.sups.{u1} (Finset.{u1} α) (Finset.hasSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t))
Case conversion may be inaccurate. Consider using '#align finset.image_subset_sups_left Finset.image_subset_sups_leftₓ'. -/
theorem image_subset_sups_left : b ∈ t → (s.image fun a => a ⊔ b) ⊆ s ⊻ t :=
  image_subset_image₂_left
#align finset.image_subset_sups_left Finset.image_subset_sups_left

/- warning: finset.image_subset_sups_right -> Finset.image_subset_sups_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {a : α}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_2) a) t) (HasSups.sups.{u1} (Finset.{u1} α) (Finset.hasSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {a : α}, (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (x._@.Mathlib.Data.Finset.Sups._hyg.772 : α) => Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_2) a x._@.Mathlib.Data.Finset.Sups._hyg.772) t) (HasSups.sups.{u1} (Finset.{u1} α) (Finset.hasSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t))
Case conversion may be inaccurate. Consider using '#align finset.image_subset_sups_right Finset.image_subset_sups_rightₓ'. -/
theorem image_subset_sups_right : a ∈ s → t.image ((· ⊔ ·) a) ⊆ s ⊻ t :=
  image_subset_image₂_right
#align finset.image_subset_sups_right Finset.image_subset_sups_right

/- warning: finset.forall_sups_iff -> Finset.forall_sups_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {p : α -> Prop}, Iff (forall (c : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) c (HasSups.sups.{u1} (Finset.{u1} α) (Finset.hasSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t)) -> (p c)) (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (forall (b : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) b t) -> (p (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_2) a b))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {p : α -> Prop}, Iff (forall (c : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) c (HasSups.sups.{u1} (Finset.{u1} α) (Finset.hasSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t)) -> (p c)) (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (forall (b : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) b t) -> (p (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_2) a b))))
Case conversion may be inaccurate. Consider using '#align finset.forall_sups_iff Finset.forall_sups_iffₓ'. -/
theorem forall_sups_iff {p : α → Prop} : (∀ c ∈ s ⊻ t, p c) ↔ ∀ a ∈ s, ∀ b ∈ t, p (a ⊔ b) :=
  forall_image₂_iff
#align finset.forall_sups_iff Finset.forall_sups_iff

/- warning: finset.sups_subset_iff -> Finset.sups_subset_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {u : Finset.{u1} α}, Iff (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (HasSups.sups.{u1} (Finset.{u1} α) (Finset.hasSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t) u) (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (forall (b : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) b t) -> (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_2) a b) u)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {u : Finset.{u1} α}, Iff (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) (HasSups.sups.{u1} (Finset.{u1} α) (Finset.hasSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t) u) (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (forall (b : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) b t) -> (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_2) a b) u)))
Case conversion may be inaccurate. Consider using '#align finset.sups_subset_iff Finset.sups_subset_iffₓ'. -/
@[simp]
theorem sups_subset_iff : s ⊻ t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a ⊔ b ∈ u :=
  image₂_subset_iff
#align finset.sups_subset_iff Finset.sups_subset_iff

#print Finset.sups_nonempty /-
@[simp]
theorem sups_nonempty : (s ⊻ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image₂_nonempty_iff
#align finset.sups_nonempty Finset.sups_nonempty
-/

#print Finset.Nonempty.sups /-
protected theorem Nonempty.sups : s.Nonempty → t.Nonempty → (s ⊻ t).Nonempty :=
  Nonempty.image₂
#align finset.nonempty.sups Finset.Nonempty.sups
-/

#print Finset.Nonempty.of_sups_left /-
theorem Nonempty.of_sups_left : (s ⊻ t).Nonempty → s.Nonempty :=
  Nonempty.of_image₂_left
#align finset.nonempty.of_sups_left Finset.Nonempty.of_sups_left
-/

#print Finset.Nonempty.of_sups_right /-
theorem Nonempty.of_sups_right : (s ⊻ t).Nonempty → t.Nonempty :=
  Nonempty.of_image₂_right
#align finset.nonempty.of_sups_right Finset.Nonempty.of_sups_right
-/

#print Finset.empty_sups /-
@[simp]
theorem empty_sups : ∅ ⊻ t = ∅ :=
  image₂_empty_left
#align finset.empty_sups Finset.empty_sups
-/

#print Finset.sups_empty /-
@[simp]
theorem sups_empty : s ⊻ ∅ = ∅ :=
  image₂_empty_right
#align finset.sups_empty Finset.sups_empty
-/

#print Finset.sups_eq_empty /-
@[simp]
theorem sups_eq_empty : s ⊻ t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image₂_eq_empty_iff
#align finset.sups_eq_empty Finset.sups_eq_empty
-/

/- warning: finset.singleton_sups -> Finset.singleton_sups is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] {t : Finset.{u1} α} {a : α}, Eq.{succ u1} (Finset.{u1} α) (HasSups.sups.{u1} (Finset.{u1} α) (Finset.hasSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a) t) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (b : α) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_2) a b) t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] {t : Finset.{u1} α} {a : α}, Eq.{succ u1} (Finset.{u1} α) (HasSups.sups.{u1} (Finset.{u1} α) (Finset.hasSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a) t) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (b : α) => Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_2) a b) t)
Case conversion may be inaccurate. Consider using '#align finset.singleton_sups Finset.singleton_supsₓ'. -/
@[simp]
theorem singleton_sups : {a} ⊻ t = t.image fun b => a ⊔ b :=
  image₂_singleton_left
#align finset.singleton_sups Finset.singleton_sups

/- warning: finset.sups_singleton -> Finset.sups_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] {s : Finset.{u1} α} {b : α}, Eq.{succ u1} (Finset.{u1} α) (HasSups.sups.{u1} (Finset.{u1} α) (Finset.hasSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) b)) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_2) a b) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] {s : Finset.{u1} α} {b : α}, Eq.{succ u1} (Finset.{u1} α) (HasSups.sups.{u1} (Finset.{u1} α) (Finset.hasSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) b)) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_2) a b) s)
Case conversion may be inaccurate. Consider using '#align finset.sups_singleton Finset.sups_singletonₓ'. -/
@[simp]
theorem sups_singleton : s ⊻ {b} = s.image fun a => a ⊔ b :=
  image₂_singleton_right
#align finset.sups_singleton Finset.sups_singleton

/- warning: finset.singleton_sups_singleton -> Finset.singleton_sups_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] {a : α} {b : α}, Eq.{succ u1} (Finset.{u1} α) (HasSups.sups.{u1} (Finset.{u1} α) (Finset.hasSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) b)) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_2) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] {a : α} {b : α}, Eq.{succ u1} (Finset.{u1} α) (HasSups.sups.{u1} (Finset.{u1} α) (Finset.hasSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) b)) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_2) a b))
Case conversion may be inaccurate. Consider using '#align finset.singleton_sups_singleton Finset.singleton_sups_singletonₓ'. -/
theorem singleton_sups_singleton : ({a} ⊻ {b} : Finset α) = {a ⊔ b} :=
  image₂_singleton
#align finset.singleton_sups_singleton Finset.singleton_sups_singleton

#print Finset.sups_union_left /-
theorem sups_union_left : (s₁ ∪ s₂) ⊻ t = s₁ ⊻ t ∪ s₂ ⊻ t :=
  image₂_union_left
#align finset.sups_union_left Finset.sups_union_left
-/

#print Finset.sups_union_right /-
theorem sups_union_right : s ⊻ (t₁ ∪ t₂) = s ⊻ t₁ ∪ s ⊻ t₂ :=
  image₂_union_right
#align finset.sups_union_right Finset.sups_union_right
-/

#print Finset.sups_inter_subset_left /-
theorem sups_inter_subset_left : (s₁ ∩ s₂) ⊻ t ⊆ s₁ ⊻ t ∩ s₂ ⊻ t :=
  image₂_inter_subset_left
#align finset.sups_inter_subset_left Finset.sups_inter_subset_left
-/

#print Finset.sups_inter_subset_right /-
theorem sups_inter_subset_right : s ⊻ (t₁ ∩ t₂) ⊆ s ⊻ t₁ ∩ s ⊻ t₂ :=
  image₂_inter_subset_right
#align finset.sups_inter_subset_right Finset.sups_inter_subset_right
-/

#print Finset.subset_sups /-
theorem subset_sups {s t : Set α} :
    ↑u ⊆ s ⊻ t → ∃ s' t' : Finset α, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' ⊻ t' :=
  subset_image₂
#align finset.subset_sups Finset.subset_sups
-/

variable (s t u v)

/- warning: finset.bUnion_image_sup_left -> Finset.bunionᵢ_image_sup_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (Finset.bunionᵢ.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) s (fun (a : α) => Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_2) a) t)) (HasSups.sups.{u1} (Finset.{u1} α) (Finset.hasSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (Finset.bunionᵢ.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) s (fun (a : α) => Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) ((fun (x._@.Mathlib.Data.Finset.Sups._hyg.1857 : α) (x._@.Mathlib.Data.Finset.Sups._hyg.1859 : α) => Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_2) x._@.Mathlib.Data.Finset.Sups._hyg.1857 x._@.Mathlib.Data.Finset.Sups._hyg.1859) a) t)) (HasSups.sups.{u1} (Finset.{u1} α) (Finset.hasSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t)
Case conversion may be inaccurate. Consider using '#align finset.bUnion_image_sup_left Finset.bunionᵢ_image_sup_leftₓ'. -/
theorem bunionᵢ_image_sup_left : (s.bunionᵢ fun a => t.image <| (· ⊔ ·) a) = s ⊻ t :=
  bunionᵢ_image_left
#align finset.bUnion_image_sup_left Finset.bunionᵢ_image_sup_left

/- warning: finset.bUnion_image_sup_right -> Finset.bunionᵢ_image_sup_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (Finset.bunionᵢ.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) t (fun (b : α) => Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_2) a b) s)) (HasSups.sups.{u1} (Finset.{u1} α) (Finset.hasSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (Finset.bunionᵢ.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) t (fun (b : α) => Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_2) a b) s)) (HasSups.sups.{u1} (Finset.{u1} α) (Finset.hasSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t)
Case conversion may be inaccurate. Consider using '#align finset.bUnion_image_sup_right Finset.bunionᵢ_image_sup_rightₓ'. -/
theorem bunionᵢ_image_sup_right : (t.bunionᵢ fun b => s.image fun a => a ⊔ b) = s ⊻ t :=
  bunionᵢ_image_right
#align finset.bUnion_image_sup_right Finset.bunionᵢ_image_sup_right

/- warning: finset.image_sup_product -> Finset.image_sup_product is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (Finset.image.{u1, u1} (Prod.{u1, u1} α α) α (fun (a : α) (b : α) => _inst_1 a b) (Function.uncurry.{u1, u1, u1} α α α (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_2))) (Finset.product.{u1, u1} α α s t)) (HasSups.sups.{u1} (Finset.{u1} α) (Finset.hasSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (Finset.image.{u1, u1} (Prod.{u1, u1} α α) α (fun (a : α) (b : α) => _inst_1 a b) (Function.uncurry.{u1, u1, u1} α α α (fun (x._@.Mathlib.Data.Finset.Sups._hyg.1973 : α) (x._@.Mathlib.Data.Finset.Sups._hyg.1975 : α) => Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_2) x._@.Mathlib.Data.Finset.Sups._hyg.1973 x._@.Mathlib.Data.Finset.Sups._hyg.1975)) (Finset.product.{u1, u1} α α s t)) (HasSups.sups.{u1} (Finset.{u1} α) (Finset.hasSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t)
Case conversion may be inaccurate. Consider using '#align finset.image_sup_product Finset.image_sup_productₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem image_sup_product (s t : Finset α) : (s ×ˢ t).image (uncurry (· ⊔ ·)) = s ⊻ t :=
  image_uncurry_product _ _ _
#align finset.image_sup_product Finset.image_sup_product

#print Finset.sups_assoc /-
theorem sups_assoc : s ⊻ t ⊻ u = s ⊻ (t ⊻ u) :=
  image₂_assoc fun _ _ _ => sup_assoc
#align finset.sups_assoc Finset.sups_assoc
-/

#print Finset.sups_comm /-
theorem sups_comm : s ⊻ t = t ⊻ s :=
  image₂_comm fun _ _ => sup_comm
#align finset.sups_comm Finset.sups_comm
-/

#print Finset.sups_left_comm /-
theorem sups_left_comm : s ⊻ (t ⊻ u) = t ⊻ (s ⊻ u) :=
  image₂_left_comm sup_left_comm
#align finset.sups_left_comm Finset.sups_left_comm
-/

#print Finset.sups_right_comm /-
theorem sups_right_comm : s ⊻ t ⊻ u = s ⊻ u ⊻ t :=
  image₂_right_comm sup_right_comm
#align finset.sups_right_comm Finset.sups_right_comm
-/

#print Finset.sups_sups_sups_comm /-
theorem sups_sups_sups_comm : s ⊻ t ⊻ (u ⊻ v) = s ⊻ u ⊻ (t ⊻ v) :=
  image₂_image₂_image₂_comm sup_sup_sup_comm
#align finset.sups_sups_sups_comm Finset.sups_sups_sups_comm
-/

end Sups

section Infs

variable [SemilatticeInf α] (s s₁ s₂ t t₁ t₂ u v : Finset α)

#print Finset.hasInfs /-
/-- `s ⊼ t` is the finset of elements of the form `a ⊓ b` where `a ∈ s`, `b ∈ t`. -/
protected def hasInfs : HasInfs (Finset α) :=
  ⟨image₂ (· ⊓ ·)⟩
#align finset.has_infs Finset.hasInfs
-/

scoped[FinsetFamily] attribute [instance] Finset.hasInfs

variable {s t} {a b c : α}

/- warning: finset.mem_infs -> Finset.mem_infs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeInf.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {c : α}, Iff (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) c (HasInfs.infs.{u1} (Finset.{u1} α) (Finset.hasInfs.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Exists.{succ u1} α (fun (b : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) b t) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) b t) => Eq.{succ u1} α (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_2) a b) c)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeInf.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {c : α}, Iff (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) c (HasInfs.infs.{u1} (Finset.{u1} α) (Finset.hasInfs.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t)) (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) (Exists.{succ u1} α (fun (b : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) b t) (Eq.{succ u1} α (Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_2) a b) c)))))
Case conversion may be inaccurate. Consider using '#align finset.mem_infs Finset.mem_infsₓ'. -/
@[simp]
theorem mem_infs : c ∈ s ⊼ t ↔ ∃ a ∈ s, ∃ b ∈ t, a ⊓ b = c := by simp [(· ⊼ ·)]
#align finset.mem_infs Finset.mem_infs

variable (s t)

#print Finset.coe_infs /-
@[simp, norm_cast]
theorem coe_infs : (↑(s ⊼ t) : Set α) = s ⊼ t :=
  coe_image₂ _ _ _
#align finset.coe_infs Finset.coe_infs
-/

#print Finset.card_infs_le /-
theorem card_infs_le : (s ⊼ t).card ≤ s.card * t.card :=
  card_image₂_le _ _ _
#align finset.card_infs_le Finset.card_infs_le
-/

/- warning: finset.card_infs_iff -> Finset.card_infs_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeInf.{u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Iff (Eq.{1} Nat (Finset.card.{u1} α (HasInfs.infs.{u1} (Finset.{u1} α) (Finset.hasInfs.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (Finset.card.{u1} α s) (Finset.card.{u1} α t))) (Set.InjOn.{u1, u1} (Prod.{u1, u1} α α) α (fun (x : Prod.{u1, u1} α α) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_2) (Prod.fst.{u1, u1} α α x) (Prod.snd.{u1, u1} α α x)) (Set.prod.{u1, u1} α α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeInf.{u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Iff (Eq.{1} Nat (Finset.card.{u1} α (HasInfs.infs.{u1} (Finset.{u1} α) (Finset.hasInfs.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (Finset.card.{u1} α s) (Finset.card.{u1} α t))) (Set.InjOn.{u1, u1} (Prod.{u1, u1} α α) α (fun (x : Prod.{u1, u1} α α) => Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_2) (Prod.fst.{u1, u1} α α x) (Prod.snd.{u1, u1} α α x)) (Set.prod.{u1, u1} α α (Finset.toSet.{u1} α s) (Finset.toSet.{u1} α t)))
Case conversion may be inaccurate. Consider using '#align finset.card_infs_iff Finset.card_infs_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem card_infs_iff :
    (s ⊼ t).card = s.card * t.card ↔ (s ×ˢ t : Set (α × α)).InjOn fun x => x.1 ⊓ x.2 :=
  card_image₂_iff
#align finset.card_infs_iff Finset.card_infs_iff

variable {s s₁ s₂ t t₁ t₂ u}

/- warning: finset.inf_mem_infs -> Finset.inf_mem_infs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeInf.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {a : α} {b : α}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) b t) -> (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_2) a b) (HasInfs.infs.{u1} (Finset.{u1} α) (Finset.hasInfs.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeInf.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {a : α} {b : α}, (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) b t) -> (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) (Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_2) a b) (HasInfs.infs.{u1} (Finset.{u1} α) (Finset.hasInfs.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t))
Case conversion may be inaccurate. Consider using '#align finset.inf_mem_infs Finset.inf_mem_infsₓ'. -/
theorem inf_mem_infs : a ∈ s → b ∈ t → a ⊓ b ∈ s ⊼ t :=
  mem_image₂_of_mem
#align finset.inf_mem_infs Finset.inf_mem_infs

#print Finset.infs_subset /-
theorem infs_subset : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ ⊼ t₁ ⊆ s₂ ⊼ t₂ :=
  image₂_subset
#align finset.infs_subset Finset.infs_subset
-/

#print Finset.infs_subset_left /-
theorem infs_subset_left : t₁ ⊆ t₂ → s ⊼ t₁ ⊆ s ⊼ t₂ :=
  image₂_subset_left
#align finset.infs_subset_left Finset.infs_subset_left
-/

#print Finset.infs_subset_right /-
theorem infs_subset_right : s₁ ⊆ s₂ → s₁ ⊼ t ⊆ s₂ ⊼ t :=
  image₂_subset_right
#align finset.infs_subset_right Finset.infs_subset_right
-/

/- warning: finset.image_subset_infs_left -> Finset.image_subset_infs_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeInf.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {b : α}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) b t) -> (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_2) a b) s) (HasInfs.infs.{u1} (Finset.{u1} α) (Finset.hasInfs.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeInf.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {b : α}, (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) b t) -> (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_2) a b) s) (HasInfs.infs.{u1} (Finset.{u1} α) (Finset.hasInfs.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t))
Case conversion may be inaccurate. Consider using '#align finset.image_subset_infs_left Finset.image_subset_infs_leftₓ'. -/
theorem image_subset_infs_left : b ∈ t → (s.image fun a => a ⊓ b) ⊆ s ⊼ t :=
  image_subset_image₂_left
#align finset.image_subset_infs_left Finset.image_subset_infs_left

/- warning: finset.image_subset_infs_right -> Finset.image_subset_infs_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeInf.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {a : α}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_2) a) t) (HasInfs.infs.{u1} (Finset.{u1} α) (Finset.hasInfs.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeInf.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {a : α}, (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (x._@.Mathlib.Data.Finset.Sups._hyg.3023 : α) => Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_2) a x._@.Mathlib.Data.Finset.Sups._hyg.3023) t) (HasInfs.infs.{u1} (Finset.{u1} α) (Finset.hasInfs.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t))
Case conversion may be inaccurate. Consider using '#align finset.image_subset_infs_right Finset.image_subset_infs_rightₓ'. -/
theorem image_subset_infs_right : a ∈ s → t.image ((· ⊓ ·) a) ⊆ s ⊼ t :=
  image_subset_image₂_right
#align finset.image_subset_infs_right Finset.image_subset_infs_right

/- warning: finset.forall_infs_iff -> Finset.forall_infs_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeInf.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {p : α -> Prop}, Iff (forall (c : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) c (HasInfs.infs.{u1} (Finset.{u1} α) (Finset.hasInfs.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t)) -> (p c)) (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (forall (b : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) b t) -> (p (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_2) a b))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeInf.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {p : α -> Prop}, Iff (forall (c : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) c (HasInfs.infs.{u1} (Finset.{u1} α) (Finset.hasInfs.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t)) -> (p c)) (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (forall (b : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) b t) -> (p (Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_2) a b))))
Case conversion may be inaccurate. Consider using '#align finset.forall_infs_iff Finset.forall_infs_iffₓ'. -/
theorem forall_infs_iff {p : α → Prop} : (∀ c ∈ s ⊼ t, p c) ↔ ∀ a ∈ s, ∀ b ∈ t, p (a ⊓ b) :=
  forall_image₂_iff
#align finset.forall_infs_iff Finset.forall_infs_iff

/- warning: finset.infs_subset_iff -> Finset.infs_subset_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeInf.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {u : Finset.{u1} α}, Iff (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (HasInfs.infs.{u1} (Finset.{u1} α) (Finset.hasInfs.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t) u) (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (forall (b : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) b t) -> (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_2) a b) u)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeInf.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {u : Finset.{u1} α}, Iff (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) (HasInfs.infs.{u1} (Finset.{u1} α) (Finset.hasInfs.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t) u) (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (forall (b : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) b t) -> (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) (Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_2) a b) u)))
Case conversion may be inaccurate. Consider using '#align finset.infs_subset_iff Finset.infs_subset_iffₓ'. -/
@[simp]
theorem infs_subset_iff : s ⊼ t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a ⊓ b ∈ u :=
  image₂_subset_iff
#align finset.infs_subset_iff Finset.infs_subset_iff

#print Finset.infs_nonempty /-
@[simp]
theorem infs_nonempty : (s ⊼ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image₂_nonempty_iff
#align finset.infs_nonempty Finset.infs_nonempty
-/

#print Finset.Nonempty.infs /-
protected theorem Nonempty.infs : s.Nonempty → t.Nonempty → (s ⊼ t).Nonempty :=
  Nonempty.image₂
#align finset.nonempty.infs Finset.Nonempty.infs
-/

#print Finset.Nonempty.of_infs_left /-
theorem Nonempty.of_infs_left : (s ⊼ t).Nonempty → s.Nonempty :=
  Nonempty.of_image₂_left
#align finset.nonempty.of_infs_left Finset.Nonempty.of_infs_left
-/

#print Finset.Nonempty.of_infs_right /-
theorem Nonempty.of_infs_right : (s ⊼ t).Nonempty → t.Nonempty :=
  Nonempty.of_image₂_right
#align finset.nonempty.of_infs_right Finset.Nonempty.of_infs_right
-/

#print Finset.empty_infs /-
@[simp]
theorem empty_infs : ∅ ⊼ t = ∅ :=
  image₂_empty_left
#align finset.empty_infs Finset.empty_infs
-/

#print Finset.infs_empty /-
@[simp]
theorem infs_empty : s ⊼ ∅ = ∅ :=
  image₂_empty_right
#align finset.infs_empty Finset.infs_empty
-/

#print Finset.infs_eq_empty /-
@[simp]
theorem infs_eq_empty : s ⊼ t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image₂_eq_empty_iff
#align finset.infs_eq_empty Finset.infs_eq_empty
-/

/- warning: finset.singleton_infs -> Finset.singleton_infs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeInf.{u1} α] {t : Finset.{u1} α} {a : α}, Eq.{succ u1} (Finset.{u1} α) (HasInfs.infs.{u1} (Finset.{u1} α) (Finset.hasInfs.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a) t) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (b : α) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_2) a b) t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeInf.{u1} α] {t : Finset.{u1} α} {a : α}, Eq.{succ u1} (Finset.{u1} α) (HasInfs.infs.{u1} (Finset.{u1} α) (Finset.hasInfs.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a) t) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (b : α) => Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_2) a b) t)
Case conversion may be inaccurate. Consider using '#align finset.singleton_infs Finset.singleton_infsₓ'. -/
@[simp]
theorem singleton_infs : {a} ⊼ t = t.image fun b => a ⊓ b :=
  image₂_singleton_left
#align finset.singleton_infs Finset.singleton_infs

/- warning: finset.infs_singleton -> Finset.infs_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeInf.{u1} α] {s : Finset.{u1} α} {b : α}, Eq.{succ u1} (Finset.{u1} α) (HasInfs.infs.{u1} (Finset.{u1} α) (Finset.hasInfs.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) b)) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_2) a b) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeInf.{u1} α] {s : Finset.{u1} α} {b : α}, Eq.{succ u1} (Finset.{u1} α) (HasInfs.infs.{u1} (Finset.{u1} α) (Finset.hasInfs.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) b)) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_2) a b) s)
Case conversion may be inaccurate. Consider using '#align finset.infs_singleton Finset.infs_singletonₓ'. -/
@[simp]
theorem infs_singleton : s ⊼ {b} = s.image fun a => a ⊓ b :=
  image₂_singleton_right
#align finset.infs_singleton Finset.infs_singleton

/- warning: finset.singleton_infs_singleton -> Finset.singleton_infs_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeInf.{u1} α] {a : α} {b : α}, Eq.{succ u1} (Finset.{u1} α) (HasInfs.infs.{u1} (Finset.{u1} α) (Finset.hasInfs.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) b)) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_2) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeInf.{u1} α] {a : α} {b : α}, Eq.{succ u1} (Finset.{u1} α) (HasInfs.infs.{u1} (Finset.{u1} α) (Finset.hasInfs.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) b)) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) (Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_2) a b))
Case conversion may be inaccurate. Consider using '#align finset.singleton_infs_singleton Finset.singleton_infs_singletonₓ'. -/
theorem singleton_infs_singleton : ({a} ⊼ {b} : Finset α) = {a ⊓ b} :=
  image₂_singleton
#align finset.singleton_infs_singleton Finset.singleton_infs_singleton

#print Finset.infs_union_left /-
theorem infs_union_left : (s₁ ∪ s₂) ⊼ t = s₁ ⊼ t ∪ s₂ ⊼ t :=
  image₂_union_left
#align finset.infs_union_left Finset.infs_union_left
-/

#print Finset.infs_union_right /-
theorem infs_union_right : s ⊼ (t₁ ∪ t₂) = s ⊼ t₁ ∪ s ⊼ t₂ :=
  image₂_union_right
#align finset.infs_union_right Finset.infs_union_right
-/

#print Finset.infs_inter_subset_left /-
theorem infs_inter_subset_left : (s₁ ∩ s₂) ⊼ t ⊆ s₁ ⊼ t ∩ s₂ ⊼ t :=
  image₂_inter_subset_left
#align finset.infs_inter_subset_left Finset.infs_inter_subset_left
-/

#print Finset.infs_inter_subset_right /-
theorem infs_inter_subset_right : s ⊼ (t₁ ∩ t₂) ⊆ s ⊼ t₁ ∩ s ⊼ t₂ :=
  image₂_inter_subset_right
#align finset.infs_inter_subset_right Finset.infs_inter_subset_right
-/

#print Finset.subset_infs /-
theorem subset_infs {s t : Set α} :
    ↑u ⊆ s ⊼ t → ∃ s' t' : Finset α, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' ⊼ t' :=
  subset_image₂
#align finset.subset_infs Finset.subset_infs
-/

variable (s t u v)

/- warning: finset.bUnion_image_inf_left -> Finset.bunionᵢ_image_inf_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeInf.{u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (Finset.bunionᵢ.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) s (fun (a : α) => Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_2) a) t)) (HasInfs.infs.{u1} (Finset.{u1} α) (Finset.hasInfs.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeInf.{u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (Finset.bunionᵢ.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) s (fun (a : α) => Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) ((fun (x._@.Mathlib.Data.Finset.Sups._hyg.4108 : α) (x._@.Mathlib.Data.Finset.Sups._hyg.4110 : α) => Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_2) x._@.Mathlib.Data.Finset.Sups._hyg.4108 x._@.Mathlib.Data.Finset.Sups._hyg.4110) a) t)) (HasInfs.infs.{u1} (Finset.{u1} α) (Finset.hasInfs.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t)
Case conversion may be inaccurate. Consider using '#align finset.bUnion_image_inf_left Finset.bunionᵢ_image_inf_leftₓ'. -/
theorem bunionᵢ_image_inf_left : (s.bunionᵢ fun a => t.image <| (· ⊓ ·) a) = s ⊼ t :=
  bunionᵢ_image_left
#align finset.bUnion_image_inf_left Finset.bunionᵢ_image_inf_left

/- warning: finset.bUnion_image_inf_right -> Finset.bunionᵢ_image_inf_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeInf.{u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (Finset.bunionᵢ.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) t (fun (b : α) => Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_2) a b) s)) (HasInfs.infs.{u1} (Finset.{u1} α) (Finset.hasInfs.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeInf.{u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (Finset.bunionᵢ.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) t (fun (b : α) => Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_2) a b) s)) (HasInfs.infs.{u1} (Finset.{u1} α) (Finset.hasInfs.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t)
Case conversion may be inaccurate. Consider using '#align finset.bUnion_image_inf_right Finset.bunionᵢ_image_inf_rightₓ'. -/
theorem bunionᵢ_image_inf_right : (t.bunionᵢ fun b => s.image fun a => a ⊓ b) = s ⊼ t :=
  bunionᵢ_image_right
#align finset.bUnion_image_inf_right Finset.bunionᵢ_image_inf_right

/- warning: finset.image_inf_product -> Finset.image_inf_product is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeInf.{u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (Finset.image.{u1, u1} (Prod.{u1, u1} α α) α (fun (a : α) (b : α) => _inst_1 a b) (Function.uncurry.{u1, u1, u1} α α α (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_2))) (Finset.product.{u1, u1} α α s t)) (HasInfs.infs.{u1} (Finset.{u1} α) (Finset.hasInfs.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeInf.{u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (Finset.image.{u1, u1} (Prod.{u1, u1} α α) α (fun (a : α) (b : α) => _inst_1 a b) (Function.uncurry.{u1, u1, u1} α α α (fun (x._@.Mathlib.Data.Finset.Sups._hyg.4224 : α) (x._@.Mathlib.Data.Finset.Sups._hyg.4226 : α) => Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_2) x._@.Mathlib.Data.Finset.Sups._hyg.4224 x._@.Mathlib.Data.Finset.Sups._hyg.4226)) (Finset.product.{u1, u1} α α s t)) (HasInfs.infs.{u1} (Finset.{u1} α) (Finset.hasInfs.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t)
Case conversion may be inaccurate. Consider using '#align finset.image_inf_product Finset.image_inf_productₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem image_inf_product (s t : Finset α) : (s ×ˢ t).image (uncurry (· ⊓ ·)) = s ⊼ t :=
  image_uncurry_product _ _ _
#align finset.image_inf_product Finset.image_inf_product

#print Finset.infs_assoc /-
theorem infs_assoc : s ⊼ t ⊼ u = s ⊼ (t ⊼ u) :=
  image₂_assoc fun _ _ _ => inf_assoc
#align finset.infs_assoc Finset.infs_assoc
-/

#print Finset.infs_comm /-
theorem infs_comm : s ⊼ t = t ⊼ s :=
  image₂_comm fun _ _ => inf_comm
#align finset.infs_comm Finset.infs_comm
-/

#print Finset.infs_left_comm /-
theorem infs_left_comm : s ⊼ (t ⊼ u) = t ⊼ (s ⊼ u) :=
  image₂_left_comm inf_left_comm
#align finset.infs_left_comm Finset.infs_left_comm
-/

#print Finset.infs_right_comm /-
theorem infs_right_comm : s ⊼ t ⊼ u = s ⊼ u ⊼ t :=
  image₂_right_comm inf_right_comm
#align finset.infs_right_comm Finset.infs_right_comm
-/

#print Finset.infs_infs_infs_comm /-
theorem infs_infs_infs_comm : s ⊼ t ⊼ (u ⊼ v) = s ⊼ u ⊼ (t ⊼ v) :=
  image₂_image₂_image₂_comm inf_inf_inf_comm
#align finset.infs_infs_infs_comm Finset.infs_infs_infs_comm
-/

end Infs

open FinsetFamily

section DistribLattice

variable [DistribLattice α] (s t u : Finset α)

#print Finset.sups_infs_subset_left /-
theorem sups_infs_subset_left : s ⊻ t ⊼ u ⊆ (s ⊻ t) ⊼ (s ⊻ u) :=
  image₂_distrib_subset_left fun _ _ _ => sup_inf_left
#align finset.sups_infs_subset_left Finset.sups_infs_subset_left
-/

#print Finset.sups_infs_subset_right /-
theorem sups_infs_subset_right : t ⊼ u ⊻ s ⊆ (t ⊻ s) ⊼ (u ⊻ s) :=
  image₂_distrib_subset_right fun _ _ _ => sup_inf_right
#align finset.sups_infs_subset_right Finset.sups_infs_subset_right
-/

#print Finset.infs_sups_subset_left /-
theorem infs_sups_subset_left : s ⊼ (t ⊻ u) ⊆ s ⊼ t ⊻ s ⊼ u :=
  image₂_distrib_subset_left fun _ _ _ => inf_sup_left
#align finset.infs_sups_subset_left Finset.infs_sups_subset_left
-/

#print Finset.infs_sups_subset_right /-
theorem infs_sups_subset_right : (t ⊻ u) ⊼ s ⊆ t ⊼ s ⊻ u ⊼ s :=
  image₂_distrib_subset_right fun _ _ _ => inf_sup_right
#align finset.infs_sups_subset_right Finset.infs_sups_subset_right
-/

end DistribLattice

section DisjSups

variable [SemilatticeSup α] [OrderBot α] [@DecidableRel α Disjoint] (s s₁ s₂ t t₁ t₂ u : Finset α)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Finset.disjSups /-
/-- The finset of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t` and `a` and `b` are disjoint.
-/
def disjSups : Finset α :=
  ((s ×ˢ t).filterₓ fun ab : α × α => Disjoint ab.1 ab.2).image fun ab => ab.1 ⊔ ab.2
#align finset.disj_sups Finset.disjSups
-/

-- mathport name: finset.disj_sups
scoped[FinsetFamily] infixl:74 " ○ " => Finset.disjSups

variable {s t u} {a b c : α}

/- warning: finset.mem_disj_sups -> Finset.mem_disjSups is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)))] [_inst_4 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2) _inst_3)] {s : Finset.{u1} α} {t : Finset.{u1} α} {c : α}, Iff (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) c (Finset.disjSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3 (fun (a : α) (b : α) => _inst_4 a b) s t)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Exists.{succ u1} α (fun (b : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) b t) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) b t) => And (Disjoint.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2) _inst_3 a b) (Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_2) a b) c))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)))] [_inst_4 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2) _inst_3)] {s : Finset.{u1} α} {t : Finset.{u1} α} {c : α}, Iff (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) c (Finset.disjSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3 (fun (a : α) (b : α) => _inst_4 a b) s t)) (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) (Exists.{succ u1} α (fun (b : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) b t) (And (Disjoint.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2) _inst_3 a b) (Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_2) a b) c))))))
Case conversion may be inaccurate. Consider using '#align finset.mem_disj_sups Finset.mem_disjSupsₓ'. -/
@[simp]
theorem mem_disjSups : c ∈ s ○ t ↔ ∃ a ∈ s, ∃ b ∈ t, Disjoint a b ∧ a ⊔ b = c := by
  simp [disj_sups, and_assoc']
#align finset.mem_disj_sups Finset.mem_disjSups

#print Finset.disjSups_subset_sups /-
theorem disjSups_subset_sups : s ○ t ⊆ s ⊻ t :=
  by
  simp_rw [subset_iff, mem_sups, mem_disj_sups]
  exact fun c ⟨a, b, ha, hb, h, hc⟩ => ⟨a, b, ha, hb, hc⟩
#align finset.disj_sups_subset_sups Finset.disjSups_subset_sups
-/

variable (s t)

#print Finset.card_disjSups_le /-
theorem card_disjSups_le : (s ○ t).card ≤ s.card * t.card :=
  (card_le_of_subset disjSups_subset_sups).trans <| card_sups_le _ _
#align finset.card_disj_sups_le Finset.card_disjSups_le
-/

variable {s s₁ s₂ t t₁ t₂ u}

#print Finset.disjSups_subset /-
theorem disjSups_subset (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : s₁ ○ t₁ ⊆ s₂ ○ t₂ :=
  image_subset_image <| filter_subset_filter _ <| product_subset_product hs ht
#align finset.disj_sups_subset Finset.disjSups_subset
-/

#print Finset.disjSups_subset_left /-
theorem disjSups_subset_left (ht : t₁ ⊆ t₂) : s ○ t₁ ⊆ s ○ t₂ :=
  disjSups_subset Subset.rfl ht
#align finset.disj_sups_subset_left Finset.disjSups_subset_left
-/

#print Finset.disjSups_subset_right /-
theorem disjSups_subset_right (hs : s₁ ⊆ s₂) : s₁ ○ t ⊆ s₂ ○ t :=
  disjSups_subset hs Subset.rfl
#align finset.disj_sups_subset_right Finset.disjSups_subset_right
-/

/- warning: finset.forall_disj_sups_iff -> Finset.forall_disjSups_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)))] [_inst_4 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2) _inst_3)] {s : Finset.{u1} α} {t : Finset.{u1} α} {p : α -> Prop}, Iff (forall (c : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) c (Finset.disjSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3 (fun (a : α) (b : α) => _inst_4 a b) s t)) -> (p c)) (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (forall (b : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) b t) -> (Disjoint.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2) _inst_3 a b) -> (p (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_2) a b))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)))] [_inst_4 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2) _inst_3)] {s : Finset.{u1} α} {t : Finset.{u1} α} {p : α -> Prop}, Iff (forall (c : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) c (Finset.disjSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3 (fun (a : α) (b : α) => _inst_4 a b) s t)) -> (p c)) (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (forall (b : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) b t) -> (Disjoint.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2) _inst_3 a b) -> (p (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_2) a b))))
Case conversion may be inaccurate. Consider using '#align finset.forall_disj_sups_iff Finset.forall_disjSups_iffₓ'. -/
theorem forall_disjSups_iff {p : α → Prop} :
    (∀ c ∈ s ○ t, p c) ↔ ∀ a ∈ s, ∀ b ∈ t, Disjoint a b → p (a ⊔ b) :=
  by
  simp_rw [mem_disj_sups]
  refine' ⟨fun h a ha b hb hab => h _ ⟨_, ha, _, hb, hab, rfl⟩, _⟩
  rintro h _ ⟨a, ha, b, hb, hab, rfl⟩
  exact h _ ha _ hb hab
#align finset.forall_disj_sups_iff Finset.forall_disjSups_iff

/- warning: finset.disj_sups_subset_iff -> Finset.disjSups_subset_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)))] [_inst_4 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2) _inst_3)] {s : Finset.{u1} α} {t : Finset.{u1} α} {u : Finset.{u1} α}, Iff (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (Finset.disjSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3 (fun (a : α) (b : α) => _inst_4 a b) s t) u) (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (forall (b : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) b t) -> (Disjoint.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2) _inst_3 a b) -> (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_2) a b) u)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)))] [_inst_4 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2) _inst_3)] {s : Finset.{u1} α} {t : Finset.{u1} α} {u : Finset.{u1} α}, Iff (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) (Finset.disjSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3 (fun (a : α) (b : α) => _inst_4 a b) s t) u) (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (forall (b : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) b t) -> (Disjoint.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2) _inst_3 a b) -> (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_2) a b) u)))
Case conversion may be inaccurate. Consider using '#align finset.disj_sups_subset_iff Finset.disjSups_subset_iffₓ'. -/
@[simp]
theorem disjSups_subset_iff : s ○ t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, Disjoint a b → a ⊔ b ∈ u :=
  forall_disjSups_iff
#align finset.disj_sups_subset_iff Finset.disjSups_subset_iff

#print Finset.Nonempty.of_disjSups_left /-
theorem Nonempty.of_disjSups_left : (s ○ t).Nonempty → s.Nonempty :=
  by
  simp_rw [Finset.Nonempty, mem_disj_sups]
  exact fun ⟨_, a, ha, _⟩ => ⟨a, ha⟩
#align finset.nonempty.of_disj_sups_left Finset.Nonempty.of_disjSups_left
-/

#print Finset.Nonempty.of_disjSups_right /-
theorem Nonempty.of_disjSups_right : (s ○ t).Nonempty → t.Nonempty :=
  by
  simp_rw [Finset.Nonempty, mem_disj_sups]
  exact fun ⟨_, _, _, b, hb, _⟩ => ⟨b, hb⟩
#align finset.nonempty.of_disj_sups_right Finset.Nonempty.of_disjSups_right
-/

#print Finset.disjSups_empty_left /-
@[simp]
theorem disjSups_empty_left : ∅ ○ t = ∅ := by simp [disj_sups]
#align finset.disj_sups_empty_left Finset.disjSups_empty_left
-/

#print Finset.disjSups_empty_right /-
@[simp]
theorem disjSups_empty_right : s ○ ∅ = ∅ := by simp [disj_sups]
#align finset.disj_sups_empty_right Finset.disjSups_empty_right
-/

/- warning: finset.disj_sups_singleton -> Finset.disjSups_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)))] [_inst_4 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2) _inst_3)] {a : α} {b : α}, Eq.{succ u1} (Finset.{u1} α) (Finset.disjSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3 (fun (a : α) (b : α) => _inst_4 a b) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) b)) (ite.{succ u1} (Finset.{u1} α) (Disjoint.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2) _inst_3 a b) (_inst_4 a b) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_2) a b)) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)))] [_inst_4 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2) _inst_3)] {a : α} {b : α}, Eq.{succ u1} (Finset.{u1} α) (Finset.disjSups.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3 (fun (a : α) (b : α) => _inst_4 a b) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) b)) (ite.{succ u1} (Finset.{u1} α) (Disjoint.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2) _inst_3 a b) (_inst_4 a b) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_2) a b)) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α)))
Case conversion may be inaccurate. Consider using '#align finset.disj_sups_singleton Finset.disjSups_singletonₓ'. -/
theorem disjSups_singleton : ({a} ○ {b} : Finset α) = if Disjoint a b then {a ⊔ b} else ∅ := by
  split_ifs <;> simp [disj_sups, filter_singleton, h]
#align finset.disj_sups_singleton Finset.disjSups_singleton

#print Finset.disjSups_union_left /-
theorem disjSups_union_left : (s₁ ∪ s₂) ○ t = s₁ ○ t ∪ s₂ ○ t := by
  simp [disj_sups, filter_union, image_union]
#align finset.disj_sups_union_left Finset.disjSups_union_left
-/

#print Finset.disjSups_union_right /-
theorem disjSups_union_right : s ○ (t₁ ∪ t₂) = s ○ t₁ ∪ s ○ t₂ := by
  simp [disj_sups, filter_union, image_union]
#align finset.disj_sups_union_right Finset.disjSups_union_right
-/

#print Finset.disjSups_inter_subset_left /-
theorem disjSups_inter_subset_left : (s₁ ∩ s₂) ○ t ⊆ s₁ ○ t ∩ s₂ ○ t := by
  simpa only [disj_sups, inter_product, filter_inter_distrib] using image_inter_subset _ _ _
#align finset.disj_sups_inter_subset_left Finset.disjSups_inter_subset_left
-/

#print Finset.disjSups_inter_subset_right /-
theorem disjSups_inter_subset_right : s ○ (t₁ ∩ t₂) ⊆ s ○ t₁ ∩ s ○ t₂ := by
  simpa only [disj_sups, product_inter, filter_inter_distrib] using image_inter_subset _ _ _
#align finset.disj_sups_inter_subset_right Finset.disjSups_inter_subset_right
-/

variable (s t)

#print Finset.disjSups_comm /-
theorem disjSups_comm : s ○ t = t ○ s := by
  ext
  rw [mem_disj_sups, exists₂_comm]
  simp [sup_comm, disjoint_comm]
#align finset.disj_sups_comm Finset.disjSups_comm
-/

end DisjSups

open FinsetFamily

section DistribLattice

variable [DistribLattice α] [OrderBot α] [@DecidableRel α Disjoint] (s t u v : Finset α)

#print Finset.disjSups_assoc /-
theorem disjSups_assoc : ∀ s t u : Finset α, s ○ t ○ u = s ○ (t ○ u) :=
  by
  refine' associative_of_commutative_of_le disj_sups_comm _
  simp only [le_eq_subset, disj_sups_subset_iff, mem_disj_sups]
  rintro s t u _ ⟨a, ha, b, hb, hab, rfl⟩ c hc habc
  rw [disjoint_sup_left] at habc
  exact ⟨a, ha, _, ⟨b, hb, c, hc, habc.2, rfl⟩, hab.sup_right habc.1, sup_assoc.symm⟩
#align finset.disj_sups_assoc Finset.disjSups_assoc
-/

#print Finset.disjSups_left_comm /-
theorem disjSups_left_comm : s ○ (t ○ u) = t ○ (s ○ u) := by
  simp_rw [← disj_sups_assoc, disj_sups_comm s]
#align finset.disj_sups_left_comm Finset.disjSups_left_comm
-/

#print Finset.disjSups_right_comm /-
theorem disjSups_right_comm : s ○ t ○ u = s ○ u ○ t := by simp_rw [disj_sups_assoc, disj_sups_comm]
#align finset.disj_sups_right_comm Finset.disjSups_right_comm
-/

#print Finset.disjSups_disjSups_disjSups_comm /-
theorem disjSups_disjSups_disjSups_comm : s ○ t ○ (u ○ v) = s ○ u ○ (t ○ v) := by
  simp_rw [← disj_sups_assoc, disj_sups_right_comm]
#align finset.disj_sups_disj_sups_disj_sups_comm Finset.disjSups_disjSups_disjSups_comm
-/

end DistribLattice

end Finset

