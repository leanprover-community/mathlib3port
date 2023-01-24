/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad

! This file was ported from Lean 3 source module data.finset.card
! leanprover-community/mathlib commit 8631e2d5ea77f6c13054d9151d82b83069680cb1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Image
import Mathbin.Tactic.ByContra

/-!
# Cardinality of a finite set

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This defines the cardinality of a `finset` and provides induction principles for finsets.

## Main declarations

* `finset.card`: `s.card : ℕ` returns the cardinality of `s : finset α`.

### Induction principles

* `finset.strong_induction`: Strong induction
* `finset.strong_induction_on`
* `finset.strong_downward_induction`
* `finset.strong_downward_induction_on`
* `finset.case_strong_induction_on`

## TODO

Should we add a noncomputable version?
-/


open Function Multiset Nat

variable {α β : Type _}

namespace Finset

variable {s t : Finset α} {a b : α}

#print Finset.card /-
/-- `s.card` is the number of elements of `s`, aka its cardinality. -/
def card (s : Finset α) : ℕ :=
  s.1.card
#align finset.card Finset.card
-/

/- warning: finset.card_def -> Finset.card_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Finset.{u1} α), Eq.{1} Nat (Finset.card.{u1} α s) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) (Finset.val.{u1} α s))
but is expected to have type
  forall {α : Type.{u1}} (s : Finset.{u1} α), Eq.{1} Nat (Finset.card.{u1} α s) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) (Finset.val.{u1} α s))
Case conversion may be inaccurate. Consider using '#align finset.card_def Finset.card_defₓ'. -/
theorem card_def (s : Finset α) : s.card = s.1.card :=
  rfl
#align finset.card_def Finset.card_def

/- warning: finset.card_mk -> Finset.card_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : Multiset.{u1} α} {nodup : Multiset.Nodup.{u1} α m}, Eq.{1} Nat (Finset.card.{u1} α (Finset.mk.{u1} α m nodup)) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) m)
but is expected to have type
  forall {α : Type.{u1}} {m : Multiset.{u1} α} {nodup : Multiset.Nodup.{u1} α m}, Eq.{1} Nat (Finset.card.{u1} α (Finset.mk.{u1} α m nodup)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) m)
Case conversion may be inaccurate. Consider using '#align finset.card_mk Finset.card_mkₓ'. -/
@[simp]
theorem card_mk {m nodup} : (⟨m, nodup⟩ : Finset α).card = m.card :=
  rfl
#align finset.card_mk Finset.card_mk

#print Finset.card_empty /-
@[simp]
theorem card_empty : card (∅ : Finset α) = 0 :=
  rfl
#align finset.card_empty Finset.card_empty
-/

#print Finset.card_le_of_subset /-
theorem card_le_of_subset : s ⊆ t → s.card ≤ t.card :=
  Multiset.card_le_of_le ∘ val_le_iff.mpr
#align finset.card_le_of_subset Finset.card_le_of_subset
-/

#print Finset.card_mono /-
@[mono]
theorem card_mono : Monotone (@card α) := by apply card_le_of_subset
#align finset.card_mono Finset.card_mono
-/

#print Finset.card_eq_zero /-
@[simp]
theorem card_eq_zero : s.card = 0 ↔ s = ∅ :=
  card_eq_zero.trans val_eq_zero
#align finset.card_eq_zero Finset.card_eq_zero
-/

#print Finset.card_pos /-
theorem card_pos : 0 < s.card ↔ s.Nonempty :=
  pos_iff_ne_zero.trans <| (not_congr card_eq_zero).trans nonempty_iff_ne_empty.symm
#align finset.card_pos Finset.card_pos
-/

alias card_pos ↔ _ nonempty.card_pos
#align finset.nonempty.card_pos Finset.Nonempty.card_pos

#print Finset.card_ne_zero_of_mem /-
theorem card_ne_zero_of_mem (h : a ∈ s) : s.card ≠ 0 :=
  (not_congr card_eq_zero).2 <| ne_empty_of_mem h
#align finset.card_ne_zero_of_mem Finset.card_ne_zero_of_mem
-/

#print Finset.card_singleton /-
@[simp]
theorem card_singleton (a : α) : card ({a} : Finset α) = 1 :=
  card_singleton _
#align finset.card_singleton Finset.card_singleton
-/

#print Finset.card_singleton_inter /-
theorem card_singleton_inter [DecidableEq α] : ({a} ∩ s).card ≤ 1 :=
  by
  cases Finset.decidableMem a s
  · simp [Finset.singleton_inter_of_not_mem h]
  · simp [Finset.singleton_inter_of_mem h]
#align finset.card_singleton_inter Finset.card_singleton_inter
-/

#print Finset.card_cons /-
@[simp]
theorem card_cons (h : a ∉ s) : (s.cons a h).card = s.card + 1 :=
  card_cons _ _
#align finset.card_cons Finset.card_cons
-/

section InsertErase

variable [DecidableEq α]

#print Finset.card_insert_of_not_mem /-
@[simp]
theorem card_insert_of_not_mem (h : a ∉ s) : (insert a s).card = s.card + 1 := by
  rw [← cons_eq_insert _ _ h, card_cons]
#align finset.card_insert_of_not_mem Finset.card_insert_of_not_mem
-/

#print Finset.card_insert_of_mem /-
theorem card_insert_of_mem (h : a ∈ s) : card (insert a s) = s.card := by rw [insert_eq_of_mem h]
#align finset.card_insert_of_mem Finset.card_insert_of_mem
-/

#print Finset.card_insert_le /-
theorem card_insert_le (a : α) (s : Finset α) : card (insert a s) ≤ s.card + 1 := by
  by_cases a ∈ s <;>
    [·
      rw [insert_eq_of_mem h]
      exact Nat.le_succ _, rw [card_insert_of_not_mem h]]
#align finset.card_insert_le Finset.card_insert_le
-/

#print Finset.card_insert_eq_ite /-
/-- If `a ∈ s` is known, see also `finset.card_insert_of_mem` and `finset.card_insert_of_not_mem`.
-/
theorem card_insert_eq_ite : card (insert a s) = if a ∈ s then s.card else s.card + 1 :=
  by
  by_cases h : a ∈ s
  · rw [card_insert_of_mem h, if_pos h]
  · rw [card_insert_of_not_mem h, if_neg h]
#align finset.card_insert_eq_ite Finset.card_insert_eq_ite
-/

#print Finset.card_doubleton /-
@[simp]
theorem card_doubleton (h : a ≠ b) : ({a, b} : Finset α).card = 2 := by
  rw [card_insert_of_not_mem (not_mem_singleton.2 h), card_singleton]
#align finset.card_doubleton Finset.card_doubleton
-/

#print Finset.card_erase_of_mem /-
@[simp]
theorem card_erase_of_mem : a ∈ s → (s.erase a).card = s.card - 1 :=
  card_erase_of_mem
#align finset.card_erase_of_mem Finset.card_erase_of_mem
-/

#print Finset.card_erase_add_one /-
@[simp]
theorem card_erase_add_one : a ∈ s → (s.erase a).card + 1 = s.card :=
  card_erase_add_one
#align finset.card_erase_add_one Finset.card_erase_add_one
-/

#print Finset.card_erase_lt_of_mem /-
theorem card_erase_lt_of_mem : a ∈ s → (s.erase a).card < s.card :=
  card_erase_lt_of_mem
#align finset.card_erase_lt_of_mem Finset.card_erase_lt_of_mem
-/

#print Finset.card_erase_le /-
theorem card_erase_le : (s.erase a).card ≤ s.card :=
  card_erase_le
#align finset.card_erase_le Finset.card_erase_le
-/

#print Finset.pred_card_le_card_erase /-
theorem pred_card_le_card_erase : s.card - 1 ≤ (s.erase a).card :=
  by
  by_cases h : a ∈ s
  · exact (card_erase_of_mem h).ge
  · rw [erase_eq_of_not_mem h]
    exact Nat.sub_le _ _
#align finset.pred_card_le_card_erase Finset.pred_card_le_card_erase
-/

#print Finset.card_erase_eq_ite /-
/-- If `a ∈ s` is known, see also `finset.card_erase_of_mem` and `finset.erase_eq_of_not_mem`. -/
theorem card_erase_eq_ite : (s.erase a).card = if a ∈ s then s.card - 1 else s.card :=
  card_erase_eq_ite
#align finset.card_erase_eq_ite Finset.card_erase_eq_ite
-/

end InsertErase

#print Finset.card_range /-
@[simp]
theorem card_range (n : ℕ) : (range n).card = n :=
  card_range n
#align finset.card_range Finset.card_range
-/

#print Finset.card_attach /-
@[simp]
theorem card_attach : s.attach.card = s.card :=
  Multiset.card_attach
#align finset.card_attach Finset.card_attach
-/

end Finset

section ToListMultiset

variable [DecidableEq α] (m : Multiset α) (l : List α)

/- warning: multiset.card_to_finset -> Multiset.card_toFinset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (m : Multiset.{u1} α), Eq.{1} Nat (Finset.card.{u1} α (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) m)) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) (Multiset.dedup.{u1} α (fun (a : α) (b : α) => _inst_1 a b) m))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (m : Multiset.{u1} α), Eq.{1} Nat (Finset.card.{u1} α (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) m)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) (Multiset.dedup.{u1} α (fun (a : α) (b : α) => _inst_1 a b) m))
Case conversion may be inaccurate. Consider using '#align multiset.card_to_finset Multiset.card_toFinsetₓ'. -/
theorem Multiset.card_toFinset : m.toFinset.card = m.dedup.card :=
  rfl
#align multiset.card_to_finset Multiset.card_toFinset

/- warning: multiset.to_finset_card_le -> Multiset.toFinset_card_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (m : Multiset.{u1} α), LE.le.{0} Nat Nat.hasLe (Finset.card.{u1} α (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) m)) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) m)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (m : Multiset.{u1} α), LE.le.{0} Nat instLENat (Finset.card.{u1} α (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) m)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) m)
Case conversion may be inaccurate. Consider using '#align multiset.to_finset_card_le Multiset.toFinset_card_leₓ'. -/
theorem Multiset.toFinset_card_le : m.toFinset.card ≤ m.card :=
  card_le_of_le <| dedup_le _
#align multiset.to_finset_card_le Multiset.toFinset_card_le

/- warning: multiset.to_finset_card_of_nodup -> Multiset.toFinset_card_of_nodup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {m : Multiset.{u1} α}, (Multiset.Nodup.{u1} α m) -> (Eq.{1} Nat (Finset.card.{u1} α (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) m)) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) m))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {m : Multiset.{u1} α}, (Multiset.Nodup.{u1} α m) -> (Eq.{1} Nat (Finset.card.{u1} α (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) m)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) m))
Case conversion may be inaccurate. Consider using '#align multiset.to_finset_card_of_nodup Multiset.toFinset_card_of_nodupₓ'. -/
theorem Multiset.toFinset_card_of_nodup {m : Multiset α} (h : m.Nodup) : m.toFinset.card = m.card :=
  congr_arg card <| Multiset.dedup_eq_self.mpr h
#align multiset.to_finset_card_of_nodup Multiset.toFinset_card_of_nodup

#print List.card_toFinset /-
theorem List.card_toFinset : l.toFinset.card = l.dedup.length :=
  rfl
#align list.card_to_finset List.card_toFinset
-/

#print List.toFinset_card_le /-
theorem List.toFinset_card_le : l.toFinset.card ≤ l.length :=
  Multiset.toFinset_card_le ⟦l⟧
#align list.to_finset_card_le List.toFinset_card_le
-/

#print List.toFinset_card_of_nodup /-
theorem List.toFinset_card_of_nodup {l : List α} (h : l.Nodup) : l.toFinset.card = l.length :=
  Multiset.toFinset_card_of_nodup h
#align list.to_finset_card_of_nodup List.toFinset_card_of_nodup
-/

end ToListMultiset

namespace Finset

variable {s t : Finset α} {f : α → β} {n : ℕ}

#print Finset.length_toList /-
@[simp]
theorem length_toList (s : Finset α) : s.toList.length = s.card :=
  by
  rw [to_list, ← Multiset.coe_card, Multiset.coe_toList]
  rfl
#align finset.length_to_list Finset.length_toList
-/

#print Finset.card_image_le /-
theorem card_image_le [DecidableEq β] : (s.image f).card ≤ s.card := by
  simpa only [card_map] using (s.1.map f).to_finset_card_le
#align finset.card_image_le Finset.card_image_le
-/

#print Finset.card_image_of_injOn /-
theorem card_image_of_injOn [DecidableEq β] (H : Set.InjOn f s) : (s.image f).card = s.card := by
  simp only [card, image_val_of_inj_on H, card_map]
#align finset.card_image_of_inj_on Finset.card_image_of_injOn
-/

#print Finset.injOn_of_card_image_eq /-
theorem injOn_of_card_image_eq [DecidableEq β] (H : (s.image f).card = s.card) : Set.InjOn f s :=
  by
  change (s.1.map f).dedup.card = s.1.card at H
  have : (s.1.map f).dedup = s.1.map f :=
    by
    refine' Multiset.eq_of_le_of_card_le (Multiset.dedup_le _) _
    rw [H]
    simp only [Multiset.card_map]
  rw [Multiset.dedup_eq_self] at this
  exact inj_on_of_nodup_map this
#align finset.inj_on_of_card_image_eq Finset.injOn_of_card_image_eq
-/

#print Finset.card_image_iff /-
theorem card_image_iff [DecidableEq β] : (s.image f).card = s.card ↔ Set.InjOn f s :=
  ⟨injOn_of_card_image_eq, card_image_of_injOn⟩
#align finset.card_image_iff Finset.card_image_iff
-/

#print Finset.card_image_of_injective /-
theorem card_image_of_injective [DecidableEq β] (s : Finset α) (H : Injective f) :
    (s.image f).card = s.card :=
  card_image_of_inj_on fun x _ y _ h => H h
#align finset.card_image_of_injective Finset.card_image_of_injective
-/

/- warning: finset.fiber_card_ne_zero_iff_mem_image -> Finset.fiber_card_ne_zero_iff_mem_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Finset.{u1} α) (f : α -> β) [_inst_1 : DecidableEq.{succ u2} β] (y : β), Iff (Ne.{1} Nat (Finset.card.{u1} α (Finset.filter.{u1} α (fun (x : α) => Eq.{succ u2} β (f x) y) (fun (a : α) => _inst_1 (f a) y) s)) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) y (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Finset.{u2} α) (f : α -> β) [_inst_1 : DecidableEq.{succ u1} β] (y : β), Iff (Ne.{1} Nat (Finset.card.{u2} α (Finset.filter.{u2} α (fun (x : α) => Eq.{succ u1} β (f x) y) (fun (a : α) => _inst_1 (f a) y) s)) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) y (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f s))
Case conversion may be inaccurate. Consider using '#align finset.fiber_card_ne_zero_iff_mem_image Finset.fiber_card_ne_zero_iff_mem_imageₓ'. -/
theorem fiber_card_ne_zero_iff_mem_image (s : Finset α) (f : α → β) [DecidableEq β] (y : β) :
    (s.filter fun x => f x = y).card ≠ 0 ↔ y ∈ s.image f := by
  rw [← pos_iff_ne_zero, card_pos, fiber_nonempty_iff_mem_image]
#align finset.fiber_card_ne_zero_iff_mem_image Finset.fiber_card_ne_zero_iff_mem_image

/- warning: finset.card_map -> Finset.card_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} (f : Function.Embedding.{succ u1, succ u2} α β), Eq.{1} Nat (Finset.card.{u2} β (Finset.map.{u1, u2} α β f s)) (Finset.card.{u1} α s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Finset.{u2} α} (f : Function.Embedding.{succ u2, succ u1} α β), Eq.{1} Nat (Finset.card.{u1} β (Finset.map.{u2, u1} α β f s)) (Finset.card.{u2} α s)
Case conversion may be inaccurate. Consider using '#align finset.card_map Finset.card_mapₓ'. -/
@[simp]
theorem card_map (f : α ↪ β) : (s.map f).card = s.card :=
  Multiset.card_map _ _
#align finset.card_map Finset.card_map

#print Finset.card_subtype /-
@[simp]
theorem card_subtype (p : α → Prop) [DecidablePred p] (s : Finset α) :
    (s.Subtype p).card = (s.filter p).card := by simp [Finset.subtype]
#align finset.card_subtype Finset.card_subtype
-/

#print Finset.card_filter_le /-
theorem card_filter_le (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (s.filter p).card ≤ s.card :=
  card_le_of_subset <| filter_subset _ _
#align finset.card_filter_le Finset.card_filter_le
-/

#print Finset.eq_of_subset_of_card_le /-
theorem eq_of_subset_of_card_le {s t : Finset α} (h : s ⊆ t) (h₂ : t.card ≤ s.card) : s = t :=
  eq_of_veq <| Multiset.eq_of_le_of_card_le (val_le_iff.mpr h) h₂
#align finset.eq_of_subset_of_card_le Finset.eq_of_subset_of_card_le
-/

#print Finset.eq_of_superset_of_card_ge /-
theorem eq_of_superset_of_card_ge (hst : s ⊆ t) (hts : t.card ≤ s.card) : t = s :=
  (eq_of_subset_of_card_le hst hts).symm
#align finset.eq_of_superset_of_card_ge Finset.eq_of_superset_of_card_ge
-/

#print Finset.subset_iff_eq_of_card_le /-
theorem subset_iff_eq_of_card_le (h : t.card ≤ s.card) : s ⊆ t ↔ s = t :=
  ⟨fun hst => eq_of_subset_of_card_le hst h, Eq.subset'⟩
#align finset.subset_iff_eq_of_card_le Finset.subset_iff_eq_of_card_le
-/

#print Finset.map_eq_of_subset /-
theorem map_eq_of_subset {f : α ↪ α} (hs : s.map f ⊆ s) : s.map f = s :=
  eq_of_subset_of_card_le hs (card_map _).ge
#align finset.map_eq_of_subset Finset.map_eq_of_subset
-/

#print Finset.filter_card_eq /-
theorem filter_card_eq {p : α → Prop} [DecidablePred p] (h : (s.filter p).card = s.card) (x : α)
    (hx : x ∈ s) : p x :=
  by
  rw [← eq_of_subset_of_card_le (s.filter_subset p) h.ge, mem_filter] at hx
  exact hx.2
#align finset.filter_card_eq Finset.filter_card_eq
-/

#print Finset.card_lt_card /-
theorem card_lt_card (h : s ⊂ t) : s.card < t.card :=
  card_lt_of_lt <| val_lt_iff.2 h
#align finset.card_lt_card Finset.card_lt_card
-/

#print Finset.card_eq_of_bijective /-
theorem card_eq_of_bijective (f : ∀ i, i < n → α) (hf : ∀ a ∈ s, ∃ i, ∃ h : i < n, f i h = a)
    (hf' : ∀ (i) (h : i < n), f i h ∈ s)
    (f_inj : ∀ (i j) (hi : i < n) (hj : j < n), f i hi = f j hj → i = j) : s.card = n := by
  classical
    have : ∀ a : α, a ∈ s ↔ ∃ (i : _)(hi : i ∈ range n), f i (mem_range.1 hi) = a := fun a =>
      ⟨fun ha =>
        let ⟨i, hi, Eq⟩ := hf a ha
        ⟨i, mem_range.2 hi, Eq⟩,
        fun ⟨i, hi, Eq⟩ => Eq ▸ hf' i (mem_range.1 hi)⟩
    have : s = (range n).attach.image fun i => f i.1 (mem_range.1 i.2) := by
      simpa only [ext_iff, mem_image, exists_prop, Subtype.exists, mem_attach, true_and_iff]
    calc
      s.card = card ((range n).attach.image fun i => f i.1 (mem_range.1 i.2)) := by rw [this]
      _ = card (range n).attach :=
        card_image_of_injective _ fun ⟨i, hi⟩ ⟨j, hj⟩ eq =>
          Subtype.eq <| f_inj i j (mem_range.1 hi) (mem_range.1 hj) Eq
      _ = card (range n) := card_attach
      _ = n := card_range n
      
#align finset.card_eq_of_bijective Finset.card_eq_of_bijective
-/

#print Finset.card_congr /-
theorem card_congr {t : Finset β} (f : ∀ a ∈ s, β) (h₁ : ∀ a ha, f a ha ∈ t)
    (h₂ : ∀ a b ha hb, f a ha = f b hb → a = b) (h₃ : ∀ b ∈ t, ∃ a ha, f a ha = b) :
    s.card = t.card := by
  classical calc
      s.card = s.attach.card := card_attach.symm
      _ = (s.attach.image fun a : { a // a ∈ s } => f a.1 a.2).card :=
        Eq.symm (card_image_of_injective _ fun a b h => Subtype.eq <| h₂ _ _ _ _ h)
      _ = t.card :=
        congr_arg card
          (Finset.ext fun b =>
            ⟨fun h =>
              let ⟨a, ha₁, ha₂⟩ := mem_image.1 h
              ha₂ ▸ h₁ _ _,
              fun h =>
              let ⟨a, ha₁, ha₂⟩ := h₃ b h
              mem_image.2 ⟨⟨a, ha₁⟩, by simp [ha₂]⟩⟩)
      
#align finset.card_congr Finset.card_congr
-/

#print Finset.card_le_card_of_inj_on /-
theorem card_le_card_of_inj_on {t : Finset β} (f : α → β) (hf : ∀ a ∈ s, f a ∈ t)
    (f_inj : ∀ a₁ ∈ s, ∀ a₂ ∈ s, f a₁ = f a₂ → a₁ = a₂) : s.card ≤ t.card := by
  classical calc
      s.card = (s.image f).card := (card_image_of_inj_on f_inj).symm
      _ ≤ t.card := card_le_of_subset <| image_subset_iff.2 hf
      
#align finset.card_le_card_of_inj_on Finset.card_le_card_of_inj_on
-/

/- warning: finset.exists_ne_map_eq_of_card_lt_of_maps_to -> Finset.exists_ne_map_eq_of_card_lt_of_maps_to is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {t : Finset.{u2} β}, (LT.lt.{0} Nat Nat.hasLt (Finset.card.{u2} β t) (Finset.card.{u1} α s)) -> (forall {f : α -> β}, (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) (f a) t)) -> (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) => Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y s) => And (Ne.{succ u1} α x y) (Eq.{succ u2} β (f x) (f y))))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {t : Finset.{u2} β}, (LT.lt.{0} Nat instLTNat (Finset.card.{u2} β t) (Finset.card.{u1} α s)) -> (forall {f : α -> β}, (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) (f a) t)) -> (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s) (Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) y s) (And (Ne.{succ u1} α x y) (Eq.{succ u2} β (f x) (f y))))))))
Case conversion may be inaccurate. Consider using '#align finset.exists_ne_map_eq_of_card_lt_of_maps_to Finset.exists_ne_map_eq_of_card_lt_of_maps_toₓ'. -/
/-- If there are more pigeons than pigeonholes, then there are two pigeons in the same pigeonhole.
-/
theorem exists_ne_map_eq_of_card_lt_of_maps_to {t : Finset β} (hc : t.card < s.card) {f : α → β}
    (hf : ∀ a ∈ s, f a ∈ t) : ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y := by
  classical
    by_contra' hz
    refine' hc.not_le (card_le_card_of_inj_on f hf _)
    intro x hx y hy
    contrapose
    exact hz x hx y hy
#align finset.exists_ne_map_eq_of_card_lt_of_maps_to Finset.exists_ne_map_eq_of_card_lt_of_maps_to

#print Finset.le_card_of_inj_on_range /-
theorem le_card_of_inj_on_range (f : ℕ → α) (hf : ∀ i < n, f i ∈ s)
    (f_inj : ∀ i < n, ∀ j < n, f i = f j → i = j) : n ≤ s.card :=
  calc
    n = card (range n) := (card_range n).symm
    _ ≤ s.card := card_le_card_of_inj_on f (by simpa only [mem_range] ) (by simpa only [mem_range] )
    
#align finset.le_card_of_inj_on_range Finset.le_card_of_inj_on_range
-/

#print Finset.surj_on_of_inj_on_of_card_le /-
theorem surj_on_of_inj_on_of_card_le {t : Finset β} (f : ∀ a ∈ s, β) (hf : ∀ a ha, f a ha ∈ t)
    (hinj : ∀ a₁ a₂ ha₁ ha₂, f a₁ ha₁ = f a₂ ha₂ → a₁ = a₂) (hst : t.card ≤ s.card) :
    ∀ b ∈ t, ∃ a ha, b = f a ha := by
  classical
    intro b hb
    have h : (s.attach.image fun a : { a // a ∈ s } => f a a.Prop).card = s.card :=
      @card_attach _ s ▸
        card_image_of_injective _ fun ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩ h => Subtype.eq <| hinj _ _ _ _ h
    have h' : image (fun a : { a // a ∈ s } => f a a.Prop) s.attach = t :=
      eq_of_subset_of_card_le
        (fun b h =>
          let ⟨a, ha₁, ha₂⟩ := mem_image.1 h
          ha₂ ▸ hf _ _)
        (by simp [hst, h])
    rw [← h'] at hb
    obtain ⟨a, ha₁, ha₂⟩ := mem_image.1 hb
    exact ⟨a, a.2, ha₂.symm⟩
#align finset.surj_on_of_inj_on_of_card_le Finset.surj_on_of_inj_on_of_card_le
-/

#print Finset.inj_on_of_surj_on_of_card_le /-
theorem inj_on_of_surj_on_of_card_le {t : Finset β} (f : ∀ a ∈ s, β) (hf : ∀ a ha, f a ha ∈ t)
    (hsurj : ∀ b ∈ t, ∃ a ha, b = f a ha) (hst : s.card ≤ t.card) ⦃a₁ a₂⦄ (ha₁ : a₁ ∈ s)
    (ha₂ : a₂ ∈ s) (ha₁a₂ : f a₁ ha₁ = f a₂ ha₂) : a₁ = a₂ :=
  haveI : Inhabited { x // x ∈ s } := ⟨⟨a₁, ha₁⟩⟩
  let f' : { x // x ∈ s } → { x // x ∈ t } := fun x => ⟨f x.1 x.2, hf x.1 x.2⟩
  let g : { x // x ∈ t } → { x // x ∈ s } :=
    @surj_inv _ _ f' fun x =>
      let ⟨y, hy₁, hy₂⟩ := hsurj x.1 x.2
      ⟨⟨y, hy₁⟩, Subtype.eq hy₂.symm⟩
  have hg : injective g := injective_surj_inv _
  have hsg : surjective g := fun x =>
    let ⟨y, hy⟩ :=
      surj_on_of_inj_on_of_card_le (fun (x : { x // x ∈ t }) (hx : x ∈ t.attach) => g x)
        (fun x _ => show g x ∈ s.attach from mem_attach _ _) (fun x y _ _ hxy => hg hxy) (by simpa)
        x (mem_attach _ _)
    ⟨y, hy.snd.symm⟩
  have hif : injective f' :=
    (left_inverse_of_surjective_of_right_inverse hsg (right_inverse_surj_inv _)).Injective
  Subtype.ext_iff_val.1 (@hif ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩ (Subtype.eq ha₁a₂))
#align finset.inj_on_of_surj_on_of_card_le Finset.inj_on_of_surj_on_of_card_le
-/

/- warning: finset.card_disj_union -> Finset.card_disjUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Finset.{u1} α) (t : Finset.{u1} α) (h : Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t), Eq.{1} Nat (Finset.card.{u1} α (Finset.disjUnion.{u1} α s t h)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Finset.card.{u1} α s) (Finset.card.{u1} α t))
but is expected to have type
  forall {α : Type.{u1}} (s : Finset.{u1} α) (t : Finset.{u1} α) (h : Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t), Eq.{1} Nat (Finset.card.{u1} α (Finset.disjUnion.{u1} α s t h)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Finset.card.{u1} α s) (Finset.card.{u1} α t))
Case conversion may be inaccurate. Consider using '#align finset.card_disj_union Finset.card_disjUnionₓ'. -/
@[simp]
theorem card_disjUnion (s t : Finset α) (h) : (s.disjUnion t h).card = s.card + t.card :=
  Multiset.card_add _ _
#align finset.card_disj_union Finset.card_disjUnion

/-! ### Lattice structure -/


section Lattice

variable [DecidableEq α]

#print Finset.card_union_add_card_inter /-
theorem card_union_add_card_inter (s t : Finset α) :
    (s ∪ t).card + (s ∩ t).card = s.card + t.card :=
  Finset.induction_on t (by simp) fun a r har => by by_cases a ∈ s <;> simp [*] <;> cc
#align finset.card_union_add_card_inter Finset.card_union_add_card_inter
-/

#print Finset.card_inter_add_card_union /-
theorem card_inter_add_card_union (s t : Finset α) :
    (s ∩ t).card + (s ∪ t).card = s.card + t.card := by rw [add_comm, card_union_add_card_inter]
#align finset.card_inter_add_card_union Finset.card_inter_add_card_union
-/

#print Finset.card_union_le /-
theorem card_union_le (s t : Finset α) : (s ∪ t).card ≤ s.card + t.card :=
  card_union_add_card_inter s t ▸ Nat.le_add_right _ _
#align finset.card_union_le Finset.card_union_le
-/

/- warning: finset.card_union_eq -> Finset.card_union_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α} {t : Finset.{u1} α} [_inst_1 : DecidableEq.{succ u1} α], (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t) -> (Eq.{1} Nat (Finset.card.{u1} α (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Finset.card.{u1} α s) (Finset.card.{u1} α t)))
but is expected to have type
  forall {α : Type.{u1}} {s : Finset.{u1} α} {t : Finset.{u1} α} [_inst_1 : DecidableEq.{succ u1} α], (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t) -> (Eq.{1} Nat (Finset.card.{u1} α (Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Finset.card.{u1} α s) (Finset.card.{u1} α t)))
Case conversion may be inaccurate. Consider using '#align finset.card_union_eq Finset.card_union_eqₓ'. -/
theorem card_union_eq (h : Disjoint s t) : (s ∪ t).card = s.card + t.card := by
  rw [← disj_union_eq_union s t h, card_disj_union _ _ _]
#align finset.card_union_eq Finset.card_union_eq

/- warning: finset.card_disjoint_union -> Finset.card_disjoint_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α} {t : Finset.{u1} α} [_inst_1 : DecidableEq.{succ u1} α], (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t) -> (Eq.{1} Nat (Finset.card.{u1} α (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Finset.card.{u1} α s) (Finset.card.{u1} α t)))
but is expected to have type
  forall {α : Type.{u1}} {s : Finset.{u1} α} {t : Finset.{u1} α} [_inst_1 : DecidableEq.{succ u1} α], (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t) -> (Eq.{1} Nat (Finset.card.{u1} α (Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Finset.card.{u1} α s) (Finset.card.{u1} α t)))
Case conversion may be inaccurate. Consider using '#align finset.card_disjoint_union Finset.card_disjoint_unionₓ'. -/
@[simp]
theorem card_disjoint_union (h : Disjoint s t) : card (s ∪ t) = s.card + t.card :=
  card_union_eq h
#align finset.card_disjoint_union Finset.card_disjoint_union

#print Finset.card_sdiff /-
theorem card_sdiff (h : s ⊆ t) : card (t \ s) = t.card - s.card :=
  by
  suffices card (t \ s) = card (t \ s ∪ s) - s.card by rwa [sdiff_union_of_subset h] at this
  rw [card_disjoint_union sdiff_disjoint, add_tsub_cancel_right]
#align finset.card_sdiff Finset.card_sdiff
-/

#print Finset.card_sdiff_add_card_eq_card /-
theorem card_sdiff_add_card_eq_card {s t : Finset α} (h : s ⊆ t) : card (t \ s) + card s = card t :=
  ((Nat.sub_eq_iff_eq_add (card_le_of_subset h)).mp (card_sdiff h).symm).symm
#align finset.card_sdiff_add_card_eq_card Finset.card_sdiff_add_card_eq_card
-/

#print Finset.le_card_sdiff /-
theorem le_card_sdiff (s t : Finset α) : t.card - s.card ≤ card (t \ s) :=
  calc
    card t - card s ≤ card t - card (s ∩ t) :=
      tsub_le_tsub_left (card_le_of_subset (inter_subset_left s t)) _
    _ = card (t \ (s ∩ t)) := (card_sdiff (inter_subset_right s t)).symm
    _ ≤ card (t \ s) := by rw [sdiff_inter_self_right t s]
    
#align finset.le_card_sdiff Finset.le_card_sdiff
-/

#print Finset.card_le_card_sdiff_add_card /-
theorem card_le_card_sdiff_add_card : s.card ≤ (s \ t).card + t.card :=
  tsub_le_iff_right.1 <| le_card_sdiff _ _
#align finset.card_le_card_sdiff_add_card Finset.card_le_card_sdiff_add_card
-/

#print Finset.card_sdiff_add_card /-
theorem card_sdiff_add_card : (s \ t).card + t.card = (s ∪ t).card := by
  rw [← card_disjoint_union sdiff_disjoint, sdiff_union_self_eq_union]
#align finset.card_sdiff_add_card Finset.card_sdiff_add_card
-/

end Lattice

/- warning: finset.filter_card_add_filter_neg_card_eq_card -> Finset.filter_card_add_filter_neg_card_eq_card is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p], Eq.{1} Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Finset.card.{u1} α (Finset.filter.{u1} α p (fun (a : α) => _inst_1 a) s)) (Finset.card.{u1} α (Finset.filter.{u1} α (Function.comp.{succ u1, 1, 1} α Prop Prop Not p) (fun (a : α) => Not.decidable (p a) (_inst_1 a)) s))) (Finset.card.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} {s : Finset.{u1} α} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] [inst._@.Mathlib.Data.Finset.Card._hyg.4827 : forall (x : α), Decidable (Not (p x))], Eq.{1} Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Finset.card.{u1} α (Finset.filter.{u1} α p (fun (a : α) => _inst_1 a) s)) (Finset.card.{u1} α (Finset.filter.{u1} α (fun (a : α) => Not (p a)) (fun (a : α) => inst._@.Mathlib.Data.Finset.Card._hyg.4827 a) s))) (Finset.card.{u1} α s)
Case conversion may be inaccurate. Consider using '#align finset.filter_card_add_filter_neg_card_eq_card Finset.filter_card_add_filter_neg_card_eq_cardₓ'. -/
theorem filter_card_add_filter_neg_card_eq_card (p : α → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter (Not ∘ p)).card = s.card := by
  classical simp [← card_union_eq, filter_union_filter_neg_eq, disjoint_filter]
#align finset.filter_card_add_filter_neg_card_eq_card Finset.filter_card_add_filter_neg_card_eq_card

#print Finset.exists_intermediate_set /-
/-- Given a set `A` and a set `B` inside it, we can shrink `A` to any appropriate size, and keep `B`
inside it. -/
theorem exists_intermediate_set {A B : Finset α} (i : ℕ) (h₁ : i + card B ≤ card A) (h₂ : B ⊆ A) :
    ∃ C : Finset α, B ⊆ C ∧ C ⊆ A ∧ card C = i + card B := by
  classical
    rcases Nat.le.dest h₁ with ⟨k, _⟩
    clear h₁
    induction' k with k ih generalizing A
    · exact ⟨A, h₂, subset.refl _, h.symm⟩
    have : (A \ B).Nonempty :=
      by
      rw [← card_pos, card_sdiff h₂, ← h, Nat.add_right_comm, add_tsub_cancel_right, Nat.add_succ]
      apply Nat.succ_pos
    rcases this with ⟨a, ha⟩
    have z : i + card B + k = card (erase A a) :=
      by
      rw [card_erase_of_mem (mem_sdiff.1 ha).1, ← h]
      rfl
    rcases ih _ z with ⟨B', hB', B'subA', cards⟩
    · exact ⟨B', hB', trans B'subA' (erase_subset _ _), cards⟩
    · rintro t th
      apply mem_erase_of_ne_of_mem _ (h₂ th)
      rintro rfl
      exact not_mem_sdiff_of_mem_right th ha
#align finset.exists_intermediate_set Finset.exists_intermediate_set
-/

#print Finset.exists_smaller_set /-
/-- We can shrink `A` to any smaller size. -/
theorem exists_smaller_set (A : Finset α) (i : ℕ) (h₁ : i ≤ card A) :
    ∃ B : Finset α, B ⊆ A ∧ card B = i :=
  let ⟨B, _, x₁, x₂⟩ := exists_intermediate_set i (by simpa) (empty_subset A)
  ⟨B, x₁, x₂⟩
#align finset.exists_smaller_set Finset.exists_smaller_set
-/

#print Finset.exists_subset_or_subset_of_two_mul_lt_card /-
theorem exists_subset_or_subset_of_two_mul_lt_card [DecidableEq α] {X Y : Finset α} {n : ℕ}
    (hXY : 2 * n < (X ∪ Y).card) : ∃ C : Finset α, n < C.card ∧ (C ⊆ X ∨ C ⊆ Y) :=
  by
  have h₁ : (X ∩ (Y \ X)).card = 0 := finset.card_eq_zero.mpr (Finset.inter_sdiff_self X Y)
  have h₂ : (X ∪ Y).card = X.card + (Y \ X).card := by
    rw [← card_union_add_card_inter X (Y \ X), Finset.union_sdiff_self_eq_union, h₁, add_zero]
  rw [h₂, two_mul] at hXY
  rcases lt_or_lt_of_add_lt_add hXY with (h | h)
  · exact ⟨X, h, Or.inl (Finset.Subset.refl X)⟩
  · exact ⟨Y \ X, h, Or.inr (Finset.sdiff_subset Y X)⟩
#align finset.exists_subset_or_subset_of_two_mul_lt_card Finset.exists_subset_or_subset_of_two_mul_lt_card
-/

/-! ### Explicit description of a finset from its card -/


#print Finset.card_eq_one /-
theorem card_eq_one : s.card = 1 ↔ ∃ a, s = {a} := by
  cases s <;> simp only [Multiset.card_eq_one, Finset.card, ← val_inj, singleton_val]
#align finset.card_eq_one Finset.card_eq_one
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (a «expr ∉ » s) -/
#print Finset.exists_eq_insert_iff /-
theorem exists_eq_insert_iff [DecidableEq α] {s t : Finset α} :
    (∃ (a : _)(_ : a ∉ s), insert a s = t) ↔ s ⊆ t ∧ s.card + 1 = t.card :=
  by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨subset_insert _ _, (card_insert_of_not_mem ha).symm⟩
  · rintro ⟨hst, h⟩
    obtain ⟨a, ha⟩ : ∃ a, t \ s = {a} :=
      card_eq_one.1 (by rw [card_sdiff hst, ← h, add_tsub_cancel_left])
    refine'
      ⟨a, fun hs => (_ : a ∉ {a}) <| mem_singleton_self _, by
        rw [insert_eq, ← ha, sdiff_union_of_subset hst]⟩
    rw [← ha]
    exact not_mem_sdiff_of_mem_right hs
#align finset.exists_eq_insert_iff Finset.exists_eq_insert_iff
-/

#print Finset.card_le_one /-
theorem card_le_one : s.card ≤ 1 ↔ ∀ a ∈ s, ∀ b ∈ s, a = b :=
  by
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · simp
  refine' (Nat.succ_le_of_lt (card_pos.2 ⟨x, hx⟩)).le_iff_eq.trans (card_eq_one.trans ⟨_, _⟩)
  · rintro ⟨y, rfl⟩
    simp
  · exact fun h => ⟨x, eq_singleton_iff_unique_mem.2 ⟨hx, fun y hy => h _ hy _ hx⟩⟩
#align finset.card_le_one Finset.card_le_one
-/

#print Finset.card_le_one_iff /-
theorem card_le_one_iff : s.card ≤ 1 ↔ ∀ {a b}, a ∈ s → b ∈ s → a = b :=
  by
  rw [card_le_one]
  tauto
#align finset.card_le_one_iff Finset.card_le_one_iff
-/

#print Finset.card_le_one_iff_subset_singleton /-
theorem card_le_one_iff_subset_singleton [Nonempty α] : s.card ≤ 1 ↔ ∃ x : α, s ⊆ {x} :=
  by
  refine' ⟨fun H => _, _⟩
  · obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
    · exact ⟨Classical.arbitrary α, empty_subset _⟩
    · exact ⟨x, fun y hy => by rw [card_le_one.1 H y hy x hx, mem_singleton]⟩
  · rintro ⟨x, hx⟩
    rw [← card_singleton x]
    exact card_le_of_subset hx
#align finset.card_le_one_iff_subset_singleton Finset.card_le_one_iff_subset_singleton
-/

#print Finset.card_le_one_of_subsingleton /-
/-- A `finset` of a subsingleton type has cardinality at most one. -/
theorem card_le_one_of_subsingleton [Subsingleton α] (s : Finset α) : s.card ≤ 1 :=
  Finset.card_le_one_iff.2 fun _ _ _ _ => Subsingleton.elim _ _
#align finset.card_le_one_of_subsingleton Finset.card_le_one_of_subsingleton
-/

/- warning: finset.one_lt_card -> Finset.one_lt_card is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α}, Iff (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (Finset.card.{u1} α s)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Exists.{succ u1} α (fun (b : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) b s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) b s) => Ne.{succ u1} α a b)))))
but is expected to have type
  forall {α : Type.{u1}} {s : Finset.{u1} α}, Iff (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (Finset.card.{u1} α s)) (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) (Exists.{succ u1} α (fun (b : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) b s) (Ne.{succ u1} α a b)))))
Case conversion may be inaccurate. Consider using '#align finset.one_lt_card Finset.one_lt_cardₓ'. -/
theorem one_lt_card : 1 < s.card ↔ ∃ a ∈ s, ∃ b ∈ s, a ≠ b :=
  by
  rw [← not_iff_not]
  push_neg
  exact card_le_one
#align finset.one_lt_card Finset.one_lt_card

#print Finset.one_lt_card_iff /-
theorem one_lt_card_iff : 1 < s.card ↔ ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b :=
  by
  rw [one_lt_card]
  simp only [exists_prop, exists_and_left]
#align finset.one_lt_card_iff Finset.one_lt_card_iff
-/

#print Finset.two_lt_card_iff /-
theorem two_lt_card_iff : 2 < s.card ↔ ∃ a b c, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  classical
    refine' ⟨fun h => _, _⟩
    · obtain ⟨c, hc⟩ := card_pos.mp (zero_lt_two.trans h)
      have : 1 < (s.erase c).card := by rwa [← add_lt_add_iff_right 1, card_erase_add_one hc]
      obtain ⟨a, b, ha, hb, hab⟩ := one_lt_card_iff.mp this
      exact
        ⟨a, b, c, mem_of_mem_erase ha, mem_of_mem_erase hb, hc, hab, ne_of_mem_erase ha,
          ne_of_mem_erase hb⟩
    · rintro ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩
      rw [← card_erase_add_one hc, ← card_erase_add_one (mem_erase_of_ne_of_mem hbc hb), ←
        card_erase_add_one (mem_erase_of_ne_of_mem hab (mem_erase_of_ne_of_mem hac ha))]
      apply Nat.le_add_left
#align finset.two_lt_card_iff Finset.two_lt_card_iff
-/

/- warning: finset.two_lt_card -> Finset.two_lt_card is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α}, Iff (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (Finset.card.{u1} α s)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Exists.{succ u1} α (fun (b : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) b s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) b s) => Exists.{succ u1} α (fun (c : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) c s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) c s) => And (Ne.{succ u1} α a b) (And (Ne.{succ u1} α a c) (Ne.{succ u1} α b c)))))))))
but is expected to have type
  forall {α : Type.{u1}} {s : Finset.{u1} α}, Iff (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (Finset.card.{u1} α s)) (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) (Exists.{succ u1} α (fun (b : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) b s) (Exists.{succ u1} α (fun (c : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) c s) (And (Ne.{succ u1} α a b) (And (Ne.{succ u1} α a c) (Ne.{succ u1} α b c)))))))))
Case conversion may be inaccurate. Consider using '#align finset.two_lt_card Finset.two_lt_cardₓ'. -/
theorem two_lt_card : 2 < s.card ↔ ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  simp_rw [two_lt_card_iff, exists_prop, exists_and_left]
#align finset.two_lt_card Finset.two_lt_card

#print Finset.exists_ne_of_one_lt_card /-
theorem exists_ne_of_one_lt_card (hs : 1 < s.card) (a : α) : ∃ b, b ∈ s ∧ b ≠ a :=
  by
  obtain ⟨x, hx, y, hy, hxy⟩ := finset.one_lt_card.mp hs
  by_cases ha : y = a
  · exact ⟨x, hx, ne_of_ne_of_eq hxy ha⟩
  · exact ⟨y, hy, ha⟩
#align finset.exists_ne_of_one_lt_card Finset.exists_ne_of_one_lt_card
-/

#print Finset.card_eq_succ /-
theorem card_eq_succ [DecidableEq α] :
    s.card = n + 1 ↔ ∃ a t, a ∉ t ∧ insert a t = s ∧ t.card = n :=
  ⟨fun h =>
    let ⟨a, has⟩ := card_pos.mp (h.symm ▸ Nat.zero_lt_succ _ : 0 < s.card)
    ⟨a, s.erase a, s.not_mem_erase a, insert_erase has, by
      simp only [h, card_erase_of_mem has, add_tsub_cancel_right]⟩,
    fun ⟨a, t, hat, s_eq, n_eq⟩ => s_eq ▸ n_eq ▸ card_insert_of_not_mem hat⟩
#align finset.card_eq_succ Finset.card_eq_succ
-/

#print Finset.card_eq_two /-
theorem card_eq_two [DecidableEq α] : s.card = 2 ↔ ∃ x y, x ≠ y ∧ s = {x, y} :=
  by
  constructor
  · rw [card_eq_succ]
    simp_rw [card_eq_one]
    rintro ⟨a, _, hab, rfl, b, rfl⟩
    exact ⟨a, b, not_mem_singleton.1 hab, rfl⟩
  · rintro ⟨x, y, h, rfl⟩
    exact card_doubleton h
#align finset.card_eq_two Finset.card_eq_two
-/

#print Finset.card_eq_three /-
theorem card_eq_three [DecidableEq α] :
    s.card = 3 ↔ ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ s = {x, y, z} :=
  by
  constructor
  · rw [card_eq_succ]
    simp_rw [card_eq_two]
    rintro ⟨a, _, abc, rfl, b, c, bc, rfl⟩
    rw [mem_insert, mem_singleton, not_or] at abc
    exact ⟨a, b, c, abc.1, abc.2, bc, rfl⟩
  · rintro ⟨x, y, z, xy, xz, yz, rfl⟩
    simp only [xy, xz, yz, mem_insert, card_insert_of_not_mem, not_false_iff, mem_singleton,
      or_self_iff, card_singleton]
#align finset.card_eq_three Finset.card_eq_three
-/

/-! ### Inductions -/


/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (t «expr ⊂ » s) -/
#print Finset.strongInduction /-
/-- Suppose that, given objects defined on all strict subsets of any finset `s`, one knows how to
define an object on `s`. Then one can inductively define an object on all finsets, starting from
the empty set and iterating. This can be used either to define data, or to prove properties. -/
def strongInduction {p : Finset α → Sort _} (H : ∀ s, (∀ (t) (_ : t ⊂ s), p t) → p s) :
    ∀ s : Finset α, p s
  | s =>
    H s fun t h =>
      have : t.card < s.card := card_lt_card h
      strong_induction t termination_by'
  ⟨_, measure_wf card⟩
#align finset.strong_induction Finset.strongInduction
-/

/- warning: finset.strong_induction_eq -> Finset.strongInduction_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : (Finset.{u1} α) -> Sort.{u2}} (H : forall (s : Finset.{u1} α), (forall (t : Finset.{u1} α), (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.hasSsubset.{u1} α) t s) -> (p t)) -> (p s)) (s : Finset.{u1} α), Eq.{u2} (p s) (Finset.strongInduction.{u1, u2} α (fun (t : Finset.{u1} α) => p t) H s) (H s (fun (t : Finset.{u1} α) (h : HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.hasSsubset.{u1} α) t s) => Finset.strongInduction.{u1, u2} α p H t))
but is expected to have type
  forall {α : Type.{u2}} {p : (Finset.{u2} α) -> Sort.{u1}} (H : forall (s : Finset.{u2} α), (forall (t : Finset.{u2} α), (HasSSubset.SSubset.{u2} (Finset.{u2} α) (Finset.instHasSSubsetFinset.{u2} α) t s) -> (p t)) -> (p s)) (s : Finset.{u2} α), Eq.{u1} (p s) (Finset.strongInduction.{u2, u1} α (fun (t : Finset.{u2} α) => p t) H s) (H s (fun (t : Finset.{u2} α) (h : HasSSubset.SSubset.{u2} (Finset.{u2} α) (Finset.instHasSSubsetFinset.{u2} α) t s) => Finset.strongInduction.{u2, u1} α (fun (t : Finset.{u2} α) => p t) H t))
Case conversion may be inaccurate. Consider using '#align finset.strong_induction_eq Finset.strongInduction_eqₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (t «expr ⊂ » s) -/
theorem strongInduction_eq {p : Finset α → Sort _} (H : ∀ s, (∀ (t) (_ : t ⊂ s), p t) → p s)
    (s : Finset α) : strongInduction H s = H s fun t h => strongInduction H t := by
  rw [strong_induction]
#align finset.strong_induction_eq Finset.strongInduction_eq

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (t «expr ⊂ » s) -/
#print Finset.strongInductionOn /-
/-- Analogue of `strong_induction` with order of arguments swapped. -/
@[elab_as_elim]
def strongInductionOn {p : Finset α → Sort _} (s : Finset α) :
    (∀ s, (∀ (t) (_ : t ⊂ s), p t) → p s) → p s := fun H => strongInduction H s
#align finset.strong_induction_on Finset.strongInductionOn
-/

/- warning: finset.strong_induction_on_eq -> Finset.strongInductionOn_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : (Finset.{u1} α) -> Sort.{u2}} (s : Finset.{u1} α) (H : forall (s : Finset.{u1} α), (forall (t : Finset.{u1} α), (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.hasSsubset.{u1} α) t s) -> (p t)) -> (p s)), Eq.{u2} (p s) (Finset.strongInductionOn.{u1, u2} α (fun (t : Finset.{u1} α) => p t) s H) (H s (fun (t : Finset.{u1} α) (h : HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.hasSsubset.{u1} α) t s) => Finset.strongInductionOn.{u1, u2} α (fun (t : Finset.{u1} α) => p t) t H))
but is expected to have type
  forall {α : Type.{u2}} {p : (Finset.{u2} α) -> Sort.{u1}} (s : Finset.{u2} α) (H : forall (s : Finset.{u2} α), (forall (t : Finset.{u2} α), (HasSSubset.SSubset.{u2} (Finset.{u2} α) (Finset.instHasSSubsetFinset.{u2} α) t s) -> (p t)) -> (p s)), Eq.{u1} (p s) (Finset.strongInductionOn.{u2, u1} α (fun (t : Finset.{u2} α) => p t) s H) (H s (fun (t : Finset.{u2} α) (h : HasSSubset.SSubset.{u2} (Finset.{u2} α) (Finset.instHasSSubsetFinset.{u2} α) t s) => Finset.strongInductionOn.{u2, u1} α (fun (t : Finset.{u2} α) => p t) t H))
Case conversion may be inaccurate. Consider using '#align finset.strong_induction_on_eq Finset.strongInductionOn_eqₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (t «expr ⊂ » s) -/
theorem strongInductionOn_eq {p : Finset α → Sort _} (s : Finset α)
    (H : ∀ s, (∀ (t) (_ : t ⊂ s), p t) → p s) :
    s.strong_induction_on H = H s fun t h => t.strong_induction_on H :=
  by
  dsimp only [strong_induction_on]
  rw [strong_induction]
#align finset.strong_induction_on_eq Finset.strongInductionOn_eq

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (t «expr ⊆ » s) -/
#print Finset.case_strong_induction_on /-
@[elab_as_elim]
theorem case_strong_induction_on [DecidableEq α] {p : Finset α → Prop} (s : Finset α) (h₀ : p ∅)
    (h₁ : ∀ a s, a ∉ s → (∀ (t) (_ : t ⊆ s), p t) → p (insert a s)) : p s :=
  Finset.strongInductionOn s fun s =>
    Finset.induction_on s (fun _ => h₀) fun a s n _ ih =>
      h₁ a s n fun t ss => ih _ (lt_of_le_of_lt ss (ssubset_insert n) : t < _)
#align finset.case_strong_induction_on Finset.case_strong_induction_on
-/

#print Finset.strongDownwardInduction /-
/-- Suppose that, given that `p t` can be defined on all supersets of `s` of cardinality less than
`n`, one knows how to define `p s`. Then one can inductively define `p s` for all finsets `s` of
cardinality less than `n`, starting from finsets of card `n` and iterating. This
can be used either to define data, or to prove properties. -/
def strongDownwardInduction {p : Finset α → Sort _} {n : ℕ}
    (H : ∀ t₁, (∀ {t₂ : Finset α}, t₂.card ≤ n → t₁ ⊂ t₂ → p t₂) → t₁.card ≤ n → p t₁) :
    ∀ s : Finset α, s.card ≤ n → p s
  | s =>
    H s fun t ht h =>
      have : n - t.card < n - s.card := (tsub_lt_tsub_iff_left_of_le ht).2 (Finset.card_lt_card h)
      strong_downward_induction t ht termination_by'
  ⟨_, measure_wf fun t : Finset α => n - t.card⟩
#align finset.strong_downward_induction Finset.strongDownwardInduction
-/

/- warning: finset.strong_downward_induction_eq -> Finset.strongDownwardInduction_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Nat} {p : (Finset.{u1} α) -> Sort.{u2}} (H : forall (t₁ : Finset.{u1} α), (forall {t₂ : Finset.{u1} α}, (LE.le.{0} Nat Nat.hasLe (Finset.card.{u1} α t₂) n) -> (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.hasSsubset.{u1} α) t₁ t₂) -> (p t₂)) -> (LE.le.{0} Nat Nat.hasLe (Finset.card.{u1} α t₁) n) -> (p t₁)) (s : Finset.{u1} α), Eq.{u2} ((LE.le.{0} Nat Nat.hasLe (Finset.card.{u1} α s) n) -> (p s)) (Finset.strongDownwardInduction.{u1, u2} α (fun (t₂ : Finset.{u1} α) => p t₂) n H s) (H s (fun (t : Finset.{u1} α) (ht : LE.le.{0} Nat Nat.hasLe (Finset.card.{u1} α t) n) (hst : HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.hasSsubset.{u1} α) s t) => Finset.strongDownwardInduction.{u1, u2} α p n H t ht))
but is expected to have type
  forall {α : Type.{u2}} {n : Nat} {p : (Finset.{u2} α) -> Sort.{u1}} (H : forall (t₁ : Finset.{u2} α), (forall {t₂ : Finset.{u2} α}, (LE.le.{0} Nat instLENat (Finset.card.{u2} α t₂) n) -> (HasSSubset.SSubset.{u2} (Finset.{u2} α) (Finset.instHasSSubsetFinset.{u2} α) t₁ t₂) -> (p t₂)) -> (LE.le.{0} Nat instLENat (Finset.card.{u2} α t₁) n) -> (p t₁)) (s : Finset.{u2} α), Eq.{u1} ((LE.le.{0} Nat instLENat (Finset.card.{u2} α s) n) -> (p s)) (Finset.strongDownwardInduction.{u2, u1} α (fun (t₂ : Finset.{u2} α) => p t₂) n H s) (H s (fun {t : Finset.{u2} α} (ht : LE.le.{0} Nat instLENat (Finset.card.{u2} α t) n) (hst : HasSSubset.SSubset.{u2} (Finset.{u2} α) (Finset.instHasSSubsetFinset.{u2} α) s t) => Finset.strongDownwardInduction.{u2, u1} α (fun (t₂ : Finset.{u2} α) => p t₂) n H t ht))
Case conversion may be inaccurate. Consider using '#align finset.strong_downward_induction_eq Finset.strongDownwardInduction_eqₓ'. -/
theorem strongDownwardInduction_eq {p : Finset α → Sort _}
    (H : ∀ t₁, (∀ {t₂ : Finset α}, t₂.card ≤ n → t₁ ⊂ t₂ → p t₂) → t₁.card ≤ n → p t₁)
    (s : Finset α) :
    strongDownwardInduction H s = H s fun t ht hst => strongDownwardInduction H t ht := by
  rw [strong_downward_induction]
#align finset.strong_downward_induction_eq Finset.strongDownwardInduction_eq

#print Finset.strongDownwardInductionOn /-
/-- Analogue of `strong_downward_induction` with order of arguments swapped. -/
@[elab_as_elim]
def strongDownwardInductionOn {p : Finset α → Sort _} (s : Finset α)
    (H : ∀ t₁, (∀ {t₂ : Finset α}, t₂.card ≤ n → t₁ ⊂ t₂ → p t₂) → t₁.card ≤ n → p t₁) :
    s.card ≤ n → p s :=
  strongDownwardInduction H s
#align finset.strong_downward_induction_on Finset.strongDownwardInductionOn
-/

/- warning: finset.strong_downward_induction_on_eq -> Finset.strongDownwardInductionOn_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Nat} {p : (Finset.{u1} α) -> Sort.{u2}} (s : Finset.{u1} α) (H : forall (t₁ : Finset.{u1} α), (forall {t₂ : Finset.{u1} α}, (LE.le.{0} Nat Nat.hasLe (Finset.card.{u1} α t₂) n) -> (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.hasSsubset.{u1} α) t₁ t₂) -> (p t₂)) -> (LE.le.{0} Nat Nat.hasLe (Finset.card.{u1} α t₁) n) -> (p t₁)), Eq.{u2} ((LE.le.{0} Nat Nat.hasLe (Finset.card.{u1} α s) n) -> (p s)) (Finset.strongDownwardInductionOn.{u1, u2} α n (fun (t₂ : Finset.{u1} α) => p t₂) s H) (H s (fun (t : Finset.{u1} α) (ht : LE.le.{0} Nat Nat.hasLe (Finset.card.{u1} α t) n) (h : HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.hasSsubset.{u1} α) s t) => Finset.strongDownwardInductionOn.{u1, u2} α n (fun (t₂ : Finset.{u1} α) => p t₂) t H ht))
but is expected to have type
  forall {α : Type.{u2}} {n : Nat} {p : (Finset.{u2} α) -> Sort.{u1}} (s : Finset.{u2} α) (H : forall (t₁ : Finset.{u2} α), (forall {t₂ : Finset.{u2} α}, (LE.le.{0} Nat instLENat (Finset.card.{u2} α t₂) n) -> (HasSSubset.SSubset.{u2} (Finset.{u2} α) (Finset.instHasSSubsetFinset.{u2} α) t₁ t₂) -> (p t₂)) -> (LE.le.{0} Nat instLENat (Finset.card.{u2} α t₁) n) -> (p t₁)), Eq.{u1} ((LE.le.{0} Nat instLENat (Finset.card.{u2} α s) n) -> (p s)) (fun (a._@.Mathlib.Data.Finset.Card._hyg.8612 : LE.le.{0} Nat instLENat (Finset.card.{u2} α s) n) => Finset.strongDownwardInductionOn.{u2, u1} α n (fun (x._@.Mathlib.Data.Finset.Card._hyg.8713 : Finset.{u2} α) => p x._@.Mathlib.Data.Finset.Card._hyg.8713) s H a._@.Mathlib.Data.Finset.Card._hyg.8612) (H s (fun {t : Finset.{u2} α} (ht : LE.le.{0} Nat instLENat (Finset.card.{u2} α t) n) (h : HasSSubset.SSubset.{u2} (Finset.{u2} α) (Finset.instHasSSubsetFinset.{u2} α) s t) => Finset.strongDownwardInductionOn.{u2, u1} α n (fun (t₂ : Finset.{u2} α) => p t₂) t H ht))
Case conversion may be inaccurate. Consider using '#align finset.strong_downward_induction_on_eq Finset.strongDownwardInductionOn_eqₓ'. -/
theorem strongDownwardInductionOn_eq {p : Finset α → Sort _} (s : Finset α)
    (H : ∀ t₁, (∀ {t₂ : Finset α}, t₂.card ≤ n → t₁ ⊂ t₂ → p t₂) → t₁.card ≤ n → p t₁) :
    s.strongDownwardInductionOn H = H s fun t ht h => t.strongDownwardInductionOn H ht :=
  by
  dsimp only [strong_downward_induction_on]
  rw [strong_downward_induction]
#align finset.strong_downward_induction_on_eq Finset.strongDownwardInductionOn_eq

#print Finset.lt_wf /-
theorem lt_wf {α} : WellFounded (@LT.lt (Finset α) _) :=
  have H : Subrelation (@LT.lt (Finset α) _) (InvImage (· < ·) card) := fun x y hxy =>
    card_lt_card hxy
  Subrelation.wf H <| InvImage.wf _ <| Nat.lt_wfRel
#align finset.lt_wf Finset.lt_wf
-/

end Finset

