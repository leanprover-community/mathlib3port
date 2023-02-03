/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Yaël Dillies

! This file was ported from Lean 3 source module data.finset.locally_finite
! leanprover-community/mathlib commit 2705404e701abc6b3127da906f40bae062a169c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.LocallyFinite
import Mathbin.Data.Set.Intervals.Monoid

/-!
# Intervals as finsets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides basic results about all the `finset.Ixx`, which are defined in
`order.locally_finite`.

## TODO

This file was originally only about `finset.Ico a b` where `a b : ℕ`. No care has yet been taken to
generalize these lemmas properly and many lemmas about `Icc`, `Ioc`, `Ioo` are missing. In general,
what's to do is taking the lemmas in `data.x.intervals` and abstract away the concrete structure.

Complete the API. See
https://github.com/leanprover-community/mathlib/pull/14448#discussion_r906109235
for some ideas.
-/


open Function OrderDual

open BigOperators FinsetInterval

variable {ι α : Type _}

namespace Finset

section Preorder

variable [Preorder α]

section LocallyFiniteOrder

variable [LocallyFiniteOrder α] {a a₁ a₂ b b₁ b₂ c x : α}

#print Finset.nonempty_Icc /-
@[simp]
theorem nonempty_Icc : (Icc a b).Nonempty ↔ a ≤ b := by
  rw [← coe_nonempty, coe_Icc, Set.nonempty_Icc]
#align finset.nonempty_Icc Finset.nonempty_Icc
-/

#print Finset.nonempty_Ico /-
@[simp]
theorem nonempty_Ico : (Ico a b).Nonempty ↔ a < b := by
  rw [← coe_nonempty, coe_Ico, Set.nonempty_Ico]
#align finset.nonempty_Ico Finset.nonempty_Ico
-/

#print Finset.nonempty_Ioc /-
@[simp]
theorem nonempty_Ioc : (Ioc a b).Nonempty ↔ a < b := by
  rw [← coe_nonempty, coe_Ioc, Set.nonempty_Ioc]
#align finset.nonempty_Ioc Finset.nonempty_Ioc
-/

#print Finset.nonempty_Ioo /-
@[simp]
theorem nonempty_Ioo [DenselyOrdered α] : (Ioo a b).Nonempty ↔ a < b := by
  rw [← coe_nonempty, coe_Ioo, Set.nonempty_Ioo]
#align finset.nonempty_Ioo Finset.nonempty_Ioo
-/

#print Finset.Icc_eq_empty_iff /-
@[simp]
theorem Icc_eq_empty_iff : Icc a b = ∅ ↔ ¬a ≤ b := by
  rw [← coe_eq_empty, coe_Icc, Set.Icc_eq_empty_iff]
#align finset.Icc_eq_empty_iff Finset.Icc_eq_empty_iff
-/

#print Finset.Ico_eq_empty_iff /-
@[simp]
theorem Ico_eq_empty_iff : Ico a b = ∅ ↔ ¬a < b := by
  rw [← coe_eq_empty, coe_Ico, Set.Ico_eq_empty_iff]
#align finset.Ico_eq_empty_iff Finset.Ico_eq_empty_iff
-/

#print Finset.Ioc_eq_empty_iff /-
@[simp]
theorem Ioc_eq_empty_iff : Ioc a b = ∅ ↔ ¬a < b := by
  rw [← coe_eq_empty, coe_Ioc, Set.Ioc_eq_empty_iff]
#align finset.Ioc_eq_empty_iff Finset.Ioc_eq_empty_iff
-/

#print Finset.Ioo_eq_empty_iff /-
@[simp]
theorem Ioo_eq_empty_iff [DenselyOrdered α] : Ioo a b = ∅ ↔ ¬a < b := by
  rw [← coe_eq_empty, coe_Ioo, Set.Ioo_eq_empty_iff]
#align finset.Ioo_eq_empty_iff Finset.Ioo_eq_empty_iff
-/

alias Icc_eq_empty_iff ↔ _ Icc_eq_empty
#align finset.Icc_eq_empty Finset.Icc_eq_empty

alias Ico_eq_empty_iff ↔ _ Ico_eq_empty
#align finset.Ico_eq_empty Finset.Ico_eq_empty

alias Ioc_eq_empty_iff ↔ _ Ioc_eq_empty
#align finset.Ioc_eq_empty Finset.Ioc_eq_empty

#print Finset.Ioo_eq_empty /-
@[simp]
theorem Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅ :=
  eq_empty_iff_forall_not_mem.2 fun x hx => h ((mem_Ioo.1 hx).1.trans (mem_Ioo.1 hx).2)
#align finset.Ioo_eq_empty Finset.Ioo_eq_empty
-/

#print Finset.Icc_eq_empty_of_lt /-
@[simp]
theorem Icc_eq_empty_of_lt (h : b < a) : Icc a b = ∅ :=
  Icc_eq_empty h.not_le
#align finset.Icc_eq_empty_of_lt Finset.Icc_eq_empty_of_lt
-/

#print Finset.Ico_eq_empty_of_le /-
@[simp]
theorem Ico_eq_empty_of_le (h : b ≤ a) : Ico a b = ∅ :=
  Ico_eq_empty h.not_lt
#align finset.Ico_eq_empty_of_le Finset.Ico_eq_empty_of_le
-/

#print Finset.Ioc_eq_empty_of_le /-
@[simp]
theorem Ioc_eq_empty_of_le (h : b ≤ a) : Ioc a b = ∅ :=
  Ioc_eq_empty h.not_lt
#align finset.Ioc_eq_empty_of_le Finset.Ioc_eq_empty_of_le
-/

#print Finset.Ioo_eq_empty_of_le /-
@[simp]
theorem Ioo_eq_empty_of_le (h : b ≤ a) : Ioo a b = ∅ :=
  Ioo_eq_empty h.not_lt
#align finset.Ioo_eq_empty_of_le Finset.Ioo_eq_empty_of_le
-/

#print Finset.left_mem_Icc /-
@[simp]
theorem left_mem_Icc : a ∈ Icc a b ↔ a ≤ b := by simp only [mem_Icc, true_and_iff, le_rfl]
#align finset.left_mem_Icc Finset.left_mem_Icc
-/

#print Finset.left_mem_Ico /-
@[simp]
theorem left_mem_Ico : a ∈ Ico a b ↔ a < b := by simp only [mem_Ico, true_and_iff, le_refl]
#align finset.left_mem_Ico Finset.left_mem_Ico
-/

#print Finset.right_mem_Icc /-
@[simp]
theorem right_mem_Icc : b ∈ Icc a b ↔ a ≤ b := by simp only [mem_Icc, and_true_iff, le_rfl]
#align finset.right_mem_Icc Finset.right_mem_Icc
-/

#print Finset.right_mem_Ioc /-
@[simp]
theorem right_mem_Ioc : b ∈ Ioc a b ↔ a < b := by simp only [mem_Ioc, and_true_iff, le_rfl]
#align finset.right_mem_Ioc Finset.right_mem_Ioc
-/

#print Finset.left_not_mem_Ioc /-
@[simp]
theorem left_not_mem_Ioc : a ∉ Ioc a b := fun h => lt_irrefl _ (mem_Ioc.1 h).1
#align finset.left_not_mem_Ioc Finset.left_not_mem_Ioc
-/

#print Finset.left_not_mem_Ioo /-
@[simp]
theorem left_not_mem_Ioo : a ∉ Ioo a b := fun h => lt_irrefl _ (mem_Ioo.1 h).1
#align finset.left_not_mem_Ioo Finset.left_not_mem_Ioo
-/

#print Finset.right_not_mem_Ico /-
@[simp]
theorem right_not_mem_Ico : b ∉ Ico a b := fun h => lt_irrefl _ (mem_Ico.1 h).2
#align finset.right_not_mem_Ico Finset.right_not_mem_Ico
-/

#print Finset.right_not_mem_Ioo /-
@[simp]
theorem right_not_mem_Ioo : b ∉ Ioo a b := fun h => lt_irrefl _ (mem_Ioo.1 h).2
#align finset.right_not_mem_Ioo Finset.right_not_mem_Ioo
-/

#print Finset.Icc_subset_Icc /-
theorem Icc_subset_Icc (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : Icc a₁ b₁ ⊆ Icc a₂ b₂ := by
  simpa [← coe_subset] using Set.Icc_subset_Icc ha hb
#align finset.Icc_subset_Icc Finset.Icc_subset_Icc
-/

#print Finset.Ico_subset_Ico /-
theorem Ico_subset_Ico (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : Ico a₁ b₁ ⊆ Ico a₂ b₂ := by
  simpa [← coe_subset] using Set.Ico_subset_Ico ha hb
#align finset.Ico_subset_Ico Finset.Ico_subset_Ico
-/

#print Finset.Ioc_subset_Ioc /-
theorem Ioc_subset_Ioc (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : Ioc a₁ b₁ ⊆ Ioc a₂ b₂ := by
  simpa [← coe_subset] using Set.Ioc_subset_Ioc ha hb
#align finset.Ioc_subset_Ioc Finset.Ioc_subset_Ioc
-/

#print Finset.Ioo_subset_Ioo /-
theorem Ioo_subset_Ioo (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : Ioo a₁ b₁ ⊆ Ioo a₂ b₂ := by
  simpa [← coe_subset] using Set.Ioo_subset_Ioo ha hb
#align finset.Ioo_subset_Ioo Finset.Ioo_subset_Ioo
-/

#print Finset.Icc_subset_Icc_left /-
theorem Icc_subset_Icc_left (h : a₁ ≤ a₂) : Icc a₂ b ⊆ Icc a₁ b :=
  Icc_subset_Icc h le_rfl
#align finset.Icc_subset_Icc_left Finset.Icc_subset_Icc_left
-/

#print Finset.Ico_subset_Ico_left /-
theorem Ico_subset_Ico_left (h : a₁ ≤ a₂) : Ico a₂ b ⊆ Ico a₁ b :=
  Ico_subset_Ico h le_rfl
#align finset.Ico_subset_Ico_left Finset.Ico_subset_Ico_left
-/

#print Finset.Ioc_subset_Ioc_left /-
theorem Ioc_subset_Ioc_left (h : a₁ ≤ a₂) : Ioc a₂ b ⊆ Ioc a₁ b :=
  Ioc_subset_Ioc h le_rfl
#align finset.Ioc_subset_Ioc_left Finset.Ioc_subset_Ioc_left
-/

#print Finset.Ioo_subset_Ioo_left /-
theorem Ioo_subset_Ioo_left (h : a₁ ≤ a₂) : Ioo a₂ b ⊆ Ioo a₁ b :=
  Ioo_subset_Ioo h le_rfl
#align finset.Ioo_subset_Ioo_left Finset.Ioo_subset_Ioo_left
-/

#print Finset.Icc_subset_Icc_right /-
theorem Icc_subset_Icc_right (h : b₁ ≤ b₂) : Icc a b₁ ⊆ Icc a b₂ :=
  Icc_subset_Icc le_rfl h
#align finset.Icc_subset_Icc_right Finset.Icc_subset_Icc_right
-/

#print Finset.Ico_subset_Ico_right /-
theorem Ico_subset_Ico_right (h : b₁ ≤ b₂) : Ico a b₁ ⊆ Ico a b₂ :=
  Ico_subset_Ico le_rfl h
#align finset.Ico_subset_Ico_right Finset.Ico_subset_Ico_right
-/

#print Finset.Ioc_subset_Ioc_right /-
theorem Ioc_subset_Ioc_right (h : b₁ ≤ b₂) : Ioc a b₁ ⊆ Ioc a b₂ :=
  Ioc_subset_Ioc le_rfl h
#align finset.Ioc_subset_Ioc_right Finset.Ioc_subset_Ioc_right
-/

#print Finset.Ioo_subset_Ioo_right /-
theorem Ioo_subset_Ioo_right (h : b₁ ≤ b₂) : Ioo a b₁ ⊆ Ioo a b₂ :=
  Ioo_subset_Ioo le_rfl h
#align finset.Ioo_subset_Ioo_right Finset.Ioo_subset_Ioo_right
-/

#print Finset.Ico_subset_Ioo_left /-
theorem Ico_subset_Ioo_left (h : a₁ < a₂) : Ico a₂ b ⊆ Ioo a₁ b :=
  by
  rw [← coe_subset, coe_Ico, coe_Ioo]
  exact Set.Ico_subset_Ioo_left h
#align finset.Ico_subset_Ioo_left Finset.Ico_subset_Ioo_left
-/

#print Finset.Ioc_subset_Ioo_right /-
theorem Ioc_subset_Ioo_right (h : b₁ < b₂) : Ioc a b₁ ⊆ Ioo a b₂ :=
  by
  rw [← coe_subset, coe_Ioc, coe_Ioo]
  exact Set.Ioc_subset_Ioo_right h
#align finset.Ioc_subset_Ioo_right Finset.Ioc_subset_Ioo_right
-/

#print Finset.Icc_subset_Ico_right /-
theorem Icc_subset_Ico_right (h : b₁ < b₂) : Icc a b₁ ⊆ Ico a b₂ :=
  by
  rw [← coe_subset, coe_Icc, coe_Ico]
  exact Set.Icc_subset_Ico_right h
#align finset.Icc_subset_Ico_right Finset.Icc_subset_Ico_right
-/

#print Finset.Ioo_subset_Ico_self /-
theorem Ioo_subset_Ico_self : Ioo a b ⊆ Ico a b :=
  by
  rw [← coe_subset, coe_Ioo, coe_Ico]
  exact Set.Ioo_subset_Ico_self
#align finset.Ioo_subset_Ico_self Finset.Ioo_subset_Ico_self
-/

#print Finset.Ioo_subset_Ioc_self /-
theorem Ioo_subset_Ioc_self : Ioo a b ⊆ Ioc a b :=
  by
  rw [← coe_subset, coe_Ioo, coe_Ioc]
  exact Set.Ioo_subset_Ioc_self
#align finset.Ioo_subset_Ioc_self Finset.Ioo_subset_Ioc_self
-/

#print Finset.Ico_subset_Icc_self /-
theorem Ico_subset_Icc_self : Ico a b ⊆ Icc a b :=
  by
  rw [← coe_subset, coe_Ico, coe_Icc]
  exact Set.Ico_subset_Icc_self
#align finset.Ico_subset_Icc_self Finset.Ico_subset_Icc_self
-/

#print Finset.Ioc_subset_Icc_self /-
theorem Ioc_subset_Icc_self : Ioc a b ⊆ Icc a b :=
  by
  rw [← coe_subset, coe_Ioc, coe_Icc]
  exact Set.Ioc_subset_Icc_self
#align finset.Ioc_subset_Icc_self Finset.Ioc_subset_Icc_self
-/

#print Finset.Ioo_subset_Icc_self /-
theorem Ioo_subset_Icc_self : Ioo a b ⊆ Icc a b :=
  Ioo_subset_Ico_self.trans Ico_subset_Icc_self
#align finset.Ioo_subset_Icc_self Finset.Ioo_subset_Icc_self
-/

#print Finset.Icc_subset_Icc_iff /-
theorem Icc_subset_Icc_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Icc a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ := by
  rw [← coe_subset, coe_Icc, coe_Icc, Set.Icc_subset_Icc_iff h₁]
#align finset.Icc_subset_Icc_iff Finset.Icc_subset_Icc_iff
-/

#print Finset.Icc_subset_Ioo_iff /-
theorem Icc_subset_Ioo_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ioo a₂ b₂ ↔ a₂ < a₁ ∧ b₁ < b₂ := by
  rw [← coe_subset, coe_Icc, coe_Ioo, Set.Icc_subset_Ioo_iff h₁]
#align finset.Icc_subset_Ioo_iff Finset.Icc_subset_Ioo_iff
-/

#print Finset.Icc_subset_Ico_iff /-
theorem Icc_subset_Ico_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ < b₂ := by
  rw [← coe_subset, coe_Icc, coe_Ico, Set.Icc_subset_Ico_iff h₁]
#align finset.Icc_subset_Ico_iff Finset.Icc_subset_Ico_iff
-/

#print Finset.Icc_subset_Ioc_iff /-
theorem Icc_subset_Ioc_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ioc a₂ b₂ ↔ a₂ < a₁ ∧ b₁ ≤ b₂ :=
  (Icc_subset_Ico_iff h₁.dual).trans and_comm
#align finset.Icc_subset_Ioc_iff Finset.Icc_subset_Ioc_iff
-/

#print Finset.Icc_sSubset_Icc_left /-
--TODO: `Ico_subset_Ioo_iff`, `Ioc_subset_Ioo_iff`
theorem Icc_sSubset_Icc_left (hI : a₂ ≤ b₂) (ha : a₂ < a₁) (hb : b₁ ≤ b₂) : Icc a₁ b₁ ⊂ Icc a₂ b₂ :=
  by
  rw [← coe_ssubset, coe_Icc, coe_Icc]
  exact Set.Icc_ssubset_Icc_left hI ha hb
#align finset.Icc_ssubset_Icc_left Finset.Icc_sSubset_Icc_left
-/

#print Finset.Icc_sSubset_Icc_right /-
theorem Icc_sSubset_Icc_right (hI : a₂ ≤ b₂) (ha : a₂ ≤ a₁) (hb : b₁ < b₂) :
    Icc a₁ b₁ ⊂ Icc a₂ b₂ := by
  rw [← coe_ssubset, coe_Icc, coe_Icc]
  exact Set.Icc_ssubset_Icc_right hI ha hb
#align finset.Icc_ssubset_Icc_right Finset.Icc_sSubset_Icc_right
-/

variable (a)

#print Finset.Ico_self /-
@[simp]
theorem Ico_self : Ico a a = ∅ :=
  Ico_eq_empty <| lt_irrefl _
#align finset.Ico_self Finset.Ico_self
-/

#print Finset.Ioc_self /-
@[simp]
theorem Ioc_self : Ioc a a = ∅ :=
  Ioc_eq_empty <| lt_irrefl _
#align finset.Ioc_self Finset.Ioc_self
-/

#print Finset.Ioo_self /-
@[simp]
theorem Ioo_self : Ioo a a = ∅ :=
  Ioo_eq_empty <| lt_irrefl _
#align finset.Ioo_self Finset.Ioo_self
-/

variable {a}

#print Set.fintypeOfMemBounds /-
/-- A set with upper and lower bounds in a locally finite order is a fintype -/
def Set.fintypeOfMemBounds {s : Set α} [DecidablePred (· ∈ s)] (ha : a ∈ lowerBounds s)
    (hb : b ∈ upperBounds s) : Fintype s :=
  Set.fintypeSubset (Set.Icc a b) fun x hx => ⟨ha hx, hb hx⟩
#align set.fintype_of_mem_bounds Set.fintypeOfMemBounds
-/

#print BddBelow.finite_of_bddAbove /-
theorem BddBelow.finite_of_bddAbove {s : Set α} (h₀ : BddBelow s) (h₁ : BddAbove s) : s.Finite :=
  by
  let ⟨a, ha⟩ := h₀
  let ⟨b, hb⟩ := h₁
  classical exact ⟨Set.fintypeOfMemBounds ha hb⟩
#align bdd_below.finite_of_bdd_above BddBelow.finite_of_bddAbove
-/

section Filter

#print Finset.Ico_filter_lt_of_le_left /-
theorem Ico_filter_lt_of_le_left [DecidablePred (· < c)] (hca : c ≤ a) :
    (Ico a b).filterₓ (· < c) = ∅ :=
  filter_false_of_mem fun x hx => (hca.trans (mem_Ico.1 hx).1).not_lt
#align finset.Ico_filter_lt_of_le_left Finset.Ico_filter_lt_of_le_left
-/

#print Finset.Ico_filter_lt_of_right_le /-
theorem Ico_filter_lt_of_right_le [DecidablePred (· < c)] (hbc : b ≤ c) :
    (Ico a b).filterₓ (· < c) = Ico a b :=
  filter_true_of_mem fun x hx => (mem_Ico.1 hx).2.trans_le hbc
#align finset.Ico_filter_lt_of_right_le Finset.Ico_filter_lt_of_right_le
-/

#print Finset.Ico_filter_lt_of_le_right /-
theorem Ico_filter_lt_of_le_right [DecidablePred (· < c)] (hcb : c ≤ b) :
    (Ico a b).filterₓ (· < c) = Ico a c := by
  ext x
  rw [mem_filter, mem_Ico, mem_Ico, and_right_comm]
  exact and_iff_left_of_imp fun h => h.2.trans_le hcb
#align finset.Ico_filter_lt_of_le_right Finset.Ico_filter_lt_of_le_right
-/

#print Finset.Ico_filter_le_of_le_left /-
theorem Ico_filter_le_of_le_left {a b c : α} [DecidablePred ((· ≤ ·) c)] (hca : c ≤ a) :
    (Ico a b).filterₓ ((· ≤ ·) c) = Ico a b :=
  filter_true_of_mem fun x hx => hca.trans (mem_Ico.1 hx).1
#align finset.Ico_filter_le_of_le_left Finset.Ico_filter_le_of_le_left
-/

#print Finset.Ico_filter_le_of_right_le /-
theorem Ico_filter_le_of_right_le {a b : α} [DecidablePred ((· ≤ ·) b)] :
    (Ico a b).filterₓ ((· ≤ ·) b) = ∅ :=
  filter_false_of_mem fun x hx => (mem_Ico.1 hx).2.not_le
#align finset.Ico_filter_le_of_right_le Finset.Ico_filter_le_of_right_le
-/

#print Finset.Ico_filter_le_of_left_le /-
theorem Ico_filter_le_of_left_le {a b c : α} [DecidablePred ((· ≤ ·) c)] (hac : a ≤ c) :
    (Ico a b).filterₓ ((· ≤ ·) c) = Ico c b := by
  ext x
  rw [mem_filter, mem_Ico, mem_Ico, and_comm', and_left_comm]
  exact and_iff_right_of_imp fun h => hac.trans h.1
#align finset.Ico_filter_le_of_left_le Finset.Ico_filter_le_of_left_le
-/

#print Finset.Icc_filter_lt_of_lt_right /-
theorem Icc_filter_lt_of_lt_right {a b c : α} [DecidablePred (· < c)] (h : b < c) :
    (Icc a b).filterₓ (· < c) = Icc a b :=
  (Finset.filter_eq_self _).2 fun x hx => lt_of_le_of_lt (mem_Icc.1 hx).2 h
#align finset.Icc_filter_lt_of_lt_right Finset.Icc_filter_lt_of_lt_right
-/

#print Finset.Ioc_filter_lt_of_lt_right /-
theorem Ioc_filter_lt_of_lt_right {a b c : α} [DecidablePred (· < c)] (h : b < c) :
    (Ioc a b).filterₓ (· < c) = Ioc a b :=
  (Finset.filter_eq_self _).2 fun x hx => lt_of_le_of_lt (mem_Ioc.1 hx).2 h
#align finset.Ioc_filter_lt_of_lt_right Finset.Ioc_filter_lt_of_lt_right
-/

#print Finset.Iic_filter_lt_of_lt_right /-
theorem Iic_filter_lt_of_lt_right {α} [Preorder α] [LocallyFiniteOrderBot α] {a c : α}
    [DecidablePred (· < c)] (h : a < c) : (Iic a).filterₓ (· < c) = Iic a :=
  (Finset.filter_eq_self _).2 fun x hx => lt_of_le_of_lt (mem_Iic.1 hx) h
#align finset.Iic_filter_lt_of_lt_right Finset.Iic_filter_lt_of_lt_right
-/

variable (a b) [Fintype α]

#print Finset.filter_lt_lt_eq_Ioo /-
theorem filter_lt_lt_eq_Ioo [DecidablePred fun j => a < j ∧ j < b] :
    (univ.filterₓ fun j => a < j ∧ j < b) = Ioo a b :=
  by
  ext
  simp
#align finset.filter_lt_lt_eq_Ioo Finset.filter_lt_lt_eq_Ioo
-/

#print Finset.filter_lt_le_eq_Ioc /-
theorem filter_lt_le_eq_Ioc [DecidablePred fun j => a < j ∧ j ≤ b] :
    (univ.filterₓ fun j => a < j ∧ j ≤ b) = Ioc a b :=
  by
  ext
  simp
#align finset.filter_lt_le_eq_Ioc Finset.filter_lt_le_eq_Ioc
-/

#print Finset.filter_le_lt_eq_Ico /-
theorem filter_le_lt_eq_Ico [DecidablePred fun j => a ≤ j ∧ j < b] :
    (univ.filterₓ fun j => a ≤ j ∧ j < b) = Ico a b :=
  by
  ext
  simp
#align finset.filter_le_lt_eq_Ico Finset.filter_le_lt_eq_Ico
-/

#print Finset.filter_le_le_eq_Icc /-
theorem filter_le_le_eq_Icc [DecidablePred fun j => a ≤ j ∧ j ≤ b] :
    (univ.filterₓ fun j => a ≤ j ∧ j ≤ b) = Icc a b :=
  by
  ext
  simp
#align finset.filter_le_le_eq_Icc Finset.filter_le_le_eq_Icc
-/

end Filter

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α]

#print Finset.Icc_subset_Ici_self /-
theorem Icc_subset_Ici_self : Icc a b ⊆ Ici a := by
  simpa [← coe_subset] using Set.Icc_subset_Ici_self
#align finset.Icc_subset_Ici_self Finset.Icc_subset_Ici_self
-/

#print Finset.Ico_subset_Ici_self /-
theorem Ico_subset_Ici_self : Ico a b ⊆ Ici a := by
  simpa [← coe_subset] using Set.Ico_subset_Ici_self
#align finset.Ico_subset_Ici_self Finset.Ico_subset_Ici_self
-/

#print Finset.Ioc_subset_Ioi_self /-
theorem Ioc_subset_Ioi_self : Ioc a b ⊆ Ioi a := by
  simpa [← coe_subset] using Set.Ioc_subset_Ioi_self
#align finset.Ioc_subset_Ioi_self Finset.Ioc_subset_Ioi_self
-/

#print Finset.Ioo_subset_Ioi_self /-
theorem Ioo_subset_Ioi_self : Ioo a b ⊆ Ioi a := by
  simpa [← coe_subset] using Set.Ioo_subset_Ioi_self
#align finset.Ioo_subset_Ioi_self Finset.Ioo_subset_Ioi_self
-/

#print Finset.Ioc_subset_Ici_self /-
theorem Ioc_subset_Ici_self : Ioc a b ⊆ Ici a :=
  Ioc_subset_Icc_self.trans Icc_subset_Ici_self
#align finset.Ioc_subset_Ici_self Finset.Ioc_subset_Ici_self
-/

#print Finset.Ioo_subset_Ici_self /-
theorem Ioo_subset_Ici_self : Ioo a b ⊆ Ici a :=
  Ioo_subset_Ico_self.trans Ico_subset_Ici_self
#align finset.Ioo_subset_Ici_self Finset.Ioo_subset_Ici_self
-/

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot

variable [LocallyFiniteOrderBot α]

#print Finset.Icc_subset_Iic_self /-
theorem Icc_subset_Iic_self : Icc a b ⊆ Iic b := by
  simpa [← coe_subset] using Set.Icc_subset_Iic_self
#align finset.Icc_subset_Iic_self Finset.Icc_subset_Iic_self
-/

#print Finset.Ioc_subset_Iic_self /-
theorem Ioc_subset_Iic_self : Ioc a b ⊆ Iic b := by
  simpa [← coe_subset] using Set.Ioc_subset_Iic_self
#align finset.Ioc_subset_Iic_self Finset.Ioc_subset_Iic_self
-/

#print Finset.Ico_subset_Iio_self /-
theorem Ico_subset_Iio_self : Ico a b ⊆ Iio b := by
  simpa [← coe_subset] using Set.Ico_subset_Iio_self
#align finset.Ico_subset_Iio_self Finset.Ico_subset_Iio_self
-/

#print Finset.Ioo_subset_Iio_self /-
theorem Ioo_subset_Iio_self : Ioo a b ⊆ Iio b := by
  simpa [← coe_subset] using Set.Ioo_subset_Iio_self
#align finset.Ioo_subset_Iio_self Finset.Ioo_subset_Iio_self
-/

#print Finset.Ico_subset_Iic_self /-
theorem Ico_subset_Iic_self : Ico a b ⊆ Iic b :=
  Ico_subset_Icc_self.trans Icc_subset_Iic_self
#align finset.Ico_subset_Iic_self Finset.Ico_subset_Iic_self
-/

#print Finset.Ioo_subset_Iic_self /-
theorem Ioo_subset_Iic_self : Ioo a b ⊆ Iic b :=
  Ioo_subset_Ioc_self.trans Ioc_subset_Iic_self
#align finset.Ioo_subset_Iic_self Finset.Ioo_subset_Iic_self
-/

end LocallyFiniteOrderBot

end LocallyFiniteOrder

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α] {a : α}

#print Finset.Ioi_subset_Ici_self /-
theorem Ioi_subset_Ici_self : Ioi a ⊆ Ici a := by simpa [← coe_subset] using Set.Ioi_subset_Ici_self
#align finset.Ioi_subset_Ici_self Finset.Ioi_subset_Ici_self
-/

#print BddBelow.finite /-
theorem BddBelow.finite {s : Set α} (hs : BddBelow s) : s.Finite :=
  let ⟨a, ha⟩ := hs
  (Ici a).finite_toSet.Subset fun x hx => mem_Ici.2 <| ha hx
#align bdd_below.finite BddBelow.finite
-/

variable [Fintype α]

#print Finset.filter_lt_eq_Ioi /-
theorem filter_lt_eq_Ioi [DecidablePred ((· < ·) a)] : univ.filterₓ ((· < ·) a) = Ioi a :=
  by
  ext
  simp
#align finset.filter_lt_eq_Ioi Finset.filter_lt_eq_Ioi
-/

#print Finset.filter_le_eq_Ici /-
theorem filter_le_eq_Ici [DecidablePred ((· ≤ ·) a)] : univ.filterₓ ((· ≤ ·) a) = Ici a :=
  by
  ext
  simp
#align finset.filter_le_eq_Ici Finset.filter_le_eq_Ici
-/

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot

variable [LocallyFiniteOrderBot α] {a : α}

#print Finset.Iio_subset_Iic_self /-
theorem Iio_subset_Iic_self : Iio a ⊆ Iic a := by simpa [← coe_subset] using Set.Iio_subset_Iic_self
#align finset.Iio_subset_Iic_self Finset.Iio_subset_Iic_self
-/

#print BddAbove.finite /-
theorem BddAbove.finite {s : Set α} (hs : BddAbove s) : s.Finite :=
  hs.dual.Finite
#align bdd_above.finite BddAbove.finite
-/

variable [Fintype α]

#print Finset.filter_gt_eq_Iio /-
theorem filter_gt_eq_Iio [DecidablePred (· < a)] : univ.filterₓ (· < a) = Iio a :=
  by
  ext
  simp
#align finset.filter_gt_eq_Iio Finset.filter_gt_eq_Iio
-/

#print Finset.filter_ge_eq_Iic /-
theorem filter_ge_eq_Iic [DecidablePred (· ≤ a)] : univ.filterₓ (· ≤ a) = Iic a :=
  by
  ext
  simp
#align finset.filter_ge_eq_Iic Finset.filter_ge_eq_Iic
-/

end LocallyFiniteOrderBot

variable [LocallyFiniteOrderTop α] [LocallyFiniteOrderBot α]

/- warning: finset.disjoint_Ioi_Iio -> Finset.disjoint_Ioi_Iio is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : LocallyFiniteOrderTop.{u1} α _inst_1] [_inst_3 : LocallyFiniteOrderBot.{u1} α _inst_1] (a : α), Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) (Finset.Ioi.{u1} α _inst_1 _inst_2 a) (Finset.Iio.{u1} α _inst_1 _inst_3 a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : LocallyFiniteOrderTop.{u1} α _inst_1] [_inst_3 : LocallyFiniteOrderBot.{u1} α _inst_1] (a : α), Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (Finset.Ioi.{u1} α _inst_1 _inst_2 a) (Finset.Iio.{u1} α _inst_1 _inst_3 a)
Case conversion may be inaccurate. Consider using '#align finset.disjoint_Ioi_Iio Finset.disjoint_Ioi_Iioₓ'. -/
theorem disjoint_Ioi_Iio (a : α) : Disjoint (Ioi a) (Iio a) :=
  disjoint_left.2 fun b hab hba => (mem_Ioi.1 hab).not_lt <| mem_Iio.1 hba
#align finset.disjoint_Ioi_Iio Finset.disjoint_Ioi_Iio

end Preorder

section PartialOrder

variable [PartialOrder α] [LocallyFiniteOrder α] {a b c : α}

#print Finset.Icc_self /-
@[simp]
theorem Icc_self (a : α) : Icc a a = {a} := by rw [← coe_eq_singleton, coe_Icc, Set.Icc_self]
#align finset.Icc_self Finset.Icc_self
-/

#print Finset.Icc_eq_singleton_iff /-
@[simp]
theorem Icc_eq_singleton_iff : Icc a b = {c} ↔ a = c ∧ b = c := by
  rw [← coe_eq_singleton, coe_Icc, Set.Icc_eq_singleton_iff]
#align finset.Icc_eq_singleton_iff Finset.Icc_eq_singleton_iff
-/

/- warning: finset.Ico_disjoint_Ico_consecutive -> Finset.Ico_disjoint_Ico_consecutive is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] (a : α) (b : α) (c : α), Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] (a : α) (b : α) (c : α), Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b c)
Case conversion may be inaccurate. Consider using '#align finset.Ico_disjoint_Ico_consecutive Finset.Ico_disjoint_Ico_consecutiveₓ'. -/
theorem Ico_disjoint_Ico_consecutive (a b c : α) : Disjoint (Ico a b) (Ico b c) :=
  disjoint_left.2 fun x hab hbc => (mem_Ico.mp hab).2.not_le (mem_Ico.mp hbc).1
#align finset.Ico_disjoint_Ico_consecutive Finset.Ico_disjoint_Ico_consecutive

section DecidableEq

variable [DecidableEq α]

#print Finset.Icc_erase_left /-
@[simp]
theorem Icc_erase_left (a b : α) : (Icc a b).eraseₓ a = Ioc a b := by simp [← coe_inj]
#align finset.Icc_erase_left Finset.Icc_erase_left
-/

#print Finset.Icc_erase_right /-
@[simp]
theorem Icc_erase_right (a b : α) : (Icc a b).eraseₓ b = Ico a b := by simp [← coe_inj]
#align finset.Icc_erase_right Finset.Icc_erase_right
-/

#print Finset.Ico_erase_left /-
@[simp]
theorem Ico_erase_left (a b : α) : (Ico a b).eraseₓ a = Ioo a b := by simp [← coe_inj]
#align finset.Ico_erase_left Finset.Ico_erase_left
-/

#print Finset.Ioc_erase_right /-
@[simp]
theorem Ioc_erase_right (a b : α) : (Ioc a b).eraseₓ b = Ioo a b := by simp [← coe_inj]
#align finset.Ioc_erase_right Finset.Ioc_erase_right
-/

#print Finset.Icc_diff_both /-
@[simp]
theorem Icc_diff_both (a b : α) : Icc a b \ {a, b} = Ioo a b := by simp [← coe_inj]
#align finset.Icc_diff_both Finset.Icc_diff_both
-/

#print Finset.Ico_insert_right /-
@[simp]
theorem Ico_insert_right (h : a ≤ b) : insert b (Ico a b) = Icc a b := by
  rw [← coe_inj, coe_insert, coe_Icc, coe_Ico, Set.insert_eq, Set.union_comm, Set.Ico_union_right h]
#align finset.Ico_insert_right Finset.Ico_insert_right
-/

#print Finset.Ioc_insert_left /-
@[simp]
theorem Ioc_insert_left (h : a ≤ b) : insert a (Ioc a b) = Icc a b := by
  rw [← coe_inj, coe_insert, coe_Ioc, coe_Icc, Set.insert_eq, Set.union_comm, Set.Ioc_union_left h]
#align finset.Ioc_insert_left Finset.Ioc_insert_left
-/

#print Finset.Ioo_insert_left /-
@[simp]
theorem Ioo_insert_left (h : a < b) : insert a (Ioo a b) = Ico a b := by
  rw [← coe_inj, coe_insert, coe_Ioo, coe_Ico, Set.insert_eq, Set.union_comm, Set.Ioo_union_left h]
#align finset.Ioo_insert_left Finset.Ioo_insert_left
-/

#print Finset.Ioo_insert_right /-
@[simp]
theorem Ioo_insert_right (h : a < b) : insert b (Ioo a b) = Ioc a b := by
  rw [← coe_inj, coe_insert, coe_Ioo, coe_Ioc, Set.insert_eq, Set.union_comm, Set.Ioo_union_right h]
#align finset.Ioo_insert_right Finset.Ioo_insert_right
-/

#print Finset.Icc_diff_Ico_self /-
@[simp]
theorem Icc_diff_Ico_self (h : a ≤ b) : Icc a b \ Ico a b = {b} := by simp [← coe_inj, h]
#align finset.Icc_diff_Ico_self Finset.Icc_diff_Ico_self
-/

#print Finset.Icc_diff_Ioc_self /-
@[simp]
theorem Icc_diff_Ioc_self (h : a ≤ b) : Icc a b \ Ioc a b = {a} := by simp [← coe_inj, h]
#align finset.Icc_diff_Ioc_self Finset.Icc_diff_Ioc_self
-/

#print Finset.Icc_diff_Ioo_self /-
@[simp]
theorem Icc_diff_Ioo_self (h : a ≤ b) : Icc a b \ Ioo a b = {a, b} := by simp [← coe_inj, h]
#align finset.Icc_diff_Ioo_self Finset.Icc_diff_Ioo_self
-/

#print Finset.Ico_diff_Ioo_self /-
@[simp]
theorem Ico_diff_Ioo_self (h : a < b) : Ico a b \ Ioo a b = {a} := by simp [← coe_inj, h]
#align finset.Ico_diff_Ioo_self Finset.Ico_diff_Ioo_self
-/

#print Finset.Ioc_diff_Ioo_self /-
@[simp]
theorem Ioc_diff_Ioo_self (h : a < b) : Ioc a b \ Ioo a b = {b} := by simp [← coe_inj, h]
#align finset.Ioc_diff_Ioo_self Finset.Ioc_diff_Ioo_self
-/

#print Finset.Ico_inter_Ico_consecutive /-
@[simp]
theorem Ico_inter_Ico_consecutive (a b c : α) : Ico a b ∩ Ico b c = ∅ :=
  (Ico_disjoint_Ico_consecutive a b c).eq_bot
#align finset.Ico_inter_Ico_consecutive Finset.Ico_inter_Ico_consecutive
-/

end DecidableEq

#print Finset.Icc_eq_cons_Ico /-
-- Those lemmas are purposefully the other way around
theorem Icc_eq_cons_Ico (h : a ≤ b) : Icc a b = (Ico a b).cons b right_not_mem_Ico := by
  classical rw [cons_eq_insert, Ico_insert_right h]
#align finset.Icc_eq_cons_Ico Finset.Icc_eq_cons_Ico
-/

#print Finset.Icc_eq_cons_Ioc /-
theorem Icc_eq_cons_Ioc (h : a ≤ b) : Icc a b = (Ioc a b).cons a left_not_mem_Ioc := by
  classical rw [cons_eq_insert, Ioc_insert_left h]
#align finset.Icc_eq_cons_Ioc Finset.Icc_eq_cons_Ioc
-/

#print Finset.Ico_filter_le_left /-
theorem Ico_filter_le_left {a b : α} [DecidablePred (· ≤ a)] (hab : a < b) :
    ((Ico a b).filterₓ fun x => x ≤ a) = {a} :=
  by
  ext x
  rw [mem_filter, mem_Ico, mem_singleton, and_right_comm, ← le_antisymm_iff, eq_comm]
  exact and_iff_left_of_imp fun h => h.le.trans_lt hab
#align finset.Ico_filter_le_left Finset.Ico_filter_le_left
-/

#print Finset.card_Ico_eq_card_Icc_sub_one /-
theorem card_Ico_eq_card_Icc_sub_one (a b : α) : (Ico a b).card = (Icc a b).card - 1 := by
  classical
    by_cases h : a ≤ b
    · rw [← Ico_insert_right h, card_insert_of_not_mem right_not_mem_Ico]
      exact (Nat.add_sub_cancel _ _).symm
    · rw [Ico_eq_empty fun h' => h h'.le, Icc_eq_empty h, card_empty, zero_tsub]
#align finset.card_Ico_eq_card_Icc_sub_one Finset.card_Ico_eq_card_Icc_sub_one
-/

#print Finset.card_Ioc_eq_card_Icc_sub_one /-
theorem card_Ioc_eq_card_Icc_sub_one (a b : α) : (Ioc a b).card = (Icc a b).card - 1 :=
  @card_Ico_eq_card_Icc_sub_one αᵒᵈ _ _ _ _
#align finset.card_Ioc_eq_card_Icc_sub_one Finset.card_Ioc_eq_card_Icc_sub_one
-/

#print Finset.card_Ioo_eq_card_Ico_sub_one /-
theorem card_Ioo_eq_card_Ico_sub_one (a b : α) : (Ioo a b).card = (Ico a b).card - 1 := by
  classical
    by_cases h : a ≤ b
    · obtain rfl | h' := h.eq_or_lt
      · rw [Ioo_self, Ico_self, card_empty]
      rw [← Ioo_insert_left h', card_insert_of_not_mem left_not_mem_Ioo]
      exact (Nat.add_sub_cancel _ _).symm
    · rw [Ioo_eq_empty fun h' => h h'.le, Ico_eq_empty fun h' => h h'.le, card_empty, zero_tsub]
#align finset.card_Ioo_eq_card_Ico_sub_one Finset.card_Ioo_eq_card_Ico_sub_one
-/

#print Finset.card_Ioo_eq_card_Ioc_sub_one /-
theorem card_Ioo_eq_card_Ioc_sub_one (a b : α) : (Ioo a b).card = (Ioc a b).card - 1 :=
  @card_Ioo_eq_card_Ico_sub_one αᵒᵈ _ _ _ _
#align finset.card_Ioo_eq_card_Ioc_sub_one Finset.card_Ioo_eq_card_Ioc_sub_one
-/

#print Finset.card_Ioo_eq_card_Icc_sub_two /-
theorem card_Ioo_eq_card_Icc_sub_two (a b : α) : (Ioo a b).card = (Icc a b).card - 2 :=
  by
  rw [card_Ioo_eq_card_Ico_sub_one, card_Ico_eq_card_Icc_sub_one]
  rfl
#align finset.card_Ioo_eq_card_Icc_sub_two Finset.card_Ioo_eq_card_Icc_sub_two
-/

end PartialOrder

section BoundedPartialOrder

variable [PartialOrder α]

section OrderTop

variable [LocallyFiniteOrderTop α]

#print Finset.Ici_erase /-
@[simp]
theorem Ici_erase [DecidableEq α] (a : α) : (Ici a).eraseₓ a = Ioi a :=
  by
  ext
  simp_rw [Finset.mem_erase, mem_Ici, mem_Ioi, lt_iff_le_and_ne, and_comm', ne_comm]
#align finset.Ici_erase Finset.Ici_erase
-/

#print Finset.Ioi_insert /-
@[simp]
theorem Ioi_insert [DecidableEq α] (a : α) : insert a (Ioi a) = Ici a :=
  by
  ext
  simp_rw [Finset.mem_insert, mem_Ici, mem_Ioi, le_iff_lt_or_eq, or_comm', eq_comm]
#align finset.Ioi_insert Finset.Ioi_insert
-/

#print Finset.not_mem_Ioi_self /-
@[simp]
theorem not_mem_Ioi_self {b : α} : b ∉ Ioi b := fun h => lt_irrefl _ (mem_Ioi.1 h)
#align finset.not_mem_Ioi_self Finset.not_mem_Ioi_self
-/

#print Finset.Ici_eq_cons_Ioi /-
-- Purposefully written the other way around
theorem Ici_eq_cons_Ioi (a : α) : Ici a = (Ioi a).cons a not_mem_Ioi_self := by
  classical rw [cons_eq_insert, Ioi_insert]
#align finset.Ici_eq_cons_Ioi Finset.Ici_eq_cons_Ioi
-/

#print Finset.card_Ioi_eq_card_Ici_sub_one /-
theorem card_Ioi_eq_card_Ici_sub_one (a : α) : (Ioi a).card = (Ici a).card - 1 := by
  rw [Ici_eq_cons_Ioi, card_cons, add_tsub_cancel_right]
#align finset.card_Ioi_eq_card_Ici_sub_one Finset.card_Ioi_eq_card_Ici_sub_one
-/

end OrderTop

section OrderBot

variable [LocallyFiniteOrderBot α]

#print Finset.Iic_erase /-
@[simp]
theorem Iic_erase [DecidableEq α] (b : α) : (Iic b).eraseₓ b = Iio b :=
  by
  ext
  simp_rw [Finset.mem_erase, mem_Iic, mem_Iio, lt_iff_le_and_ne, and_comm']
#align finset.Iic_erase Finset.Iic_erase
-/

#print Finset.Iio_insert /-
@[simp]
theorem Iio_insert [DecidableEq α] (b : α) : insert b (Iio b) = Iic b :=
  by
  ext
  simp_rw [Finset.mem_insert, mem_Iic, mem_Iio, le_iff_lt_or_eq, or_comm']
#align finset.Iio_insert Finset.Iio_insert
-/

#print Finset.not_mem_Iio_self /-
@[simp]
theorem not_mem_Iio_self {b : α} : b ∉ Iio b := fun h => lt_irrefl _ (mem_Iio.1 h)
#align finset.not_mem_Iio_self Finset.not_mem_Iio_self
-/

#print Finset.Iic_eq_cons_Iio /-
-- Purposefully written the other way around
theorem Iic_eq_cons_Iio (b : α) : Iic b = (Iio b).cons b not_mem_Iio_self := by
  classical rw [cons_eq_insert, Iio_insert]
#align finset.Iic_eq_cons_Iio Finset.Iic_eq_cons_Iio
-/

#print Finset.card_Iio_eq_card_Iic_sub_one /-
theorem card_Iio_eq_card_Iic_sub_one (a : α) : (Iio a).card = (Iic a).card - 1 := by
  rw [Iic_eq_cons_Iio, card_cons, add_tsub_cancel_right]
#align finset.card_Iio_eq_card_Iic_sub_one Finset.card_Iio_eq_card_Iic_sub_one
-/

end OrderBot

end BoundedPartialOrder

section LinearOrder

variable [LinearOrder α]

section LocallyFiniteOrder

variable [LocallyFiniteOrder α] {a b : α}

#print Finset.Ico_subset_Ico_iff /-
theorem Ico_subset_Ico_iff {a₁ b₁ a₂ b₂ : α} (h : a₁ < b₁) :
    Ico a₁ b₁ ⊆ Ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ := by
  rw [← coe_subset, coe_Ico, coe_Ico, Set.Ico_subset_Ico_iff h]
#align finset.Ico_subset_Ico_iff Finset.Ico_subset_Ico_iff
-/

/- warning: finset.Ico_union_Ico_eq_Ico -> Finset.Ico_union_Ico_eq_Ico is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) b c) -> (Eq.{succ u1} (Finset.{u1} α) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => Eq.decidable.{u1} α _inst_1 a b)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 a b) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 b c)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) b c) -> (Eq.{succ u1} (Finset.{u1} α) (Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => instDecidableEq.{u1} α _inst_1 a b)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 a b) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 b c)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 a c))
Case conversion may be inaccurate. Consider using '#align finset.Ico_union_Ico_eq_Ico Finset.Ico_union_Ico_eq_Icoₓ'. -/
theorem Ico_union_Ico_eq_Ico {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) :
    Ico a b ∪ Ico b c = Ico a c := by
  rw [← coe_inj, coe_union, coe_Ico, coe_Ico, coe_Ico, Set.Ico_union_Ico_eq_Ico hab hbc]
#align finset.Ico_union_Ico_eq_Ico Finset.Ico_union_Ico_eq_Ico

/- warning: finset.Ioc_union_Ioc_eq_Ioc -> Finset.Ioc_union_Ioc_eq_Ioc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) b c) -> (Eq.{succ u1} (Finset.{u1} α) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => Eq.decidable.{u1} α _inst_1 a b)) (Finset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 a b) (Finset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 b c)) (Finset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) b c) -> (Eq.{succ u1} (Finset.{u1} α) (Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => instDecidableEq.{u1} α _inst_1 a b)) (Finset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 a b) (Finset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 b c)) (Finset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 a c))
Case conversion may be inaccurate. Consider using '#align finset.Ioc_union_Ioc_eq_Ioc Finset.Ioc_union_Ioc_eq_Iocₓ'. -/
@[simp]
theorem Ioc_union_Ioc_eq_Ioc {a b c : α} (h₁ : a ≤ b) (h₂ : b ≤ c) : Ioc a b ∪ Ioc b c = Ioc a c :=
  by rw [← coe_inj, coe_union, coe_Ioc, coe_Ioc, coe_Ioc, Set.Ioc_union_Ioc_eq_Ioc h₁ h₂]
#align finset.Ioc_union_Ioc_eq_Ioc Finset.Ioc_union_Ioc_eq_Ioc

/- warning: finset.Ico_subset_Ico_union_Ico -> Finset.Ico_subset_Ico_union_Ico is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))] {a : α} {b : α} {c : α}, HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 a c) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => Eq.decidable.{u1} α _inst_1 a b)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 a b) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))] {a : α} {b : α} {c : α}, HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 a c) (Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => instDecidableEq.{u1} α _inst_1 a b)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 a b) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 b c))
Case conversion may be inaccurate. Consider using '#align finset.Ico_subset_Ico_union_Ico Finset.Ico_subset_Ico_union_Icoₓ'. -/
theorem Ico_subset_Ico_union_Ico {a b c : α} : Ico a c ⊆ Ico a b ∪ Ico b c :=
  by
  rw [← coe_subset, coe_union, coe_Ico, coe_Ico, coe_Ico]
  exact Set.Ico_subset_Ico_union_Ico
#align finset.Ico_subset_Ico_union_Ico Finset.Ico_subset_Ico_union_Ico

/- warning: finset.Ico_union_Ico' -> Finset.Ico_union_Ico' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) c b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a d) -> (Eq.{succ u1} (Finset.{u1} α) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => Eq.decidable.{u1} α _inst_1 a b)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 a b) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 c d)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 (LinearOrder.min.{u1} α _inst_1 a c) (LinearOrder.max.{u1} α _inst_1 b d)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) c b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a d) -> (Eq.{succ u1} (Finset.{u1} α) (Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => instDecidableEq.{u1} α _inst_1 a b)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 a b) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 c d)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) a c) (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) b d)))
Case conversion may be inaccurate. Consider using '#align finset.Ico_union_Ico' Finset.Ico_union_Ico'ₓ'. -/
theorem Ico_union_Ico' {a b c d : α} (hcb : c ≤ b) (had : a ≤ d) :
    Ico a b ∪ Ico c d = Ico (min a c) (max b d) := by
  rw [← coe_inj, coe_union, coe_Ico, coe_Ico, coe_Ico, Set.Ico_union_Ico' hcb had]
#align finset.Ico_union_Ico' Finset.Ico_union_Ico'

/- warning: finset.Ico_union_Ico -> Finset.Ico_union_Ico is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (LinearOrder.min.{u1} α _inst_1 a b) (LinearOrder.max.{u1} α _inst_1 c d)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (LinearOrder.min.{u1} α _inst_1 c d) (LinearOrder.max.{u1} α _inst_1 a b)) -> (Eq.{succ u1} (Finset.{u1} α) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => Eq.decidable.{u1} α _inst_1 a b)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 a b) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 c d)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 (LinearOrder.min.{u1} α _inst_1 a c) (LinearOrder.max.{u1} α _inst_1 b d)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) a b) (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) c d)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) c d) (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) a b)) -> (Eq.{succ u1} (Finset.{u1} α) (Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => instDecidableEq.{u1} α _inst_1 a b)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 a b) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 c d)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) a c) (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) b d)))
Case conversion may be inaccurate. Consider using '#align finset.Ico_union_Ico Finset.Ico_union_Icoₓ'. -/
theorem Ico_union_Ico {a b c d : α} (h₁ : min a b ≤ max c d) (h₂ : min c d ≤ max a b) :
    Ico a b ∪ Ico c d = Ico (min a c) (max b d) := by
  rw [← coe_inj, coe_union, coe_Ico, coe_Ico, coe_Ico, Set.Ico_union_Ico h₁ h₂]
#align finset.Ico_union_Ico Finset.Ico_union_Ico

/- warning: finset.Ico_inter_Ico -> Finset.Ico_inter_Ico is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))] {a : α} {b : α} {c : α} {d : α}, Eq.{succ u1} (Finset.{u1} α) (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => Eq.decidable.{u1} α _inst_1 a b)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 a b) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 c d)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 (LinearOrder.max.{u1} α _inst_1 a c) (LinearOrder.min.{u1} α _inst_1 b d))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))] {a : α} {b : α} {c : α} {d : α}, Eq.{succ u1} (Finset.{u1} α) (Inter.inter.{u1} (Finset.{u1} α) (Finset.instInterFinset.{u1} α (fun (a : α) (b : α) => instDecidableEq.{u1} α _inst_1 a b)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 a b) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 c d)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) a c) (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) b d))
Case conversion may be inaccurate. Consider using '#align finset.Ico_inter_Ico Finset.Ico_inter_Icoₓ'. -/
theorem Ico_inter_Ico {a b c d : α} : Ico a b ∩ Ico c d = Ico (max a c) (min b d) := by
  rw [← coe_inj, coe_inter, coe_Ico, coe_Ico, coe_Ico, ← inf_eq_min, ← sup_eq_max,
    Set.Ico_inter_Ico]
#align finset.Ico_inter_Ico Finset.Ico_inter_Ico

#print Finset.Ico_filter_lt /-
@[simp]
theorem Ico_filter_lt (a b c : α) : ((Ico a b).filterₓ fun x => x < c) = Ico a (min b c) :=
  by
  cases le_total b c
  · rw [Ico_filter_lt_of_right_le h, min_eq_left h]
  · rw [Ico_filter_lt_of_le_right h, min_eq_right h]
#align finset.Ico_filter_lt Finset.Ico_filter_lt
-/

#print Finset.Ico_filter_le /-
@[simp]
theorem Ico_filter_le (a b c : α) : ((Ico a b).filterₓ fun x => c ≤ x) = Ico (max a c) b :=
  by
  cases le_total a c
  · rw [Ico_filter_le_of_left_le h, max_eq_right h]
  · rw [Ico_filter_le_of_le_left h, max_eq_left h]
#align finset.Ico_filter_le Finset.Ico_filter_le
-/

#print Finset.Ioo_filter_lt /-
@[simp]
theorem Ioo_filter_lt (a b c : α) : (Ioo a b).filterₓ (· < c) = Ioo a (min b c) :=
  by
  ext
  simp [and_assoc']
#align finset.Ioo_filter_lt Finset.Ioo_filter_lt
-/

#print Finset.Iio_filter_lt /-
@[simp]
theorem Iio_filter_lt {α} [LinearOrder α] [LocallyFiniteOrderBot α] (a b : α) :
    (Iio a).filterₓ (· < b) = Iio (min a b) := by
  ext
  simp [and_assoc']
#align finset.Iio_filter_lt Finset.Iio_filter_lt
-/

/- warning: finset.Ico_diff_Ico_left -> Finset.Ico_diff_Ico_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.hasSdiff.{u1} α (fun (a : α) (b : α) => Eq.decidable.{u1} α _inst_1 a b)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 a b) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 a c)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 (LinearOrder.max.{u1} α _inst_1 a c) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.instSDiffFinset.{u1} α (fun (a : α) (b : α) => instDecidableEq.{u1} α _inst_1 a b)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 a b) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 a c)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) a c) b)
Case conversion may be inaccurate. Consider using '#align finset.Ico_diff_Ico_left Finset.Ico_diff_Ico_leftₓ'. -/
@[simp]
theorem Ico_diff_Ico_left (a b c : α) : Ico a b \ Ico a c = Ico (max a c) b :=
  by
  cases le_total a c
  · ext x
    rw [mem_sdiff, mem_Ico, mem_Ico, mem_Ico, max_eq_right h, and_right_comm, not_and, not_lt]
    exact and_congr_left' ⟨fun hx => hx.2 hx.1, fun hx => ⟨h.trans hx, fun _ => hx⟩⟩
  · rw [Ico_eq_empty_of_le h, sdiff_empty, max_eq_left h]
#align finset.Ico_diff_Ico_left Finset.Ico_diff_Ico_left

/- warning: finset.Ico_diff_Ico_right -> Finset.Ico_diff_Ico_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.hasSdiff.{u1} α (fun (a : α) (b : α) => Eq.decidable.{u1} α _inst_1 a b)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 a b) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 c b)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 a (LinearOrder.min.{u1} α _inst_1 b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.instSDiffFinset.{u1} α (fun (a : α) (b : α) => instDecidableEq.{u1} α _inst_1 a b)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 a b) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 c b)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 a (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) b c))
Case conversion may be inaccurate. Consider using '#align finset.Ico_diff_Ico_right Finset.Ico_diff_Ico_rightₓ'. -/
@[simp]
theorem Ico_diff_Ico_right (a b c : α) : Ico a b \ Ico c b = Ico a (min b c) :=
  by
  cases le_total b c
  · rw [Ico_eq_empty_of_le h, sdiff_empty, min_eq_left h]
  · ext x
    rw [mem_sdiff, mem_Ico, mem_Ico, mem_Ico, min_eq_right h, and_assoc', not_and', not_le]
    exact and_congr_right' ⟨fun hx => hx.2 hx.1, fun hx => ⟨hx.trans_le h, fun _ => hx⟩⟩
#align finset.Ico_diff_Ico_right Finset.Ico_diff_Ico_right

end LocallyFiniteOrder

variable [Fintype α] [LocallyFiniteOrderTop α] [LocallyFiniteOrderBot α]

/- warning: finset.Ioi_disj_union_Iio -> Finset.Ioi_disjUnion_Iio is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : Fintype.{u1} α] [_inst_3 : LocallyFiniteOrderTop.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))] [_inst_4 : LocallyFiniteOrderBot.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))] (a : α), Eq.{succ u1} (Finset.{u1} α) (Finset.disjUnion.{u1} α (Finset.Ioi.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_3 a) (Finset.Iio.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_4 a) (Finset.disjoint_Ioi_Iio.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_3 _inst_4 a)) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_2 (fun (a : α) (b : α) => Eq.decidable.{u1} α _inst_1 a b))) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : Fintype.{u1} α] [_inst_3 : LocallyFiniteOrderTop.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))] [_inst_4 : LocallyFiniteOrderBot.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))] (a : α), Eq.{succ u1} (Finset.{u1} α) (Finset.disjUnion.{u1} α (Finset.Ioi.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_3 a) (Finset.Iio.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_4 a) (Finset.disjoint_Ioi_Iio.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_3 _inst_4 a)) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_2 (fun (a : α) (b : α) => instDecidableEq.{u1} α _inst_1 a b))) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a))
Case conversion may be inaccurate. Consider using '#align finset.Ioi_disj_union_Iio Finset.Ioi_disjUnion_Iioₓ'. -/
theorem Ioi_disjUnion_Iio (a : α) :
    (Ioi a).disjUnion (Iio a) (disjoint_Ioi_Iio a) = ({a} : Finset α)ᶜ :=
  by
  ext
  simp [eq_comm]
#align finset.Ioi_disj_union_Iio Finset.Ioi_disjUnion_Iio

end LinearOrder

section Lattice

variable [Lattice α] [LocallyFiniteOrder α] {a a₁ a₂ b b₁ b₂ c x : α}

#print Finset.uIcc_toDual /-
theorem uIcc_toDual (a b : α) : [toDual a, toDual b] = [a, b].map toDual.toEmbedding :=
  Icc_toDual _ _
#align finset.uIcc_to_dual Finset.uIcc_toDual
-/

#print Finset.uIcc_of_le /-
@[simp]
theorem uIcc_of_le (h : a ≤ b) : [a, b] = Icc a b := by rw [uIcc, inf_eq_left.2 h, sup_eq_right.2 h]
#align finset.uIcc_of_le Finset.uIcc_of_le
-/

#print Finset.uIcc_of_ge /-
@[simp]
theorem uIcc_of_ge (h : b ≤ a) : [a, b] = Icc b a := by rw [uIcc, inf_eq_right.2 h, sup_eq_left.2 h]
#align finset.uIcc_of_ge Finset.uIcc_of_ge
-/

#print Finset.uIcc_comm /-
theorem uIcc_comm (a b : α) : [a, b] = [b, a] := by rw [uIcc, uIcc, inf_comm, sup_comm]
#align finset.uIcc_comm Finset.uIcc_comm
-/

#print Finset.uIcc_self /-
@[simp]
theorem uIcc_self : [a, a] = {a} := by simp [uIcc]
#align finset.uIcc_self Finset.uIcc_self
-/

#print Finset.nonempty_uIcc /-
@[simp]
theorem nonempty_uIcc : Finset.Nonempty [a, b] :=
  nonempty_Icc.2 inf_le_sup
#align finset.nonempty_uIcc Finset.nonempty_uIcc
-/

#print Finset.Icc_subset_uIcc /-
theorem Icc_subset_uIcc : Icc a b ⊆ [a, b] :=
  Icc_subset_Icc inf_le_left le_sup_right
#align finset.Icc_subset_uIcc Finset.Icc_subset_uIcc
-/

#print Finset.Icc_subset_uIcc' /-
theorem Icc_subset_uIcc' : Icc b a ⊆ [a, b] :=
  Icc_subset_Icc inf_le_right le_sup_left
#align finset.Icc_subset_uIcc' Finset.Icc_subset_uIcc'
-/

#print Finset.left_mem_uIcc /-
@[simp]
theorem left_mem_uIcc : a ∈ [a, b] :=
  mem_Icc.2 ⟨inf_le_left, le_sup_left⟩
#align finset.left_mem_uIcc Finset.left_mem_uIcc
-/

#print Finset.right_mem_uIcc /-
@[simp]
theorem right_mem_uIcc : b ∈ [a, b] :=
  mem_Icc.2 ⟨inf_le_right, le_sup_right⟩
#align finset.right_mem_uIcc Finset.right_mem_uIcc
-/

#print Finset.mem_uIcc_of_le /-
theorem mem_uIcc_of_le (ha : a ≤ x) (hb : x ≤ b) : x ∈ [a, b] :=
  Icc_subset_uIcc <| mem_Icc.2 ⟨ha, hb⟩
#align finset.mem_uIcc_of_le Finset.mem_uIcc_of_le
-/

#print Finset.mem_uIcc_of_ge /-
theorem mem_uIcc_of_ge (hb : b ≤ x) (ha : x ≤ a) : x ∈ [a, b] :=
  Icc_subset_uIcc' <| mem_Icc.2 ⟨hb, ha⟩
#align finset.mem_uIcc_of_ge Finset.mem_uIcc_of_ge
-/

#print Finset.uIcc_subset_uIcc /-
theorem uIcc_subset_uIcc (h₁ : a₁ ∈ [a₂, b₂]) (h₂ : b₁ ∈ [a₂, b₂]) : [a₁, b₁] ⊆ [a₂, b₂] :=
  by
  rw [mem_uIcc] at h₁ h₂
  exact Icc_subset_Icc (le_inf h₁.1 h₂.1) (sup_le h₁.2 h₂.2)
#align finset.uIcc_subset_uIcc Finset.uIcc_subset_uIcc
-/

#print Finset.uIcc_subset_Icc /-
theorem uIcc_subset_Icc (ha : a₁ ∈ Icc a₂ b₂) (hb : b₁ ∈ Icc a₂ b₂) : [a₁, b₁] ⊆ Icc a₂ b₂ :=
  by
  rw [mem_Icc] at ha hb
  exact Icc_subset_Icc (le_inf ha.1 hb.1) (sup_le ha.2 hb.2)
#align finset.uIcc_subset_Icc Finset.uIcc_subset_Icc
-/

#print Finset.uIcc_subset_uIcc_iff_mem /-
theorem uIcc_subset_uIcc_iff_mem : [a₁, b₁] ⊆ [a₂, b₂] ↔ a₁ ∈ [a₂, b₂] ∧ b₁ ∈ [a₂, b₂] :=
  ⟨fun h => ⟨h left_mem_uIcc, h right_mem_uIcc⟩, fun h => uIcc_subset_uIcc h.1 h.2⟩
#align finset.uIcc_subset_uIcc_iff_mem Finset.uIcc_subset_uIcc_iff_mem
-/

#print Finset.uIcc_subset_uIcc_iff_le' /-
theorem uIcc_subset_uIcc_iff_le' : [a₁, b₁] ⊆ [a₂, b₂] ↔ a₂ ⊓ b₂ ≤ a₁ ⊓ b₁ ∧ a₁ ⊔ b₁ ≤ a₂ ⊔ b₂ :=
  Icc_subset_Icc_iff inf_le_sup
#align finset.uIcc_subset_uIcc_iff_le' Finset.uIcc_subset_uIcc_iff_le'
-/

#print Finset.uIcc_subset_uIcc_right /-
theorem uIcc_subset_uIcc_right (h : x ∈ [a, b]) : [x, b] ⊆ [a, b] :=
  uIcc_subset_uIcc h right_mem_uIcc
#align finset.uIcc_subset_uIcc_right Finset.uIcc_subset_uIcc_right
-/

#print Finset.uIcc_subset_uIcc_left /-
theorem uIcc_subset_uIcc_left (h : x ∈ [a, b]) : [a, x] ⊆ [a, b] :=
  uIcc_subset_uIcc left_mem_uIcc h
#align finset.uIcc_subset_uIcc_left Finset.uIcc_subset_uIcc_left
-/

end Lattice

section DistribLattice

variable [DistribLattice α] [LocallyFiniteOrder α] {a a₁ a₂ b b₁ b₂ c x : α}

#print Finset.eq_of_mem_uIcc_of_mem_uIcc /-
theorem eq_of_mem_uIcc_of_mem_uIcc : a ∈ [b, c] → b ∈ [a, c] → a = b :=
  by
  simp_rw [mem_uIcc]
  exact Set.eq_of_mem_uIcc_of_mem_uIcc
#align finset.eq_of_mem_uIcc_of_mem_uIcc Finset.eq_of_mem_uIcc_of_mem_uIcc
-/

#print Finset.eq_of_mem_uIcc_of_mem_uIcc' /-
theorem eq_of_mem_uIcc_of_mem_uIcc' : b ∈ [a, c] → c ∈ [a, b] → b = c :=
  by
  simp_rw [mem_uIcc]
  exact Set.eq_of_mem_uIcc_of_mem_uIcc'
#align finset.eq_of_mem_uIcc_of_mem_uIcc' Finset.eq_of_mem_uIcc_of_mem_uIcc'
-/

#print Finset.uIcc_injective_right /-
theorem uIcc_injective_right (a : α) : Injective fun b => [b, a] := fun b c h =>
  by
  rw [ext_iff] at h
  exact eq_of_mem_uIcc_of_mem_uIcc ((h _).1 left_mem_uIcc) ((h _).2 left_mem_uIcc)
#align finset.uIcc_injective_right Finset.uIcc_injective_right
-/

#print Finset.uIcc_injective_left /-
theorem uIcc_injective_left (a : α) : Injective (uIcc a) := by
  simpa only [uIcc_comm] using uIcc_injective_right a
#align finset.uIcc_injective_left Finset.uIcc_injective_left
-/

end DistribLattice

section LinearOrder

variable [LinearOrder α] [LocallyFiniteOrder α] {a a₁ a₂ b b₁ b₂ c x : α}

/- warning: finset.Icc_min_max -> Finset.Icc_min_max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))] {a : α} {b : α}, Eq.{succ u1} (Finset.{u1} α) (Finset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 (LinearOrder.min.{u1} α _inst_1 a b) (LinearOrder.max.{u1} α _inst_1 a b)) (Finset.uIcc.{u1} α (LinearOrder.toLattice.{u1} α _inst_1) _inst_2 a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))] {a : α} {b : α}, Eq.{succ u1} (Finset.{u1} α) (Finset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) a b) (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) a b)) (Finset.uIcc.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)) _inst_2 a b)
Case conversion may be inaccurate. Consider using '#align finset.Icc_min_max Finset.Icc_min_maxₓ'. -/
theorem Icc_min_max : Icc (min a b) (max a b) = [a, b] :=
  rfl
#align finset.Icc_min_max Finset.Icc_min_max

#print Finset.uIcc_of_not_le /-
theorem uIcc_of_not_le (h : ¬a ≤ b) : [a, b] = Icc b a :=
  uIcc_of_ge <| le_of_not_ge h
#align finset.uIcc_of_not_le Finset.uIcc_of_not_le
-/

#print Finset.uIcc_of_not_ge /-
theorem uIcc_of_not_ge (h : ¬b ≤ a) : [a, b] = Icc a b :=
  uIcc_of_le <| le_of_not_ge h
#align finset.uIcc_of_not_ge Finset.uIcc_of_not_ge
-/

/- warning: finset.uIcc_eq_union -> Finset.uIcc_eq_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))] {a : α} {b : α}, Eq.{succ u1} (Finset.{u1} α) (Finset.uIcc.{u1} α (LinearOrder.toLattice.{u1} α _inst_1) _inst_2 a b) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => Eq.decidable.{u1} α _inst_1 a b)) (Finset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 a b) (Finset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))] {a : α} {b : α}, Eq.{succ u1} (Finset.{u1} α) (Finset.uIcc.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)) _inst_2 a b) (Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => instDecidableEq.{u1} α _inst_1 a b)) (Finset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 a b) (Finset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 b a))
Case conversion may be inaccurate. Consider using '#align finset.uIcc_eq_union Finset.uIcc_eq_unionₓ'. -/
theorem uIcc_eq_union : [a, b] = Icc a b ∪ Icc b a :=
  coe_injective <| by
    push_cast
    exact Set.uIcc_eq_union
#align finset.uIcc_eq_union Finset.uIcc_eq_union

#print Finset.mem_uIcc' /-
theorem mem_uIcc' : a ∈ [b, c] ↔ b ≤ a ∧ a ≤ c ∨ c ≤ a ∧ a ≤ b := by simp [uIcc_eq_union]
#align finset.mem_uIcc' Finset.mem_uIcc'
-/

#print Finset.not_mem_uIcc_of_lt /-
theorem not_mem_uIcc_of_lt : c < a → c < b → c ∉ [a, b] :=
  by
  rw [mem_uIcc]
  exact Set.not_mem_uIcc_of_lt
#align finset.not_mem_uIcc_of_lt Finset.not_mem_uIcc_of_lt
-/

#print Finset.not_mem_uIcc_of_gt /-
theorem not_mem_uIcc_of_gt : a < c → b < c → c ∉ [a, b] :=
  by
  rw [mem_uIcc]
  exact Set.not_mem_uIcc_of_gt
#align finset.not_mem_uIcc_of_gt Finset.not_mem_uIcc_of_gt
-/

/- warning: finset.uIcc_subset_uIcc_iff_le -> Finset.uIcc_subset_uIcc_iff_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, Iff (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (Finset.uIcc.{u1} α (LinearOrder.toLattice.{u1} α _inst_1) _inst_2 a₁ b₁) (Finset.uIcc.{u1} α (LinearOrder.toLattice.{u1} α _inst_1) _inst_2 a₂ b₂)) (And (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (LinearOrder.min.{u1} α _inst_1 a₂ b₂) (LinearOrder.min.{u1} α _inst_1 a₁ b₁)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (LinearOrder.max.{u1} α _inst_1 a₁ b₁) (LinearOrder.max.{u1} α _inst_1 a₂ b₂)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, Iff (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) (Finset.uIcc.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)) _inst_2 a₁ b₁) (Finset.uIcc.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)) _inst_2 a₂ b₂)) (And (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) a₂ b₂) (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) a₁ b₁)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) a₁ b₁) (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) a₂ b₂)))
Case conversion may be inaccurate. Consider using '#align finset.uIcc_subset_uIcc_iff_le Finset.uIcc_subset_uIcc_iff_leₓ'. -/
theorem uIcc_subset_uIcc_iff_le :
    [a₁, b₁] ⊆ [a₂, b₂] ↔ min a₂ b₂ ≤ min a₁ b₁ ∧ max a₁ b₁ ≤ max a₂ b₂ :=
  uIcc_subset_uIcc_iff_le'
#align finset.uIcc_subset_uIcc_iff_le Finset.uIcc_subset_uIcc_iff_le

/- warning: finset.uIcc_subset_uIcc_union_uIcc -> Finset.uIcc_subset_uIcc_union_uIcc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))] {a : α} {b : α} {c : α}, HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (Finset.uIcc.{u1} α (LinearOrder.toLattice.{u1} α _inst_1) _inst_2 a c) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => Eq.decidable.{u1} α _inst_1 a b)) (Finset.uIcc.{u1} α (LinearOrder.toLattice.{u1} α _inst_1) _inst_2 a b) (Finset.uIcc.{u1} α (LinearOrder.toLattice.{u1} α _inst_1) _inst_2 b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))] {a : α} {b : α} {c : α}, HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) (Finset.uIcc.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)) _inst_2 a c) (Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => instDecidableEq.{u1} α _inst_1 a b)) (Finset.uIcc.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)) _inst_2 a b) (Finset.uIcc.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)) _inst_2 b c))
Case conversion may be inaccurate. Consider using '#align finset.uIcc_subset_uIcc_union_uIcc Finset.uIcc_subset_uIcc_union_uIccₓ'. -/
/-- A sort of triangle inequality. -/
theorem uIcc_subset_uIcc_union_uIcc : [a, c] ⊆ [a, b] ∪ [b, c] :=
  coe_subset.1 <| by
    push_cast
    exact Set.uIcc_subset_uIcc_union_uIcc
#align finset.uIcc_subset_uIcc_union_uIcc Finset.uIcc_subset_uIcc_union_uIcc

end LinearOrder

section OrderedCancelAddCommMonoid

variable [OrderedCancelAddCommMonoid α] [ExistsAddOfLE α] [LocallyFiniteOrder α]

/- warning: finset.map_add_left_Icc -> Finset.map_add_left_Icc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (Finset.map.{u1, u1} α α (addLeftEmbedding.{u1} α (AddLeftCancelMonoid.toAddLeftCancelSemigroup.{u1} α (AddCancelCommMonoid.toAddLeftCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))) c) (Finset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Finset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c a) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (Finset.map.{u1, u1} α α (addLeftEmbedding.{u1} α (AddLeftCancelMonoid.toAddLeftCancelSemigroup.{u1} α (AddCancelCommMonoid.toAddLeftCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))) c) (Finset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Finset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c a) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c b))
Case conversion may be inaccurate. Consider using '#align finset.map_add_left_Icc Finset.map_add_left_Iccₓ'. -/
@[simp]
theorem map_add_left_Icc (a b c : α) : (Icc a b).map (addLeftEmbedding c) = Icc (c + a) (c + b) :=
  by
  rw [← coe_inj, coe_map, coe_Icc, coe_Icc]
  exact Set.image_const_add_Icc _ _ _
#align finset.map_add_left_Icc Finset.map_add_left_Icc

/- warning: finset.map_add_right_Icc -> Finset.map_add_right_Icc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (Finset.map.{u1, u1} α α (addRightEmbedding.{u1} α (AddRightCancelMonoid.toAddRightCancelSemigroup.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))) c) (Finset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Finset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (Finset.map.{u1, u1} α α (addRightEmbedding.{u1} α (AddRightCancelMonoid.toAddRightCancelSemigroup.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))) c) (Finset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Finset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) b c))
Case conversion may be inaccurate. Consider using '#align finset.map_add_right_Icc Finset.map_add_right_Iccₓ'. -/
@[simp]
theorem map_add_right_Icc (a b c : α) : (Icc a b).map (addRightEmbedding c) = Icc (a + c) (b + c) :=
  by
  rw [← coe_inj, coe_map, coe_Icc, coe_Icc]
  exact Set.image_add_const_Icc _ _ _
#align finset.map_add_right_Icc Finset.map_add_right_Icc

/- warning: finset.map_add_left_Ico -> Finset.map_add_left_Ico is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (Finset.map.{u1, u1} α α (addLeftEmbedding.{u1} α (AddLeftCancelMonoid.toAddLeftCancelSemigroup.{u1} α (AddCancelCommMonoid.toAddLeftCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))) c) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c a) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (Finset.map.{u1, u1} α α (addLeftEmbedding.{u1} α (AddLeftCancelMonoid.toAddLeftCancelSemigroup.{u1} α (AddCancelCommMonoid.toAddLeftCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))) c) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c a) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c b))
Case conversion may be inaccurate. Consider using '#align finset.map_add_left_Ico Finset.map_add_left_Icoₓ'. -/
@[simp]
theorem map_add_left_Ico (a b c : α) : (Ico a b).map (addLeftEmbedding c) = Ico (c + a) (c + b) :=
  by
  rw [← coe_inj, coe_map, coe_Ico, coe_Ico]
  exact Set.image_const_add_Ico _ _ _
#align finset.map_add_left_Ico Finset.map_add_left_Ico

/- warning: finset.map_add_right_Ico -> Finset.map_add_right_Ico is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (Finset.map.{u1, u1} α α (addRightEmbedding.{u1} α (AddRightCancelMonoid.toAddRightCancelSemigroup.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))) c) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (Finset.map.{u1, u1} α α (addRightEmbedding.{u1} α (AddRightCancelMonoid.toAddRightCancelSemigroup.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))) c) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) b c))
Case conversion may be inaccurate. Consider using '#align finset.map_add_right_Ico Finset.map_add_right_Icoₓ'. -/
@[simp]
theorem map_add_right_Ico (a b c : α) : (Ico a b).map (addRightEmbedding c) = Ico (a + c) (b + c) :=
  by
  rw [← coe_inj, coe_map, coe_Ico, coe_Ico]
  exact Set.image_add_const_Ico _ _ _
#align finset.map_add_right_Ico Finset.map_add_right_Ico

/- warning: finset.map_add_left_Ioc -> Finset.map_add_left_Ioc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (Finset.map.{u1, u1} α α (addLeftEmbedding.{u1} α (AddLeftCancelMonoid.toAddLeftCancelSemigroup.{u1} α (AddCancelCommMonoid.toAddLeftCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))) c) (Finset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Finset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c a) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (Finset.map.{u1, u1} α α (addLeftEmbedding.{u1} α (AddLeftCancelMonoid.toAddLeftCancelSemigroup.{u1} α (AddCancelCommMonoid.toAddLeftCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))) c) (Finset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Finset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c a) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c b))
Case conversion may be inaccurate. Consider using '#align finset.map_add_left_Ioc Finset.map_add_left_Iocₓ'. -/
@[simp]
theorem map_add_left_Ioc (a b c : α) : (Ioc a b).map (addLeftEmbedding c) = Ioc (c + a) (c + b) :=
  by
  rw [← coe_inj, coe_map, coe_Ioc, coe_Ioc]
  exact Set.image_const_add_Ioc _ _ _
#align finset.map_add_left_Ioc Finset.map_add_left_Ioc

/- warning: finset.map_add_right_Ioc -> Finset.map_add_right_Ioc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (Finset.map.{u1, u1} α α (addRightEmbedding.{u1} α (AddRightCancelMonoid.toAddRightCancelSemigroup.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))) c) (Finset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Finset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (Finset.map.{u1, u1} α α (addRightEmbedding.{u1} α (AddRightCancelMonoid.toAddRightCancelSemigroup.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))) c) (Finset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Finset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) b c))
Case conversion may be inaccurate. Consider using '#align finset.map_add_right_Ioc Finset.map_add_right_Iocₓ'. -/
@[simp]
theorem map_add_right_Ioc (a b c : α) : (Ioc a b).map (addRightEmbedding c) = Ioc (a + c) (b + c) :=
  by
  rw [← coe_inj, coe_map, coe_Ioc, coe_Ioc]
  exact Set.image_add_const_Ioc _ _ _
#align finset.map_add_right_Ioc Finset.map_add_right_Ioc

/- warning: finset.map_add_left_Ioo -> Finset.map_add_left_Ioo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (Finset.map.{u1, u1} α α (addLeftEmbedding.{u1} α (AddLeftCancelMonoid.toAddLeftCancelSemigroup.{u1} α (AddCancelCommMonoid.toAddLeftCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))) c) (Finset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Finset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c a) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (Finset.map.{u1, u1} α α (addLeftEmbedding.{u1} α (AddLeftCancelMonoid.toAddLeftCancelSemigroup.{u1} α (AddCancelCommMonoid.toAddLeftCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))) c) (Finset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Finset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c a) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c b))
Case conversion may be inaccurate. Consider using '#align finset.map_add_left_Ioo Finset.map_add_left_Iooₓ'. -/
@[simp]
theorem map_add_left_Ioo (a b c : α) : (Ioo a b).map (addLeftEmbedding c) = Ioo (c + a) (c + b) :=
  by
  rw [← coe_inj, coe_map, coe_Ioo, coe_Ioo]
  exact Set.image_const_add_Ioo _ _ _
#align finset.map_add_left_Ioo Finset.map_add_left_Ioo

/- warning: finset.map_add_right_Ioo -> Finset.map_add_right_Ioo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (Finset.map.{u1, u1} α α (addRightEmbedding.{u1} α (AddRightCancelMonoid.toAddRightCancelSemigroup.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))) c) (Finset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Finset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (Finset.map.{u1, u1} α α (addRightEmbedding.{u1} α (AddRightCancelMonoid.toAddRightCancelSemigroup.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))) c) (Finset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Finset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) b c))
Case conversion may be inaccurate. Consider using '#align finset.map_add_right_Ioo Finset.map_add_right_Iooₓ'. -/
@[simp]
theorem map_add_right_Ioo (a b c : α) : (Ioo a b).map (addRightEmbedding c) = Ioo (a + c) (b + c) :=
  by
  rw [← coe_inj, coe_map, coe_Ioo, coe_Ioo]
  exact Set.image_add_const_Ioo _ _ _
#align finset.map_add_right_Ioo Finset.map_add_right_Ioo

variable [DecidableEq α]

/- warning: finset.image_add_left_Icc -> Finset.image_add_left_Icc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] [_inst_4 : DecidableEq.{succ u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_4 a b) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c) (Finset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Finset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c a) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] [_inst_4 : DecidableEq.{succ u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_4 a b) ((fun (x._@.Mathlib.Data.Finset.LocallyFinite._hyg.10884 : α) (x._@.Mathlib.Data.Finset.LocallyFinite._hyg.10886 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) x._@.Mathlib.Data.Finset.LocallyFinite._hyg.10884 x._@.Mathlib.Data.Finset.LocallyFinite._hyg.10886) c) (Finset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Finset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c a) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c b))
Case conversion may be inaccurate. Consider using '#align finset.image_add_left_Icc Finset.image_add_left_Iccₓ'. -/
@[simp]
theorem image_add_left_Icc (a b c : α) : (Icc a b).image ((· + ·) c) = Icc (c + a) (c + b) :=
  by
  rw [← map_add_left_Icc, map_eq_image]
  rfl
#align finset.image_add_left_Icc Finset.image_add_left_Icc

/- warning: finset.image_add_left_Ico -> Finset.image_add_left_Ico is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] [_inst_4 : DecidableEq.{succ u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_4 a b) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c a) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] [_inst_4 : DecidableEq.{succ u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_4 a b) ((fun (x._@.Mathlib.Data.Finset.LocallyFinite._hyg.10985 : α) (x._@.Mathlib.Data.Finset.LocallyFinite._hyg.10987 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) x._@.Mathlib.Data.Finset.LocallyFinite._hyg.10985 x._@.Mathlib.Data.Finset.LocallyFinite._hyg.10987) c) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c a) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c b))
Case conversion may be inaccurate. Consider using '#align finset.image_add_left_Ico Finset.image_add_left_Icoₓ'. -/
@[simp]
theorem image_add_left_Ico (a b c : α) : (Ico a b).image ((· + ·) c) = Ico (c + a) (c + b) :=
  by
  rw [← map_add_left_Ico, map_eq_image]
  rfl
#align finset.image_add_left_Ico Finset.image_add_left_Ico

/- warning: finset.image_add_left_Ioc -> Finset.image_add_left_Ioc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] [_inst_4 : DecidableEq.{succ u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_4 a b) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c) (Finset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Finset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c a) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] [_inst_4 : DecidableEq.{succ u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_4 a b) ((fun (x._@.Mathlib.Data.Finset.LocallyFinite._hyg.11086 : α) (x._@.Mathlib.Data.Finset.LocallyFinite._hyg.11088 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) x._@.Mathlib.Data.Finset.LocallyFinite._hyg.11086 x._@.Mathlib.Data.Finset.LocallyFinite._hyg.11088) c) (Finset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Finset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c a) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c b))
Case conversion may be inaccurate. Consider using '#align finset.image_add_left_Ioc Finset.image_add_left_Iocₓ'. -/
@[simp]
theorem image_add_left_Ioc (a b c : α) : (Ioc a b).image ((· + ·) c) = Ioc (c + a) (c + b) :=
  by
  rw [← map_add_left_Ioc, map_eq_image]
  rfl
#align finset.image_add_left_Ioc Finset.image_add_left_Ioc

/- warning: finset.image_add_left_Ioo -> Finset.image_add_left_Ioo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] [_inst_4 : DecidableEq.{succ u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_4 a b) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c) (Finset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Finset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c a) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] [_inst_4 : DecidableEq.{succ u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_4 a b) ((fun (x._@.Mathlib.Data.Finset.LocallyFinite._hyg.11187 : α) (x._@.Mathlib.Data.Finset.LocallyFinite._hyg.11189 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) x._@.Mathlib.Data.Finset.LocallyFinite._hyg.11187 x._@.Mathlib.Data.Finset.LocallyFinite._hyg.11189) c) (Finset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Finset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c a) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c b))
Case conversion may be inaccurate. Consider using '#align finset.image_add_left_Ioo Finset.image_add_left_Iooₓ'. -/
@[simp]
theorem image_add_left_Ioo (a b c : α) : (Ioo a b).image ((· + ·) c) = Ioo (c + a) (c + b) :=
  by
  rw [← map_add_left_Ioo, map_eq_image]
  rfl
#align finset.image_add_left_Ioo Finset.image_add_left_Ioo

/- warning: finset.image_add_right_Icc -> Finset.image_add_right_Icc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] [_inst_4 : DecidableEq.{succ u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_4 a b) (fun (_x : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) _x c) (Finset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Finset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] [_inst_4 : DecidableEq.{succ u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_4 a b) (fun (_x : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) _x c) (Finset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Finset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) b c))
Case conversion may be inaccurate. Consider using '#align finset.image_add_right_Icc Finset.image_add_right_Iccₓ'. -/
@[simp]
theorem image_add_right_Icc (a b c : α) : (Icc a b).image (· + c) = Icc (a + c) (b + c) :=
  by
  rw [← map_add_right_Icc, map_eq_image]
  rfl
#align finset.image_add_right_Icc Finset.image_add_right_Icc

/- warning: finset.image_add_right_Ico -> Finset.image_add_right_Ico is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] [_inst_4 : DecidableEq.{succ u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_4 a b) (fun (_x : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) _x c) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] [_inst_4 : DecidableEq.{succ u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_4 a b) (fun (_x : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) _x c) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) b c))
Case conversion may be inaccurate. Consider using '#align finset.image_add_right_Ico Finset.image_add_right_Icoₓ'. -/
theorem image_add_right_Ico (a b c : α) : (Ico a b).image (· + c) = Ico (a + c) (b + c) :=
  by
  rw [← map_add_right_Ico, map_eq_image]
  rfl
#align finset.image_add_right_Ico Finset.image_add_right_Ico

/- warning: finset.image_add_right_Ioc -> Finset.image_add_right_Ioc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] [_inst_4 : DecidableEq.{succ u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_4 a b) (fun (_x : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) _x c) (Finset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Finset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] [_inst_4 : DecidableEq.{succ u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_4 a b) (fun (_x : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) _x c) (Finset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Finset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) b c))
Case conversion may be inaccurate. Consider using '#align finset.image_add_right_Ioc Finset.image_add_right_Iocₓ'. -/
theorem image_add_right_Ioc (a b c : α) : (Ioc a b).image (· + c) = Ioc (a + c) (b + c) :=
  by
  rw [← map_add_right_Ioc, map_eq_image]
  rfl
#align finset.image_add_right_Ioc Finset.image_add_right_Ioc

/- warning: finset.image_add_right_Ioo -> Finset.image_add_right_Ioo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] [_inst_4 : DecidableEq.{succ u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_4 a b) (fun (_x : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) _x c) (Finset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Finset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] [_inst_4 : DecidableEq.{succ u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} (Finset.{u1} α) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_4 a b) (fun (_x : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) _x c) (Finset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Finset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) b c))
Case conversion may be inaccurate. Consider using '#align finset.image_add_right_Ioo Finset.image_add_right_Iooₓ'. -/
theorem image_add_right_Ioo (a b c : α) : (Ioo a b).image (· + c) = Ioo (a + c) (b + c) :=
  by
  rw [← map_add_right_Ioo, map_eq_image]
  rfl
#align finset.image_add_right_Ioo Finset.image_add_right_Ioo

end OrderedCancelAddCommMonoid

/- warning: finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag -> Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : LinearOrder.{u1} ι] [_inst_3 : LocallyFiniteOrderTop.{u1} ι (PartialOrder.toPreorder.{u1} ι (SemilatticeInf.toPartialOrder.{u1} ι (Lattice.toSemilatticeInf.{u1} ι (LinearOrder.toLattice.{u1} ι _inst_2))))] [_inst_4 : LocallyFiniteOrderBot.{u1} ι (PartialOrder.toPreorder.{u1} ι (SemilatticeInf.toPartialOrder.{u1} ι (Lattice.toSemilatticeInf.{u1} ι (LinearOrder.toLattice.{u1} ι _inst_2))))] [_inst_5 : CommMonoid.{u2} α] (f : ι -> ι -> α), Eq.{succ u2} α (Finset.prod.{u2, u1} α ι _inst_5 (Finset.univ.{u1} ι _inst_1) (fun (i : ι) => Finset.prod.{u2, u1} α ι _inst_5 (Finset.Ioi.{u1} ι (PartialOrder.toPreorder.{u1} ι (SemilatticeInf.toPartialOrder.{u1} ι (Lattice.toSemilatticeInf.{u1} ι (LinearOrder.toLattice.{u1} ι _inst_2)))) _inst_3 i) (fun (j : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_5)))) (f j i) (f i j)))) (Finset.prod.{u2, u1} α ι _inst_5 (Finset.univ.{u1} ι _inst_1) (fun (i : ι) => Finset.prod.{u2, u1} α ι _inst_5 (HasCompl.compl.{u1} (Finset.{u1} ι) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} ι) (Finset.booleanAlgebra.{u1} ι _inst_1 (fun (a : ι) (b : ι) => Eq.decidable.{u1} ι _inst_2 a b))) (Singleton.singleton.{u1, u1} ι (Finset.{u1} ι) (Finset.hasSingleton.{u1} ι) i)) (fun (j : ι) => f j i)))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} ι] [_inst_2 : LinearOrder.{u2} ι] [_inst_3 : LocallyFiniteOrderTop.{u2} ι (PartialOrder.toPreorder.{u2} ι (SemilatticeInf.toPartialOrder.{u2} ι (Lattice.toSemilatticeInf.{u2} ι (DistribLattice.toLattice.{u2} ι (instDistribLattice.{u2} ι _inst_2)))))] [_inst_4 : LocallyFiniteOrderBot.{u2} ι (PartialOrder.toPreorder.{u2} ι (SemilatticeInf.toPartialOrder.{u2} ι (Lattice.toSemilatticeInf.{u2} ι (DistribLattice.toLattice.{u2} ι (instDistribLattice.{u2} ι _inst_2)))))] [_inst_5 : CommMonoid.{u1} α] (f : ι -> ι -> α), Eq.{succ u1} α (Finset.prod.{u1, u2} α ι _inst_5 (Finset.univ.{u2} ι _inst_1) (fun (i : ι) => Finset.prod.{u1, u2} α ι _inst_5 (Finset.Ioi.{u2} ι (PartialOrder.toPreorder.{u2} ι (SemilatticeInf.toPartialOrder.{u2} ι (Lattice.toSemilatticeInf.{u2} ι (DistribLattice.toLattice.{u2} ι (instDistribLattice.{u2} ι _inst_2))))) _inst_3 i) (fun (j : ι) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_5)))) (f j i) (f i j)))) (Finset.prod.{u1, u2} α ι _inst_5 (Finset.univ.{u2} ι _inst_1) (fun (i : ι) => Finset.prod.{u1, u2} α ι _inst_5 (HasCompl.compl.{u2} (Finset.{u2} ι) (BooleanAlgebra.toHasCompl.{u2} (Finset.{u2} ι) (Finset.instBooleanAlgebraFinset.{u2} ι _inst_1 (fun (a : ι) (b : ι) => instDecidableEq.{u2} ι _inst_2 a b))) (Singleton.singleton.{u2, u2} ι (Finset.{u2} ι) (Finset.instSingletonFinset.{u2} ι) i)) (fun (j : ι) => f j i)))
Case conversion may be inaccurate. Consider using '#align finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diagₓ'. -/
@[to_additive]
theorem prod_prod_Ioi_mul_eq_prod_prod_off_diag [Fintype ι] [LinearOrder ι]
    [LocallyFiniteOrderTop ι] [LocallyFiniteOrderBot ι] [CommMonoid α] (f : ι → ι → α) :
    (∏ i, ∏ j in Ioi i, f j i * f i j) = ∏ i, ∏ j in {i}ᶜ, f j i :=
  by
  simp_rw [← Ioi_disj_union_Iio, prod_disj_union, prod_mul_distrib]
  congr 1
  rw [prod_sigma', prod_sigma']
  refine' prod_bij' (fun i hi => ⟨i.2, i.1⟩) _ _ (fun i hi => ⟨i.2, i.1⟩) _ _ _ <;> simp
#align finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag
#align finset.sum_sum_Ioi_add_eq_sum_sum_off_diag Finset.sum_sum_Ioi_add_eq_sum_sum_off_diag

end Finset

