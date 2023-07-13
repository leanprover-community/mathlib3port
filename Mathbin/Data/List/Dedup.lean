/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.list.dedup
! leanprover-community/mathlib commit d9e96a3e3e0894e93e10aff5244f4c96655bac1c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Nodup

/-!
# Erasure of duplicates in a list

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves basic results about `list.dedup` (definition in `data.list.defs`).
`dedup l` returns `l` without its duplicates. It keeps the earliest (that is, rightmost)
occurrence of each.

## Tags

duplicate, multiplicity, nodup, `nub`
-/


universe u

namespace List

variable {α : Type u} [DecidableEq α]

#print List.dedup_nil /-
@[simp]
theorem dedup_nil : dedup [] = ([] : List α) :=
  rfl
#align list.dedup_nil List.dedup_nil
-/

#print List.dedup_cons_of_mem' /-
theorem dedup_cons_of_mem' {a : α} {l : List α} (h : a ∈ dedup l) : dedup (a :: l) = dedup l :=
  pwFilter_cons_of_neg <| by simpa only [forall_mem_ne] using h
#align list.dedup_cons_of_mem' List.dedup_cons_of_mem'
-/

#print List.dedup_cons_of_not_mem' /-
theorem dedup_cons_of_not_mem' {a : α} {l : List α} (h : a ∉ dedup l) :
    dedup (a :: l) = a :: dedup l :=
  pwFilter_cons_of_pos <| by simpa only [forall_mem_ne] using h
#align list.dedup_cons_of_not_mem' List.dedup_cons_of_not_mem'
-/

#print List.mem_dedup /-
@[simp]
theorem mem_dedup {a : α} {l : List α} : a ∈ dedup l ↔ a ∈ l := by
  simpa only [dedup, forall_mem_ne, Classical.not_not] using
    not_congr
      (@forall_mem_pw_filter α (· ≠ ·) _
        (fun x y z xz => not_and_or.1 <| mt (fun h => Eq.trans h.1 h.2) xz) a l)
#align list.mem_dedup List.mem_dedup
-/

#print List.dedup_cons_of_mem /-
@[simp]
theorem dedup_cons_of_mem {a : α} {l : List α} (h : a ∈ l) : dedup (a :: l) = dedup l :=
  dedup_cons_of_mem' <| mem_dedup.2 h
#align list.dedup_cons_of_mem List.dedup_cons_of_mem
-/

#print List.dedup_cons_of_not_mem /-
@[simp]
theorem dedup_cons_of_not_mem {a : α} {l : List α} (h : a ∉ l) : dedup (a :: l) = a :: dedup l :=
  dedup_cons_of_not_mem' <| mt mem_dedup.1 h
#align list.dedup_cons_of_not_mem List.dedup_cons_of_not_mem
-/

#print List.dedup_sublist /-
theorem dedup_sublist : ∀ l : List α, dedup l <+ l :=
  pwFilter_sublist
#align list.dedup_sublist List.dedup_sublist
-/

#print List.dedup_subset /-
theorem dedup_subset : ∀ l : List α, dedup l ⊆ l :=
  pwFilter_subset
#align list.dedup_subset List.dedup_subset
-/

#print List.subset_dedup /-
theorem subset_dedup (l : List α) : l ⊆ dedup l := fun a => mem_dedup.2
#align list.subset_dedup List.subset_dedup
-/

#print List.nodup_dedup /-
theorem nodup_dedup : ∀ l : List α, Nodup (dedup l) :=
  pairwise_pwFilter
#align list.nodup_dedup List.nodup_dedup
-/

theorem headI_dedup [Inhabited α] (l : List α) :
    l.dedup.headI = if l.headI ∈ l.tail then l.tail.dedup.headI else l.headI :=
  match l with
  | [] => rfl
  | a :: l => by by_cases ha : a ∈ l <;> simp [ha, List.dedup_cons_of_mem]
#align list.head_dedup List.headI_dedup

theorem tail_dedup [Inhabited α] (l : List α) :
    l.dedup.tail = if l.headI ∈ l.tail then l.tail.dedup.tail else l.tail.dedup :=
  match l with
  | [] => rfl
  | a :: l => by by_cases ha : a ∈ l <;> simp [ha, List.dedup_cons_of_mem]
#align list.tail_dedup List.tail_dedup

#print List.dedup_eq_self /-
theorem dedup_eq_self {l : List α} : dedup l = l ↔ Nodup l :=
  pwFilter_eq_self
#align list.dedup_eq_self List.dedup_eq_self
-/

theorem dedup_eq_cons (l : List α) (a : α) (l' : List α) :
    l.dedup = a :: l' ↔ a ∈ l ∧ a ∉ l' ∧ l.dedup.tail = l' :=
  by
  refine' ⟨fun h => _, fun h => _⟩
  · refine' ⟨mem_dedup.1 (h.symm ▸ mem_cons_self _ _), fun ha => _, by rw [h, tail_cons]⟩
    have : count a l.dedup ≤ 1 := nodup_iff_count_le_one.1 (nodup_dedup l) a
    rw [h, count_cons_self, add_le_iff_nonpos_left] at this 
    exact not_le_of_lt (count_pos.2 ha) this
  · have := @cons_head_tail α ⟨a⟩ _ (ne_nil_of_mem (mem_dedup.2 h.1))
    have hal : a ∈ l.dedup := mem_dedup.2 h.1
    rw [← this, mem_cons_iff, or_iff_not_imp_right] at hal 
    exact this ▸ h.2.2.symm ▸ cons_eq_cons.2 ⟨(hal (h.2.2.symm ▸ h.2.1)).symm, rfl⟩
#align list.dedup_eq_cons List.dedup_eq_cons

@[simp]
theorem dedup_eq_nil (l : List α) : l.dedup = [] ↔ l = [] :=
  by
  induction' l with a l hl
  · exact Iff.rfl
  · by_cases h : a ∈ l
    · simp only [List.dedup_cons_of_mem h, hl, List.ne_nil_of_mem h]
    · simp only [List.dedup_cons_of_not_mem h, List.cons_ne_nil]
#align list.dedup_eq_nil List.dedup_eq_nil

#print List.Nodup.dedup /-
protected theorem Nodup.dedup {l : List α} (h : l.Nodup) : l.dedup = l :=
  List.dedup_eq_self.2 h
#align list.nodup.dedup List.Nodup.dedup
-/

#print List.dedup_idempotent /-
@[simp]
theorem dedup_idempotent {l : List α} : dedup (dedup l) = dedup l :=
  pwFilter_idempotent
#align list.dedup_idempotent List.dedup_idempotent
-/

#print List.dedup_append /-
theorem dedup_append (l₁ l₂ : List α) : dedup (l₁ ++ l₂) = l₁ ∪ dedup l₂ :=
  by
  induction' l₁ with a l₁ IH; · rfl; rw [cons_union, ← IH]
  show dedup (a :: (l₁ ++ l₂)) = insert a (dedup (l₁ ++ l₂))
  by_cases a ∈ dedup (l₁ ++ l₂) <;> [rw [dedup_cons_of_mem' h, insert_of_mem h];
    rw [dedup_cons_of_not_mem' h, insert_of_not_mem h]]
#align list.dedup_append List.dedup_append
-/

#print List.replicate_dedup /-
theorem replicate_dedup {x : α} : ∀ {k}, k ≠ 0 → (replicate k x).dedup = [x]
  | 0, h => (h rfl).elim
  | 1, _ => rfl
  | n + 2, _ => by
    rw [replicate_succ, dedup_cons_of_mem (mem_replicate.2 ⟨n.succ_ne_zero, rfl⟩),
      replicate_dedup n.succ_ne_zero]
#align list.replicate_dedup List.replicate_dedup
-/

#print List.count_dedup /-
theorem count_dedup (l : List α) (a : α) : l.dedup.count a = if a ∈ l then 1 else 0 := by
  simp_rw [count_eq_of_nodup <| nodup_dedup l, mem_dedup]
#align list.count_dedup List.count_dedup
-/

#print List.sum_map_count_dedup_filter_eq_countp /-
/-- Summing the count of `x` over a list filtered by some `p` is just `countp` applied to `p` -/
theorem sum_map_count_dedup_filter_eq_countp (p : α → Prop) [DecidablePred p] (l : List α) :
    ((l.dedup.filterₓ p).map fun x => l.count x).Sum = l.countp p :=
  by
  induction' l with a as h
  · simp
  · simp_rw [List.countp_cons, List.count_cons', List.sum_map_add]
    congr 1
    · refine' trans _ h
      by_cases ha : a ∈ as
      · simp [dedup_cons_of_mem ha]
      · simp only [dedup_cons_of_not_mem ha, List.filter]
        split_ifs with hp <;> simp [List.map_cons, List.sum_cons, List.count_eq_zero.2 ha, zero_add]
    · by_cases hp : p a
      · refine' trans (sum_map_eq_nsmul_single a _ fun _ h _ => by simp [h]) _
        simp [hp, count_dedup]
      · refine' trans (List.sum_eq_zero fun n hn => _) (by simp [hp])
        obtain ⟨a', ha'⟩ := List.mem_map.1 hn
        simp only [(fun h => hp (h ▸ (List.mem_filter.1 ha'.1).2) : a' ≠ a), if_false] at ha' 
        exact ha'.2.symm
#align list.sum_map_count_dedup_filter_eq_countp List.sum_map_count_dedup_filter_eq_countp
-/

#print List.sum_map_count_dedup_eq_length /-
theorem sum_map_count_dedup_eq_length (l : List α) :
    (l.dedup.map fun x => l.count x).Sum = l.length := by
  simpa using sum_map_count_dedup_filter_eq_countp (fun _ => True) l
#align list.sum_map_count_dedup_eq_length List.sum_map_count_dedup_eq_length
-/

end List

