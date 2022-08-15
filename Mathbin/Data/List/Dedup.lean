/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.List.Nodup

/-!
# Erasure of duplicates in a list

This file proves basic results about `list.dedup` (definition in `data.list.defs`).
`dedup l` returns `l` without its duplicates. It keeps the earliest (that is, rightmost)
occurrence of each.

## Tags

duplicate, multiplicity, nodup, `nub`
-/


universe u

namespace List

variable {α : Type u} [DecidableEq α]

@[simp]
theorem dedup_nil : dedup [] = ([] : List α) :=
  rfl

theorem dedup_cons_of_mem' {a : α} {l : List α} (h : a ∈ dedup l) : dedup (a :: l) = dedup l :=
  pw_filter_cons_of_neg <| by
    simpa only [← forall_mem_ne] using h

theorem dedup_cons_of_not_mem' {a : α} {l : List α} (h : a ∉ dedup l) : dedup (a :: l) = a :: dedup l :=
  pw_filter_cons_of_pos <| by
    simpa only [← forall_mem_ne] using h

@[simp]
theorem mem_dedup {a : α} {l : List α} : a ∈ dedup l ↔ a ∈ l := by
  simpa only [← dedup, ← forall_mem_ne, ← not_not] using
    not_congr (@forall_mem_pw_filter α (· ≠ ·) _ (fun x y z xz => not_and_distrib.1 <| mt (And.ndrec Eq.trans) xz) a l)

@[simp]
theorem dedup_cons_of_mem {a : α} {l : List α} (h : a ∈ l) : dedup (a :: l) = dedup l :=
  dedup_cons_of_mem' <| mem_dedup.2 h

@[simp]
theorem dedup_cons_of_not_mem {a : α} {l : List α} (h : a ∉ l) : dedup (a :: l) = a :: dedup l :=
  dedup_cons_of_not_mem' <| mt mem_dedup.1 h

theorem dedup_sublist : ∀ l : List α, dedup l <+ l :=
  pw_filter_sublist

theorem dedup_subset : ∀ l : List α, dedup l ⊆ l :=
  pw_filter_subset

theorem subset_dedup (l : List α) : l ⊆ dedup l := fun a => mem_dedup.2

theorem nodup_dedup : ∀ l : List α, Nodupₓ (dedup l) :=
  pairwise_pw_filter

theorem dedup_eq_self {l : List α} : dedup l = l ↔ Nodupₓ l :=
  pw_filter_eq_self

protected theorem Nodupₓ.dedup {l : List α} (h : l.Nodup) : l.dedup = l :=
  List.dedup_eq_self.2 h

@[simp]
theorem dedup_idempotent {l : List α} : dedup (dedup l) = dedup l :=
  pw_filter_idempotent

theorem dedup_append (l₁ l₂ : List α) : dedup (l₁ ++ l₂) = l₁ ∪ dedup l₂ := by
  induction' l₁ with a l₁ IH
  · rfl
    
  rw [cons_union, ← IH]
  show dedup (a :: (l₁ ++ l₂)) = insert a (dedup (l₁ ++ l₂))
  by_cases' a ∈ dedup (l₁ ++ l₂) <;> [rw [dedup_cons_of_mem' h, insert_of_mem h],
    rw [dedup_cons_of_not_mem' h, insert_of_not_mem h]]

theorem repeat_dedup {x : α} : ∀ {k}, k ≠ 0 → (repeat x k).dedup = [x]
  | 0, h => (h rfl).elim
  | 1, _ => rfl
  | n + 2, _ => by
    rw [repeat_succ, dedup_cons_of_mem (mem_repeat.2 ⟨n.succ_ne_zero, rfl⟩), repeat_dedup n.succ_ne_zero]

theorem count_dedup (l : List α) (a : α) : l.dedup.count a = if a ∈ l then 1 else 0 := by
  simp_rw [count_eq_of_nodup <| nodup_dedup l, mem_dedup]

/-- Summing the count of `x` over a list filtered by some `p` is just `countp` applied to `p` -/
theorem sum_map_count_dedup_filter_eq_countp (p : α → Prop) [DecidablePred p] (l : List α) :
    ((l.dedup.filter p).map fun x => l.count x).Sum = l.countp p := by
  induction' l with a as h
  · simp
    
  · simp_rw [List.countp_cons, List.count_cons', List.sum_map_add]
    congr 1
    · refine' trans _ h
      by_cases' ha : a ∈ as
      · simp [← dedup_cons_of_mem ha]
        
      · simp only [← dedup_cons_of_not_mem ha, ← List.filterₓ]
        split_ifs with hp <;> simp [← List.map_cons, ← List.sum_cons, ← List.count_eq_zero.2 ha, ← zero_addₓ]
        
      
    · by_cases' hp : p a
      · refine'
          trans
            (sum_map_eq_nsmul_single a _ fun _ h _ => by
              simp [← h])
            _
        simp [← hp, ← count_dedup]
        
      · refine'
          trans (List.sum_eq_zero fun n hn => _)
            (by
              simp [← hp])
        obtain ⟨a', ha'⟩ := List.mem_mapₓ.1 hn
        simp only [← (fun h => hp (h ▸ (List.mem_filterₓ.1 ha'.1).2) : a' ≠ a), ← if_false] at ha'
        exact ha'.2.symm
        
      
    

theorem sum_map_count_dedup_eq_length (l : List α) : (l.dedup.map fun x => l.count x).Sum = l.length := by
  simpa using sum_map_count_dedup_filter_eq_countp (fun _ => True) l

end List

