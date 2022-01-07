import Mathbin.Data.List.Nodup

/-!
# Erasure of duplicates in a list

This file proves basic results about `list.erase_dup` (definition in `data.list.defs`).
`erase_dup l` returns `l` without its duplicates. It keeps the earliest (that is, rightmost)
occurrence of each.

## Tags

duplicate, multiplicity, nodup, `nub`
-/


universe u

namespace List

variable {α : Type u} [DecidableEq α]

@[simp]
theorem erase_dup_nil : erase_dup [] = ([] : List α) :=
  rfl

theorem erase_dup_cons_of_mem' {a : α} {l : List α} (h : a ∈ erase_dup l) : erase_dup (a :: l) = erase_dup l :=
  pw_filter_cons_of_neg $ by
    simpa only [forall_mem_ne] using h

theorem erase_dup_cons_of_not_mem' {a : α} {l : List α} (h : a ∉ erase_dup l) : erase_dup (a :: l) = a :: erase_dup l :=
  pw_filter_cons_of_pos $ by
    simpa only [forall_mem_ne] using h

@[simp]
theorem mem_erase_dup {a : α} {l : List α} : a ∈ erase_dup l ↔ a ∈ l := by
  simpa only [erase_dup, forall_mem_ne, not_not] using
    not_congr (@forall_mem_pw_filter α (· ≠ ·) _ (fun x y z xz => not_and_distrib.1 $ mt (And.ndrec Eq.trans) xz) a l)

@[simp]
theorem erase_dup_cons_of_mem {a : α} {l : List α} (h : a ∈ l) : erase_dup (a :: l) = erase_dup l :=
  erase_dup_cons_of_mem' $ mem_erase_dup.2 h

@[simp]
theorem erase_dup_cons_of_not_mem {a : α} {l : List α} (h : a ∉ l) : erase_dup (a :: l) = a :: erase_dup l :=
  erase_dup_cons_of_not_mem' $ mt mem_erase_dup.1 h

theorem erase_dup_sublist : ∀ l : List α, erase_dup l <+ l :=
  pw_filter_sublist

theorem erase_dup_subset : ∀ l : List α, erase_dup l ⊆ l :=
  pw_filter_subset

theorem subset_erase_dup (l : List α) : l ⊆ erase_dup l := fun a => mem_erase_dup.2

theorem nodup_erase_dup : ∀ l : List α, nodup (erase_dup l) :=
  pairwise_pw_filter

theorem erase_dup_eq_self {l : List α} : erase_dup l = l ↔ nodup l :=
  pw_filter_eq_self

protected theorem nodup.erase_dup {l : List α} (h : l.nodup) : l.erase_dup = l :=
  List.erase_dup_eq_self.2 h

@[simp]
theorem erase_dup_idempotent {l : List α} : erase_dup (erase_dup l) = erase_dup l :=
  pw_filter_idempotent

theorem erase_dup_append (l₁ l₂ : List α) : erase_dup (l₁ ++ l₂) = l₁ ∪ erase_dup l₂ := by
  induction' l₁ with a l₁ IH
  · rfl
    
  rw [cons_union, ← IH]
  show erase_dup (a :: (l₁ ++ l₂)) = insert a (erase_dup (l₁ ++ l₂))
  by_cases' a ∈ erase_dup (l₁ ++ l₂) <;> [rw [erase_dup_cons_of_mem' h, insert_of_mem h],
    rw [erase_dup_cons_of_not_mem' h, insert_of_not_mem h]]

end List

