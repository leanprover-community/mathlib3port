/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Data.Multiset.Nodup

#align_import data.multiset.dedup from "leanprover-community/mathlib"@"f2f413b9d4be3a02840d0663dace76e8fe3da053"

/-!
# Erasing duplicates in a multiset.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


namespace Multiset

open List

variable {α β : Type _} [DecidableEq α]

/-! ### dedup -/


#print Multiset.dedup /-
/-- `dedup s` removes duplicates from `s`, yielding a `nodup` multiset. -/
def dedup (s : Multiset α) : Multiset α :=
  Quot.liftOn s (fun l => (l.dedup : Multiset α)) fun s t p => Quot.sound p.dedup
#align multiset.dedup Multiset.dedup
-/

#print Multiset.coe_dedup /-
@[simp]
theorem coe_dedup (l : List α) : @dedup α _ l = l.dedup :=
  rfl
#align multiset.coe_dedup Multiset.coe_dedup
-/

#print Multiset.dedup_zero /-
@[simp]
theorem dedup_zero : @dedup α _ 0 = 0 :=
  rfl
#align multiset.dedup_zero Multiset.dedup_zero
-/

#print Multiset.mem_dedup /-
@[simp]
theorem mem_dedup {a : α} {s : Multiset α} : a ∈ dedup s ↔ a ∈ s :=
  Quot.inductionOn s fun l => mem_dedup
#align multiset.mem_dedup Multiset.mem_dedup
-/

#print Multiset.dedup_cons_of_mem /-
@[simp]
theorem dedup_cons_of_mem {a : α} {s : Multiset α} : a ∈ s → dedup (a ::ₘ s) = dedup s :=
  Quot.inductionOn s fun l m => @congr_arg _ _ _ _ coe <| dedup_cons_of_mem m
#align multiset.dedup_cons_of_mem Multiset.dedup_cons_of_mem
-/

#print Multiset.dedup_cons_of_not_mem /-
@[simp]
theorem dedup_cons_of_not_mem {a : α} {s : Multiset α} : a ∉ s → dedup (a ::ₘ s) = a ::ₘ dedup s :=
  Quot.inductionOn s fun l m => congr_arg coe <| dedup_cons_of_not_mem m
#align multiset.dedup_cons_of_not_mem Multiset.dedup_cons_of_not_mem
-/

#print Multiset.dedup_le /-
theorem dedup_le (s : Multiset α) : dedup s ≤ s :=
  Quot.inductionOn s fun l => (dedup_sublist _).Subperm
#align multiset.dedup_le Multiset.dedup_le
-/

#print Multiset.dedup_subset /-
theorem dedup_subset (s : Multiset α) : dedup s ⊆ s :=
  subset_of_le <| dedup_le _
#align multiset.dedup_subset Multiset.dedup_subset
-/

#print Multiset.subset_dedup /-
theorem subset_dedup (s : Multiset α) : s ⊆ dedup s := fun a => mem_dedup.2
#align multiset.subset_dedup Multiset.subset_dedup
-/

#print Multiset.dedup_subset' /-
@[simp]
theorem dedup_subset' {s t : Multiset α} : dedup s ⊆ t ↔ s ⊆ t :=
  ⟨Subset.trans (subset_dedup _), Subset.trans (dedup_subset _)⟩
#align multiset.dedup_subset' Multiset.dedup_subset'
-/

#print Multiset.subset_dedup' /-
@[simp]
theorem subset_dedup' {s t : Multiset α} : s ⊆ dedup t ↔ s ⊆ t :=
  ⟨fun h => Subset.trans h (dedup_subset _), fun h => Subset.trans h (subset_dedup _)⟩
#align multiset.subset_dedup' Multiset.subset_dedup'
-/

#print Multiset.nodup_dedup /-
@[simp]
theorem nodup_dedup (s : Multiset α) : Nodup (dedup s) :=
  Quot.inductionOn s nodup_dedup
#align multiset.nodup_dedup Multiset.nodup_dedup
-/

#print Multiset.dedup_eq_self /-
theorem dedup_eq_self {s : Multiset α} : dedup s = s ↔ Nodup s :=
  ⟨fun e => e ▸ nodup_dedup s, Quot.inductionOn s fun l h => congr_arg coe h.dedup⟩
#align multiset.dedup_eq_self Multiset.dedup_eq_self
-/

alias ⟨_, nodup.dedup⟩ := dedup_eq_self
#align multiset.nodup.dedup Multiset.Nodup.dedup

#print Multiset.count_dedup /-
theorem count_dedup (m : Multiset α) (a : α) : m.dedup.count a = if a ∈ m then 1 else 0 :=
  Quot.inductionOn m fun l => count_dedup _ _
#align multiset.count_dedup Multiset.count_dedup
-/

#print Multiset.dedup_idem /-
@[simp]
theorem dedup_idem {m : Multiset α} : m.dedup.dedup = m.dedup :=
  Quot.inductionOn m fun l => @congr_arg _ _ _ _ coe dedup_idem
#align multiset.dedup_idempotent Multiset.dedup_idem
-/

#print Multiset.dedup_bind_dedup /-
@[simp]
theorem dedup_bind_dedup [DecidableEq β] (m : Multiset α) (f : α → Multiset β) :
    (m.dedup.bind f).dedup = (m.bind f).dedup := by ext x;
  simp_rw [count_dedup, mem_bind, mem_dedup]
#align multiset.dedup_bind_dedup Multiset.dedup_bind_dedup
-/

#print Multiset.dedup_eq_zero /-
theorem dedup_eq_zero {s : Multiset α} : dedup s = 0 ↔ s = 0 :=
  ⟨fun h => eq_zero_of_subset_zero <| h ▸ subset_dedup _, fun h => h.symm ▸ dedup_zero⟩
#align multiset.dedup_eq_zero Multiset.dedup_eq_zero
-/

#print Multiset.dedup_singleton /-
@[simp]
theorem dedup_singleton {a : α} : dedup ({a} : Multiset α) = {a} :=
  (nodup_singleton _).dedup
#align multiset.dedup_singleton Multiset.dedup_singleton
-/

#print Multiset.le_dedup /-
theorem le_dedup {s t : Multiset α} : s ≤ dedup t ↔ s ≤ t ∧ Nodup s :=
  ⟨fun h => ⟨le_trans h (dedup_le _), nodup_of_le h (nodup_dedup _)⟩, fun ⟨l, d⟩ =>
    (le_iff_subset d).2 <| Subset.trans (subset_of_le l) (subset_dedup _)⟩
#align multiset.le_dedup Multiset.le_dedup
-/

#print Multiset.le_dedup_self /-
theorem le_dedup_self {s : Multiset α} : s ≤ dedup s ↔ Nodup s := by
  rw [le_dedup, and_iff_right le_rfl]
#align multiset.le_dedup_self Multiset.le_dedup_self
-/

#print Multiset.dedup_ext /-
theorem dedup_ext {s t : Multiset α} : dedup s = dedup t ↔ ∀ a, a ∈ s ↔ a ∈ t := by simp [nodup.ext]
#align multiset.dedup_ext Multiset.dedup_ext
-/

#print Multiset.dedup_map_dedup_eq /-
theorem dedup_map_dedup_eq [DecidableEq β] (f : α → β) (s : Multiset α) :
    dedup (map f (dedup s)) = dedup (map f s) := by simp [dedup_ext]
#align multiset.dedup_map_dedup_eq Multiset.dedup_map_dedup_eq
-/

#print Multiset.dedup_nsmul /-
@[simp]
theorem dedup_nsmul {s : Multiset α} {n : ℕ} (h0 : n ≠ 0) : (n • s).dedup = s.dedup :=
  by
  ext a
  by_cases h : a ∈ s <;> simp [h, h0]
#align multiset.dedup_nsmul Multiset.dedup_nsmul
-/

#print Multiset.Nodup.le_dedup_iff_le /-
theorem Nodup.le_dedup_iff_le {s t : Multiset α} (hno : s.Nodup) : s ≤ t.dedup ↔ s ≤ t := by
  simp [le_dedup, hno]
#align multiset.nodup.le_dedup_iff_le Multiset.Nodup.le_dedup_iff_le
-/

end Multiset

#print Multiset.Nodup.le_nsmul_iff_le /-
theorem Multiset.Nodup.le_nsmul_iff_le {α : Type _} {s t : Multiset α} {n : ℕ} (h : s.Nodup)
    (hn : n ≠ 0) : s ≤ n • t ↔ s ≤ t := by classical
#align multiset.nodup.le_nsmul_iff_le Multiset.Nodup.le_nsmul_iff_le
-/

