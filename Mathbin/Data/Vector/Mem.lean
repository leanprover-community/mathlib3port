/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Data.Vector.Basic

#align_import data.vector.mem from "leanprover-community/mathlib"@"327c3c0d9232d80e250dc8f65e7835b82b266ea5"

/-!
# Theorems about membership of elements in vectors

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains theorems for membership in a `v.to_list` for a vector `v`.
Having the length available in the type allows some of the lemmas to be
  simpler and more general than the original version for lists.
In particular we can avoid some assumptions about types being `inhabited`,
  and make more general statements about `head` and `tail`.
-/


namespace Mathlib.Vector

variable {α β : Type _} {n : ℕ} (a a' : α)

#print Mathlib.Vector.get_mem /-
@[simp]
theorem Mathlib.Vector.get_mem (i : Fin n) (v : Mathlib.Vector α n) : v.get? i ∈ v.toList := by
  rw [nth_eq_nth_le]; exact List.nthLe_mem _ _ _
#align vector.nth_mem Mathlib.Vector.get_mem
-/

#print Mathlib.Vector.mem_iff_get /-
theorem Mathlib.Vector.mem_iff_get (v : Mathlib.Vector α n) : a ∈ v.toList ↔ ∃ i, v.get? i = a := by
  simp only [List.mem_iff_nthLe, Fin.exists_iff, Mathlib.Vector.get_eq_get] <;>
    exact
      ⟨fun ⟨i, hi, h⟩ => ⟨i, by rwa [to_list_length] at hi, h⟩, fun ⟨i, hi, h⟩ =>
        ⟨i, by rwa [to_list_length], h⟩⟩
#align vector.mem_iff_nth Mathlib.Vector.mem_iff_get
-/

#print Mathlib.Vector.not_mem_nil /-
theorem Mathlib.Vector.not_mem_nil : a ∉ (Mathlib.Vector.nil : Mathlib.Vector α 0).toList :=
  id
#align vector.not_mem_nil Mathlib.Vector.not_mem_nil
-/

#print Mathlib.Vector.not_mem_zero /-
theorem Mathlib.Vector.not_mem_zero (v : Mathlib.Vector α 0) : a ∉ v.toList :=
  (Mathlib.Vector.eq_nil v).symm ▸ Mathlib.Vector.not_mem_nil a
#align vector.not_mem_zero Mathlib.Vector.not_mem_zero
-/

#print Mathlib.Vector.mem_cons_iff /-
theorem Mathlib.Vector.mem_cons_iff (v : Mathlib.Vector α n) :
    a' ∈ (a ::ᵥ v).toList ↔ a' = a ∨ a' ∈ v.toList := by
  rw [Mathlib.Vector.toList_cons, List.mem_cons]
#align vector.mem_cons_iff Mathlib.Vector.mem_cons_iff
-/

#print Mathlib.Vector.mem_succ_iff /-
theorem Mathlib.Vector.mem_succ_iff (v : Mathlib.Vector α (n + 1)) :
    a ∈ v.toList ↔ a = v.headI ∨ a ∈ v.tail.toList :=
  by
  obtain ⟨a', v', h⟩ := exists_eq_cons v
  simp_rw [h, Mathlib.Vector.mem_cons_iff, Mathlib.Vector.head_cons, Mathlib.Vector.tail_cons]
#align vector.mem_succ_iff Mathlib.Vector.mem_succ_iff
-/

#print Mathlib.Vector.mem_cons_self /-
theorem Mathlib.Vector.mem_cons_self (v : Mathlib.Vector α n) : a ∈ (a ::ᵥ v).toList :=
  (Mathlib.Vector.mem_iff_get a (a ::ᵥ v)).2 ⟨0, Mathlib.Vector.get_cons_zero a v⟩
#align vector.mem_cons_self Mathlib.Vector.mem_cons_self
-/

#print Mathlib.Vector.head_mem /-
@[simp]
theorem Mathlib.Vector.head_mem (v : Mathlib.Vector α (n + 1)) : v.headI ∈ v.toList :=
  (Mathlib.Vector.mem_iff_get v.headI v).2 ⟨0, Mathlib.Vector.get_zero v⟩
#align vector.head_mem Mathlib.Vector.head_mem
-/

#print Mathlib.Vector.mem_cons_of_mem /-
theorem Mathlib.Vector.mem_cons_of_mem (v : Mathlib.Vector α n) (ha' : a' ∈ v.toList) :
    a' ∈ (a ::ᵥ v).toList :=
  (Mathlib.Vector.mem_cons_iff a a' v).2 (Or.inr ha')
#align vector.mem_cons_of_mem Mathlib.Vector.mem_cons_of_mem
-/

#print Mathlib.Vector.mem_of_mem_tail /-
theorem Mathlib.Vector.mem_of_mem_tail (v : Mathlib.Vector α n) (ha : a ∈ v.tail.toList) :
    a ∈ v.toList := by
  induction' n with n hn
  · exact False.elim (Mathlib.Vector.not_mem_zero a v.tail ha)
  · exact (mem_succ_iff a v).2 (Or.inr ha)
#align vector.mem_of_mem_tail Mathlib.Vector.mem_of_mem_tail
-/

#print Mathlib.Vector.mem_map_iff /-
theorem Mathlib.Vector.mem_map_iff (b : β) (v : Mathlib.Vector α n) (f : α → β) :
    b ∈ (v.map f).toList ↔ ∃ a : α, a ∈ v.toList ∧ f a = b := by
  rw [Mathlib.Vector.toList_map, List.mem_map]
#align vector.mem_map_iff Mathlib.Vector.mem_map_iff
-/

#print Mathlib.Vector.not_mem_map_zero /-
theorem Mathlib.Vector.not_mem_map_zero (b : β) (v : Mathlib.Vector α 0) (f : α → β) :
    b ∉ (v.map f).toList := by
  simpa only [Mathlib.Vector.eq_nil v, Mathlib.Vector.map_nil, Mathlib.Vector.toList_nil] using
    List.not_mem_nil b
#align vector.not_mem_map_zero Mathlib.Vector.not_mem_map_zero
-/

#print Mathlib.Vector.mem_map_succ_iff /-
theorem Mathlib.Vector.mem_map_succ_iff (b : β) (v : Mathlib.Vector α (n + 1)) (f : α → β) :
    b ∈ (v.map f).toList ↔ f v.headI = b ∨ ∃ a : α, a ∈ v.tail.toList ∧ f a = b := by
  rw [mem_succ_iff, head_map, tail_map, mem_map_iff, @eq_comm _ b]
#align vector.mem_map_succ_iff Mathlib.Vector.mem_map_succ_iff
-/

end Mathlib.Vector

