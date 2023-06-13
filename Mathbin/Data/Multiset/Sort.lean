/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.multiset.sort
! leanprover-community/mathlib commit 327c3c0d9232d80e250dc8f65e7835b82b266ea5
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Sort
import Mathbin.Data.Multiset.Basic

/-!
# Construct a sorted list from a multiset.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


namespace Multiset

open List

variable {α : Type _}

section Sort

variable (r : α → α → Prop) [DecidableRel r] [IsTrans α r] [IsAntisymm α r] [IsTotal α r]

#print Multiset.sort /-
/-- `sort s` constructs a sorted list from the multiset `s`.
  (Uses merge sort algorithm.) -/
def sort (s : Multiset α) : List α :=
  Quot.liftOn s (mergeSort r) fun a b h =>
    eq_of_perm_of_sorted ((perm_mergeSort _ _).trans <| h.trans (perm_mergeSort _ _).symm)
      (sorted_mergeSort r _) (sorted_mergeSort r _)
#align multiset.sort Multiset.sort
-/

#print Multiset.coe_sort /-
@[simp]
theorem coe_sort (l : List α) : sort r l = mergeSort r l :=
  rfl
#align multiset.coe_sort Multiset.coe_sort
-/

#print Multiset.sort_sorted /-
@[simp]
theorem sort_sorted (s : Multiset α) : Sorted r (sort r s) :=
  Quot.inductionOn s fun l => sorted_mergeSort r _
#align multiset.sort_sorted Multiset.sort_sorted
-/

#print Multiset.sort_eq /-
@[simp]
theorem sort_eq (s : Multiset α) : ↑(sort r s) = s :=
  Quot.inductionOn s fun l => Quot.sound <| perm_mergeSort _ _
#align multiset.sort_eq Multiset.sort_eq
-/

#print Multiset.mem_sort /-
@[simp]
theorem mem_sort {s : Multiset α} {a : α} : a ∈ sort r s ↔ a ∈ s := by rw [← mem_coe, sort_eq]
#align multiset.mem_sort Multiset.mem_sort
-/

#print Multiset.length_sort /-
@[simp]
theorem length_sort {s : Multiset α} : (sort r s).length = s.card :=
  Quot.inductionOn s <| length_mergeSort _
#align multiset.length_sort Multiset.length_sort
-/

#print Multiset.sort_zero /-
@[simp]
theorem sort_zero : sort r 0 = [] :=
  List.mergeSort_nil r
#align multiset.sort_zero Multiset.sort_zero
-/

#print Multiset.sort_singleton /-
@[simp]
theorem sort_singleton (a : α) : sort r {a} = [a] :=
  List.mergeSort_singleton r a
#align multiset.sort_singleton Multiset.sort_singleton
-/

end Sort

-- TODO: use a sort order if available, gh-18166
unsafe instance [Repr α] : Repr (Multiset α) :=
  ⟨fun s => "{" ++ String.intercalate ", " (s.unquot.map repr) ++ "}"⟩

end Multiset

