/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, Yury Kudryashov

! This file was ported from Lean 3 source module data.list.lemmas
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Function
import Mathbin.Data.List.Basic

/-! # Some lemmas about lists involving sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Split out from `data.list.basic` to reduce its dependencies.
-/


open List

variable {α β : Type _}

namespace List

#print List.range_map /-
theorem range_map (f : α → β) : Set.range (map f) = { l | ∀ x ∈ l, x ∈ Set.range f } :=
  by
  refine'
    Set.Subset.antisymm
      (Set.range_subset_iff.2 fun l => forall_mem_map_iff.2 fun y _ => Set.mem_range_self _)
      fun l hl => _
  induction' l with a l ihl; · exact ⟨[], rfl⟩
  rcases ihl fun x hx => hl x <| subset_cons _ _ hx with ⟨l, rfl⟩
  rcases hl a (mem_cons_self _ _) with ⟨a, rfl⟩
  exact ⟨a :: l, map_cons _ _ _⟩
#align list.range_map List.range_map
-/

#print List.range_map_coe /-
theorem range_map_coe (s : Set α) : Set.range (map (coe : s → α)) = { l | ∀ x ∈ l, x ∈ s } := by
  rw [range_map, Subtype.range_coe]
#align list.range_map_coe List.range_map_coe
-/

/-- If each element of a list can be lifted to some type, then the whole list can be lifted to this
type. -/
instance canLift (c) (p) [CanLift α β c p] :
    CanLift (List α) (List β) (List.map c) fun l => ∀ x ∈ l, p x
    where prf l H := by
    rw [← Set.mem_range, range_map]
    exact fun a ha => CanLift.prf a (H a ha)
#align list.can_lift List.canLift

#print List.injOn_insertNth_index_of_not_mem /-
theorem injOn_insertNth_index_of_not_mem (l : List α) (x : α) (hx : x ∉ l) :
    Set.InjOn (fun k => insertNth k x l) { n | n ≤ l.length } :=
  by
  induction' l with hd tl IH
  · intro n hn m hm h
    simp only [Set.mem_singleton_iff, Set.setOf_eq_eq_singleton, length, nonpos_iff_eq_zero] at
      hn hm
    simp [hn, hm]
  · intro n hn m hm h
    simp only [length, Set.mem_setOf_eq] at hn hm
    simp only [mem_cons_iff, not_or] at hx
    cases n <;> cases m
    · rfl
    · simpa [hx.left] using h
    · simpa [Ne.symm hx.left] using h
    · simp only [true_and_iff, eq_self_iff_true, insert_nth_succ_cons] at h
      rw [Nat.succ_inj']
      refine' IH hx.right _ _ h
      · simpa [Nat.succ_le_succ_iff] using hn
      · simpa [Nat.succ_le_succ_iff] using hm
#align list.inj_on_insert_nth_index_of_not_mem List.injOn_insertNth_index_of_not_mem
-/

end List

