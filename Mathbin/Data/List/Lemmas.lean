/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, Yury Kudryashov

! This file was ported from Lean 3 source module data.list.lemmas
! leanprover-community/mathlib commit 2ec920d35348cb2d13ac0e1a2ad9df0fdf1a76b4
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

variable {α β γ : Type _}

namespace List

#print List.injOn_insertNth_index_of_not_mem /-
theorem injOn_insertNth_index_of_not_mem (l : List α) (x : α) (hx : x ∉ l) :
    Set.InjOn (fun k => insertNth k x l) {n | n ≤ l.length} :=
  by
  induction' l with hd tl IH
  · intro n hn m hm h
    simp only [Set.mem_singleton_iff, Set.setOf_eq_eq_singleton, length, nonpos_iff_eq_zero] at hn
      hm 
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

#print List.foldr_range_subset_of_range_subset /-
theorem foldr_range_subset_of_range_subset {f : β → α → α} {g : γ → α → α}
    (hfg : Set.range f ⊆ Set.range g) (a : α) : Set.range (foldr f a) ⊆ Set.range (foldr g a) :=
  by
  rintro _ ⟨l, rfl⟩
  induction' l with b l H
  · exact ⟨[], rfl⟩
  · cases' hfg (Set.mem_range_self b) with c hgf
    cases' H with m hgf'
    rw [foldr_cons, ← hgf, ← hgf']
    exact ⟨c :: m, rfl⟩
#align list.foldr_range_subset_of_range_subset List.foldr_range_subset_of_range_subset
-/

#print List.foldl_range_subset_of_range_subset /-
theorem foldl_range_subset_of_range_subset {f : α → β → α} {g : α → γ → α}
    (hfg : (Set.range fun a c => f c a) ⊆ Set.range fun b c => g c b) (a : α) :
    Set.range (foldl f a) ⊆ Set.range (foldl g a) :=
  by
  change (Set.range fun l => _) ⊆ Set.range fun l => _
  simp_rw [← foldr_reverse] at hfg ⊢
  simp_rw [Set.range_comp _ List.reverse, reverse_involutive.bijective.surjective.range_eq,
    Set.image_univ]
  exact foldr_range_subset_of_range_subset hfg a
#align list.foldl_range_subset_of_range_subset List.foldl_range_subset_of_range_subset
-/

#print List.foldr_range_eq_of_range_eq /-
theorem foldr_range_eq_of_range_eq {f : β → α → α} {g : γ → α → α} (hfg : Set.range f = Set.range g)
    (a : α) : Set.range (foldr f a) = Set.range (foldr g a) :=
  (foldr_range_subset_of_range_subset hfg.le a).antisymm
    (foldr_range_subset_of_range_subset hfg.ge a)
#align list.foldr_range_eq_of_range_eq List.foldr_range_eq_of_range_eq
-/

#print List.foldl_range_eq_of_range_eq /-
theorem foldl_range_eq_of_range_eq {f : α → β → α} {g : α → γ → α}
    (hfg : (Set.range fun a c => f c a) = Set.range fun b c => g c b) (a : α) :
    Set.range (foldl f a) = Set.range (foldl g a) :=
  (foldl_range_subset_of_range_subset hfg.le a).antisymm
    (foldl_range_subset_of_range_subset hfg.ge a)
#align list.foldl_range_eq_of_range_eq List.foldl_range_eq_of_range_eq
-/

end List

