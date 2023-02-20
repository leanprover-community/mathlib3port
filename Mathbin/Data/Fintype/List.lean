/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky

! This file was ported from Lean 3 source module data.fintype.list
! leanprover-community/mathlib commit 28aa996fc6fb4317f0083c4e6daf79878d81be33
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Basic
import Mathbin.Data.Finset.Powerset

/-!

# Fintype instance for nodup lists

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The subtype of `{l : list α // l.nodup}` over a `[fintype α]`
admits a `fintype` instance.

## Implementation details
To construct the `fintype` instance, a function lifting a `multiset α`
to the `finset (list α)` that can construct it is provided.
This function is applied to the `finset.powerset` of `finset.univ`.

In general, a `decidable_eq` instance is not necessary to define this function,
but a proof of `(list.permutations l).nodup` is required to avoid it,
which is a TODO.

-/


variable {α : Type _} [DecidableEq α]

open List

namespace Multiset

#print Multiset.lists /-
/-- The `finset` of `l : list α` that, given `m : multiset α`, have the property `⟦l⟧ = m`.
-/
def lists : Multiset α → Finset (List α) := fun s =>
  Quotient.liftOn s (fun l => l.permutations.toFinset) fun l l' (h : l ~ l') =>
    by
    ext sl
    simp only [mem_permutations, List.mem_toFinset]
    exact ⟨fun hs => hs.trans h, fun hs => hs.trans h.symm⟩
#align multiset.lists Multiset.lists
-/

#print Multiset.lists_coe /-
@[simp]
theorem lists_coe (l : List α) : lists (l : Multiset α) = l.permutations.toFinset :=
  rfl
#align multiset.lists_coe Multiset.lists_coe
-/

#print Multiset.mem_lists_iff /-
@[simp]
theorem mem_lists_iff (s : Multiset α) (l : List α) : l ∈ lists s ↔ s = ⟦l⟧ :=
  by
  induction s using Quotient.inductionOn
  simpa using perm_comm
#align multiset.mem_lists_iff Multiset.mem_lists_iff
-/

end Multiset

#print fintypeNodupList /-
instance fintypeNodupList [Fintype α] : Fintype { l : List α // l.Nodup } :=
  Fintype.subtype ((Finset.univ : Finset α).powerset.bunionᵢ fun s => s.val.lists) fun l =>
    by
    suffices (∃ a : Finset α, a.val = ↑l) ↔ l.nodup by simpa
    constructor
    · rintro ⟨s, hs⟩
      simpa [← Multiset.coe_nodup, ← hs] using s.nodup
    · intro hl
      refine' ⟨⟨↑l, hl⟩, _⟩
      simp
#align fintype_nodup_list fintypeNodupList
-/

