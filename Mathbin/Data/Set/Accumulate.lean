/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Data.Set.Lattice

#align_import data.set.accumulate from "leanprover-community/mathlib"@"c3291da49cfa65f0d43b094750541c0731edc932"

/-!
# Accumulate

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The function `accumulate` takes a set `s` and returns `⋃ y ≤ x, s y`.
-/


variable {α β γ : Type _} {s : α → Set β} {t : α → Set γ}

namespace Set

#print Set.Accumulate /-
/-- `accumulate s` is the union of `s y` for `y ≤ x`. -/
def Accumulate [LE α] (s : α → Set β) (x : α) : Set β :=
  ⋃ y ≤ x, s y
#align set.accumulate Set.Accumulate
-/

variable {s}

#print Set.accumulate_def /-
theorem accumulate_def [LE α] {x : α} : Accumulate s x = ⋃ y ≤ x, s y :=
  rfl
#align set.accumulate_def Set.accumulate_def
-/

#print Set.mem_accumulate /-
@[simp]
theorem mem_accumulate [LE α] {x : α} {z : β} : z ∈ Accumulate s x ↔ ∃ y ≤ x, z ∈ s y :=
  mem_iUnion₂
#align set.mem_accumulate Set.mem_accumulate
-/

#print Set.subset_accumulate /-
theorem subset_accumulate [Preorder α] {x : α} : s x ⊆ Accumulate s x := fun z => mem_biUnion le_rfl
#align set.subset_accumulate Set.subset_accumulate
-/

#print Set.monotone_accumulate /-
theorem monotone_accumulate [Preorder α] : Monotone (Accumulate s) := fun x y hxy =>
  biUnion_subset_biUnion_left fun z hz => le_trans hz hxy
#align set.monotone_accumulate Set.monotone_accumulate
-/

#print Set.biUnion_accumulate /-
theorem biUnion_accumulate [Preorder α] (x : α) : (⋃ y ≤ x, Accumulate s y) = ⋃ y ≤ x, s y :=
  by
  apply subset.antisymm
  · exact Union₂_subset fun y hy => monotone_accumulate hy
  · exact Union₂_mono fun y hy => subset_accumulate
#align set.bUnion_accumulate Set.biUnion_accumulate
-/

#print Set.iUnion_accumulate /-
theorem iUnion_accumulate [Preorder α] : (⋃ x, Accumulate s x) = ⋃ x, s x :=
  by
  apply subset.antisymm
  · simp only [subset_def, mem_Union, exists_imp, mem_accumulate]
    intro z x x' hx'x hz; exact ⟨x', hz⟩
  · exact Union_mono fun i => subset_accumulate
#align set.Union_accumulate Set.iUnion_accumulate
-/

end Set

