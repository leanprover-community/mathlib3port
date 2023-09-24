/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau
-/
import Data.Finset.Basic

#align_import data.finset.order from "leanprover-community/mathlib"@"e04043d6bf7264a3c84bc69711dc354958ca4516"

/-!
# Finsets of ordered types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


universe u v w

variable {α : Type u}

#print Directed.finset_le /-
theorem Directed.finset_le {r : α → α → Prop} [IsTrans α r] {ι} [hι : Nonempty ι] {f : ι → α}
    (D : Directed r f) (s : Finset ι) : ∃ z, ∀ i ∈ s, r (f i) (f z) :=
  show ∃ z, ∀ i ∈ s.1, r (f i) (f z) from
    Multiset.induction_on s.1
      (let ⟨z⟩ := hι
      ⟨z, fun _ => False.elim⟩)
      fun i s ⟨j, H⟩ =>
      let ⟨k, h₁, h₂⟩ := D i j
      ⟨k, fun a h =>
        Or.cases_on (Multiset.mem_cons.1 h) (fun h => h.symm ▸ h₁) fun h => trans (H _ h) h₂⟩
#align directed.finset_le Directed.finset_le
-/

#print Finset.exists_le /-
theorem Finset.exists_le [Nonempty α] [Preorder α] [IsDirected α (· ≤ ·)] (s : Finset α) :
    ∃ M, ∀ i ∈ s, i ≤ M :=
  directed_id.finset_le _
#align finset.exists_le Finset.exists_le
-/

