/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module logic.encodable.lattice
! leanprover-community/mathlib commit 9116dd6709f303dcf781632e15fdef382b0fc579
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Encodable.Basic
import Mathbin.Logic.Pairwise

/-!
# Lattice operations on encodable types

Lemmas about lattice and set operations on encodable types

## Implementation Notes

This is a separate file, to avoid unnecessary imports in basic files.

Previously some of these results were in the `measure_theory` folder.
-/


open Set

namespace Encodable

variable {α : Type _} {β : Type _} [Encodable β]

theorem supr_decode₂ [CompleteLattice α] (f : β → α) :
    (⨆ (i : ℕ) (b ∈ decode₂ β i), f b) = ⨆ b, f b := by
  rw [supᵢ_comm]
  simp [mem_decode₂]
#align encodable.supr_decode₂ Encodable.supr_decode₂

theorem Union_decode₂ (f : β → Set α) : (⋃ (i : ℕ) (b ∈ decode₂ β i), f b) = ⋃ b, f b :=
  supr_decode₂ f
#align encodable.Union_decode₂ Encodable.Union_decode₂

@[elab_as_elim]
theorem Union_decode₂_cases {f : β → Set α} {C : Set α → Prop} (H0 : C ∅) (H1 : ∀ b, C (f b)) {n} :
    C (⋃ b ∈ decode₂ β n, f b) :=
  match decode₂ β n with
  | none => by 
    simp
    apply H0
  | some b => by 
    convert H1 b
    simp [ext_iff]
#align encodable.Union_decode₂_cases Encodable.Union_decode₂_cases

theorem Union_decode₂_disjoint_on {f : β → Set α} (hd : Pairwise (Disjoint on f)) :
    Pairwise (Disjoint on fun i => ⋃ b ∈ decode₂ β i, f b) := by
  rintro i j ij
  refine' disjoint_left.mpr fun x => _
  suffices ∀ a, encode a = i → x ∈ f a → ∀ b, encode b = j → x ∉ f b by simpa [decode₂_eq_some]
  rintro a rfl ha b rfl hb
  exact (hd (mt (congr_arg encode) ij)).le_bot ⟨ha, hb⟩
#align encodable.Union_decode₂_disjoint_on Encodable.Union_decode₂_disjoint_on

end Encodable

