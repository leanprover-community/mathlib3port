/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Order.UpperLower
import Mathbin.Topology.Separation

/-!
# Priestley spaces

This file defines Priestley spaces. A Priestley space is an ordered compact topological space such
that any two distinct points can be separated by a clopen upper set.

## Main declarations

* `priestley_space`: Prop-valued mixin stating the Priestley separation axiom: Any two distinct
  points can be separated by a clopen upper set.

## Implementation notes

We do not include compactness in the definition, so a Priestley space is to be declared as follows:
`[preorder α] [topological_space α] [compact_space α] [priestley_space α]`

## References

* [Wikipedia, *Priestley space*](https://en.wikipedia.org/wiki/Priestley_space)
* [Davey, Priestley *Introduction to Lattices and Order*][davey_priestley]
-/


open Set

variable {α : Type _}

/-- A Priestley space is an ordered topological space such that any two distinct points can be
separated by a clopen upper set. Compactness is often assumed, but we do not include it here. -/
class PriestleySpace (α : Type _) [Preorderₓ α] [TopologicalSpace α] where
  priestley {x y : α} : ¬x ≤ y → ∃ U : Set α, IsClopen U ∧ IsUpperSet U ∧ x ∈ U ∧ y ∉ U

variable [TopologicalSpace α]

section Preorderₓ

variable [Preorderₓ α] [PriestleySpace α] {x y : α}

theorem exists_clopen_upper_of_not_le : ¬x ≤ y → ∃ U : Set α, IsClopen U ∧ IsUpperSet U ∧ x ∈ U ∧ y ∉ U :=
  PriestleySpace.priestley

theorem exists_clopen_lower_of_not_le (h : ¬x ≤ y) : ∃ U : Set α, IsClopen U ∧ IsLowerSet U ∧ x ∉ U ∧ y ∈ U :=
  let ⟨U, hU, hU', hx, hy⟩ := exists_clopen_upper_of_not_le h
  ⟨Uᶜ, hU.compl, hU'.compl, not_not.2 hx, hy⟩

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α] [PriestleySpace α] {x y : α}

theorem exists_clopen_upper_or_lower_of_ne (h : x ≠ y) :
    ∃ U : Set α, IsClopen U ∧ (IsUpperSet U ∨ IsLowerSet U) ∧ x ∈ U ∧ y ∉ U := by
  obtain h | h := h.not_le_or_not_le
  · exact (exists_clopen_upper_of_not_le h).imp fun U => And.imp_right <| And.imp_left Or.inl
    
  · obtain ⟨U, hU, hU', hy, hx⟩ := exists_clopen_lower_of_not_le h
    exact ⟨U, hU, Or.inr hU', hx, hy⟩
    

-- See note [lower instance priority]
instance (priority := 100) PriestleySpace.to_t2_space : T2Space α :=
  ⟨fun x y h =>
    let ⟨U, hU, _, hx, hy⟩ := exists_clopen_upper_or_lower_of_ne h
    ⟨U, Uᶜ, hU.IsOpen, hU.compl.IsOpen, hx, hy, disjoint_compl_right⟩⟩

end PartialOrderₓ

