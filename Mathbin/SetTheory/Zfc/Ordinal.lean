/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathbin.SetTheory.Zfc.Basic

/-!
# Von Neumann ordinals

This file works towards the development of von Neumann ordinals, i.e. transitive sets, well-ordered
under `∈`. We currently only have an initial development of transitive sets.

Further development can be found on the branch `von_neumann_v2`.

## Definitions

- `Set.is_transitive` means that every element of a set is a subset.

## Todo

- Define von Neumann ordinals.
- Define the basic arithmetic operations on ordinals from a purely set-theoretic perspective.
- Prove the equivalences between these definitions and those provided in
  `set_theory/ordinal/arithmetic.lean`.
-/


universe u

variable {x y z : Setₓ.{u}}

namespace Setₓ

/-- A transitive set is one where every element is a subset. -/
def IsTransitive (x : Setₓ) : Prop :=
  ∀ y ∈ x, y ⊆ x

@[simp]
theorem empty_is_transitive : IsTransitive ∅ := fun y hy => (mem_empty y hy).elim

theorem IsTransitive.subset_of_mem (h : x.IsTransitive) : y ∈ x → y ⊆ x :=
  h y

theorem is_transitive_iff_mem_trans : z.IsTransitive ↔ ∀ {x y : Setₓ}, x ∈ y → y ∈ z → x ∈ z :=
  ⟨fun h x y hx hy => h.subset_of_mem hy hx, fun H x hx y hy => H hy hx⟩

alias is_transitive_iff_mem_trans ↔ is_transitive.mem_trans _

protected theorem IsTransitive.inter (hx : x.IsTransitive) (hy : y.IsTransitive) : (x ∩ y).IsTransitive :=
  fun z hz w hw => by
  rw [mem_inter] at hz⊢
  exact ⟨hx.mem_trans hw hz.1, hy.mem_trans hw hz.2⟩

protected theorem IsTransitive.sUnion (h : x.IsTransitive) : (⋃₀x).IsTransitive := fun y hy z hz => by
  rcases mem_sUnion.1 hy with ⟨w, hw, hw'⟩
  exact mem_sUnion_of_mem hz (h.mem_trans hw' hw)

theorem IsTransitive.sUnion' (H : ∀ y ∈ x, IsTransitive y) : (⋃₀x).IsTransitive := fun y hy z hz => by
  rcases mem_sUnion.1 hy with ⟨w, hw, hw'⟩
  exact mem_sUnion_of_mem ((H w hw).mem_trans hz hw') hw

theorem is_transitive_iff_sUnion_subset : x.IsTransitive ↔ ⋃₀x ⊆ x :=
  ⟨fun h y hy => by
    rcases mem_sUnion.1 hy with ⟨z, hz, hz'⟩
    exact h.mem_trans hz' hz, fun H y hy z hz => H <| mem_sUnion_of_mem hz hy⟩

alias is_transitive_iff_sUnion_subset ↔ is_transitive.sUnion_subset _

theorem is_transitive_iff_subset_powerset : x.IsTransitive ↔ x ⊆ powerset x :=
  ⟨fun h y hy => mem_powerset.2 <| h.subset_of_mem hy, fun H y hy z hz => mem_powerset.1 (H hy) hz⟩

alias is_transitive_iff_subset_powerset ↔ is_transitive.subset_powerset _

end Setₓ

