/-
Copyright (c) 2022 Jake Levinson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Levinson
-/
import Mathbin.Order.UpperLower

/-!
# Young diagrams

A Young diagram is a finite set of up-left justified boxes:

```text
□□□□□
□□□
□□□
□
```
This Young diagram corresponds to the [5, 3, 3, 1] partition of 12.

We represent it as a lower set in `ℕ × ℕ` in the product partial order. We write `(i, j) ∈ μ`
to say that `(i, j)` (in matrix coordinates) is in the Young diagram `μ`.

## Main definitions

- `young_diagram` : Young diagrams
- `young_diagram.card` : the number of cells in a Young diagram (its *cardinality*)
- `young_diagram.distrib_lattice` : a distributive lattice instance for Young diagrams
  ordered by containment, with `(⊥ : young_diagram)` the empty diagram.

## Notation

In "English notation", a Young diagram is drawn so that (i1, j1) ≤ (i2, j2)
means (i1, j1) is weakly up-and-left of (i2, j2). This terminology is used
below, e.g. in `young_diagram.up_left_mem`.

## Tags

Young diagram

## References

<https://en.wikipedia.org/wiki/Young_tableau>

-/


/-- A Young diagram is a finite collection of cells on the `ℕ × ℕ` grid such that whenever
a cell is present, so are all the ones above and to the left of it. Like matrices, an `(i, j)` cell
is a cell in row `i` and column `j`, where rows are enumerated downward and columns rightward.

Young diagrams are modeled as finite sets in `ℕ × ℕ` that are lower sets with respect to the
standard order on products. -/
@[ext]
structure YoungDiagram where
  cells : Finset (ℕ × ℕ)
  IsLowerSet : IsLowerSet (cells : Set (ℕ × ℕ))

namespace YoungDiagram

instance : SetLike YoungDiagram (ℕ × ℕ) where
  coe := coe YoungDiagram.cells
  coe_injective' := fun μ ν h => by
    rwa [YoungDiagram.ext_iff, ← Finset.coe_inj]

@[simp]
theorem mem_cells {μ : YoungDiagram} (c : ℕ × ℕ) : c ∈ μ.cells ↔ c ∈ μ :=
  Iff.rfl

/-- In "English notation", a Young diagram is drawn so that (i1, j1) ≤ (i2, j2)
    means (i1, j1) is weakly up-and-left of (i2, j2). -/
theorem up_left_mem (μ : YoungDiagram) {i1 i2 j1 j2 : ℕ} (hi : i1 ≤ i2) (hj : j1 ≤ j2) (hcell : (i2, j2) ∈ μ) :
    (i1, j1) ∈ μ :=
  μ.IsLowerSet (Prod.mk_le_mk.mpr ⟨hi, hj⟩) hcell

section DistribLattice

@[simp]
theorem cells_subset_iff {μ ν : YoungDiagram} : μ.cells ⊆ ν.cells ↔ μ ≤ ν :=
  Iff.rfl

@[simp]
theorem cells_ssubset_iff {μ ν : YoungDiagram} : μ.cells ⊂ ν.cells ↔ μ < ν :=
  Iff.rfl

instance :
    HasSup YoungDiagram where sup := fun μ ν =>
    { cells := μ.cells ∪ ν.cells,
      IsLowerSet := by
        rw [Finset.coe_union]
        exact μ.is_lower_set.union ν.is_lower_set }

@[simp]
theorem cells_sup (μ ν : YoungDiagram) : (μ⊔ν).cells = μ.cells ∪ ν.cells :=
  rfl

@[simp, norm_cast]
theorem coe_sup (μ ν : YoungDiagram) : ↑(μ⊔ν) = (μ ∪ ν : Set (ℕ × ℕ)) :=
  Finset.coe_union _ _

@[simp]
theorem mem_sup {μ ν : YoungDiagram} {x : ℕ × ℕ} : x ∈ μ⊔ν ↔ x ∈ μ ∨ x ∈ ν :=
  Finset.mem_union

instance :
    HasInf YoungDiagram where inf := fun μ ν =>
    { cells := μ.cells ∩ ν.cells,
      IsLowerSet := by
        rw [Finset.coe_inter]
        exact μ.is_lower_set.inter ν.is_lower_set }

@[simp]
theorem cells_inf (μ ν : YoungDiagram) : (μ⊓ν).cells = μ.cells ∩ ν.cells :=
  rfl

@[simp, norm_cast]
theorem coe_inf (μ ν : YoungDiagram) : ↑(μ⊓ν) = (μ ∩ ν : Set (ℕ × ℕ)) :=
  Finset.coe_inter _ _

@[simp]
theorem mem_inf {μ ν : YoungDiagram} {x : ℕ × ℕ} : x ∈ μ⊓ν ↔ x ∈ μ ∧ x ∈ ν :=
  Finset.mem_inter

/-- The empty Young diagram is (⊥ : young_diagram). -/
instance : OrderBot YoungDiagram where
  bot := { cells := ∅, IsLowerSet := fun _ _ _ => False.elim }
  bot_le := fun _ _ => False.elim

@[simp]
theorem cells_bot : (⊥ : YoungDiagram).cells = ∅ :=
  rfl

@[simp, norm_cast]
theorem coe_bot : ↑(⊥ : YoungDiagram) = (∅ : Set (ℕ × ℕ)) :=
  rfl

@[simp]
theorem not_mem_bot (x : ℕ × ℕ) : x ∉ (⊥ : YoungDiagram) :=
  Finset.not_mem_empty x

instance : Inhabited YoungDiagram :=
  ⟨⊥⟩

instance : DistribLattice YoungDiagram :=
  Function.Injective.distribLattice YoungDiagram.cells
    (fun μ ν h => by
      rwa [YoungDiagram.ext_iff])
    (fun _ _ => rfl) fun _ _ => rfl

end DistribLattice

/-- Cardinality of a Young diagram -/
@[reducible]
protected def card (μ : YoungDiagram) : ℕ :=
  μ.cells.card

end YoungDiagram

