/-
Copyright (c) 2022 Jake Levinson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Levinson
-/
import Mathbin.Order.UpperLower
import Mathbin.Data.Finset.Preimage

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
- `young_diagram.row` and `young_diagram.row_len`: rows of a Young diagram and their lengths
- `young_diagram.col` and `young_diagram.col_len`: columns of a Young diagram and their lengths

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

@[simp]
theorem mem_mk (c : ℕ × ℕ) (cells) (is_lower_set) : c ∈ YoungDiagram.mk cells IsLowerSet ↔ c ∈ cells :=
  Iff.rfl

instance decidableMem (μ : YoungDiagram) : DecidablePred (· ∈ μ) :=
  show DecidablePred (· ∈ μ.cells) by
    infer_instance

/-- In "English notation", a Young diagram is drawn so that (i1, j1) ≤ (i2, j2)
    means (i1, j1) is weakly up-and-left of (i2, j2). -/
theorem up_left_mem (μ : YoungDiagram) {i1 i2 j1 j2 : ℕ} (hi : i1 ≤ i2) (hj : j1 ≤ j2) (hcell : (i2, j2) ∈ μ) :
    (i1, j1) ∈ μ :=
  μ.IsLowerSet (Prod.mk_le_mkₓ.mpr ⟨hi, hj⟩) hcell

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
theorem cells_sup (μ ν : YoungDiagram) : (μ ⊔ ν).cells = μ.cells ∪ ν.cells :=
  rfl

@[simp, norm_cast]
theorem coe_sup (μ ν : YoungDiagram) : ↑(μ ⊔ ν) = (μ ∪ ν : Set (ℕ × ℕ)) :=
  Finset.coe_union _ _

@[simp]
theorem mem_sup {μ ν : YoungDiagram} {x : ℕ × ℕ} : x ∈ μ ⊔ ν ↔ x ∈ μ ∨ x ∈ ν :=
  Finset.mem_union

instance :
    HasInf YoungDiagram where inf := fun μ ν =>
    { cells := μ.cells ∩ ν.cells,
      IsLowerSet := by
        rw [Finset.coe_inter]
        exact μ.is_lower_set.inter ν.is_lower_set }

@[simp]
theorem cells_inf (μ ν : YoungDiagram) : (μ ⊓ ν).cells = μ.cells ∩ ν.cells :=
  rfl

@[simp, norm_cast]
theorem coe_inf (μ ν : YoungDiagram) : ↑(μ ⊓ ν) = (μ ∩ ν : Set (ℕ × ℕ)) :=
  Finset.coe_inter _ _

@[simp]
theorem mem_inf {μ ν : YoungDiagram} {x : ℕ × ℕ} : x ∈ μ ⊓ ν ↔ x ∈ μ ∧ x ∈ ν :=
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

section Transpose

/-- The `transpose` of a Young diagram is obtained by swapping i's with j's. -/
def transpose (μ : YoungDiagram) : YoungDiagram where
  cells := (Equivₓ.prodComm _ _).finsetCongr μ.cells
  IsLowerSet := fun _ _ h => by
    simp only [Finset.mem_coe, Equivₓ.finset_congr_apply, Finset.mem_map_equiv]
    intro hcell
    apply μ.is_lower_set _ hcell
    simp [h]

@[simp]
theorem mem_transpose {μ : YoungDiagram} {c : ℕ × ℕ} : c ∈ μ.transpose ↔ c.swap ∈ μ := by
  simp [transpose]

@[simp]
theorem transpose_transpose (μ : YoungDiagram) : μ.transpose.transpose = μ := by
  ext
  simp

theorem transpose_eq_iff_eq_transpose {μ ν : YoungDiagram} : μ.transpose = ν ↔ μ = ν.transpose := by
  constructor <;>
    · rintro rfl
      simp
      

@[simp]
theorem transpose_eq_iff {μ ν : YoungDiagram} : μ.transpose = ν.transpose ↔ μ = ν := by
  rw [transpose_eq_iff_eq_transpose]
  simp

-- This is effectively both directions of `transpose_le_iff` below.
protected theorem le_of_transpose_le {μ ν : YoungDiagram} (h_le : μ.transpose ≤ ν) : μ ≤ ν.transpose := fun c hc => by
  simp only [mem_transpose]
  apply h_le
  simpa

@[simp]
theorem transpose_le_iff {μ ν : YoungDiagram} : μ.transpose ≤ ν.transpose ↔ μ ≤ ν :=
  ⟨fun h => by
    convert YoungDiagram.le_of_transpose_le h
    simp , fun h => by
    convert @YoungDiagram.le_of_transpose_le _ _ _
    simpa⟩

@[mono]
protected theorem transpose_mono {μ ν : YoungDiagram} (h_le : μ ≤ ν) : μ.transpose ≤ ν.transpose :=
  transpose_le_iff.mpr h_le

/-- Transposing Young diagrams is an `order_iso`. -/
@[simps]
def transposeOrderIso : YoungDiagram ≃o YoungDiagram :=
  ⟨⟨transpose, transpose, fun _ => by
      simp , fun _ => by
      simp ⟩,
    by
    simp ⟩

end Transpose

section Rows

/-! ### Rows and row lengths of Young diagrams.

This section defines `μ.row` and `μ.row_len`, with the following API:
      1.  `(i, j) ∈ μ ↔ j < μ.row_len i`
      2.  `μ.row i = {i} ×ˢ (finset.range (μ.row_len i))`
      3.  `μ.row_len i = (μ.row i).card`
      4.  `∀ {i1 i2}, i1 ≤ i2 → μ.row_len i2 ≤ μ.row_len i1`

Note: #3 is not convenient for defining `μ.row_len`; instead, `μ.row_len` is defined
as the smallest `j` such that `(i, j) ∉ μ`. -/


/-- The `i`-th row of a Young diagram consists of the cells whose first coordinate is `i`. -/
def row (μ : YoungDiagram) (i : ℕ) : Finset (ℕ × ℕ) :=
  μ.cells.filter fun c => c.fst = i

theorem mem_row_iff {μ : YoungDiagram} {i : ℕ} {c : ℕ × ℕ} : c ∈ μ.row i ↔ c ∈ μ ∧ c.fst = i := by
  simp [row]

theorem mk_mem_row_iff {μ : YoungDiagram} {i j : ℕ} : (i, j) ∈ μ.row i ↔ (i, j) ∈ μ := by
  simp [row]

protected theorem exists_not_mem_row (μ : YoungDiagram) (i : ℕ) : ∃ j, (i, j) ∉ μ := by
  obtain ⟨j, hj⟩ :=
    Infinite.exists_not_mem_finset
      (μ.cells.Preimage (Prod.mk i) fun _ _ _ _ h => by
        cases h
        rfl)
  rw [Finset.mem_preimage] at hj
  exact ⟨j, hj⟩

/-- Length of a row of a Young diagram -/
def rowLen (μ : YoungDiagram) (i : ℕ) : ℕ :=
  Nat.findₓ <| μ.exists_not_mem_row i

theorem mem_iff_lt_row_len {μ : YoungDiagram} {i j : ℕ} : (i, j) ∈ μ ↔ j < μ.rowLen i := by
  rw [row_len, Nat.lt_find_iff]
  push_neg
  exact
    ⟨fun h _ hmj =>
      μ.up_left_mem
        (by
          rfl)
        hmj h,
      fun h =>
      h _
        (by
          rfl)⟩

-- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation
theorem row_eq_prod {μ : YoungDiagram} {i : ℕ} : μ.row i = {i} ×ˢ Finset.range (μ.rowLen i) := by
  ext ⟨a, b⟩
  simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range, mem_row_iff, mem_iff_lt_row_len, and_comm,
    And.congr_right_iff]
  rintro rfl
  rfl

theorem row_len_eq_card (μ : YoungDiagram) {i : ℕ} : μ.rowLen i = (μ.row i).card := by
  simp [row_eq_prod]

@[mono]
theorem row_len_anti (μ : YoungDiagram) (i1 i2 : ℕ) (hi : i1 ≤ i2) : μ.rowLen i2 ≤ μ.rowLen i1 := by
  by_contra' h_lt
  rw [← lt_self_iff_falseₓ (μ.row_len i1)]
  rw [← mem_iff_lt_row_len] at h_lt⊢
  exact
    μ.up_left_mem hi
      (by
        rfl)
      h_lt

end Rows

section Columns

/-! ### Columns and column lengths of Young diagrams.

This section has an identical API to the rows section. -/


/-- The `j`-th column of a Young diagram consists of the cells whose second coordinate is `j`. -/
def col (μ : YoungDiagram) (j : ℕ) : Finset (ℕ × ℕ) :=
  μ.cells.filter fun c => c.snd = j

theorem mem_col_iff {μ : YoungDiagram} {j : ℕ} {c : ℕ × ℕ} : c ∈ μ.col j ↔ c ∈ μ ∧ c.snd = j := by
  simp [col]

theorem mk_mem_col_iff {μ : YoungDiagram} {i j : ℕ} : (i, j) ∈ μ.col j ↔ (i, j) ∈ μ := by
  simp [col]

protected theorem exists_not_mem_col (μ : YoungDiagram) (j : ℕ) : ∃ i, (i, j) ∉ μ.cells := by
  convert μ.transpose.exists_not_mem_row j
  simp

/-- Length of a column of a Young diagram -/
def colLen (μ : YoungDiagram) (j : ℕ) : ℕ :=
  Nat.findₓ <| μ.exists_not_mem_col j

@[simp]
theorem col_len_transpose (μ : YoungDiagram) (j : ℕ) : μ.transpose.colLen j = μ.rowLen j := by
  simp [row_len, col_len]

@[simp]
theorem row_len_transpose (μ : YoungDiagram) (i : ℕ) : μ.transpose.rowLen i = μ.colLen i := by
  simp [row_len, col_len]

theorem mem_iff_lt_col_len {μ : YoungDiagram} {i j : ℕ} : (i, j) ∈ μ ↔ i < μ.colLen j := by
  rw [← row_len_transpose, ← mem_iff_lt_row_len]
  simp

-- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation
theorem col_eq_prod {μ : YoungDiagram} {j : ℕ} : μ.col j = Finset.range (μ.colLen j) ×ˢ {j} := by
  ext ⟨a, b⟩
  simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range, mem_col_iff, mem_iff_lt_col_len, and_comm,
    And.congr_right_iff]
  rintro rfl
  rfl

theorem col_len_eq_card (μ : YoungDiagram) {j : ℕ} : μ.colLen j = (μ.col j).card := by
  simp [col_eq_prod]

@[mono]
theorem col_len_anti (μ : YoungDiagram) (j1 j2 : ℕ) (hj : j1 ≤ j2) : μ.colLen j2 ≤ μ.colLen j1 := by
  convert μ.transpose.row_len_anti j1 j2 hj <;> simp

end Columns

end YoungDiagram

