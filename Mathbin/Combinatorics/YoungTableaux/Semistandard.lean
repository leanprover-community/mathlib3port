/-
Copyright (c) 2022 Jake Levinson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Levinson
-/
import Mathbin.Combinatorics.YoungDiagram

/-!
# Semistandard Young tableaux

A semistandard Young tableau is a filling of a Young diagram by natural numbers, such that
the entries are weakly increasing left-to-right along rows (i.e. for fixed `i`), and
strictly-increasing top-to-bottom along columns (i.e. for fixed `j`).

An example of an SSYT of shape `μ = [4, 2, 1]` is:

```text
0 0 0 2
1 1
2
```

We represent an SSYT as a function `ℕ → ℕ → ℕ`, which is required to be zero for all pairs
`(i, j) ∉ μ` and to satisfy the row-weak and column-strict conditions on `μ`.


## Main definitions

- `ssyt (μ : young_diagram)` : semistandard Young tableaux of shape `μ`. There is
  a `has_coe_to_fun` instance such that `T i j` is value of the `(i, j)` entry of the SSYT `T`.
- `ssyt.highest_weight (μ : young_diagram)`: the semistandard Young tableau whose `i`th row
  consists entirely of `i`s, for each `i`.

## Tags

Semistandard Young tableau

## References

<https://en.wikipedia.org/wiki/Young_tableau>

-/


/-- A semistandard Young tableau (SSYT) is a filling of the cells of a Young diagram by natural
numbers, such that the entries in each row are weakly increasing (left to right), and the entries
in each column are strictly increasing (top to bottom).

Here, an SSYT is represented as an unrestricted function `ℕ → ℕ → ℕ` that, for reasons
of extensionality, is required to vanish outside `μ`. --/
structure Ssyt (μ : YoungDiagram) where
  entry : ℕ → ℕ → ℕ
  row_weak' : ∀ {i j1 j2 : ℕ}, j1 < j2 → (i, j2) ∈ μ → entry i j1 ≤ entry i j2
  col_strict' : ∀ {i1 i2 j : ℕ}, i1 < i2 → (i2, j) ∈ μ → entry i1 j < entry i2 j
  zeros' : ∀ {i j}, (i, j) ∉ μ → entry i j = 0

namespace Ssyt

instance funLike {μ : YoungDiagram} : FunLike (Ssyt μ) ℕ fun _ => ℕ → ℕ where
  coe := Ssyt.entry
  coe_injective' := fun T T' h => by
    cases T
    cases T'
    congr

/-- Helper instance for when there's too many metavariables to apply
`fun_like.has_coe_to_fun` directly. -/
instance {μ : YoungDiagram} : CoeFun (Ssyt μ) fun _ => ℕ → ℕ → ℕ :=
  FunLike.hasCoeToFun

@[simp]
theorem to_fun_eq_coe {μ : YoungDiagram} {T : Ssyt μ} : T.entry = (T : ℕ → ℕ → ℕ) :=
  rfl

@[ext]
theorem ext {μ : YoungDiagram} {T T' : Ssyt μ} (h : ∀ i j, T i j = T' i j) : T = T' :=
  FunLike.ext T T' fun x => by
    funext
    apply h

/-- Copy of an `ssyt μ` with a new `entry` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy {μ : YoungDiagram} {T : Ssyt μ} (entry' : ℕ → ℕ → ℕ) (h : entry' = T) : Ssyt μ where
  entry := entry'
  row_weak' := fun _ _ _ => h.symm ▸ T.row_weak'
  col_strict' := fun _ _ _ => h.symm ▸ T.col_strict'
  zeros' := fun _ _ => h.symm ▸ T.zeros'

theorem row_weak {μ : YoungDiagram} (T : Ssyt μ) {i j1 j2 : ℕ} (hj : j1 < j2) (hcell : (i, j2) ∈ μ) : T i j1 ≤ T i j2 :=
  T.row_weak' hj hcell

theorem col_strict {μ : YoungDiagram} (T : Ssyt μ) {i1 i2 j : ℕ} (hi : i1 < i2) (hcell : (i2, j) ∈ μ) :
    T i1 j < T i2 j :=
  T.col_strict' hi hcell

theorem zeros {μ : YoungDiagram} (T : Ssyt μ) {i j : ℕ} (not_cell : (i, j) ∉ μ) : T i j = 0 :=
  T.zeros' not_cell

theorem row_weak_of_le {μ : YoungDiagram} (T : Ssyt μ) {i j1 j2 : ℕ} (hj : j1 ≤ j2) (cell : (i, j2) ∈ μ) :
    T i j1 ≤ T i j2 := by
  cases eq_or_lt_of_leₓ hj
  subst h
  exact T.row_weak h cell

theorem col_weak {μ : YoungDiagram} (T : Ssyt μ) {i1 i2 j : ℕ} (hi : i1 ≤ i2) (cell : (i2, j) ∈ μ) : T i1 j ≤ T i2 j :=
  by
  cases eq_or_lt_of_leₓ hi
  subst h
  exact le_of_ltₓ (T.col_strict h cell)

/-- The "highest weight" SSYT of a given shape is has all i's in row i, for each i. --/
def highestWeight (μ : YoungDiagram) : Ssyt μ where
  entry := fun i j => if (i, j) ∈ μ then i else 0
  row_weak' := fun i j1 j2 hj hcell => by rw [if_pos hcell, if_pos (μ.up_left_mem (by rfl) (le_of_ltₓ hj) hcell)]
  col_strict' := fun i1 i2 j hi hcell => by rwa [if_pos hcell, if_pos (μ.up_left_mem (le_of_ltₓ hi) (by rfl) hcell)]
  zeros' := fun i j not_cell => if_neg not_cell

@[simp]
theorem highest_weight_apply {μ : YoungDiagram} {i j : ℕ} : highestWeight μ i j = if (i, j) ∈ μ then i else 0 :=
  rfl

instance {μ : YoungDiagram} : Inhabited (Ssyt μ) :=
  ⟨Ssyt.highestWeight μ⟩

end Ssyt

