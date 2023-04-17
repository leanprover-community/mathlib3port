/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash

! This file was ported from Lean 3 source module algebra.lie.cartan_matrix
! leanprover-community/mathlib commit 65ec59902eb17e4ab7da8d7e3d0bd9774d1b8b99
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Lie.Free
import Mathbin.Algebra.Lie.Quotient
import Mathbin.Data.Matrix.Notation

/-!
# Lie algebras from Cartan matrices

Split semi-simple Lie algebras are uniquely determined by their Cartan matrix. Indeed, if `A` is
an `l × l` Cartan matrix, the corresponding Lie algebra may be obtained as the Lie algebra on
`3l` generators: $H_1, H_2, \ldots H_l, E_1, E_2, \ldots, E_l, F_1, F_2, \ldots, F_l$
subject to the following relations:
$$
\begin{align}
  [H_i, H_j] &= 0\\
  [E_i, F_i] &= H_i\\
  [E_i, F_j] &= 0 \quad\text{if $i \ne j$}\\
  [H_i, E_j] &= A_{ij}E_j\\
  [H_i, F_j] &= -A_{ij}F_j\\
  ad(E_i)^{1 - A_{ij}}(E_j) &= 0 \quad\text{if $i \ne j$}\\
  ad(F_i)^{1 - A_{ij}}(F_j) &= 0 \quad\text{if $i \ne j$}\\
\end{align}
$$

In this file we provide the above construction. It is defined for any square matrix of integers but
the results for non-Cartan matrices should be regarded as junk.

Recall that a Cartan matrix is a square matrix of integers `A` such that:
 * For diagonal values we have: `A i i = 2`.
 * For off-diagonal values (`i ≠ j`) we have: `A i j ∈ {-3, -2, -1, 0}`.
 * `A i j = 0 ↔ A j i = 0`.
 * There exists a diagonal matrix `D` over ℝ such that `D ⬝ A ⬝ D⁻¹` is symmetric positive definite.

## Alternative construction

This construction is sometimes performed within the free unital associative algebra
`free_algebra R X`, rather than within the free Lie algebra `free_lie_algebra R X`, as we do here.
However the difference is illusory since the construction stays inside the Lie subalgebra of
`free_algebra R X` generated by `X`, and this is naturally isomorphic to `free_lie_algebra R X`
(though the proof of this seems to require Poincaré–Birkhoff–Witt).

## Definitions of exceptional Lie algebras

This file also contains the Cartan matrices of the exceptional Lie algebras. By using these in the
above construction, it thus provides definitions of the exceptional Lie algebras. These definitions
make sense over any commutative ring. When the ring is ℝ, these are the split real forms of the
exceptional semisimple Lie algebras.

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*](bourbaki1968) plates V -- IX,
  pages 275--290

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 7--9*](bourbaki1975b) chapter VIII, §4.3

* [J.P. Serre, *Complex Semisimple Lie Algebras*](serre1965) chapter VI, appendix

## Main definitions

  * `matrix.to_lie_algebra`
  * `cartan_matrix.E₆`
  * `cartan_matrix.E₇`
  * `cartan_matrix.E₈`
  * `cartan_matrix.F₄`
  * `cartan_matrix.G₂`
  * `lie_algebra.e₆`
  * `lie_algebra.e₇`
  * `lie_algebra.e₈`
  * `lie_algebra.f₄`
  * `lie_algebra.g₂`

## Tags

lie algebra, semi-simple, cartan matrix
-/


universe u v w

noncomputable section

variable (R : Type u) {B : Type v} [CommRing R] [DecidableEq B] [Fintype B]

variable (A : Matrix B B ℤ)

namespace CartanMatrix

variable (B)

/-- The generators of the free Lie algebra from which we construct the Lie algebra of a Cartan
matrix as a quotient. -/
inductive Generators
  | H : B → generators
  | E : B → generators
  | F : B → generators
#align cartan_matrix.generators CartanMatrix.Generators

instance [Inhabited B] : Inhabited (Generators B) :=
  ⟨Generators.H default⟩

variable {B}

namespace Relations

open Function

-- mathport name: exprH
local notation "H" => FreeLieAlgebra.of R ∘ Generators.H

-- mathport name: exprE
local notation "E" => FreeLieAlgebra.of R ∘ Generators.E

-- mathport name: exprF
local notation "F" => FreeLieAlgebra.of R ∘ Generators.F

-- mathport name: exprad
local notation "ad" => LieAlgebra.ad R (FreeLieAlgebra R (Generators B))

/-- The terms correpsonding to the `⁅H, H⁆`-relations. -/
def hH : B × B → FreeLieAlgebra R (Generators B) :=
  uncurry fun i j => ⁅H i, H j⁆
#align cartan_matrix.relations.HH CartanMatrix.Relations.hH

/-- The terms correpsonding to the `⁅E, F⁆`-relations. -/
def eF : B × B → FreeLieAlgebra R (Generators B) :=
  uncurry fun i j => if i = j then ⁅E i, F i⁆ - H i else ⁅E i, F j⁆
#align cartan_matrix.relations.EF CartanMatrix.Relations.eF

/-- The terms correpsonding to the `⁅H, E⁆`-relations. -/
def hE : B × B → FreeLieAlgebra R (Generators B) :=
  uncurry fun i j => ⁅H i, E j⁆ - A i j • E j
#align cartan_matrix.relations.HE CartanMatrix.Relations.hE

/-- The terms correpsonding to the `⁅H, F⁆`-relations. -/
def hF : B × B → FreeLieAlgebra R (Generators B) :=
  uncurry fun i j => ⁅H i, F j⁆ + A i j • F j
#align cartan_matrix.relations.HF CartanMatrix.Relations.hF

/-- The terms correpsonding to the `ad E`-relations.

Note that we use `int.to_nat` so that we can take the power and that we do not bother
restricting to the case `i ≠ j` since these relations are zero anyway. We also defensively
ensure this with `ad_E_of_eq_eq_zero`. -/
def adE : B × B → FreeLieAlgebra R (Generators B) :=
  uncurry fun i j => ad (E i) ^ (-A i j).toNat <| ⁅E i, E j⁆
#align cartan_matrix.relations.ad_E CartanMatrix.Relations.adE

/-- The terms correpsonding to the `ad F`-relations.

See also `ad_E` docstring. -/
def adF : B × B → FreeLieAlgebra R (Generators B) :=
  uncurry fun i j => ad (F i) ^ (-A i j).toNat <| ⁅F i, F j⁆
#align cartan_matrix.relations.ad_F CartanMatrix.Relations.adF

private theorem ad_E_of_eq_eq_zero (i : B) (h : A i i = 2) : adE R A ⟨i, i⟩ = 0 :=
  by
  have h' : (-2 : ℤ).toNat = 0 := by rfl
  simp [ad_E, h, h']
#align cartan_matrix.relations.ad_E_of_eq_eq_zero cartan_matrix.relations.ad_E_of_eq_eq_zero

private theorem ad_F_of_eq_eq_zero (i : B) (h : A i i = 2) : adF R A ⟨i, i⟩ = 0 :=
  by
  have h' : (-2 : ℤ).toNat = 0 := by rfl
  simp [ad_F, h, h']
#align cartan_matrix.relations.ad_F_of_eq_eq_zero cartan_matrix.relations.ad_F_of_eq_eq_zero

/-- The union of all the relations as a subset of the free Lie algebra. -/
def toSet : Set (FreeLieAlgebra R (Generators B)) :=
  (Set.range <| hH R) ∪ (Set.range <| eF R) ∪ (Set.range <| hE R A) ∪ (Set.range <| hF R A) ∪
      (Set.range <| adE R A) ∪
    (Set.range <| adF R A)
#align cartan_matrix.relations.to_set CartanMatrix.Relations.toSet

/-- The ideal of the free Lie algebra generated by the relations. -/
def toIdeal : LieIdeal R (FreeLieAlgebra R (Generators B)) :=
  LieSubmodule.lieSpan R _ <| toSet R A
#align cartan_matrix.relations.to_ideal CartanMatrix.Relations.toIdeal

end Relations

end CartanMatrix

/- ./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler lie_algebra[lie_algebra] R -/
/-- The Lie algebra corresponding to a Cartan matrix.

Note that it is defined for any matrix of integers. Its value for non-Cartan matrices should be
regarded as junk. -/
def Matrix.ToLieAlgebra :=
  FreeLieAlgebra R _ ⧸ CartanMatrix.Relations.toIdeal R A deriving Inhabited, LieRing,
  «./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler lie_algebra[lie_algebra] R»
#align matrix.to_lie_algebra Matrix.ToLieAlgebra

namespace CartanMatrix

/- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:31:4: unsupported: too many args: matrix.notation ... #[[]] -/
/-- The Cartan matrix of type e₆. See [bourbaki1968] plate V, page 277.

The corresponding Dynkin diagram is:
```
            o
            |
o --- o --- o --- o --- o
```
-/
def e₆ : Matrix (Fin 6) (Fin 6) ℤ :=
  !![2, 0, -1, 0, 0, 0;
    0, 2, 0, -1, 0, 0;
    -1, 0, 2, -1, 0, 0;
    0, -1, -1, 2, -1, 0;
    0, 0, 0, -1, 2, -1;
    0, 0, 0, 0, -1, 2]
#align cartan_matrix.E₆ CartanMatrix.e₆

/- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:31:4: unsupported: too many args: matrix.notation ... #[[]] -/
/-- The Cartan matrix of type e₇. See [bourbaki1968] plate VI, page 281.

The corresponding Dynkin diagram is:
```
            o
            |
o --- o --- o --- o --- o --- o
```
-/
def e₇ : Matrix (Fin 7) (Fin 7) ℤ :=
  !![2, 0, -1, 0, 0, 0, 0;
    0, 2, 0, -1, 0, 0, 0;
    -1, 0, 2, -1, 0, 0, 0;
    0, -1, -1, 2, -1, 0, 0;
    0, 0, 0, -1, 2, -1, 0;
    0, 0, 0, 0, -1, 2, -1;
    0, 0, 0, 0, 0, -1, 2]
#align cartan_matrix.E₇ CartanMatrix.e₇

/- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:31:4: unsupported: too many args: matrix.notation ... #[[]] -/
/-- The Cartan matrix of type e₈. See [bourbaki1968] plate VII, page 285.

The corresponding Dynkin diagram is:
```
            o
            |
o --- o --- o --- o --- o --- o --- o
```
-/
def e₈ : Matrix (Fin 8) (Fin 8) ℤ :=
  !![2, 0, -1, 0, 0, 0, 0, 0;
    0, 2, 0, -1, 0, 0, 0, 0;
    -1, 0, 2, -1, 0, 0, 0, 0;
    0, -1, -1, 2, -1, 0, 0, 0;
    0, 0, 0, -1, 2, -1, 0, 0;
    0, 0, 0, 0, -1, 2, -1, 0;
    0, 0, 0, 0, 0, -1, 2, -1;
    0, 0, 0, 0, 0, 0, -1, 2]
#align cartan_matrix.E₈ CartanMatrix.e₈

/- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:31:4: unsupported: too many args: matrix.notation ... #[[]] -/
/-- The Cartan matrix of type f₄. See [bourbaki1968] plate VIII, page 288.

The corresponding Dynkin diagram is:
```
o --- o =>= o --- o
```
-/
def f₄ : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, -1, 0, 0; -1, 2, -2, 0; 0, -1, 2, -1; 0, 0, -1, 2]
#align cartan_matrix.F₄ CartanMatrix.f₄

/- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:31:4: unsupported: too many args: matrix.notation ... #[[]] -/
/-- The Cartan matrix of type g₂. See [bourbaki1968] plate IX, page 290.

The corresponding Dynkin diagram is:
```
o ≡>≡ o
```
Actually we are using the transpose of Bourbaki's matrix. This is to make this matrix consistent
with `cartan_matrix.F₄`, in the sense that all non-zero values below the diagonal are -1. -/
def g₂ : Matrix (Fin 2) (Fin 2) ℤ :=
  !![2, -3; -1, 2]
#align cartan_matrix.G₂ CartanMatrix.g₂

end CartanMatrix

namespace LieAlgebra

/-- The exceptional split Lie algebra of type e₆. -/
abbrev E₆ :=
  CartanMatrix.e₆.ToLieAlgebra R
#align lie_algebra.e₆ LieAlgebra.E₆

/-- The exceptional split Lie algebra of type e₇. -/
abbrev E₇ :=
  CartanMatrix.e₇.ToLieAlgebra R
#align lie_algebra.e₇ LieAlgebra.E₇

/-- The exceptional split Lie algebra of type e₈. -/
abbrev E₈ :=
  CartanMatrix.e₈.ToLieAlgebra R
#align lie_algebra.e₈ LieAlgebra.E₈

/-- The exceptional split Lie algebra of type f₄. -/
abbrev F₄ :=
  CartanMatrix.f₄.ToLieAlgebra R
#align lie_algebra.f₄ LieAlgebra.F₄

/-- The exceptional split Lie algebra of type g₂. -/
abbrev G₂ :=
  CartanMatrix.g₂.ToLieAlgebra R
#align lie_algebra.g₂ LieAlgebra.G₂

end LieAlgebra

