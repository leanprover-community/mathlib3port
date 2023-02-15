/-
Copyright (c) 2022 Yaël Dillies, Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Violeta Hernández Palacios, Grayson Burton, Vladimir Ivanov

! This file was ported from Lean 3 source module order.grade
! leanprover-community/mathlib commit 369525b73f229ccd76a6ec0e0e0bf2be57599768
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Basic
import Mathbin.Data.Int.SuccPred

/-!
# Graded orders

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines graded orders, also known as ranked orders.

A `𝕆`-graded order is an order `α` equipped with a distinguished "grade" function `α → 𝕆` which
should be understood as giving the "height" of the elements. Usual graded orders are `ℕ`-graded,
cograded orders are `ℕᵒᵈ`-graded, but we can also grade by `ℤ`, and polytopes are naturally
`fin n`-graded.

Visually, `grade ℕ a` is the height of `a` in the Hasse diagram of `α`.

## Main declarations

* `grade_order`: Graded order.
* `grade_min_order`: Graded order where minimal elements have minimal grades.
* `grade_max_order`: Graded order where maximal elements have maximal grades.
* `grade_bounded_order`: Graded order where minimal elements have minimal grades and maximal
  elements have maximal grades.
* `grade`: The grade of an element. Because an order can admit several gradings, the first argument
  is the order we grade by.
* `grade_max_order`: Graded orders with maximal elements. All maximal elements have the same grade.
* `max_grade`: The maximum grade in a `grade_max_order`.
* `order_embedding.grade`: The grade of an element in a linear order as an order embedding.

## How to grade your order

Here are the translations between common references and our `grade_order`:
* [Stanley][stanley2012] defines a graded order of rank `n` as an order where all maximal chains
  have "length" `n` (so the number of elements of a chain is `n + 1`). This corresponds to
  `grade_bounded_order (fin (n + 1)) α`.
* [Engel][engel1997]'s ranked orders are somewhere between `grade_order ℕ α` and
  `grade_min_order ℕ α`, in that he requires `∃ a, is_min a ∧ grade ℕ a + 0` rather than
  `∀ a, is_min a → grade ℕ a = 0`. He defines a graded order as an order where all minimal elements
  have grade `0` and all maximal elements have the same grade. This is roughly a less bundled
  version of `grade_bounded_order (fin n) α`, assuming we discard orders with infinite chains.

## Implementation notes

One possible definition of graded orders is as the bounded orders whose flags (maximal chains)
all have the same finite length (see Stanley p. 99). However, this means that all graded orders must
have minimal and maximal elements and that the grade is not data.

Instead, we define graded orders by their grade function, without talking about flags yet.

## References

* [Konrad Engel, *Sperner Theory*][engel1997]
* [Richard Stanley, *Enumerative Combinatorics*][stanley2012]
-/


open Finset Nat OrderDual

variable {𝕆 ℙ α β : Type _}

#print GradeOrder /-
/-- An `𝕆`-graded order is an order `α` equipped with a strictly monotone function `grade 𝕆 : α → 𝕆`
which preserves order covering (`covby`). -/
class GradeOrder (𝕆 α : Type _) [Preorder 𝕆] [Preorder α] where
  grade : α → 𝕆
  grade_strictMono : StrictMono grade
  covby_grade ⦃a b : α⦄ : a ⋖ b → grade a ⋖ grade b
#align grade_order GradeOrder
-/

#print GradeMinOrder /-
/-- A `𝕆`-graded order where minimal elements have minimal grades. -/
class GradeMinOrder (𝕆 α : Type _) [Preorder 𝕆] [Preorder α] extends GradeOrder 𝕆 α where
  isMin_grade ⦃a : α⦄ : IsMin a → IsMin (grade a)
#align grade_min_order GradeMinOrder
-/

#print GradeMaxOrder /-
/-- A `𝕆`-graded order where maximal elements have maximal grades. -/
class GradeMaxOrder (𝕆 α : Type _) [Preorder 𝕆] [Preorder α] extends GradeOrder 𝕆 α where
  isMax_grade ⦃a : α⦄ : IsMax a → IsMax (grade a)
#align grade_max_order GradeMaxOrder
-/

#print GradeBoundedOrder /-
/-- A `𝕆`-graded order where minimal elements have minimal grades and maximal elements have maximal
grades. -/
class GradeBoundedOrder (𝕆 α : Type _) [Preorder 𝕆] [Preorder α] extends GradeMinOrder 𝕆 α,
  GradeMaxOrder 𝕆 α
#align grade_bounded_order GradeBoundedOrder
-/

section Preorder

-- grading
variable [Preorder 𝕆]

section Preorder

-- graded order
variable [Preorder α]

section GradeOrder

variable (𝕆) [GradeOrder 𝕆 α] {a b : α}

/- warning: grade -> grade is a dubious translation:
lean 3 declaration is
  forall (𝕆 : Type.{u1}) {α : Type.{u2}} [_inst_1 : Preorder.{u1} 𝕆] [_inst_2 : Preorder.{u2} α] [_inst_3 : GradeOrder.{u1, u2} 𝕆 α _inst_1 _inst_2], α -> 𝕆
but is expected to have type
  forall (𝕆 : Type.{u1}) {α : Type.{u2}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} 𝕆] [_inst_3 : GradeOrder.{u1, u2} 𝕆 α _inst_2 _inst_1], α -> 𝕆
Case conversion may be inaccurate. Consider using '#align grade gradeₓ'. -/
/-- The grade of an element in a graded order. Morally, this is the number of elements you need to
go down by to get to `⊥`. -/
def grade : α → 𝕆 :=
  GradeOrder.grade
#align grade grade

/- warning: covby.grade -> Covby.grade is a dubious translation:
lean 3 declaration is
  forall (𝕆 : Type.{u1}) {α : Type.{u2}} [_inst_1 : Preorder.{u1} 𝕆] [_inst_2 : Preorder.{u2} α] [_inst_3 : GradeOrder.{u1, u2} 𝕆 α _inst_1 _inst_2] {a : α} {b : α}, (Covby.{u2} α (Preorder.toLT.{u2} α _inst_2) a b) -> (Covby.{u1} 𝕆 (Preorder.toLT.{u1} 𝕆 _inst_1) (grade.{u1, u2} 𝕆 α _inst_1 _inst_2 _inst_3 a) (grade.{u1, u2} 𝕆 α _inst_1 _inst_2 _inst_3 b))
but is expected to have type
  forall (𝕆 : Type.{u1}) {α : Type.{u2}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} 𝕆] [_inst_3 : GradeOrder.{u1, u2} 𝕆 α _inst_2 _inst_1] {a : α} {b : α}, (Covby.{u2} α (Preorder.toLT.{u2} α _inst_1) a b) -> (Covby.{u1} 𝕆 (Preorder.toLT.{u1} 𝕆 _inst_2) (grade.{u1, u2} 𝕆 α _inst_1 _inst_2 _inst_3 a) (grade.{u1, u2} 𝕆 α _inst_1 _inst_2 _inst_3 b))
Case conversion may be inaccurate. Consider using '#align covby.grade Covby.gradeₓ'. -/
protected theorem Covby.grade (h : a ⋖ b) : grade 𝕆 a ⋖ grade 𝕆 b :=
  GradeOrder.covby_grade h
#align covby.grade Covby.grade

variable {𝕆}

/- warning: grade_strict_mono -> grade_strictMono is a dubious translation:
lean 3 declaration is
  forall {𝕆 : Type.{u1}} {α : Type.{u2}} [_inst_1 : Preorder.{u1} 𝕆] [_inst_2 : Preorder.{u2} α] [_inst_3 : GradeOrder.{u1, u2} 𝕆 α _inst_1 _inst_2], StrictMono.{u2, u1} α 𝕆 _inst_2 _inst_1 (grade.{u1, u2} 𝕆 α _inst_1 _inst_2 _inst_3)
but is expected to have type
  forall {𝕆 : Type.{u1}} {α : Type.{u2}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} 𝕆] [_inst_3 : GradeOrder.{u1, u2} 𝕆 α _inst_2 _inst_1], StrictMono.{u2, u1} α 𝕆 _inst_1 _inst_2 (grade.{u1, u2} 𝕆 α _inst_1 _inst_2 _inst_3)
Case conversion may be inaccurate. Consider using '#align grade_strict_mono grade_strictMonoₓ'. -/
theorem grade_strictMono : StrictMono (grade 𝕆 : α → 𝕆) :=
  GradeOrder.grade_strictMono
#align grade_strict_mono grade_strictMono

/- warning: covby_iff_lt_covby_grade -> covby_iff_lt_covby_grade is a dubious translation:
lean 3 declaration is
  forall {𝕆 : Type.{u1}} {α : Type.{u2}} [_inst_1 : Preorder.{u1} 𝕆] [_inst_2 : Preorder.{u2} α] [_inst_3 : GradeOrder.{u1, u2} 𝕆 α _inst_1 _inst_2] {a : α} {b : α}, Iff (Covby.{u2} α (Preorder.toLT.{u2} α _inst_2) a b) (And (LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) a b) (Covby.{u1} 𝕆 (Preorder.toLT.{u1} 𝕆 _inst_1) (grade.{u1, u2} 𝕆 α _inst_1 _inst_2 _inst_3 a) (grade.{u1, u2} 𝕆 α _inst_1 _inst_2 _inst_3 b)))
but is expected to have type
  forall {𝕆 : Type.{u1}} {α : Type.{u2}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} 𝕆] [_inst_3 : GradeOrder.{u1, u2} 𝕆 α _inst_2 _inst_1] {a : α} {b : α}, Iff (Covby.{u2} α (Preorder.toLT.{u2} α _inst_1) a b) (And (LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_1) a b) (Covby.{u1} 𝕆 (Preorder.toLT.{u1} 𝕆 _inst_2) (grade.{u1, u2} 𝕆 α _inst_1 _inst_2 _inst_3 a) (grade.{u1, u2} 𝕆 α _inst_1 _inst_2 _inst_3 b)))
Case conversion may be inaccurate. Consider using '#align covby_iff_lt_covby_grade covby_iff_lt_covby_gradeₓ'. -/
theorem covby_iff_lt_covby_grade : a ⋖ b ↔ a < b ∧ grade 𝕆 a ⋖ grade 𝕆 b :=
  ⟨fun h => ⟨h.1, h.grade _⟩,
    And.imp_right fun h c ha hb => h.2 (grade_strictMono ha) <| grade_strictMono hb⟩
#align covby_iff_lt_covby_grade covby_iff_lt_covby_grade

end GradeOrder

section GradeMinOrder

variable (𝕆) [GradeMinOrder 𝕆 α] {a : α}

/- warning: is_min.grade -> IsMin.grade is a dubious translation:
lean 3 declaration is
  forall (𝕆 : Type.{u1}) {α : Type.{u2}} [_inst_1 : Preorder.{u1} 𝕆] [_inst_2 : Preorder.{u2} α] [_inst_3 : GradeMinOrder.{u1, u2} 𝕆 α _inst_1 _inst_2] {a : α}, (IsMin.{u2} α (Preorder.toLE.{u2} α _inst_2) a) -> (IsMin.{u1} 𝕆 (Preorder.toLE.{u1} 𝕆 _inst_1) (grade.{u1, u2} 𝕆 α _inst_1 _inst_2 (GradeMinOrder.toGradeOrder.{u1, u2} 𝕆 α _inst_1 _inst_2 _inst_3) a))
but is expected to have type
  forall (𝕆 : Type.{u1}) {α : Type.{u2}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} 𝕆] [_inst_3 : GradeMinOrder.{u1, u2} 𝕆 α _inst_2 _inst_1] {a : α}, (IsMin.{u2} α (Preorder.toLE.{u2} α _inst_1) a) -> (IsMin.{u1} 𝕆 (Preorder.toLE.{u1} 𝕆 _inst_2) (grade.{u1, u2} 𝕆 α _inst_1 _inst_2 (GradeMinOrder.toGradeOrder.{u1, u2} 𝕆 α _inst_2 _inst_1 _inst_3) a))
Case conversion may be inaccurate. Consider using '#align is_min.grade IsMin.gradeₓ'. -/
protected theorem IsMin.grade (h : IsMin a) : IsMin (grade 𝕆 a) :=
  GradeMinOrder.isMin_grade h
#align is_min.grade IsMin.grade

variable {𝕆}

/- warning: is_min_grade_iff -> isMin_grade_iff is a dubious translation:
lean 3 declaration is
  forall {𝕆 : Type.{u1}} {α : Type.{u2}} [_inst_1 : Preorder.{u1} 𝕆] [_inst_2 : Preorder.{u2} α] [_inst_3 : GradeMinOrder.{u1, u2} 𝕆 α _inst_1 _inst_2] {a : α}, Iff (IsMin.{u1} 𝕆 (Preorder.toLE.{u1} 𝕆 _inst_1) (grade.{u1, u2} 𝕆 α _inst_1 _inst_2 (GradeMinOrder.toGradeOrder.{u1, u2} 𝕆 α _inst_1 _inst_2 _inst_3) a)) (IsMin.{u2} α (Preorder.toLE.{u2} α _inst_2) a)
but is expected to have type
  forall {𝕆 : Type.{u2}} {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} 𝕆] [_inst_3 : GradeMinOrder.{u2, u1} 𝕆 α _inst_2 _inst_1] {a : α}, Iff (IsMin.{u2} 𝕆 (Preorder.toLE.{u2} 𝕆 _inst_2) (grade.{u2, u1} 𝕆 α _inst_1 _inst_2 (GradeMinOrder.toGradeOrder.{u2, u1} 𝕆 α _inst_2 _inst_1 _inst_3) a)) (IsMin.{u1} α (Preorder.toLE.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align is_min_grade_iff isMin_grade_iffₓ'. -/
@[simp]
theorem isMin_grade_iff : IsMin (grade 𝕆 a) ↔ IsMin a :=
  ⟨grade_strictMono.isMin_of_apply, IsMin.grade _⟩
#align is_min_grade_iff isMin_grade_iff

end GradeMinOrder

section GradeMaxOrder

variable (𝕆) [GradeMaxOrder 𝕆 α] {a : α}

/- warning: is_max.grade -> IsMax.grade is a dubious translation:
lean 3 declaration is
  forall (𝕆 : Type.{u1}) {α : Type.{u2}} [_inst_1 : Preorder.{u1} 𝕆] [_inst_2 : Preorder.{u2} α] [_inst_3 : GradeMaxOrder.{u1, u2} 𝕆 α _inst_1 _inst_2] {a : α}, (IsMax.{u2} α (Preorder.toLE.{u2} α _inst_2) a) -> (IsMax.{u1} 𝕆 (Preorder.toLE.{u1} 𝕆 _inst_1) (grade.{u1, u2} 𝕆 α _inst_1 _inst_2 (GradeMaxOrder.toGradeOrder.{u1, u2} 𝕆 α _inst_1 _inst_2 _inst_3) a))
but is expected to have type
  forall (𝕆 : Type.{u1}) {α : Type.{u2}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} 𝕆] [_inst_3 : GradeMaxOrder.{u1, u2} 𝕆 α _inst_2 _inst_1] {a : α}, (IsMax.{u2} α (Preorder.toLE.{u2} α _inst_1) a) -> (IsMax.{u1} 𝕆 (Preorder.toLE.{u1} 𝕆 _inst_2) (grade.{u1, u2} 𝕆 α _inst_1 _inst_2 (GradeMaxOrder.toGradeOrder.{u1, u2} 𝕆 α _inst_2 _inst_1 _inst_3) a))
Case conversion may be inaccurate. Consider using '#align is_max.grade IsMax.gradeₓ'. -/
protected theorem IsMax.grade (h : IsMax a) : IsMax (grade 𝕆 a) :=
  GradeMaxOrder.isMax_grade h
#align is_max.grade IsMax.grade

variable {𝕆}

/- warning: is_max_grade_iff -> isMax_grade_iff is a dubious translation:
lean 3 declaration is
  forall {𝕆 : Type.{u1}} {α : Type.{u2}} [_inst_1 : Preorder.{u1} 𝕆] [_inst_2 : Preorder.{u2} α] [_inst_3 : GradeMaxOrder.{u1, u2} 𝕆 α _inst_1 _inst_2] {a : α}, Iff (IsMax.{u1} 𝕆 (Preorder.toLE.{u1} 𝕆 _inst_1) (grade.{u1, u2} 𝕆 α _inst_1 _inst_2 (GradeMaxOrder.toGradeOrder.{u1, u2} 𝕆 α _inst_1 _inst_2 _inst_3) a)) (IsMax.{u2} α (Preorder.toLE.{u2} α _inst_2) a)
but is expected to have type
  forall {𝕆 : Type.{u2}} {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} 𝕆] [_inst_3 : GradeMaxOrder.{u2, u1} 𝕆 α _inst_2 _inst_1] {a : α}, Iff (IsMax.{u2} 𝕆 (Preorder.toLE.{u2} 𝕆 _inst_2) (grade.{u2, u1} 𝕆 α _inst_1 _inst_2 (GradeMaxOrder.toGradeOrder.{u2, u1} 𝕆 α _inst_2 _inst_1 _inst_3) a)) (IsMax.{u1} α (Preorder.toLE.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align is_max_grade_iff isMax_grade_iffₓ'. -/
@[simp]
theorem isMax_grade_iff : IsMax (grade 𝕆 a) ↔ IsMax a :=
  ⟨grade_strictMono.isMax_of_apply, IsMax.grade _⟩
#align is_max_grade_iff isMax_grade_iff

end GradeMaxOrder

end Preorder

/- warning: grade_mono -> grade_mono is a dubious translation:
lean 3 declaration is
  forall {𝕆 : Type.{u1}} {α : Type.{u2}} [_inst_1 : Preorder.{u1} 𝕆] [_inst_2 : PartialOrder.{u2} α] [_inst_3 : GradeOrder.{u1, u2} 𝕆 α _inst_1 (PartialOrder.toPreorder.{u2} α _inst_2)], Monotone.{u2, u1} α 𝕆 (PartialOrder.toPreorder.{u2} α _inst_2) _inst_1 (grade.{u1, u2} 𝕆 α _inst_1 (PartialOrder.toPreorder.{u2} α _inst_2) _inst_3)
but is expected to have type
  forall {𝕆 : Type.{u1}} {α : Type.{u2}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : Preorder.{u1} 𝕆] [_inst_3 : GradeOrder.{u1, u2} 𝕆 α _inst_2 (PartialOrder.toPreorder.{u2} α _inst_1)], Monotone.{u2, u1} α 𝕆 (PartialOrder.toPreorder.{u2} α _inst_1) _inst_2 (grade.{u1, u2} 𝕆 α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_2 _inst_3)
Case conversion may be inaccurate. Consider using '#align grade_mono grade_monoₓ'. -/
-- graded order
theorem grade_mono [PartialOrder α] [GradeOrder 𝕆 α] : Monotone (grade 𝕆 : α → 𝕆) :=
  grade_strictMono.Monotone
#align grade_mono grade_mono

section LinearOrder

-- graded order
variable [LinearOrder α] [GradeOrder 𝕆 α] {a b : α}

/- warning: grade_injective -> grade_injective is a dubious translation:
lean 3 declaration is
  forall {𝕆 : Type.{u1}} {α : Type.{u2}} [_inst_1 : Preorder.{u1} 𝕆] [_inst_2 : LinearOrder.{u2} α] [_inst_3 : GradeOrder.{u1, u2} 𝕆 α _inst_1 (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (LinearOrder.toLattice.{u2} α _inst_2))))], Function.Injective.{succ u2, succ u1} α 𝕆 (grade.{u1, u2} 𝕆 α _inst_1 (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (LinearOrder.toLattice.{u2} α _inst_2)))) _inst_3)
but is expected to have type
  forall {𝕆 : Type.{u1}} {α : Type.{u2}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : Preorder.{u1} 𝕆] [_inst_3 : GradeOrder.{u1, u2} 𝕆 α _inst_2 (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))], Function.Injective.{succ u2, succ u1} α 𝕆 (grade.{u1, u2} 𝕆 α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) _inst_2 _inst_3)
Case conversion may be inaccurate. Consider using '#align grade_injective grade_injectiveₓ'. -/
theorem grade_injective : Function.Injective (grade 𝕆 : α → 𝕆) :=
  grade_strictMono.Injective
#align grade_injective grade_injective

/- warning: grade_le_grade_iff -> grade_le_grade_iff is a dubious translation:
lean 3 declaration is
  forall {𝕆 : Type.{u1}} {α : Type.{u2}} [_inst_1 : Preorder.{u1} 𝕆] [_inst_2 : LinearOrder.{u2} α] [_inst_3 : GradeOrder.{u1, u2} 𝕆 α _inst_1 (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (LinearOrder.toLattice.{u2} α _inst_2))))] {a : α} {b : α}, Iff (LE.le.{u1} 𝕆 (Preorder.toLE.{u1} 𝕆 _inst_1) (grade.{u1, u2} 𝕆 α _inst_1 (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (LinearOrder.toLattice.{u2} α _inst_2)))) _inst_3 a) (grade.{u1, u2} 𝕆 α _inst_1 (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (LinearOrder.toLattice.{u2} α _inst_2)))) _inst_3 b)) (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (LinearOrder.toLattice.{u2} α _inst_2))))) a b)
but is expected to have type
  forall {𝕆 : Type.{u2}} {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : Preorder.{u2} 𝕆] [_inst_3 : GradeOrder.{u2, u1} 𝕆 α _inst_2 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))] {a : α} {b : α}, Iff (LE.le.{u2} 𝕆 (Preorder.toLE.{u2} 𝕆 _inst_2) (grade.{u2, u1} 𝕆 α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 _inst_3 a) (grade.{u2, u1} 𝕆 α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 _inst_3 b)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a b)
Case conversion may be inaccurate. Consider using '#align grade_le_grade_iff grade_le_grade_iffₓ'. -/
@[simp]
theorem grade_le_grade_iff : grade 𝕆 a ≤ grade 𝕆 b ↔ a ≤ b :=
  grade_strictMono.le_iff_le
#align grade_le_grade_iff grade_le_grade_iff

/- warning: grade_lt_grade_iff -> grade_lt_grade_iff is a dubious translation:
lean 3 declaration is
  forall {𝕆 : Type.{u1}} {α : Type.{u2}} [_inst_1 : Preorder.{u1} 𝕆] [_inst_2 : LinearOrder.{u2} α] [_inst_3 : GradeOrder.{u1, u2} 𝕆 α _inst_1 (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (LinearOrder.toLattice.{u2} α _inst_2))))] {a : α} {b : α}, Iff (LT.lt.{u1} 𝕆 (Preorder.toLT.{u1} 𝕆 _inst_1) (grade.{u1, u2} 𝕆 α _inst_1 (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (LinearOrder.toLattice.{u2} α _inst_2)))) _inst_3 a) (grade.{u1, u2} 𝕆 α _inst_1 (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (LinearOrder.toLattice.{u2} α _inst_2)))) _inst_3 b)) (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (LinearOrder.toLattice.{u2} α _inst_2))))) a b)
but is expected to have type
  forall {𝕆 : Type.{u2}} {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : Preorder.{u2} 𝕆] [_inst_3 : GradeOrder.{u2, u1} 𝕆 α _inst_2 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))] {a : α} {b : α}, Iff (LT.lt.{u2} 𝕆 (Preorder.toLT.{u2} 𝕆 _inst_2) (grade.{u2, u1} 𝕆 α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 _inst_3 a) (grade.{u2, u1} 𝕆 α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 _inst_3 b)) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a b)
Case conversion may be inaccurate. Consider using '#align grade_lt_grade_iff grade_lt_grade_iffₓ'. -/
@[simp]
theorem grade_lt_grade_iff : grade 𝕆 a < grade 𝕆 b ↔ a < b :=
  grade_strictMono.lt_iff_lt
#align grade_lt_grade_iff grade_lt_grade_iff

/- warning: grade_eq_grade_iff -> grade_eq_grade_iff is a dubious translation:
lean 3 declaration is
  forall {𝕆 : Type.{u1}} {α : Type.{u2}} [_inst_1 : Preorder.{u1} 𝕆] [_inst_2 : LinearOrder.{u2} α] [_inst_3 : GradeOrder.{u1, u2} 𝕆 α _inst_1 (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (LinearOrder.toLattice.{u2} α _inst_2))))] {a : α} {b : α}, Iff (Eq.{succ u1} 𝕆 (grade.{u1, u2} 𝕆 α _inst_1 (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (LinearOrder.toLattice.{u2} α _inst_2)))) _inst_3 a) (grade.{u1, u2} 𝕆 α _inst_1 (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (LinearOrder.toLattice.{u2} α _inst_2)))) _inst_3 b)) (Eq.{succ u2} α a b)
but is expected to have type
  forall {𝕆 : Type.{u2}} {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : Preorder.{u2} 𝕆] [_inst_3 : GradeOrder.{u2, u1} 𝕆 α _inst_2 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))] {a : α} {b : α}, Iff (Eq.{succ u2} 𝕆 (grade.{u2, u1} 𝕆 α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 _inst_3 a) (grade.{u2, u1} 𝕆 α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 _inst_3 b)) (Eq.{succ u1} α a b)
Case conversion may be inaccurate. Consider using '#align grade_eq_grade_iff grade_eq_grade_iffₓ'. -/
@[simp]
theorem grade_eq_grade_iff : grade 𝕆 a = grade 𝕆 b ↔ a = b :=
  grade_injective.eq_iff
#align grade_eq_grade_iff grade_eq_grade_iff

/- warning: grade_ne_grade_iff -> grade_ne_grade_iff is a dubious translation:
lean 3 declaration is
  forall {𝕆 : Type.{u1}} {α : Type.{u2}} [_inst_1 : Preorder.{u1} 𝕆] [_inst_2 : LinearOrder.{u2} α] [_inst_3 : GradeOrder.{u1, u2} 𝕆 α _inst_1 (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (LinearOrder.toLattice.{u2} α _inst_2))))] {a : α} {b : α}, Iff (Ne.{succ u1} 𝕆 (grade.{u1, u2} 𝕆 α _inst_1 (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (LinearOrder.toLattice.{u2} α _inst_2)))) _inst_3 a) (grade.{u1, u2} 𝕆 α _inst_1 (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (LinearOrder.toLattice.{u2} α _inst_2)))) _inst_3 b)) (Ne.{succ u2} α a b)
but is expected to have type
  forall {𝕆 : Type.{u2}} {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : Preorder.{u2} 𝕆] [_inst_3 : GradeOrder.{u2, u1} 𝕆 α _inst_2 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))] {a : α} {b : α}, Iff (Ne.{succ u2} 𝕆 (grade.{u2, u1} 𝕆 α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 _inst_3 a) (grade.{u2, u1} 𝕆 α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 _inst_3 b)) (Ne.{succ u1} α a b)
Case conversion may be inaccurate. Consider using '#align grade_ne_grade_iff grade_ne_grade_iffₓ'. -/
theorem grade_ne_grade_iff : grade 𝕆 a ≠ grade 𝕆 b ↔ a ≠ b :=
  grade_injective.ne_iff
#align grade_ne_grade_iff grade_ne_grade_iff

/- warning: grade_covby_grade_iff -> grade_covby_grade_iff is a dubious translation:
lean 3 declaration is
  forall {𝕆 : Type.{u1}} {α : Type.{u2}} [_inst_1 : Preorder.{u1} 𝕆] [_inst_2 : LinearOrder.{u2} α] [_inst_3 : GradeOrder.{u1, u2} 𝕆 α _inst_1 (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (LinearOrder.toLattice.{u2} α _inst_2))))] {a : α} {b : α}, Iff (Covby.{u1} 𝕆 (Preorder.toLT.{u1} 𝕆 _inst_1) (grade.{u1, u2} 𝕆 α _inst_1 (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (LinearOrder.toLattice.{u2} α _inst_2)))) _inst_3 a) (grade.{u1, u2} 𝕆 α _inst_1 (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (LinearOrder.toLattice.{u2} α _inst_2)))) _inst_3 b)) (Covby.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (LinearOrder.toLattice.{u2} α _inst_2))))) a b)
but is expected to have type
  forall {𝕆 : Type.{u2}} {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : Preorder.{u2} 𝕆] [_inst_3 : GradeOrder.{u2, u1} 𝕆 α _inst_2 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))] {a : α} {b : α}, Iff (Covby.{u2} 𝕆 (Preorder.toLT.{u2} 𝕆 _inst_2) (grade.{u2, u1} 𝕆 α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 _inst_3 a) (grade.{u2, u1} 𝕆 α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 _inst_3 b)) (Covby.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a b)
Case conversion may be inaccurate. Consider using '#align grade_covby_grade_iff grade_covby_grade_iffₓ'. -/
theorem grade_covby_grade_iff : grade 𝕆 a ⋖ grade 𝕆 b ↔ a ⋖ b :=
  (covby_iff_lt_covby_grade.trans <| and_iff_right_of_imp fun h => grade_lt_grade_iff.1 h.1).symm
#align grade_covby_grade_iff grade_covby_grade_iff

end LinearOrder

-- graded order
end Preorder

-- grading
section PartialOrder

variable [PartialOrder 𝕆] [Preorder α]

/- warning: grade_bot -> grade_bot is a dubious translation:
lean 3 declaration is
  forall {𝕆 : Type.{u1}} {α : Type.{u2}} [_inst_1 : PartialOrder.{u1} 𝕆] [_inst_2 : Preorder.{u2} α] [_inst_3 : OrderBot.{u1} 𝕆 (Preorder.toLE.{u1} 𝕆 (PartialOrder.toPreorder.{u1} 𝕆 _inst_1))] [_inst_4 : OrderBot.{u2} α (Preorder.toLE.{u2} α _inst_2)] [_inst_5 : GradeMinOrder.{u1, u2} 𝕆 α (PartialOrder.toPreorder.{u1} 𝕆 _inst_1) _inst_2], Eq.{succ u1} 𝕆 (grade.{u1, u2} 𝕆 α (PartialOrder.toPreorder.{u1} 𝕆 _inst_1) _inst_2 (GradeMinOrder.toGradeOrder.{u1, u2} 𝕆 α (PartialOrder.toPreorder.{u1} 𝕆 _inst_1) _inst_2 _inst_5) (Bot.bot.{u2} α (OrderBot.toHasBot.{u2} α (Preorder.toLE.{u2} α _inst_2) _inst_4))) (Bot.bot.{u1} 𝕆 (OrderBot.toHasBot.{u1} 𝕆 (Preorder.toLE.{u1} 𝕆 (PartialOrder.toPreorder.{u1} 𝕆 _inst_1)) _inst_3))
but is expected to have type
  forall {𝕆 : Type.{u2}} {α : Type.{u1}} [_inst_1 : PartialOrder.{u2} 𝕆] [_inst_2 : Preorder.{u1} α] [_inst_3 : OrderBot.{u2} 𝕆 (Preorder.toLE.{u2} 𝕆 (PartialOrder.toPreorder.{u2} 𝕆 _inst_1))] [_inst_4 : OrderBot.{u1} α (Preorder.toLE.{u1} α _inst_2)] [_inst_5 : GradeMinOrder.{u2, u1} 𝕆 α (PartialOrder.toPreorder.{u2} 𝕆 _inst_1) _inst_2], Eq.{succ u2} 𝕆 (grade.{u2, u1} 𝕆 α _inst_2 (PartialOrder.toPreorder.{u2} 𝕆 _inst_1) (GradeMinOrder.toGradeOrder.{u2, u1} 𝕆 α (PartialOrder.toPreorder.{u2} 𝕆 _inst_1) _inst_2 _inst_5) (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α _inst_2) _inst_4))) (Bot.bot.{u2} 𝕆 (OrderBot.toBot.{u2} 𝕆 (Preorder.toLE.{u2} 𝕆 (PartialOrder.toPreorder.{u2} 𝕆 _inst_1)) _inst_3))
Case conversion may be inaccurate. Consider using '#align grade_bot grade_botₓ'. -/
@[simp]
theorem grade_bot [OrderBot 𝕆] [OrderBot α] [GradeMinOrder 𝕆 α] : grade 𝕆 (⊥ : α) = ⊥ :=
  (isMin_bot.grade _).eq_bot
#align grade_bot grade_bot

/- warning: grade_top -> grade_top is a dubious translation:
lean 3 declaration is
  forall {𝕆 : Type.{u1}} {α : Type.{u2}} [_inst_1 : PartialOrder.{u1} 𝕆] [_inst_2 : Preorder.{u2} α] [_inst_3 : OrderTop.{u1} 𝕆 (Preorder.toLE.{u1} 𝕆 (PartialOrder.toPreorder.{u1} 𝕆 _inst_1))] [_inst_4 : OrderTop.{u2} α (Preorder.toLE.{u2} α _inst_2)] [_inst_5 : GradeMaxOrder.{u1, u2} 𝕆 α (PartialOrder.toPreorder.{u1} 𝕆 _inst_1) _inst_2], Eq.{succ u1} 𝕆 (grade.{u1, u2} 𝕆 α (PartialOrder.toPreorder.{u1} 𝕆 _inst_1) _inst_2 (GradeMaxOrder.toGradeOrder.{u1, u2} 𝕆 α (PartialOrder.toPreorder.{u1} 𝕆 _inst_1) _inst_2 _inst_5) (Top.top.{u2} α (OrderTop.toHasTop.{u2} α (Preorder.toLE.{u2} α _inst_2) _inst_4))) (Top.top.{u1} 𝕆 (OrderTop.toHasTop.{u1} 𝕆 (Preorder.toLE.{u1} 𝕆 (PartialOrder.toPreorder.{u1} 𝕆 _inst_1)) _inst_3))
but is expected to have type
  forall {𝕆 : Type.{u2}} {α : Type.{u1}} [_inst_1 : PartialOrder.{u2} 𝕆] [_inst_2 : Preorder.{u1} α] [_inst_3 : OrderTop.{u2} 𝕆 (Preorder.toLE.{u2} 𝕆 (PartialOrder.toPreorder.{u2} 𝕆 _inst_1))] [_inst_4 : OrderTop.{u1} α (Preorder.toLE.{u1} α _inst_2)] [_inst_5 : GradeMaxOrder.{u2, u1} 𝕆 α (PartialOrder.toPreorder.{u2} 𝕆 _inst_1) _inst_2], Eq.{succ u2} 𝕆 (grade.{u2, u1} 𝕆 α _inst_2 (PartialOrder.toPreorder.{u2} 𝕆 _inst_1) (GradeMaxOrder.toGradeOrder.{u2, u1} 𝕆 α (PartialOrder.toPreorder.{u2} 𝕆 _inst_1) _inst_2 _inst_5) (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α _inst_2) _inst_4))) (Top.top.{u2} 𝕆 (OrderTop.toTop.{u2} 𝕆 (Preorder.toLE.{u2} 𝕆 (PartialOrder.toPreorder.{u2} 𝕆 _inst_1)) _inst_3))
Case conversion may be inaccurate. Consider using '#align grade_top grade_topₓ'. -/
@[simp]
theorem grade_top [OrderTop 𝕆] [OrderTop α] [GradeMaxOrder 𝕆 α] : grade 𝕆 (⊤ : α) = ⊤ :=
  (isMax_top.grade _).eq_top
#align grade_top grade_top

end PartialOrder

/-! ### Instances -/


variable [Preorder 𝕆] [Preorder ℙ] [Preorder α] [Preorder β]

#print Preorder.toGradeBoundedOrder /-
instance Preorder.toGradeBoundedOrder : GradeBoundedOrder α α
    where
  grade := id
  isMin_grade _ := id
  isMax_grade _ := id
  grade_strictMono := strictMono_id
  covby_grade a b := id
#align preorder.to_grade_bounded_order Preorder.toGradeBoundedOrder
-/

#print grade_self /-
@[simp]
theorem grade_self (a : α) : grade α a = a :=
  rfl
#align grade_self grade_self
-/

/-! #### Dual -/


instance [GradeOrder 𝕆 α] : GradeOrder 𝕆ᵒᵈ αᵒᵈ
    where
  grade := toDual ∘ grade 𝕆 ∘ ofDual
  grade_strictMono := grade_strictMono.dual
  covby_grade a b h := (h.ofDual.grade _).toDual

instance [GradeMaxOrder 𝕆 α] : GradeMinOrder 𝕆ᵒᵈ αᵒᵈ :=
  { OrderDual.gradeOrder with isMin_grade := fun _ => IsMax.grade _ }

instance [GradeMinOrder 𝕆 α] : GradeMaxOrder 𝕆ᵒᵈ αᵒᵈ :=
  { OrderDual.gradeOrder with isMax_grade := fun _ => IsMin.grade _ }

instance [GradeBoundedOrder 𝕆 α] : GradeBoundedOrder 𝕆ᵒᵈ αᵒᵈ :=
  { OrderDual.gradeMinOrder, OrderDual.gradeMaxOrder with }

/- warning: grade_to_dual -> grade_toDual is a dubious translation:
lean 3 declaration is
  forall {𝕆 : Type.{u1}} {α : Type.{u2}} [_inst_1 : Preorder.{u1} 𝕆] [_inst_3 : Preorder.{u2} α] [_inst_5 : GradeOrder.{u1, u2} 𝕆 α _inst_1 _inst_3] (a : α), Eq.{succ u1} (OrderDual.{u1} 𝕆) (grade.{u1, u2} (OrderDual.{u1} 𝕆) (OrderDual.{u2} α) (OrderDual.preorder.{u1} 𝕆 _inst_1) (OrderDual.preorder.{u2} α _inst_3) (OrderDual.gradeOrder.{u1, u2} 𝕆 α _inst_1 _inst_3 _inst_5) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (fun (_x : Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) => α -> (OrderDual.{u2} α)) (Equiv.hasCoeToFun.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α) a)) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} 𝕆 (OrderDual.{u1} 𝕆)) (fun (_x : Equiv.{succ u1, succ u1} 𝕆 (OrderDual.{u1} 𝕆)) => 𝕆 -> (OrderDual.{u1} 𝕆)) (Equiv.hasCoeToFun.{succ u1, succ u1} 𝕆 (OrderDual.{u1} 𝕆)) (OrderDual.toDual.{u1} 𝕆) (grade.{u1, u2} 𝕆 α _inst_1 _inst_3 _inst_5 a))
but is expected to have type
  forall {𝕆 : Type.{u2}} {α : Type.{u1}} [_inst_1 : Preorder.{u2} 𝕆] [_inst_3 : Preorder.{u1} α] [_inst_5 : GradeOrder.{u2, u1} 𝕆 α _inst_1 _inst_3] (a : α), Eq.{succ u2} (OrderDual.{u2} 𝕆) (grade.{u2, u1} (OrderDual.{u2} 𝕆) ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => OrderDual.{u1} α) a) (OrderDual.preorder.{u1} α _inst_3) (OrderDual.preorder.{u2} 𝕆 _inst_1) (OrderDual.gradeOrder.{u2, u1} 𝕆 α _inst_1 _inst_3 _inst_5) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => OrderDual.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α) a)) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} 𝕆 (OrderDual.{u2} 𝕆)) 𝕆 (fun (_x : 𝕆) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : 𝕆) => OrderDual.{u2} 𝕆) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} 𝕆 (OrderDual.{u2} 𝕆)) (OrderDual.toDual.{u2} 𝕆) (grade.{u2, u1} 𝕆 α _inst_3 _inst_1 _inst_5 a))
Case conversion may be inaccurate. Consider using '#align grade_to_dual grade_toDualₓ'. -/
@[simp]
theorem grade_toDual [GradeOrder 𝕆 α] (a : α) : grade 𝕆ᵒᵈ (toDual a) = toDual (grade 𝕆 a) :=
  rfl
#align grade_to_dual grade_toDual

/- warning: grade_of_dual -> grade_ofDual is a dubious translation:
lean 3 declaration is
  forall {𝕆 : Type.{u1}} {α : Type.{u2}} [_inst_1 : Preorder.{u1} 𝕆] [_inst_3 : Preorder.{u2} α] [_inst_5 : GradeOrder.{u1, u2} 𝕆 α _inst_1 _inst_3] (a : OrderDual.{u2} α), Eq.{succ u1} 𝕆 (grade.{u1, u2} 𝕆 α _inst_1 _inst_3 _inst_5 (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (fun (_x : Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) => (OrderDual.{u2} α) -> α) (Equiv.hasCoeToFun.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.ofDual.{u2} α) a)) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} 𝕆) 𝕆) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} 𝕆) 𝕆) => (OrderDual.{u1} 𝕆) -> 𝕆) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} 𝕆) 𝕆) (OrderDual.ofDual.{u1} 𝕆) (grade.{u1, u2} (OrderDual.{u1} 𝕆) (OrderDual.{u2} α) (OrderDual.preorder.{u1} 𝕆 _inst_1) (OrderDual.preorder.{u2} α _inst_3) (OrderDual.gradeOrder.{u1, u2} 𝕆 α _inst_1 _inst_3 _inst_5) a))
but is expected to have type
  forall {𝕆 : Type.{u2}} {α : Type.{u1}} [_inst_1 : Preorder.{u2} 𝕆] [_inst_3 : Preorder.{u1} α] [_inst_5 : GradeOrder.{u2, u1} 𝕆 α _inst_1 _inst_3] (a : OrderDual.{u1} α), Eq.{succ u2} 𝕆 (grade.{u2, u1} 𝕆 ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : OrderDual.{u1} α) => α) a) _inst_3 _inst_1 _inst_5 (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.{u1} α) (fun (_x : OrderDual.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : OrderDual.{u1} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α) a)) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} 𝕆) 𝕆) (OrderDual.{u2} 𝕆) (fun (_x : OrderDual.{u2} 𝕆) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : OrderDual.{u2} 𝕆) => 𝕆) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} (OrderDual.{u2} 𝕆) 𝕆) (OrderDual.ofDual.{u2} 𝕆) (grade.{u2, u1} (OrderDual.{u2} 𝕆) (OrderDual.{u1} α) (OrderDual.preorder.{u1} α _inst_3) (OrderDual.preorder.{u2} 𝕆 _inst_1) (OrderDual.gradeOrder.{u2, u1} 𝕆 α _inst_1 _inst_3 _inst_5) a))
Case conversion may be inaccurate. Consider using '#align grade_of_dual grade_ofDualₓ'. -/
@[simp]
theorem grade_ofDual [GradeOrder 𝕆 α] (a : αᵒᵈ) : grade 𝕆 (ofDual a) = ofDual (grade 𝕆ᵒᵈ a) :=
  rfl
#align grade_of_dual grade_ofDual

/-! #### Lifting a graded order -/


#print GradeOrder.liftLeft /-
-- See note [reducible non-instances]
/-- Lifts a graded order along a strictly monotone function. -/
@[reducible]
def GradeOrder.liftLeft [GradeOrder 𝕆 α] (f : 𝕆 → ℙ) (hf : StrictMono f)
    (hcovby : ∀ a b, a ⋖ b → f a ⋖ f b) : GradeOrder ℙ α
    where
  grade := f ∘ grade 𝕆
  grade_strictMono := hf.comp grade_strictMono
  covby_grade a b h := hcovby _ _ <| h.grade _
#align grade_order.lift_left GradeOrder.liftLeft
-/

#print GradeMinOrder.liftLeft /-
-- See note [reducible non-instances]
/-- Lifts a graded order along a strictly monotone function. -/
@[reducible]
def GradeMinOrder.liftLeft [GradeMinOrder 𝕆 α] (f : 𝕆 → ℙ) (hf : StrictMono f)
    (hcovby : ∀ a b, a ⋖ b → f a ⋖ f b) (hmin : ∀ a, IsMin a → IsMin (f a)) : GradeMinOrder ℙ α :=
  { GradeOrder.liftLeft f hf hcovby with isMin_grade := fun a ha => hmin _ <| ha.grade _ }
#align grade_min_order.lift_left GradeMinOrder.liftLeft
-/

#print GradeMaxOrder.liftLeft /-
-- See note [reducible non-instances]
/-- Lifts a graded order along a strictly monotone function. -/
@[reducible]
def GradeMaxOrder.liftLeft [GradeMaxOrder 𝕆 α] (f : 𝕆 → ℙ) (hf : StrictMono f)
    (hcovby : ∀ a b, a ⋖ b → f a ⋖ f b) (hmax : ∀ a, IsMax a → IsMax (f a)) : GradeMaxOrder ℙ α :=
  { GradeOrder.liftLeft f hf hcovby with isMax_grade := fun a ha => hmax _ <| ha.grade _ }
#align grade_max_order.lift_left GradeMaxOrder.liftLeft
-/

#print GradeBoundedOrder.liftLeft /-
-- See note [reducible non-instances]
/-- Lifts a graded order along a strictly monotone function. -/
@[reducible]
def GradeBoundedOrder.liftLeft [GradeBoundedOrder 𝕆 α] (f : 𝕆 → ℙ) (hf : StrictMono f)
    (hcovby : ∀ a b, a ⋖ b → f a ⋖ f b) (hmin : ∀ a, IsMin a → IsMin (f a))
    (hmax : ∀ a, IsMax a → IsMax (f a)) : GradeBoundedOrder ℙ α :=
  { GradeMinOrder.liftLeft f hf hcovby hmin, GradeMaxOrder.liftLeft f hf hcovby hmax with }
#align grade_bounded_order.lift_left GradeBoundedOrder.liftLeft
-/

#print GradeOrder.liftRight /-
-- See note [reducible non-instances]
/-- Lifts a graded order along a strictly monotone function. -/
@[reducible]
def GradeOrder.liftRight [GradeOrder 𝕆 β] (f : α → β) (hf : StrictMono f)
    (hcovby : ∀ a b, a ⋖ b → f a ⋖ f b) : GradeOrder 𝕆 α
    where
  grade := grade 𝕆 ∘ f
  grade_strictMono := grade_strictMono.comp hf
  covby_grade a b h := (hcovby _ _ h).grade _
#align grade_order.lift_right GradeOrder.liftRight
-/

#print GradeMinOrder.liftRight /-
-- See note [reducible non-instances]
/-- Lifts a graded order along a strictly monotone function. -/
@[reducible]
def GradeMinOrder.liftRight [GradeMinOrder 𝕆 β] (f : α → β) (hf : StrictMono f)
    (hcovby : ∀ a b, a ⋖ b → f a ⋖ f b) (hmin : ∀ a, IsMin a → IsMin (f a)) : GradeMinOrder 𝕆 α :=
  { GradeOrder.liftRight f hf hcovby with isMin_grade := fun a ha => (hmin _ ha).grade _ }
#align grade_min_order.lift_right GradeMinOrder.liftRight
-/

#print GradeMaxOrder.liftRight /-
-- See note [reducible non-instances]
/-- Lifts a graded order along a strictly monotone function. -/
@[reducible]
def GradeMaxOrder.liftRight [GradeMaxOrder 𝕆 β] (f : α → β) (hf : StrictMono f)
    (hcovby : ∀ a b, a ⋖ b → f a ⋖ f b) (hmax : ∀ a, IsMax a → IsMax (f a)) : GradeMaxOrder 𝕆 α :=
  { GradeOrder.liftRight f hf hcovby with isMax_grade := fun a ha => (hmax _ ha).grade _ }
#align grade_max_order.lift_right GradeMaxOrder.liftRight
-/

#print GradeBoundedOrder.liftRight /-
-- See note [reducible non-instances]
/-- Lifts a graded order along a strictly monotone function. -/
@[reducible]
def GradeBoundedOrder.liftRight [GradeBoundedOrder 𝕆 β] (f : α → β) (hf : StrictMono f)
    (hcovby : ∀ a b, a ⋖ b → f a ⋖ f b) (hmin : ∀ a, IsMin a → IsMin (f a))
    (hmax : ∀ a, IsMax a → IsMax (f a)) : GradeBoundedOrder 𝕆 α :=
  { GradeMinOrder.liftRight f hf hcovby hmin, GradeMaxOrder.liftRight f hf hcovby hmax with }
#align grade_bounded_order.lift_right GradeBoundedOrder.liftRight
-/

/-! #### `fin n`-graded to `ℕ`-graded to `ℤ`-graded -/


/- warning: grade_order.fin_to_nat -> GradeOrder.finToNat is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_3 : Preorder.{u1} α] (n : Nat) [_inst_5 : GradeOrder.{0, u1} (Fin n) α (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) _inst_3], GradeOrder.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) _inst_3
but is expected to have type
  forall {α : Type.{u1}} [_inst_3 : Preorder.{u1} α] (n : Nat) [_inst_5 : GradeOrder.{0, u1} (Fin n) α (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) _inst_3], GradeOrder.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) _inst_3
Case conversion may be inaccurate. Consider using '#align grade_order.fin_to_nat GradeOrder.finToNatₓ'. -/
-- See note [reducible non-instances]
/-- A `fin n`-graded order is also `ℕ`-graded. We do not mark this an instance because `n` is not
inferrable. -/
@[reducible]
def GradeOrder.finToNat (n : ℕ) [GradeOrder (Fin n) α] : GradeOrder ℕ α :=
  GradeOrder.liftLeft (_ : Fin n → ℕ) Fin.val_strictMono fun _ _ => Covby.coe_fin
#align grade_order.fin_to_nat GradeOrder.finToNat

/- warning: grade_min_order.fin_to_nat -> GradeMinOrder.finToNat is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_3 : Preorder.{u1} α] (n : Nat) [_inst_5 : GradeMinOrder.{0, u1} (Fin n) α (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) _inst_3], GradeMinOrder.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) _inst_3
but is expected to have type
  forall {α : Type.{u1}} [_inst_3 : Preorder.{u1} α] (n : Nat) [_inst_5 : GradeMinOrder.{0, u1} (Fin n) α (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) _inst_3], GradeMinOrder.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) _inst_3
Case conversion may be inaccurate. Consider using '#align grade_min_order.fin_to_nat GradeMinOrder.finToNatₓ'. -/
-- See note [reducible non-instances]
/-- A `fin n`-graded order is also `ℕ`-graded. We do not mark this an instance because `n` is not
inferrable. -/
@[reducible]
def GradeMinOrder.finToNat (n : ℕ) [GradeMinOrder (Fin n) α] : GradeMinOrder ℕ α :=
  GradeMinOrder.liftLeft (_ : Fin n → ℕ) Fin.val_strictMono (fun _ _ => Covby.coe_fin) fun a h =>
    by
    cases n
    · exact ((@Fin.elim0 fun _ => False) <| grade (Fin 0) a).elim
    rw [h.eq_bot, Fin.bot_eq_zero]
    exact isMin_bot
#align grade_min_order.fin_to_nat GradeMinOrder.finToNat

#print GradeOrder.natToInt /-
instance GradeOrder.natToInt [GradeOrder ℕ α] : GradeOrder ℤ α :=
  GradeOrder.liftLeft _ Int.coe_nat_strictMono fun _ _ => Covby.cast_int
#align grade_order.nat_to_int GradeOrder.natToInt
-/

