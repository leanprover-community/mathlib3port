/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Johannes Hölzl, Reid Barton

! This file was ported from Lean 3 source module category_theory.category.preorder
! leanprover-community/mathlib commit e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Equivalence
import Mathbin.Order.Hom.Basic

/-!

# Preorders as categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We install a category instance on any preorder. This is not to be confused with the category _of_
preorders, defined in `order/category/Preorder`.

We show that monotone functions between preorders correspond to functors of the associated
categories.

## Main definitions

* `hom_of_le` and `le_of_hom` provide translations between inequalities in the preorder, and
  morphisms in the associated category.
* `monotone.functor` is the functor associated to a monotone function.

-/


universe u v

namespace Preorder

open CategoryTheory

#print Preorder.smallCategory /-
-- see Note [lower instance priority]
/--
The category structure coming from a preorder. There is a morphism `X ⟶ Y` if and only if `X ≤ Y`.

Because we don't allow morphisms to live in `Prop`,
we have to define `X ⟶ Y` as `ulift (plift (X ≤ Y))`.
See `category_theory.hom_of_le` and `category_theory.le_of_hom`.

See <https://stacks.math.columbia.edu/tag/00D3>.
-/
instance (priority := 100) smallCategory (α : Type u) [Preorder α] : SmallCategory α
    where
  Hom U V := ULift (PLift (U ≤ V))
  id X := ⟨⟨le_refl X⟩⟩
  comp X Y Z f g := ⟨⟨le_trans _ _ _ f.down.down g.down.down⟩⟩
#align preorder.small_category Preorder.smallCategory
-/

end Preorder

namespace CategoryTheory

open Opposite

variable {X : Type u} [Preorder X]

/- warning: category_theory.hom_of_le -> CategoryTheory.homOfLE is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : Preorder.{u1} X] {x : X} {y : X}, (LE.le.{u1} X (Preorder.toHasLe.{u1} X _inst_1) x y) -> (Quiver.Hom.{succ u1, u1} X (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} X (CategoryTheory.Category.toCategoryStruct.{u1, u1} X (Preorder.smallCategory.{u1} X _inst_1))) x y)
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : Preorder.{u1} X] {x : X} {y : X}, (LE.le.{u1} X (Preorder.toLE.{u1} X _inst_1) x y) -> (Quiver.Hom.{succ u1, u1} X (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} X (CategoryTheory.Category.toCategoryStruct.{u1, u1} X (Preorder.smallCategory.{u1} X _inst_1))) x y)
Case conversion may be inaccurate. Consider using '#align category_theory.hom_of_le CategoryTheory.homOfLEₓ'. -/
/-- Express an inequality as a morphism in the corresponding preorder category.
-/
def homOfLE {x y : X} (h : x ≤ y) : x ⟶ y :=
  ULift.up (PLift.up h)
#align category_theory.hom_of_le CategoryTheory.homOfLE

/- warning: has_le.le.hom -> LE.le.hom is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : Preorder.{u1} X] {x : X} {y : X}, (LE.le.{u1} X (Preorder.toHasLe.{u1} X _inst_1) x y) -> (Quiver.Hom.{succ u1, u1} X (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} X (CategoryTheory.Category.toCategoryStruct.{u1, u1} X (Preorder.smallCategory.{u1} X _inst_1))) x y)
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : Preorder.{u1} X] {x : X} {y : X}, (LE.le.{u1} X (Preorder.toLE.{u1} X _inst_1) x y) -> (Quiver.Hom.{succ u1, u1} X (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} X (CategoryTheory.Category.toCategoryStruct.{u1, u1} X (Preorder.smallCategory.{u1} X _inst_1))) x y)
Case conversion may be inaccurate. Consider using '#align has_le.le.hom LE.le.homₓ'. -/
alias hom_of_le ← _root_.has_le.le.hom
#align has_le.le.hom LE.le.hom

#print CategoryTheory.homOfLE_refl /-
@[simp]
theorem homOfLE_refl {x : X} : (le_refl x).Hom = 𝟙 x :=
  rfl
#align category_theory.hom_of_le_refl CategoryTheory.homOfLE_refl
-/

/- warning: category_theory.hom_of_le_comp -> CategoryTheory.homOfLE_comp is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : Preorder.{u1} X] {x : X} {y : X} {z : X} (h : LE.le.{u1} X (Preorder.toHasLe.{u1} X _inst_1) x y) (k : LE.le.{u1} X (Preorder.toHasLe.{u1} X _inst_1) y z), Eq.{succ u1} (Quiver.Hom.{succ u1, u1} X (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} X (CategoryTheory.Category.toCategoryStruct.{u1, u1} X (Preorder.smallCategory.{u1} X _inst_1))) x z) (CategoryTheory.CategoryStruct.comp.{u1, u1} X (CategoryTheory.Category.toCategoryStruct.{u1, u1} X (Preorder.smallCategory.{u1} X _inst_1)) x y z (LE.le.hom.{u1} X _inst_1 x y h) (LE.le.hom.{u1} X _inst_1 y z k)) (LE.le.hom.{u1} X _inst_1 x z (LE.le.trans.{u1} X _inst_1 x y z h k))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : Preorder.{u1} X] {x : X} {y : X} {z : X} (h : LE.le.{u1} X (Preorder.toLE.{u1} X _inst_1) x y) (k : LE.le.{u1} X (Preorder.toLE.{u1} X _inst_1) y z), Eq.{succ u1} (Quiver.Hom.{succ u1, u1} X (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} X (CategoryTheory.Category.toCategoryStruct.{u1, u1} X (Preorder.smallCategory.{u1} X _inst_1))) x z) (CategoryTheory.CategoryStruct.comp.{u1, u1} X (CategoryTheory.Category.toCategoryStruct.{u1, u1} X (Preorder.smallCategory.{u1} X _inst_1)) x y z (CategoryTheory.homOfLE.{u1} X _inst_1 x y h) (CategoryTheory.homOfLE.{u1} X _inst_1 y z k)) (CategoryTheory.homOfLE.{u1} X _inst_1 x z (LE.le.trans.{u1} X _inst_1 x y z h k))
Case conversion may be inaccurate. Consider using '#align category_theory.hom_of_le_comp CategoryTheory.homOfLE_compₓ'. -/
@[simp]
theorem homOfLE_comp {x y z : X} (h : x ≤ y) (k : y ≤ z) : h.Hom ≫ k.Hom = (h.trans k).Hom :=
  rfl
#align category_theory.hom_of_le_comp CategoryTheory.homOfLE_comp

/- warning: category_theory.le_of_hom -> CategoryTheory.leOfHom is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : Preorder.{u1} X] {x : X} {y : X}, (Quiver.Hom.{succ u1, u1} X (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} X (CategoryTheory.Category.toCategoryStruct.{u1, u1} X (Preorder.smallCategory.{u1} X _inst_1))) x y) -> (LE.le.{u1} X (Preorder.toHasLe.{u1} X _inst_1) x y)
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : Preorder.{u1} X] {x : X} {y : X}, (Quiver.Hom.{succ u1, u1} X (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} X (CategoryTheory.Category.toCategoryStruct.{u1, u1} X (Preorder.smallCategory.{u1} X _inst_1))) x y) -> (LE.le.{u1} X (Preorder.toLE.{u1} X _inst_1) x y)
Case conversion may be inaccurate. Consider using '#align category_theory.le_of_hom CategoryTheory.leOfHomₓ'. -/
/-- Extract the underlying inequality from a morphism in a preorder category.
-/
theorem leOfHom {x y : X} (h : x ⟶ y) : x ≤ y :=
  h.down.down
#align category_theory.le_of_hom CategoryTheory.leOfHom

/- warning: quiver.hom.le -> Quiver.Hom.le is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : Preorder.{u1} X] {x : X} {y : X}, (Quiver.Hom.{succ u1, u1} X (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} X (CategoryTheory.Category.toCategoryStruct.{u1, u1} X (Preorder.smallCategory.{u1} X _inst_1))) x y) -> (LE.le.{u1} X (Preorder.toHasLe.{u1} X _inst_1) x y)
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : Preorder.{u1} X] {x : X} {y : X}, (Quiver.Hom.{succ u1, u1} X (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} X (CategoryTheory.Category.toCategoryStruct.{u1, u1} X (Preorder.smallCategory.{u1} X _inst_1))) x y) -> (LE.le.{u1} X (Preorder.toLE.{u1} X _inst_1) x y)
Case conversion may be inaccurate. Consider using '#align quiver.hom.le Quiver.Hom.leₓ'. -/
alias le_of_hom ← _root_.quiver.hom.le
#align quiver.hom.le Quiver.Hom.le

/- warning: category_theory.le_of_hom_hom_of_le -> CategoryTheory.leOfHom_homOfLE is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : Preorder.{u1} X] {x : X} {y : X} (h : LE.le.{u1} X (Preorder.toHasLe.{u1} X _inst_1) x y), Eq.{0} (LE.le.{u1} X (Preorder.toHasLe.{u1} X _inst_1) x y) (Quiver.Hom.le.{u1} X _inst_1 x y (LE.le.hom.{u1} X _inst_1 x y h)) h
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : Preorder.{u1} X] {x : X} {y : X} (h : LE.le.{u1} X (Preorder.toLE.{u1} X _inst_1) x y), Eq.{0} (LE.le.{u1} X (Preorder.toLE.{u1} X _inst_1) x y) (Quiver.Hom.le.{u1} X _inst_1 x y (LE.le.hom.{u1} X _inst_1 x y h)) h
Case conversion may be inaccurate. Consider using '#align category_theory.le_of_hom_hom_of_le CategoryTheory.leOfHom_homOfLEₓ'. -/
@[simp]
theorem leOfHom_homOfLE {x y : X} (h : x ≤ y) : h.Hom.le = h :=
  rfl
#align category_theory.le_of_hom_hom_of_le CategoryTheory.leOfHom_homOfLE

#print CategoryTheory.homOfLE_leOfHom /-
@[simp]
theorem homOfLE_leOfHom {x y : X} (h : x ⟶ y) : h.le.Hom = h :=
  by
  cases h
  cases h
  rfl
#align category_theory.hom_of_le_le_of_hom CategoryTheory.homOfLE_leOfHom
-/

/- warning: category_theory.op_hom_of_le -> CategoryTheory.opHomOfLe is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : Preorder.{u1} X] {x : Opposite.{succ u1} X} {y : Opposite.{succ u1} X}, (LE.le.{u1} X (Preorder.toHasLe.{u1} X _inst_1) (Opposite.unop.{succ u1} X x) (Opposite.unop.{succ u1} X y)) -> (Quiver.Hom.{succ u1, u1} (Opposite.{succ u1} X) (Quiver.opposite.{u1, succ u1} X (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} X (CategoryTheory.Category.toCategoryStruct.{u1, u1} X (Preorder.smallCategory.{u1} X _inst_1)))) y x)
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : Preorder.{u1} X] {x : Opposite.{succ u1} X} {y : Opposite.{succ u1} X}, (LE.le.{u1} X (Preorder.toLE.{u1} X _inst_1) (Opposite.unop.{succ u1} X x) (Opposite.unop.{succ u1} X y)) -> (Quiver.Hom.{succ u1, u1} (Opposite.{succ u1} X) (Quiver.opposite.{u1, succ u1} X (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} X (CategoryTheory.Category.toCategoryStruct.{u1, u1} X (Preorder.smallCategory.{u1} X _inst_1)))) y x)
Case conversion may be inaccurate. Consider using '#align category_theory.op_hom_of_le CategoryTheory.opHomOfLeₓ'. -/
/-- Construct a morphism in the opposite of a preorder category from an inequality. -/
def opHomOfLe {x y : Xᵒᵖ} (h : unop x ≤ unop y) : y ⟶ x :=
  h.Hom.op
#align category_theory.op_hom_of_le CategoryTheory.opHomOfLe

/- warning: category_theory.le_of_op_hom -> CategoryTheory.le_of_op_hom is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : Preorder.{u1} X] {x : Opposite.{succ u1} X} {y : Opposite.{succ u1} X}, (Quiver.Hom.{succ u1, u1} (Opposite.{succ u1} X) (Quiver.opposite.{u1, succ u1} X (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} X (CategoryTheory.Category.toCategoryStruct.{u1, u1} X (Preorder.smallCategory.{u1} X _inst_1)))) x y) -> (LE.le.{u1} X (Preorder.toHasLe.{u1} X _inst_1) (Opposite.unop.{succ u1} X y) (Opposite.unop.{succ u1} X x))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : Preorder.{u1} X] {x : Opposite.{succ u1} X} {y : Opposite.{succ u1} X}, (Quiver.Hom.{succ u1, u1} (Opposite.{succ u1} X) (Quiver.opposite.{u1, succ u1} X (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} X (CategoryTheory.Category.toCategoryStruct.{u1, u1} X (Preorder.smallCategory.{u1} X _inst_1)))) x y) -> (LE.le.{u1} X (Preorder.toLE.{u1} X _inst_1) (Opposite.unop.{succ u1} X y) (Opposite.unop.{succ u1} X x))
Case conversion may be inaccurate. Consider using '#align category_theory.le_of_op_hom CategoryTheory.le_of_op_homₓ'. -/
theorem le_of_op_hom {x y : Xᵒᵖ} (h : x ⟶ y) : unop y ≤ unop x :=
  h.unop.le
#align category_theory.le_of_op_hom CategoryTheory.le_of_op_hom

/- warning: category_theory.unique_to_top -> CategoryTheory.uniqueToTop is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : Preorder.{u1} X] [_inst_2 : OrderTop.{u1} X (Preorder.toHasLe.{u1} X _inst_1)] {x : X}, Unique.{succ u1} (Quiver.Hom.{succ u1, u1} X (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} X (CategoryTheory.Category.toCategoryStruct.{u1, u1} X (Preorder.smallCategory.{u1} X _inst_1))) x (Top.top.{u1} X (OrderTop.toHasTop.{u1} X (Preorder.toHasLe.{u1} X _inst_1) _inst_2)))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : Preorder.{u1} X] [_inst_2 : OrderTop.{u1} X (Preorder.toLE.{u1} X _inst_1)] {x : X}, Unique.{succ u1} (Quiver.Hom.{succ u1, u1} X (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} X (CategoryTheory.Category.toCategoryStruct.{u1, u1} X (Preorder.smallCategory.{u1} X _inst_1))) x (Top.top.{u1} X (OrderTop.toTop.{u1} X (Preorder.toLE.{u1} X _inst_1) _inst_2)))
Case conversion may be inaccurate. Consider using '#align category_theory.unique_to_top CategoryTheory.uniqueToTopₓ'. -/
instance uniqueToTop [OrderTop X] {x : X} : Unique (x ⟶ ⊤) := by tidy
#align category_theory.unique_to_top CategoryTheory.uniqueToTop

/- warning: category_theory.unique_from_bot -> CategoryTheory.uniqueFromBot is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : Preorder.{u1} X] [_inst_2 : OrderBot.{u1} X (Preorder.toHasLe.{u1} X _inst_1)] {x : X}, Unique.{succ u1} (Quiver.Hom.{succ u1, u1} X (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} X (CategoryTheory.Category.toCategoryStruct.{u1, u1} X (Preorder.smallCategory.{u1} X _inst_1))) (Bot.bot.{u1} X (OrderBot.toHasBot.{u1} X (Preorder.toHasLe.{u1} X _inst_1) _inst_2)) x)
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : Preorder.{u1} X] [_inst_2 : OrderBot.{u1} X (Preorder.toLE.{u1} X _inst_1)] {x : X}, Unique.{succ u1} (Quiver.Hom.{succ u1, u1} X (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} X (CategoryTheory.Category.toCategoryStruct.{u1, u1} X (Preorder.smallCategory.{u1} X _inst_1))) (Bot.bot.{u1} X (OrderBot.toBot.{u1} X (Preorder.toLE.{u1} X _inst_1) _inst_2)) x)
Case conversion may be inaccurate. Consider using '#align category_theory.unique_from_bot CategoryTheory.uniqueFromBotₓ'. -/
instance uniqueFromBot [OrderBot X] {x : X} : Unique (⊥ ⟶ x) := by tidy
#align category_theory.unique_from_bot CategoryTheory.uniqueFromBot

end CategoryTheory

section

variable {X : Type u} {Y : Type v} [Preorder X] [Preorder Y]

#print Monotone.functor /-
/-- A monotone function between preorders induces a functor between the associated categories.
-/
def Monotone.functor {f : X → Y} (h : Monotone f) : X ⥤ Y
    where
  obj := f
  map x₁ x₂ g := (h g.le).Hom
#align monotone.functor Monotone.functor
-/

/- warning: monotone.functor_obj -> Monotone.functor_obj is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : Preorder.{u1} X] [_inst_2 : Preorder.{u2} Y] {f : X -> Y} (h : Monotone.{u1, u2} X Y _inst_1 _inst_2 f), Eq.{max (succ u1) (succ u2)} (X -> Y) (CategoryTheory.Functor.obj.{u1, u2, u1, u2} X (Preorder.smallCategory.{u1} X _inst_1) Y (Preorder.smallCategory.{u2} Y _inst_2) (Monotone.functor.{u1, u2} X Y _inst_1 _inst_2 f h)) f
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : Preorder.{u1} X] [_inst_2 : Preorder.{u2} Y] {f : X -> Y} (h : Monotone.{u1, u2} X Y _inst_1 _inst_2 f), Eq.{max (succ u1) (succ u2)} (X -> Y) (Prefunctor.obj.{succ u1, succ u2, u1, u2} X (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} X (CategoryTheory.Category.toCategoryStruct.{u1, u1} X (Preorder.smallCategory.{u1} X _inst_1))) Y (CategoryTheory.CategoryStruct.toQuiver.{u2, u2} Y (CategoryTheory.Category.toCategoryStruct.{u2, u2} Y (Preorder.smallCategory.{u2} Y _inst_2))) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u1, u2} X (Preorder.smallCategory.{u1} X _inst_1) Y (Preorder.smallCategory.{u2} Y _inst_2) (Monotone.functor.{u1, u2} X Y _inst_1 _inst_2 f h))) f
Case conversion may be inaccurate. Consider using '#align monotone.functor_obj Monotone.functor_objₓ'. -/
@[simp]
theorem Monotone.functor_obj {f : X → Y} (h : Monotone f) : h.Functor.obj = f :=
  rfl
#align monotone.functor_obj Monotone.functor_obj

end

namespace CategoryTheory

section Preorder

variable {X : Type u} {Y : Type v} [Preorder X] [Preorder Y]

/- warning: category_theory.functor.monotone -> CategoryTheory.Functor.monotone is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : Preorder.{u1} X] [_inst_2 : Preorder.{u2} Y] (f : CategoryTheory.Functor.{u1, u2, u1, u2} X (Preorder.smallCategory.{u1} X _inst_1) Y (Preorder.smallCategory.{u2} Y _inst_2)), Monotone.{u1, u2} X Y _inst_1 _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u1, u2} X (Preorder.smallCategory.{u1} X _inst_1) Y (Preorder.smallCategory.{u2} Y _inst_2) f)
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : Preorder.{u1} X] [_inst_2 : Preorder.{u2} Y] (f : CategoryTheory.Functor.{u1, u2, u1, u2} X (Preorder.smallCategory.{u1} X _inst_1) Y (Preorder.smallCategory.{u2} Y _inst_2)), Monotone.{u1, u2} X Y _inst_1 _inst_2 (Prefunctor.obj.{succ u1, succ u2, u1, u2} X (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} X (CategoryTheory.Category.toCategoryStruct.{u1, u1} X (Preorder.smallCategory.{u1} X _inst_1))) Y (CategoryTheory.CategoryStruct.toQuiver.{u2, u2} Y (CategoryTheory.Category.toCategoryStruct.{u2, u2} Y (Preorder.smallCategory.{u2} Y _inst_2))) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u1, u2} X (Preorder.smallCategory.{u1} X _inst_1) Y (Preorder.smallCategory.{u2} Y _inst_2) f))
Case conversion may be inaccurate. Consider using '#align category_theory.functor.monotone CategoryTheory.Functor.monotoneₓ'. -/
/-- A functor between preorder categories is monotone.
-/
@[mono]
theorem Functor.monotone (f : X ⥤ Y) : Monotone f.obj := fun x y hxy => (f.map hxy.Hom).le
#align category_theory.functor.monotone CategoryTheory.Functor.monotone

end Preorder

section PartialOrder

variable {X : Type u} {Y : Type v} [PartialOrder X] [PartialOrder Y]

#print CategoryTheory.Iso.to_eq /-
theorem Iso.to_eq {x y : X} (f : x ≅ y) : x = y :=
  le_antisymm f.Hom.le f.inv.le
#align category_theory.iso.to_eq CategoryTheory.Iso.to_eq
-/

/- warning: category_theory.equivalence.to_order_iso -> CategoryTheory.Equivalence.toOrderIso is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PartialOrder.{u1} X] [_inst_2 : PartialOrder.{u2} Y], (CategoryTheory.Equivalence.{u1, u2, u1, u2} X (Preorder.smallCategory.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1)) Y (Preorder.smallCategory.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2))) -> (OrderIso.{u1, u2} X Y (Preorder.toHasLe.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1)) (Preorder.toHasLe.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2)))
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PartialOrder.{u1} X] [_inst_2 : PartialOrder.{u2} Y], (CategoryTheory.Equivalence.{u1, u2, u1, u2} X Y (Preorder.smallCategory.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1)) (Preorder.smallCategory.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2))) -> (OrderIso.{u1, u2} X Y (Preorder.toLE.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1)) (Preorder.toLE.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2)))
Case conversion may be inaccurate. Consider using '#align category_theory.equivalence.to_order_iso CategoryTheory.Equivalence.toOrderIsoₓ'. -/
/-- A categorical equivalence between partial orders is just an order isomorphism.
-/
def Equivalence.toOrderIso (e : X ≌ Y) : X ≃o Y
    where
  toFun := e.Functor.obj
  invFun := e.inverse.obj
  left_inv a := (e.unitIso.app a).to_eq.symm
  right_inv b := (e.counitIso.app b).to_eq
  map_rel_iff' a a' :=
    ⟨fun h =>
      ((Equivalence.unit e).app a ≫ e.inverse.map h.Hom ≫ (Equivalence.unitInv e).app a').le,
      fun h : a ≤ a' => (e.Functor.map h.Hom).le⟩
#align category_theory.equivalence.to_order_iso CategoryTheory.Equivalence.toOrderIso

/- warning: category_theory.equivalence.to_order_iso_apply -> CategoryTheory.Equivalence.toOrderIso_apply is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PartialOrder.{u1} X] [_inst_2 : PartialOrder.{u2} Y] (e : CategoryTheory.Equivalence.{u1, u2, u1, u2} X (Preorder.smallCategory.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1)) Y (Preorder.smallCategory.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2))) (x : X), Eq.{succ u2} Y (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} X Y (Preorder.toHasLe.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1)) (Preorder.toHasLe.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2))) (fun (_x : RelIso.{u1, u2} X Y (LE.le.{u1} X (Preorder.toHasLe.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1))) (LE.le.{u2} Y (Preorder.toHasLe.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2)))) => X -> Y) (RelIso.hasCoeToFun.{u1, u2} X Y (LE.le.{u1} X (Preorder.toHasLe.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1))) (LE.le.{u2} Y (Preorder.toHasLe.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2)))) (CategoryTheory.Equivalence.toOrderIso.{u1, u2} X Y _inst_1 _inst_2 e) x) (CategoryTheory.Functor.obj.{u1, u2, u1, u2} X (Preorder.smallCategory.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1)) Y (Preorder.smallCategory.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2)) (CategoryTheory.Equivalence.functor.{u1, u2, u1, u2} X (Preorder.smallCategory.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1)) Y (Preorder.smallCategory.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2)) e) x)
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PartialOrder.{u1} X] [_inst_2 : PartialOrder.{u2} Y] (e : CategoryTheory.Equivalence.{u1, u2, u1, u2} X Y (Preorder.smallCategory.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1)) (Preorder.smallCategory.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2))) (x : X), Eq.{succ u2} Y (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RelIso.{u1, u2} X Y (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : X) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : X) => LE.le.{u1} X (Preorder.toLE.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1)) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Y) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Y) => LE.le.{u2} Y (Preorder.toLE.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2)) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) X (fun (_x : X) => Y) (RelHomClass.toFunLike.{max u1 u2, u1, u2} (RelIso.{u1, u2} X Y (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : X) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : X) => LE.le.{u1} X (Preorder.toLE.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1)) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Y) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Y) => LE.le.{u2} Y (Preorder.toLE.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2)) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) X Y (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : X) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : X) => LE.le.{u1} X (Preorder.toLE.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1)) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Y) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Y) => LE.le.{u2} Y (Preorder.toLE.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2)) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.instRelHomClassRelIso.{u1, u2} X Y (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : X) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : X) => LE.le.{u1} X (Preorder.toLE.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1)) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Y) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Y) => LE.le.{u2} Y (Preorder.toLE.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2)) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298))) (CategoryTheory.Equivalence.toOrderIso.{u1, u2} X Y _inst_1 _inst_2 e) x) (Prefunctor.obj.{succ u1, succ u2, u1, u2} X (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} X (CategoryTheory.Category.toCategoryStruct.{u1, u1} X (Preorder.smallCategory.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1)))) Y (CategoryTheory.CategoryStruct.toQuiver.{u2, u2} Y (CategoryTheory.Category.toCategoryStruct.{u2, u2} Y (Preorder.smallCategory.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2)))) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u1, u2} X (Preorder.smallCategory.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1)) Y (Preorder.smallCategory.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2)) (CategoryTheory.Equivalence.functor.{u1, u2, u1, u2} X Y (Preorder.smallCategory.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1)) (Preorder.smallCategory.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2)) e)) x)
Case conversion may be inaccurate. Consider using '#align category_theory.equivalence.to_order_iso_apply CategoryTheory.Equivalence.toOrderIso_applyₓ'. -/
-- `@[simps]` on `equivalence.to_order_iso` produces lemmas that fail the `simp_nf` linter,
-- so we provide them by hand:
@[simp]
theorem Equivalence.toOrderIso_apply (e : X ≌ Y) (x : X) : e.toOrderIso x = e.Functor.obj x :=
  rfl
#align category_theory.equivalence.to_order_iso_apply CategoryTheory.Equivalence.toOrderIso_apply

/- warning: category_theory.equivalence.to_order_iso_symm_apply -> CategoryTheory.Equivalence.toOrderIso_symm_apply is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PartialOrder.{u1} X] [_inst_2 : PartialOrder.{u2} Y] (e : CategoryTheory.Equivalence.{u1, u2, u1, u2} X (Preorder.smallCategory.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1)) Y (Preorder.smallCategory.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2))) (y : Y), Eq.{succ u1} X (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (OrderIso.{u2, u1} Y X (Preorder.toHasLe.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2)) (Preorder.toHasLe.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1))) (fun (_x : RelIso.{u2, u1} Y X (LE.le.{u2} Y (Preorder.toHasLe.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2))) (LE.le.{u1} X (Preorder.toHasLe.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1)))) => Y -> X) (RelIso.hasCoeToFun.{u2, u1} Y X (LE.le.{u2} Y (Preorder.toHasLe.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2))) (LE.le.{u1} X (Preorder.toHasLe.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1)))) (OrderIso.symm.{u1, u2} X Y (Preorder.toHasLe.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1)) (Preorder.toHasLe.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2)) (CategoryTheory.Equivalence.toOrderIso.{u1, u2} X Y _inst_1 _inst_2 e)) y) (CategoryTheory.Functor.obj.{u2, u1, u2, u1} Y (Preorder.smallCategory.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2)) X (Preorder.smallCategory.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1)) (CategoryTheory.Equivalence.inverse.{u1, u2, u1, u2} X (Preorder.smallCategory.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1)) Y (Preorder.smallCategory.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2)) e) y)
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PartialOrder.{u1} X] [_inst_2 : PartialOrder.{u2} Y] (e : CategoryTheory.Equivalence.{u1, u2, u1, u2} X Y (Preorder.smallCategory.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1)) (Preorder.smallCategory.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2))) (y : Y), Eq.{succ u1} X (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RelIso.{u2, u1} Y X (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Y) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Y) => LE.le.{u2} Y (Preorder.toLE.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2)) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : X) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : X) => LE.le.{u1} X (Preorder.toLE.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1)) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) Y (fun (_x : Y) => X) (RelHomClass.toFunLike.{max u2 u1, u2, u1} (RelIso.{u2, u1} Y X (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Y) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Y) => LE.le.{u2} Y (Preorder.toLE.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2)) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : X) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : X) => LE.le.{u1} X (Preorder.toLE.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1)) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) Y X (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Y) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Y) => LE.le.{u2} Y (Preorder.toLE.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2)) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : X) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : X) => LE.le.{u1} X (Preorder.toLE.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1)) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.instRelHomClassRelIso.{u2, u1} Y X (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Y) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Y) => LE.le.{u2} Y (Preorder.toLE.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2)) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : X) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : X) => LE.le.{u1} X (Preorder.toLE.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1)) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298))) (OrderIso.symm.{u1, u2} X Y (Preorder.toLE.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1)) (Preorder.toLE.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2)) (CategoryTheory.Equivalence.toOrderIso.{u1, u2} X Y _inst_1 _inst_2 e)) y) (Prefunctor.obj.{succ u2, succ u1, u2, u1} Y (CategoryTheory.CategoryStruct.toQuiver.{u2, u2} Y (CategoryTheory.Category.toCategoryStruct.{u2, u2} Y (Preorder.smallCategory.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2)))) X (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} X (CategoryTheory.Category.toCategoryStruct.{u1, u1} X (Preorder.smallCategory.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1)))) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u2, u1} Y (Preorder.smallCategory.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2)) X (Preorder.smallCategory.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1)) (CategoryTheory.Equivalence.inverse.{u1, u2, u1, u2} X Y (Preorder.smallCategory.{u1} X (PartialOrder.toPreorder.{u1} X _inst_1)) (Preorder.smallCategory.{u2} Y (PartialOrder.toPreorder.{u2} Y _inst_2)) e)) y)
Case conversion may be inaccurate. Consider using '#align category_theory.equivalence.to_order_iso_symm_apply CategoryTheory.Equivalence.toOrderIso_symm_applyₓ'. -/
@[simp]
theorem Equivalence.toOrderIso_symm_apply (e : X ≌ Y) (y : Y) :
    e.toOrderIso.symm y = e.inverse.obj y :=
  rfl
#align category_theory.equivalence.to_order_iso_symm_apply CategoryTheory.Equivalence.toOrderIso_symm_apply

end PartialOrder

end CategoryTheory

