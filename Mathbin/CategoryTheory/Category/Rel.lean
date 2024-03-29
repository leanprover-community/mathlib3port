/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import CategoryTheory.Category.Basic

#align_import category_theory.category.Rel from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The category of types with binary relations as morphisms.
-/


namespace CategoryTheory

universe u

#print CategoryTheory.RelCat /-
/-- A type synonym for `Type`, which carries the category instance for which
    morphisms are binary relations. -/
def RelCat :=
  Type u
#align category_theory.Rel CategoryTheory.RelCat
-/

#print CategoryTheory.RelCat.inhabited /-
instance RelCat.inhabited : Inhabited RelCat := by unfold Rel <;> infer_instance
#align category_theory.Rel.inhabited CategoryTheory.RelCat.inhabited
-/

#print CategoryTheory.rel /-
/-- The category of types with binary relations as morphisms. -/
instance rel : LargeCategory RelCat
    where
  Hom X Y := X → Y → Prop
  id X x y := x = y
  comp X Y Z f g x z := ∃ y, f x y ∧ g y z
#align category_theory.rel CategoryTheory.rel
-/

end CategoryTheory

