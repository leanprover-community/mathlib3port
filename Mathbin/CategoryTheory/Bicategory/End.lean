/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.bicategory.End
! leanprover-community/mathlib commit ef7acf407d265ad4081c8998687e994fa80ba70c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Bicategory.Basic
import Mathbin.CategoryTheory.Monoidal.Category

/-!
# Endomorphisms of an object in a bicategory, as a monoidal category.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


namespace CategoryTheory

variable {C : Type _} [Bicategory C]

#print CategoryTheory.EndMonoidal /-
/-- The endomorphisms of an object in a bicategory can be considered as a monoidal category. -/
def EndMonoidal (X : C) :=
  X ⟶ X deriving Category
#align category_theory.End_monoidal CategoryTheory.EndMonoidal
-/

instance (X : C) : Inhabited (EndMonoidal X) :=
  ⟨𝟙 X⟩

open scoped Bicategory

open MonoidalCategory

open Bicategory

instance (X : C) : MonoidalCategory (EndMonoidal X)
    where
  tensorObj f g := f ≫ g
  tensorHom f g h i η θ := η ▷ h ≫ g ◁ θ
  tensorUnit := 𝟙 _
  associator f g h := α_ f g h
  leftUnitor f := λ_ f
  rightUnitor f := ρ_ f
  tensor_comp' := by
    intros
    rw [bicategory.whisker_left_comp, bicategory.comp_whisker_right, category.assoc, category.assoc,
      bicategory.whisker_exchange_assoc]

end CategoryTheory

