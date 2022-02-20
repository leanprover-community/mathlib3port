/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Monoidal.Category
import Mathbin.CategoryTheory.Adjunction.Basic

/-!
# Closed monoidal categories

Define (right) closed objects and (right) closed monoidal categories.

## TODO
Some of the theorems proved about cartesian closed categories
should be generalised and moved to this file.
-/


universe v u u₂

namespace CategoryTheory

open Category MonoidalCategory

/-- An object `X` is (right) closed if `(X ⊗ -)` is a left adjoint. -/
class Closed {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] (X : C) where
  isAdj : IsLeftAdjoint (tensorLeft X)

/-- A monoidal category `C` is (right) monoidal closed if every object is (right) closed. -/
class MonoidalClosed (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] where
  Closed : ∀ X : C, Closed X

attribute [instance] monoidal_closed.closed

/-- The unit object is always closed.
This isn't an instance because most of the time we'll prove closedness for all objects at once,
rather than just for this one.
-/
def unitClosed {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] : Closed (𝟙_ C) where
  isAdj :=
    { right := 𝟭 C,
      adj :=
        Adjunction.mkOfHomEquiv
          { homEquiv := fun X _ =>
              { toFun := fun a => (leftUnitor X).inv ≫ a, invFun := fun a => (leftUnitor X).Hom ≫ a,
                left_inv := by
                  tidy,
                right_inv := by
                  tidy },
            hom_equiv_naturality_left_symm' := fun X' X Y f g => by
              dsimp
              rw [left_unitor_naturality_assoc] } }

end CategoryTheory

