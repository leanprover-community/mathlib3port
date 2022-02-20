/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Preadditive.AdditiveFunctor
import Mathbin.CategoryTheory.Monoidal.Category

/-!
# Preadditive monoidal categories

A monoidal category is `monoidal_preadditive` if it is preadditive and tensor product of morphisms
is linear in both factors.
-/


noncomputable section

namespace CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.MonoidalCategory

variable (C : Type _) [Category C] [Preadditive C] [MonoidalCategory C]

/-- A category is `monoidal_preadditive` if tensoring is linear in both factors.

Note we don't `extend preadditive C` here, as `abelian C` already extends it,
and we'll need to have both typeclasses sometimes.
-/
class MonoidalPreadditive where
  tensor_zero' : ∀ {W X Y Z : C} f : W ⟶ X, f ⊗ (0 : Y ⟶ Z) = 0 := by
    run_tac
      obviously
  zero_tensor' : ∀ {W X Y Z : C} f : Y ⟶ Z, (0 : W ⟶ X) ⊗ f = 0 := by
    run_tac
      obviously
  tensor_add' : ∀ {W X Y Z : C} f : W ⟶ X g h : Y ⟶ Z, f ⊗ (g + h) = f ⊗ g + f ⊗ h := by
    run_tac
      obviously
  add_tensor' : ∀ {W X Y Z : C} f g : W ⟶ X h : Y ⟶ Z, (f + g) ⊗ h = f ⊗ h + g ⊗ h := by
    run_tac
      obviously

restate_axiom monoidal_preadditive.tensor_zero'

restate_axiom monoidal_preadditive.zero_tensor'

restate_axiom monoidal_preadditive.tensor_add'

restate_axiom monoidal_preadditive.add_tensor'

attribute [simp] monoidal_preadditive.tensor_zero monoidal_preadditive.zero_tensor

variable [MonoidalPreadditive C]

attribute [local simp] monoidal_preadditive.tensor_add monoidal_preadditive.add_tensor

instance tensoring_left_additive (X : C) : ((tensoringLeft C).obj X).Additive :=
  {  }

instance tensoring_right_additive (X : C) : ((tensoringRight C).obj X).Additive :=
  {  }

end CategoryTheory

