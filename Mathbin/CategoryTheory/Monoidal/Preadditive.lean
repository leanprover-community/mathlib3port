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

variable (C : Type _) [category C] [preadditive C] [monoidal_category C]

/--
A category is `monoidal_preadditive` if tensoring is linear in both factors.

Note we don't `extend preadditive C` here, as `abelian C` already extends it,
and we'll need to have both typeclasses sometimes.
-/
class monoidal_preadditive where 
  tensor_zero' : ∀ {W X Y Z : C} f : W ⟶ X, f ⊗ (0 : Y ⟶ Z) = 0 :=  by 
  runTac 
    obviously 
  zero_tensor' : ∀ {W X Y Z : C} f : Y ⟶ Z, (0 : W ⟶ X) ⊗ f = 0 :=  by 
  runTac 
    obviously 
  tensor_add' : ∀ {W X Y Z : C} f : W ⟶ X g h : Y ⟶ Z, (f ⊗ g+h) = (f ⊗ g)+f ⊗ h :=  by 
  runTac 
    obviously 
  add_tensor' : ∀ {W X Y Z : C} f g : W ⟶ X h : Y ⟶ Z, (f+g) ⊗ h = (f ⊗ h)+g ⊗ h :=  by 
  runTac 
    obviously

restate_axiom monoidal_preadditive.tensor_zero'

restate_axiom monoidal_preadditive.zero_tensor'

restate_axiom monoidal_preadditive.tensor_add'

restate_axiom monoidal_preadditive.add_tensor'

attribute [simp] monoidal_preadditive.tensor_zero monoidal_preadditive.zero_tensor

variable [monoidal_preadditive C]

attribute [local simp] monoidal_preadditive.tensor_add monoidal_preadditive.add_tensor

instance tensoring_left_additive (X : C) : ((tensoring_left C).obj X).Additive :=
  {  }

instance tensoring_right_additive (X : C) : ((tensoring_right C).obj X).Additive :=
  {  }

end CategoryTheory

