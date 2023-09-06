/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Linear.LinearFunctor
import Mathbin.CategoryTheory.Monoidal.Preadditive

#align_import category_theory.monoidal.linear from "leanprover-community/mathlib"@"31ca6f9cf5f90a6206092cd7f84b359dcb6d52e0"

/-!
# Linear monoidal categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A monoidal category is `monoidal_linear R` if it is monoidal preadditive and
tensor product of morphisms is `R`-linear in both factors.
-/


namespace CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.MonoidalCategory

variable (R : Type _) [Semiring R]

variable (C : Type _) [Category C] [Preadditive C] [Linear R C]

variable [MonoidalCategory C] [MonoidalPreadditive C]

#print CategoryTheory.MonoidalLinear /-
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A category is `monoidal_linear R` if tensoring is `R`-linear in both factors.
-/
class MonoidalLinear : Prop where
  tensor_smul' : ∀ {W X Y Z : C} (f : W ⟶ X) (r : R) (g : Y ⟶ Z), f ⊗ r • g = r • (f ⊗ g) := by
    obviously
  smul_tensor' : ∀ {W X Y Z : C} (r : R) (f : W ⟶ X) (g : Y ⟶ Z), r • f ⊗ g = r • (f ⊗ g) := by
    obviously
#align category_theory.monoidal_linear CategoryTheory.MonoidalLinear
-/

attribute [simp] monoidal_linear.tensor_smul monoidal_linear.smul_tensor

variable {C} [MonoidalLinear R C]

#print CategoryTheory.tensorLeft_linear /-
instance tensorLeft_linear (X : C) : (tensorLeft X).Linear R where
#align category_theory.tensor_left_linear CategoryTheory.tensorLeft_linear
-/

#print CategoryTheory.tensorRight_linear /-
instance tensorRight_linear (X : C) : (tensorRight X).Linear R where
#align category_theory.tensor_right_linear CategoryTheory.tensorRight_linear
-/

#print CategoryTheory.tensoringLeft_linear /-
instance tensoringLeft_linear (X : C) : ((tensoringLeft C).obj X).Linear R where
#align category_theory.tensoring_left_linear CategoryTheory.tensoringLeft_linear
-/

#print CategoryTheory.tensoringRight_linear /-
instance tensoringRight_linear (X : C) : ((tensoringRight C).obj X).Linear R where
#align category_theory.tensoring_right_linear CategoryTheory.tensoringRight_linear
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.monoidalLinearOfFaithful /-
/-- A faithful linear monoidal functor to a linear monoidal category
ensures that the domain is linear monoidal. -/
theorem monoidalLinearOfFaithful {D : Type _} [Category D] [Preadditive D] [Linear R D]
    [MonoidalCategory D] [MonoidalPreadditive D] (F : MonoidalFunctor D C) [Faithful F.toFunctor]
    [F.toFunctor.Additive] [F.toFunctor.Linear R] : MonoidalLinear R D :=
  { tensor_smul' := by
      intros
      apply F.to_functor.map_injective
      simp only [F.to_functor.map_smul r (f ⊗ g), F.to_functor.map_smul r g, F.map_tensor,
        monoidal_linear.tensor_smul, linear.smul_comp, linear.comp_smul]
    smul_tensor' := by
      intros
      apply F.to_functor.map_injective
      simp only [F.to_functor.map_smul r (f ⊗ g), F.to_functor.map_smul r f, F.map_tensor,
        monoidal_linear.smul_tensor, linear.smul_comp, linear.comp_smul] }
#align category_theory.monoidal_linear_of_faithful CategoryTheory.monoidalLinearOfFaithful
-/

end CategoryTheory

