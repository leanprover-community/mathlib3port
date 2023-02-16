/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.monoidal.linear
! leanprover-community/mathlib commit 32253a1a1071173b33dc7d6a218cf722c6feb514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Linear.LinearFunctor
import Mathbin.CategoryTheory.Monoidal.Preadditive

/-!
# Linear monoidal categories

A monoidal category is `monoidal_linear R` if it is monoidal preadditive and
tensor product of morphisms is `R`-linear in both factors.
-/


namespace CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.MonoidalCategory

variable (R : Type _) [Semiring R]

variable (C : Type _) [Category C] [Preadditive C] [Linear R C]

variable [MonoidalCategory C] [MonoidalPreadditive C]

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

restate_axiom monoidal_linear.tensor_smul'

restate_axiom monoidal_linear.smul_tensor'

attribute [simp] monoidal_linear.tensor_smul monoidal_linear.smul_tensor

variable {C} [MonoidalLinear R C]

instance tensorLeftLinear (X : C) : (tensorLeft X).Linear R where
#align category_theory.tensor_left_linear CategoryTheory.tensorLeftLinear

instance tensorRightLinear (X : C) : (tensorRight X).Linear R where
#align category_theory.tensor_right_linear CategoryTheory.tensorRightLinear

instance tensoringLeftLinear (X : C) : ((tensoringLeft C).obj X).Linear R where
#align category_theory.tensoring_left_linear CategoryTheory.tensoringLeftLinear

instance tensoringRightLinear (X : C) : ((tensoringRight C).obj X).Linear R where
#align category_theory.tensoring_right_linear CategoryTheory.tensoringRightLinear

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
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

end CategoryTheory

