/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.monoidal.linear
! leanprover-community/mathlib commit 986c4d5761f938b2e1c43c01f001b6d9d88c2055
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

restate_axiom monoidal_linear.tensor_smul'

restate_axiom monoidal_linear.smul_tensor'

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

/- warning: category_theory.tensoring_left_linear -> CategoryTheory.tensoringLeft_linear is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : Semiring.{u1} R] {C : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u3, u2} C] [_inst_3 : CategoryTheory.Preadditive.{u3, u2} C _inst_2] [_inst_4 : CategoryTheory.Linear.{u1, u3, u2} R _inst_1 C _inst_2 _inst_3] [_inst_5 : CategoryTheory.MonoidalCategory.{u3, u2} C _inst_2] [_inst_6 : CategoryTheory.MonoidalPreadditive.{u2, u3} C _inst_2 _inst_3 _inst_5] [_inst_7 : CategoryTheory.MonoidalLinear.{u1, u2, u3} R _inst_1 C _inst_2 _inst_3 _inst_4 _inst_5 _inst_6] (X : C), CategoryTheory.Functor.Linear.{u1, u2, u2, u3, u3} R _inst_1 C C _inst_2 _inst_2 _inst_3 _inst_3 _inst_4 _inst_4 (CategoryTheory.Functor.obj.{u3, max u2 u3, u2, max u3 u2} C _inst_2 (CategoryTheory.Functor.{u3, u3, u2, u2} C _inst_2 C _inst_2) (CategoryTheory.Functor.category.{u3, u3, u2, u2} C _inst_2 C _inst_2) (CategoryTheory.MonoidalCategory.tensoringLeft.{u3, u2} C _inst_2 _inst_5) X) (CategoryTheory.tensoringLeft_additive.{u2, u3} C _inst_2 _inst_3 _inst_5 _inst_6 X)
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : Semiring.{u1} R] {C : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u3, u2} C] [_inst_3 : CategoryTheory.Preadditive.{u3, u2} C _inst_2] [_inst_4 : CategoryTheory.Linear.{u1, u3, u2} R _inst_1 C _inst_2 _inst_3] [_inst_5 : CategoryTheory.MonoidalCategory.{u3, u2} C _inst_2] [_inst_6 : CategoryTheory.MonoidalPreadditive.{u2, u3} C _inst_2 _inst_3 _inst_5] [_inst_7 : CategoryTheory.MonoidalLinear.{u1, u2, u3} R _inst_1 C _inst_2 _inst_3 _inst_4 _inst_5 _inst_6] (X : C), CategoryTheory.Functor.Linear.{u1, u2, u2, u3, u3} R _inst_1 C C _inst_2 _inst_2 _inst_3 _inst_3 _inst_4 _inst_4 (Prefunctor.obj.{succ u3, max (succ u2) (succ u3), u2, max u2 u3} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u2} C (CategoryTheory.Category.toCategoryStruct.{u3, u2} C _inst_2)) (CategoryTheory.Functor.{u3, u3, u2, u2} C _inst_2 C _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u3, max u2 u3} (CategoryTheory.Functor.{u3, u3, u2, u2} C _inst_2 C _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u2 u3, max u2 u3} (CategoryTheory.Functor.{u3, u3, u2, u2} C _inst_2 C _inst_2) (CategoryTheory.Functor.category.{u3, u3, u2, u2} C _inst_2 C _inst_2))) (CategoryTheory.Functor.toPrefunctor.{u3, max u2 u3, u2, max u2 u3} C _inst_2 (CategoryTheory.Functor.{u3, u3, u2, u2} C _inst_2 C _inst_2) (CategoryTheory.Functor.category.{u3, u3, u2, u2} C _inst_2 C _inst_2) (CategoryTheory.MonoidalCategory.tensoringLeft.{u3, u2} C _inst_2 _inst_5)) X) (CategoryTheory.tensoringLeft_additive.{u2, u3} C _inst_2 _inst_3 _inst_5 _inst_6 X)
Case conversion may be inaccurate. Consider using '#align category_theory.tensoring_left_linear CategoryTheory.tensoringLeft_linearₓ'. -/
instance tensoringLeft_linear (X : C) : ((tensoringLeft C).obj X).Linear R where
#align category_theory.tensoring_left_linear CategoryTheory.tensoringLeft_linear

/- warning: category_theory.tensoring_right_linear -> CategoryTheory.tensoringRight_linear is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : Semiring.{u1} R] {C : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u3, u2} C] [_inst_3 : CategoryTheory.Preadditive.{u3, u2} C _inst_2] [_inst_4 : CategoryTheory.Linear.{u1, u3, u2} R _inst_1 C _inst_2 _inst_3] [_inst_5 : CategoryTheory.MonoidalCategory.{u3, u2} C _inst_2] [_inst_6 : CategoryTheory.MonoidalPreadditive.{u2, u3} C _inst_2 _inst_3 _inst_5] [_inst_7 : CategoryTheory.MonoidalLinear.{u1, u2, u3} R _inst_1 C _inst_2 _inst_3 _inst_4 _inst_5 _inst_6] (X : C), CategoryTheory.Functor.Linear.{u1, u2, u2, u3, u3} R _inst_1 C C _inst_2 _inst_2 _inst_3 _inst_3 _inst_4 _inst_4 (CategoryTheory.Functor.obj.{u3, max u2 u3, u2, max u3 u2} C _inst_2 (CategoryTheory.Functor.{u3, u3, u2, u2} C _inst_2 C _inst_2) (CategoryTheory.Functor.category.{u3, u3, u2, u2} C _inst_2 C _inst_2) (CategoryTheory.MonoidalCategory.tensoringRight.{u3, u2} C _inst_2 _inst_5) X) (CategoryTheory.tensoringRight_additive.{u2, u3} C _inst_2 _inst_3 _inst_5 _inst_6 X)
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : Semiring.{u1} R] {C : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u3, u2} C] [_inst_3 : CategoryTheory.Preadditive.{u3, u2} C _inst_2] [_inst_4 : CategoryTheory.Linear.{u1, u3, u2} R _inst_1 C _inst_2 _inst_3] [_inst_5 : CategoryTheory.MonoidalCategory.{u3, u2} C _inst_2] [_inst_6 : CategoryTheory.MonoidalPreadditive.{u2, u3} C _inst_2 _inst_3 _inst_5] [_inst_7 : CategoryTheory.MonoidalLinear.{u1, u2, u3} R _inst_1 C _inst_2 _inst_3 _inst_4 _inst_5 _inst_6] (X : C), CategoryTheory.Functor.Linear.{u1, u2, u2, u3, u3} R _inst_1 C C _inst_2 _inst_2 _inst_3 _inst_3 _inst_4 _inst_4 (Prefunctor.obj.{succ u3, max (succ u2) (succ u3), u2, max u2 u3} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u2} C (CategoryTheory.Category.toCategoryStruct.{u3, u2} C _inst_2)) (CategoryTheory.Functor.{u3, u3, u2, u2} C _inst_2 C _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u3, max u2 u3} (CategoryTheory.Functor.{u3, u3, u2, u2} C _inst_2 C _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u2 u3, max u2 u3} (CategoryTheory.Functor.{u3, u3, u2, u2} C _inst_2 C _inst_2) (CategoryTheory.Functor.category.{u3, u3, u2, u2} C _inst_2 C _inst_2))) (CategoryTheory.Functor.toPrefunctor.{u3, max u2 u3, u2, max u2 u3} C _inst_2 (CategoryTheory.Functor.{u3, u3, u2, u2} C _inst_2 C _inst_2) (CategoryTheory.Functor.category.{u3, u3, u2, u2} C _inst_2 C _inst_2) (CategoryTheory.MonoidalCategory.tensoringRight.{u3, u2} C _inst_2 _inst_5)) X) (CategoryTheory.tensoringRight_additive.{u2, u3} C _inst_2 _inst_3 _inst_5 _inst_6 X)
Case conversion may be inaccurate. Consider using '#align category_theory.tensoring_right_linear CategoryTheory.tensoringRight_linearₓ'. -/
instance tensoringRight_linear (X : C) : ((tensoringRight C).obj X).Linear R where
#align category_theory.tensoring_right_linear CategoryTheory.tensoringRight_linear

/- warning: category_theory.monoidal_linear_of_faithful -> CategoryTheory.monoidalLinearOfFaithful is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : Semiring.{u1} R] {C : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u3, u2} C] [_inst_3 : CategoryTheory.Preadditive.{u3, u2} C _inst_2] [_inst_4 : CategoryTheory.Linear.{u1, u3, u2} R _inst_1 C _inst_2 _inst_3] [_inst_5 : CategoryTheory.MonoidalCategory.{u3, u2} C _inst_2] [_inst_6 : CategoryTheory.MonoidalPreadditive.{u2, u3} C _inst_2 _inst_3 _inst_5] [_inst_7 : CategoryTheory.MonoidalLinear.{u1, u2, u3} R _inst_1 C _inst_2 _inst_3 _inst_4 _inst_5 _inst_6] {D : Type.{u4}} [_inst_8 : CategoryTheory.Category.{u5, u4} D] [_inst_9 : CategoryTheory.Preadditive.{u5, u4} D _inst_8] [_inst_10 : CategoryTheory.Linear.{u1, u5, u4} R _inst_1 D _inst_8 _inst_9] [_inst_11 : CategoryTheory.MonoidalCategory.{u5, u4} D _inst_8] [_inst_12 : CategoryTheory.MonoidalPreadditive.{u4, u5} D _inst_8 _inst_9 _inst_11] (F : CategoryTheory.MonoidalFunctor.{u5, u3, u4, u2} D _inst_8 _inst_11 C _inst_2 _inst_5) [_inst_13 : CategoryTheory.Faithful.{u5, u3, u4, u2} D _inst_8 C _inst_2 (CategoryTheory.LaxMonoidalFunctor.toFunctor.{u5, u3, u4, u2} D _inst_8 _inst_11 C _inst_2 _inst_5 (CategoryTheory.MonoidalFunctor.toLaxMonoidalFunctor.{u5, u3, u4, u2} D _inst_8 _inst_11 C _inst_2 _inst_5 F))] [_inst_14 : CategoryTheory.Functor.Additive.{u4, u2, u5, u3} D C _inst_8 _inst_2 _inst_9 _inst_3 (CategoryTheory.LaxMonoidalFunctor.toFunctor.{u5, u3, u4, u2} D _inst_8 _inst_11 C _inst_2 _inst_5 (CategoryTheory.MonoidalFunctor.toLaxMonoidalFunctor.{u5, u3, u4, u2} D _inst_8 _inst_11 C _inst_2 _inst_5 F))] [_inst_15 : CategoryTheory.Functor.Linear.{u1, u4, u2, u5, u3} R _inst_1 D C _inst_8 _inst_2 _inst_9 _inst_3 _inst_10 _inst_4 (CategoryTheory.LaxMonoidalFunctor.toFunctor.{u5, u3, u4, u2} D _inst_8 _inst_11 C _inst_2 _inst_5 (CategoryTheory.MonoidalFunctor.toLaxMonoidalFunctor.{u5, u3, u4, u2} D _inst_8 _inst_11 C _inst_2 _inst_5 F)) _inst_14], CategoryTheory.MonoidalLinear.{u1, u4, u5} R _inst_1 D _inst_8 _inst_9 _inst_10 _inst_11 _inst_12
but is expected to have type
  forall (R : Type.{u3}) [_inst_1 : Semiring.{u3} R] {C : Type.{u1}} [_inst_2 : CategoryTheory.Category.{u2, u1} C] [_inst_3 : CategoryTheory.Preadditive.{u2, u1} C _inst_2] [_inst_4 : CategoryTheory.Linear.{u3, u2, u1} R _inst_1 C _inst_2 _inst_3] [_inst_5 : CategoryTheory.MonoidalCategory.{u2, u1} C _inst_2] [_inst_6 : CategoryTheory.MonoidalPreadditive.{u1, u2} C _inst_2 _inst_3 _inst_5] [_inst_7 : CategoryTheory.MonoidalLinear.{u3, u1, u2} R _inst_1 C _inst_2 _inst_3 _inst_4 _inst_5 _inst_6] {D : Type.{u5}} [_inst_8 : CategoryTheory.Category.{u4, u5} D] [_inst_9 : CategoryTheory.Preadditive.{u4, u5} D _inst_8] [_inst_10 : CategoryTheory.Linear.{u3, u4, u5} R _inst_1 D _inst_8 _inst_9] [_inst_11 : CategoryTheory.MonoidalCategory.{u4, u5} D _inst_8] [_inst_12 : CategoryTheory.MonoidalPreadditive.{u5, u4} D _inst_8 _inst_9 _inst_11] (F : CategoryTheory.MonoidalFunctor.{u4, u2, u5, u1} D _inst_8 _inst_11 C _inst_2 _inst_5) [_inst_13 : CategoryTheory.Faithful.{u4, u2, u5, u1} D _inst_8 C _inst_2 (CategoryTheory.LaxMonoidalFunctor.toFunctor.{u4, u2, u5, u1} D _inst_8 _inst_11 C _inst_2 _inst_5 (CategoryTheory.MonoidalFunctor.toLaxMonoidalFunctor.{u4, u2, u5, u1} D _inst_8 _inst_11 C _inst_2 _inst_5 F))] [_inst_14 : CategoryTheory.Functor.Additive.{u5, u1, u4, u2} D C _inst_8 _inst_2 _inst_9 _inst_3 (CategoryTheory.LaxMonoidalFunctor.toFunctor.{u4, u2, u5, u1} D _inst_8 _inst_11 C _inst_2 _inst_5 (CategoryTheory.MonoidalFunctor.toLaxMonoidalFunctor.{u4, u2, u5, u1} D _inst_8 _inst_11 C _inst_2 _inst_5 F))] [_inst_15 : CategoryTheory.Functor.Linear.{u3, u5, u1, u4, u2} R _inst_1 D C _inst_8 _inst_2 _inst_9 _inst_3 _inst_10 _inst_4 (CategoryTheory.LaxMonoidalFunctor.toFunctor.{u4, u2, u5, u1} D _inst_8 _inst_11 C _inst_2 _inst_5 (CategoryTheory.MonoidalFunctor.toLaxMonoidalFunctor.{u4, u2, u5, u1} D _inst_8 _inst_11 C _inst_2 _inst_5 F)) _inst_14], CategoryTheory.MonoidalLinear.{u3, u5, u4} R _inst_1 D _inst_8 _inst_9 _inst_10 _inst_11 _inst_12
Case conversion may be inaccurate. Consider using '#align category_theory.monoidal_linear_of_faithful CategoryTheory.monoidalLinearOfFaithfulₓ'. -/
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

