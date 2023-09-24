/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import CategoryTheory.Preadditive.Yoneda.Basic
import Algebra.Category.Module.Abelian

#align_import category_theory.preadditive.yoneda.limits from "leanprover-community/mathlib"@"0b7c740e25651db0ba63648fbae9f9d6f941e31b"

/-!
# The Yoneda embedding for preadditive categories preserves limits

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The Yoneda embedding for preadditive categories preserves limits.

## Implementation notes

This is in a separate file to avoid having to import the development of the abelian structure on
`Module` in the main file about the preadditive Yoneda embedding.

-/


universe v u

open CategoryTheory.Preadditive Opposite CategoryTheory.Limits

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]

#print CategoryTheory.preservesLimitsPreadditiveYonedaObj /-
instance preservesLimitsPreadditiveYonedaObj (X : C) : PreservesLimits (preadditiveYonedaObj X) :=
  have : PreservesLimits (preadditiveYonedaObj X ⋙ forget _) :=
    (inferInstance : PreservesLimits (yoneda.obj X))
  preserves_limits_of_reflects_of_preserves _ (forget _)
#align category_theory.preserves_limits_preadditive_yoneda_obj CategoryTheory.preservesLimitsPreadditiveYonedaObj
-/

#print CategoryTheory.preservesLimitsPreadditiveCoyonedaObj /-
instance preservesLimitsPreadditiveCoyonedaObj (X : Cᵒᵖ) :
    PreservesLimits (preadditiveCoyonedaObj X) :=
  have : PreservesLimits (preadditiveCoyonedaObj X ⋙ forget _) :=
    (inferInstance : PreservesLimits (coyoneda.obj X))
  preserves_limits_of_reflects_of_preserves _ (forget _)
#align category_theory.preserves_limits_preadditive_coyoneda_obj CategoryTheory.preservesLimitsPreadditiveCoyonedaObj
-/

#print CategoryTheory.PreservesLimitsPreadditiveYoneda.obj /-
instance PreservesLimitsPreadditiveYoneda.obj (X : C) : PreservesLimits (preadditiveYoneda.obj X) :=
  show PreservesLimits (preadditiveYonedaObj X ⋙ forget₂ _ _) from inferInstance
#align category_theory.preserves_limits_preadditive_yoneda.obj CategoryTheory.PreservesLimitsPreadditiveYoneda.obj
-/

#print CategoryTheory.PreservesLimitsPreadditiveCoyoneda.obj /-
instance PreservesLimitsPreadditiveCoyoneda.obj (X : Cᵒᵖ) :
    PreservesLimits (preadditiveCoyoneda.obj X) :=
  show PreservesLimits (preadditiveCoyonedaObj X ⋙ forget₂ _ _) from inferInstance
#align category_theory.preserves_limits_preadditive_coyoneda.obj CategoryTheory.PreservesLimitsPreadditiveCoyoneda.obj
-/

end CategoryTheory

