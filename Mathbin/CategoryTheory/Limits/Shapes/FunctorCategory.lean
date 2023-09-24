/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import CategoryTheory.Limits.Shapes.FiniteLimits
import CategoryTheory.Limits.FunctorCategory

#align_import category_theory.limits.shapes.functor_category from "leanprover-community/mathlib"@"69c6a5a12d8a2b159f20933e60115a4f2de62b58"

/-!
# If `D` has finite (co)limits, so do the functor categories `C ⥤ D`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

These are boiler-plate instances, in their own file as neither import otherwise needs the other.
-/


open CategoryTheory

namespace CategoryTheory.Limits

universe v₁ v₂ u₁ u₂ w

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D]

#print CategoryTheory.Limits.functor_category_hasFiniteLimits /-
instance functor_category_hasFiniteLimits [HasFiniteLimits D] : HasFiniteLimits (C ⥤ D)
    where out J _ _ := inferInstance
#align category_theory.limits.functor_category_has_finite_limits CategoryTheory.Limits.functor_category_hasFiniteLimits
-/

#print CategoryTheory.Limits.functor_category_hasFiniteColimits /-
instance functor_category_hasFiniteColimits [HasFiniteColimits D] : HasFiniteColimits (C ⥤ D)
    where out J _ _ := inferInstance
#align category_theory.limits.functor_category_has_finite_colimits CategoryTheory.Limits.functor_category_hasFiniteColimits
-/

end CategoryTheory.Limits

