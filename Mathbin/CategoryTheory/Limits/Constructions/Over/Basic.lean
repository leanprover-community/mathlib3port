/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta
-/
import CategoryTheory.Limits.Connected
import CategoryTheory.Limits.Constructions.Over.Products
import CategoryTheory.Limits.Constructions.Over.Connected
import CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import CategoryTheory.Limits.Constructions.Equalizers

#align_import category_theory.limits.constructions.over.basic from "leanprover-community/mathlib"@"728ef9dbb281241906f25cbeb30f90d83e0bb451"

/-!
# Limits in the over category

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Declare instances for limits in the over category: If `C` has finite wide pullbacks, `over B` has
finite limits, and if `C` has arbitrary wide pullbacks then `over B` has limits.
-/


universe w v u

-- morphism levels before object levels. See note [category_theory universes].
open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

variable {X : C}

namespace CategoryTheory.Over

/-- Make sure we can derive pullbacks in `over B`. -/
instance {B : C} [HasPullbacks C] : HasPullbacks (Over B) :=
  by
  letI : has_limits_of_shape (ULiftHom.{v} (ULift.{v} walking_cospan)) C :=
    has_limits_of_shape_of_equivalence (ULiftHomULiftCategory.equiv.{v} _)
  letI : category (ULiftHom.{v} (ULift.{v} walking_cospan)) := inferInstance
  exact has_limits_of_shape_of_equivalence (ULiftHomULiftCategory.equiv.{v, v} _).symm

/-- Make sure we can derive equalizers in `over B`. -/
instance {B : C} [HasEqualizers C] : HasEqualizers (Over B) :=
  by
  letI : has_limits_of_shape (ULiftHom.{v} (ULift.{v} walking_parallel_pair)) C :=
    has_limits_of_shape_of_equivalence (ULiftHomULiftCategory.equiv.{v} _)
  letI : category (ULiftHom.{v} (ULift.{v} walking_parallel_pair)) := inferInstance
  exact has_limits_of_shape_of_equivalence (ULiftHomULiftCategory.equiv.{v, v} _).symm

#print CategoryTheory.Over.hasFiniteLimits /-
instance hasFiniteLimits {B : C} [HasFiniteWidePullbacks C] : HasFiniteLimits (Over B) :=
  by
  apply @has_finite_limits_of_has_equalizers_and_finite_products _ _ _ _
  · exact construct_products.over_finite_products_of_finite_wide_pullbacks
  · apply @has_equalizers_of_has_pullbacks_and_binary_products _ _ _ _
    · haveI : has_pullbacks C := ⟨by infer_instance⟩
      exact construct_products.over_binary_product_of_pullback
    · infer_instance
#align category_theory.over.has_finite_limits CategoryTheory.Over.hasFiniteLimits
-/

#print CategoryTheory.Over.hasLimits /-
instance hasLimits {B : C} [HasWidePullbacks.{w} C] : HasLimitsOfSize.{w} (Over B) :=
  by
  apply @has_limits_of_has_equalizers_and_products _ _ _ _
  · exact construct_products.over_products_of_wide_pullbacks
  · apply @has_equalizers_of_has_pullbacks_and_binary_products _ _ _ _
    · haveI : has_pullbacks C := ⟨inferInstance⟩
      exact construct_products.over_binary_product_of_pullback
    · infer_instance
#align category_theory.over.has_limits CategoryTheory.Over.hasLimits
-/

end CategoryTheory.Over

