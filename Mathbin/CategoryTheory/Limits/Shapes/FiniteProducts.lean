/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathbin.CategoryTheory.Limits.Shapes.Products

/-!
# Categories with finite (co)products

Typeclasses representing categories with (co)products over finite indexing types.
-/


universe w v u

open CategoryTheory

open Classical

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]

-- We can't simply make this an abbreviation, as we do with other `has_Xs` limits typeclasses,
-- because of https://github.com/leanprover-community/lean/issues/429
/-- A category has finite products if there is a chosen limit for every diagram
with shape `discrete J`, where we have `[fintype J]`.
-/
class HasFiniteProducts : Prop where
  out (J : Type) [Fintype J] : HasLimitsOfShape (Discrete J) C
#align category_theory.limits.has_finite_products CategoryTheory.Limits.HasFiniteProducts

instance has_limits_of_shape_discrete (J : Type) [Finite J] [HasFiniteProducts C] : HasLimitsOfShape (Discrete J) C :=
  by
  cases nonempty_fintype J
  haveI := @has_finite_products.out C _ _ J
  infer_instance
#align category_theory.limits.has_limits_of_shape_discrete CategoryTheory.Limits.has_limits_of_shape_discrete

/-- If `C` has finite limits then it has finite products. -/
instance (priority := 10) has_finite_products_of_has_finite_limits [HasFiniteLimits C] : HasFiniteProducts C :=
  ⟨fun J 𝒥 => by
    skip
    infer_instance⟩
#align
  category_theory.limits.has_finite_products_of_has_finite_limits CategoryTheory.Limits.has_finite_products_of_has_finite_limits

instance has_fintype_products [HasFiniteProducts C] (ι : Type w) [Finite ι] : HasLimitsOfShape (Discrete ι) C := by
  cases nonempty_fintype ι <;>
    exact has_limits_of_shape_of_equivalence (discrete.equivalence (Equiv.ulift.{0}.trans (Fintype.equivFin ι).symm))
#align category_theory.limits.has_fintype_products CategoryTheory.Limits.has_fintype_products

/-- We can now write this for powers. -/
noncomputable example [HasFiniteProducts C] (X : C) : C :=
  ∏ fun i : Fin 5 => X

/-- If a category has all products then in particular it has finite products.
-/
theorem has_finite_products_of_has_products [HasProducts.{w} C] : HasFiniteProducts C :=
  ⟨fun J _ => has_limits_of_shape_of_equivalence (Discrete.equivalence Equiv.ulift.{w})⟩
#align
  category_theory.limits.has_finite_products_of_has_products CategoryTheory.Limits.has_finite_products_of_has_products

/-- A category has finite coproducts if there is a chosen colimit for every diagram
with shape `discrete J`, where we have `[fintype J]`.
-/
class HasFiniteCoproducts : Prop where
  out (J : Type) [Fintype J] : HasColimitsOfShape (Discrete J) C
#align category_theory.limits.has_finite_coproducts CategoryTheory.Limits.HasFiniteCoproducts

attribute [class] has_finite_coproducts

instance has_colimits_of_shape_discrete (J : Type) [Finite J] [HasFiniteCoproducts C] :
    HasColimitsOfShape (Discrete J) C := by
  cases nonempty_fintype J
  haveI := @has_finite_coproducts.out C _ _ J
  infer_instance
#align category_theory.limits.has_colimits_of_shape_discrete CategoryTheory.Limits.has_colimits_of_shape_discrete

/-- If `C` has finite colimits then it has finite coproducts. -/
instance (priority := 10) has_finite_coproducts_of_has_finite_colimits [HasFiniteColimits C] : HasFiniteCoproducts C :=
  ⟨fun J 𝒥 => by
    skip
    infer_instance⟩
#align
  category_theory.limits.has_finite_coproducts_of_has_finite_colimits CategoryTheory.Limits.has_finite_coproducts_of_has_finite_colimits

instance has_fintype_coproducts [HasFiniteCoproducts C] (ι : Type w) [Fintype ι] : HasColimitsOfShape (Discrete ι) C :=
  by
  cases nonempty_fintype ι <;>
    exact has_colimits_of_shape_of_equivalence (discrete.equivalence (Equiv.ulift.{0}.trans (Fintype.equivFin ι).symm))
#align category_theory.limits.has_fintype_coproducts CategoryTheory.Limits.has_fintype_coproducts

/-- If a category has all coproducts then in particular it has finite coproducts.
-/
theorem has_finite_coproducts_of_has_coproducts [HasCoproducts.{w} C] : HasFiniteCoproducts C :=
  ⟨fun J _ => has_colimits_of_shape_of_equivalence (Discrete.equivalence Equiv.ulift.{w})⟩
#align
  category_theory.limits.has_finite_coproducts_of_has_coproducts CategoryTheory.Limits.has_finite_coproducts_of_has_coproducts

end CategoryTheory.Limits

