import Mathbin.CategoryTheory.Limits.Connected 
import Mathbin.CategoryTheory.Limits.Constructions.Over.Products 
import Mathbin.CategoryTheory.Limits.Constructions.Over.Connected 
import Mathbin.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers 
import Mathbin.CategoryTheory.Limits.Constructions.Equalizers

/-!
# Limits in the over category

Declare instances for limits in the over category: If `C` has finite wide pullbacks, `over B` has
finite limits, and if `C` has arbitrary wide pullbacks then `over B` has limits.
-/


universe v u

open CategoryTheory CategoryTheory.Limits

variable{J : Type v}[small_category J]

variable{C : Type u}[category.{v} C]

variable{X : C}

namespace CategoryTheory.Over

/-- Make sure we can derive pullbacks in `over B`. -/
example  {B : C} [has_pullbacks C] : has_pullbacks (over B) :=
  by 
    infer_instance

/-- Make sure we can derive equalizers in `over B`. -/
example  {B : C} [has_equalizers C] : has_equalizers (over B) :=
  by 
    infer_instance

-- error in CategoryTheory.Limits.Constructions.Over.Default: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance has_finite_limits {B : C} [has_finite_wide_pullbacks C] : has_finite_limits (over B) :=
begin
  apply [expr @finite_limits_from_equalizers_and_finite_products _ _ _ _],
  { exact [expr construct_products.over_finite_products_of_finite_wide_pullbacks] },
  { apply [expr @has_equalizers_of_pullbacks_and_binary_products _ _ _ _],
    { haveI [] [":", expr has_pullbacks C] [":=", expr ⟨by apply_instance⟩],
      exact [expr construct_products.over_binary_product_of_pullback] },
    { apply_instance } }
end

-- error in CategoryTheory.Limits.Constructions.Over.Default: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance has_limits {B : C} [has_wide_pullbacks C] : has_limits (over B) :=
begin
  apply [expr @limits_from_equalizers_and_products _ _ _ _],
  { exact [expr construct_products.over_products_of_wide_pullbacks] },
  { apply [expr @has_equalizers_of_pullbacks_and_binary_products _ _ _ _],
    { haveI [] [":", expr has_pullbacks C] [":=", expr ⟨by apply_instance⟩],
      exact [expr construct_products.over_binary_product_of_pullback] },
    { apply_instance } }
end

end CategoryTheory.Over

