import Mathbin.CategoryTheory.Limits.Preserves.Basic
import Mathbin.CategoryTheory.Filtered

/-!
# Preservation of filtered colimits and cofiltered limits.
Typically forgetful functors from algebraic categories preserve filtered colimits
(although not general colimits). See e.g. `algebra/category/Mon/filtered_colimits`.
-/


open CategoryTheory

open CategoryTheory.Functor

namespace CategoryTheory.Limits

universe v u₁ u₂ u₃

variable {C : Type u₁} [category.{v} C]

variable {D : Type u₂} [category.{v} D]

variable {E : Type u₃} [category.{v} E]

variable {J : Type v} [small_category J] {K : J ⥤ C}

/-- 
A functor is said to preserve filtered colimits, if it preserves all colimits of shape `J`, where
`J` is a filtered category.
-/
class preserves_filtered_colimits (F : C ⥤ D) : Type max u₁ u₂ (v + 1) where
  PreservesFilteredColimits : ∀ J : Type v [small_category J] [is_filtered J], preserves_colimits_of_shape J F

attribute [instance] preserves_filtered_colimits.preserves_filtered_colimits

instance (priority := 100) preserves_colimits.preserves_filtered_colimits (F : C ⥤ D) [preserves_colimits F] :
    preserves_filtered_colimits F where
  PreservesFilteredColimits := inferInstance

-- failed to format: format: uncaught backtrack exception
instance
  comp_preserves_filtered_colimits
  ( F : C ⥤ D ) ( G : D ⥤ E ) [ preserves_filtered_colimits F ] [ preserves_filtered_colimits G ]
    : preserves_filtered_colimits ( F ⋙ G )
  where PreservesFilteredColimits J _ _ := by exact inferInstance

/-- 
A functor is said to preserve cofiltered limits, if it preserves all limits of shape `J`, where
`J` is a cofiltered category.
-/
class preserves_cofiltered_limits (F : C ⥤ D) : Type max u₁ u₂ (v + 1) where
  PreservesCofilteredLimits : ∀ J : Type v [small_category J] [is_cofiltered J], preserves_limits_of_shape J F

attribute [instance] preserves_cofiltered_limits.preserves_cofiltered_limits

instance (priority := 100) preserves_limits.preserves_cofiltered_limits (F : C ⥤ D) [preserves_limits F] :
    preserves_cofiltered_limits F where
  PreservesCofilteredLimits := inferInstance

-- failed to format: format: uncaught backtrack exception
instance
  comp_preserves_cofiltered_limits
  ( F : C ⥤ D ) ( G : D ⥤ E ) [ preserves_cofiltered_limits F ] [ preserves_cofiltered_limits G ]
    : preserves_cofiltered_limits ( F ⋙ G )
  where PreservesCofilteredLimits J _ _ := by exact inferInstance

end CategoryTheory.Limits

