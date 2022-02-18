import Mathbin.CategoryTheory.Limits.Preserves.Basic
import Mathbin.CategoryTheory.FinCategory

/-!
# Preservation of finite (co)limits.

These functors are also known as left exact (flat) or right exact functors when the categories
involved are abelian, or more generally, finitely (co)complete.

## Related results
* `category_theory.limits.preserves_finite_limits_of_preserves_equalizers_and_finite_products` :
  see `category_theory/limits/constructions/limits_of_products_and_equalizers.lean`. Also provides
  the dual version.
* `category_theory.limits.preserves_finite_limits_iff_flat` :
  see `category_theory/flat_functors.lean`.

-/


open CategoryTheory

namespace CategoryTheory.Limits

universe v u₁ u₂ u₃

variable {C : Type u₁} [Category.{v} C]

variable {D : Type u₂} [Category.{v} D]

variable {E : Type u₃} [Category.{v} E]

variable {J : Type v} [SmallCategory J] {K : J ⥤ C}

/-- A functor is said to preserve finite limits, if it preserves all limits of shape `J`, where
`J` is a finite category.
-/
class preserves_finite_limits (F : C ⥤ D) where
  PreservesFiniteLimits : ∀ J : Type v [SmallCategory J] [FinCategory J], PreservesLimitsOfShape J F := by
    run_tac
      tactic.apply_instance

attribute [instance] preserves_finite_limits.preserves_finite_limits

instance (priority := 100) preserves_limits.preserves_finite_limits (F : C ⥤ D) [PreservesLimits F] :
    PreservesFiniteLimits F :=
  {  }

instance id_preserves_finite_limits : PreservesFiniteLimits (𝟭 C) :=
  {  }

/-- The composition of two left exact functors is left exact. -/
def comp_preserves_finite_limits (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteLimits F] [PreservesFiniteLimits G] :
    PreservesFiniteLimits (F ⋙ G) :=
  ⟨fun _ _ _ => by
    skip
    infer_instance⟩

/-- A functor is said to preserve finite colimits, if it preserves all colimits of shape `J`, where
`J` is a finite category.
-/
class preserves_finite_colimits (F : C ⥤ D) where
  PreservesFiniteColimits : ∀ J : Type v [SmallCategory J] [FinCategory J], PreservesColimitsOfShape J F := by
    run_tac
      tactic.apply_instance

attribute [instance] preserves_finite_colimits.preserves_finite_colimits

instance (priority := 100) preserves_colimits.preserves_finite_colimits (F : C ⥤ D) [PreservesColimits F] :
    PreservesFiniteColimits F :=
  {  }

instance id_preserves_finite_colimits : PreservesFiniteColimits (𝟭 C) :=
  {  }

/-- The composition of two right exact functors is right exact. -/
def comp_preserves_finite_colimits (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteColimits F] [PreservesFiniteColimits G] :
    PreservesFiniteColimits (F ⋙ G) :=
  ⟨fun _ _ _ => by
    skip
    infer_instance⟩

end CategoryTheory.Limits

