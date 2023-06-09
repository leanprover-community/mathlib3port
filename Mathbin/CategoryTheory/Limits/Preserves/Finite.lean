/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module category_theory.limits.preserves.finite
! leanprover-community/mathlib commit 3974a774a707e2e06046a14c0eaef4654584fada
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Preserves.Basic
import Mathbin.CategoryTheory.FinCategory

/-!
# Preservation of finite (co)limits.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

-- declare the `v`'s first; see `category_theory.category` for an explanation
universe w w₂ v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D]

variable {E : Type u₃} [Category.{v₃} E]

variable {J : Type w} [SmallCategory J] {K : J ⥤ C}

#print CategoryTheory.Limits.PreservesFiniteLimits /-
/-- A functor is said to preserve finite limits, if it preserves all limits of shape `J`,
where `J : Type` is a finite category.
-/
class PreservesFiniteLimits (F : C ⥤ D) where
  PreservesFiniteLimits :
    ∀ (J : Type) [SmallCategory J] [FinCategory J], PreservesLimitsOfShape J F := by infer_instance
#align category_theory.limits.preserves_finite_limits CategoryTheory.Limits.PreservesFiniteLimits
-/

attribute [instance] preserves_finite_limits.preserves_finite_limits

#print CategoryTheory.Limits.preservesLimitsOfShapeOfPreservesFiniteLimits /-
/-- Preserving finite limits also implies preserving limits over finite shapes in higher universes,
though through a noncomputable instance. -/
noncomputable instance (priority := 100) preservesLimitsOfShapeOfPreservesFiniteLimits (F : C ⥤ D)
    [PreservesFiniteLimits F] (J : Type w) [SmallCategory J] [FinCategory J] :
    PreservesLimitsOfShape J F := by
  apply preserves_limits_of_shape_of_equiv (fin_category.equiv_as_type J)
#align category_theory.limits.preserves_limits_of_shape_of_preserves_finite_limits CategoryTheory.Limits.preservesLimitsOfShapeOfPreservesFiniteLimits
-/

/- warning: category_theory.limits.preserves_limits_of_size.preserves_finite_limits clashes with category_theory.limits.preserves_limits.preserves_finite_limits_of_size -> CategoryTheory.Limits.PreservesLimitsOfSize.preservesFiniteLimits
Case conversion may be inaccurate. Consider using '#align category_theory.limits.preserves_limits_of_size.preserves_finite_limits CategoryTheory.Limits.PreservesLimitsOfSize.preservesFiniteLimitsₓ'. -/
#print CategoryTheory.Limits.PreservesLimitsOfSize.preservesFiniteLimits /-
-- This is a dangerous instance as it has unbound universe variables.
/-- If we preserve limits of some arbitrary size, then we preserve all finite limits. -/
noncomputable def PreservesLimitsOfSize.preservesFiniteLimits (F : C ⥤ D)
    [PreservesLimitsOfSize.{w, w₂} F] : PreservesFiniteLimits F :=
  ⟨fun J sJ fJ =>
    haveI := preserves_smallest_limits_of_preserves_limits F
    preserves_limits_of_shape_of_equiv (fin_category.equiv_as_type J) F⟩
#align category_theory.limits.preserves_limits_of_size.preserves_finite_limits CategoryTheory.Limits.PreservesLimitsOfSize.preservesFiniteLimits
-/

-- Added as a specialization of the dangerous instance above, for limits indexed in Type 0.
noncomputable instance (priority := 120) PreservesLimitsOfSize.Zero.preservesFiniteLimits
    (F : C ⥤ D) [PreservesLimitsOfSize.{0, 0} F] : PreservesFiniteLimits F :=
  PreservesLimitsOfSize.preservesFiniteLimits F
#align category_theory.limits.preserves_limits_of_size.zero.preserves_finite_limits CategoryTheory.Limits.PreservesLimitsOfSize.Zero.preservesFiniteLimits

#print CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits /-
-- An alternative specialization of the dangerous instance for small limits.
noncomputable instance (priority := 120) PreservesLimits.preservesFiniteLimits (F : C ⥤ D)
    [PreservesLimits F] : PreservesFiniteLimits F :=
  PreservesLimitsOfSize.preservesFiniteLimits F
#align category_theory.limits.preserves_limits.preserves_finite_limits CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits
-/

#print CategoryTheory.Limits.preservesFiniteLimitsOfPreservesFiniteLimitsOfSize /-
/-- We can always derive `preserves_finite_limits C` by showing that we are preserving limits at an
arbitrary universe. -/
def preservesFiniteLimitsOfPreservesFiniteLimitsOfSize (F : C ⥤ D)
    (h :
      ∀ (J : Type w) {𝒥 : SmallCategory J} (hJ : @FinCategory J 𝒥), by skip;
        exact preserves_limits_of_shape J F) :
    PreservesFiniteLimits F :=
  ⟨fun J hJ hhJ => by
    skip
    let this.1 : Category.{w, w} (ULiftHom.{w} (ULift.{w, 0} J)) := by apply ULiftHom.category.{0};
      exact CategoryTheory.uliftCategory J
    haveI := h (ULiftHom.{w} (ULift.{w} J)) CategoryTheory.finCategoryUlift
    exact preserves_limits_of_shape_of_equiv (ULiftHomULiftCategory.equiv.{w, w} J).symm F⟩
#align category_theory.limits.preserves_finite_limits_of_preserves_finite_limits_of_size CategoryTheory.Limits.preservesFiniteLimitsOfPreservesFiniteLimitsOfSize
-/

#print CategoryTheory.Limits.idPreservesFiniteLimits /-
instance idPreservesFiniteLimits : PreservesFiniteLimits (𝟭 C) where
#align category_theory.limits.id_preserves_finite_limits CategoryTheory.Limits.idPreservesFiniteLimits
-/

#print CategoryTheory.Limits.compPreservesFiniteLimits /-
/-- The composition of two left exact functors is left exact. -/
def compPreservesFiniteLimits (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteLimits F]
    [PreservesFiniteLimits G] : PreservesFiniteLimits (F ⋙ G) :=
  ⟨fun _ _ _ => by skip; infer_instance⟩
#align category_theory.limits.comp_preserves_finite_limits CategoryTheory.Limits.compPreservesFiniteLimits
-/

#print CategoryTheory.Limits.PreservesFiniteColimits /-
/-- A functor is said to preserve finite colimits, if it preserves all colimits of
shape `J`, where `J : Type` is a finite category.
-/
class PreservesFiniteColimits (F : C ⥤ D) where
  PreservesFiniteColimits :
    ∀ (J : Type) [SmallCategory J] [FinCategory J], PreservesColimitsOfShape J F := by
    infer_instance
#align category_theory.limits.preserves_finite_colimits CategoryTheory.Limits.PreservesFiniteColimits
-/

attribute [instance] preserves_finite_colimits.preserves_finite_colimits

#print CategoryTheory.Limits.preservesColimitsOfShapeOfPreservesFiniteColimits /-
/-- Preserving finite limits also implies preserving limits over finite shapes in higher universes,
though through a noncomputable instance. -/
noncomputable instance (priority := 100) preservesColimitsOfShapeOfPreservesFiniteColimits
    (F : C ⥤ D) [PreservesFiniteColimits F] (J : Type w) [SmallCategory J] [FinCategory J] :
    PreservesColimitsOfShape J F := by
  apply preserves_colimits_of_shape_of_equiv (fin_category.equiv_as_type J)
#align category_theory.limits.preserves_colimits_of_shape_of_preserves_finite_colimits CategoryTheory.Limits.preservesColimitsOfShapeOfPreservesFiniteColimits
-/

#print CategoryTheory.Limits.PreservesColimitsOfSize.preservesFiniteColimits /-
-- This is a dangerous instance as it has unbound universe variables.
/-- If we preserve colimits of some arbitrary size, then we preserve all finite colimits. -/
noncomputable def PreservesColimitsOfSize.preservesFiniteColimits (F : C ⥤ D)
    [PreservesColimitsOfSize.{w, w₂} F] : PreservesFiniteColimits F :=
  ⟨fun J sJ fJ =>
    haveI := preserves_smallest_colimits_of_preserves_colimits F
    preserves_colimits_of_shape_of_equiv (fin_category.equiv_as_type J) F⟩
#align category_theory.limits.preserves_colimits_of_size.preserves_finite_colimits CategoryTheory.Limits.PreservesColimitsOfSize.preservesFiniteColimits
-/

-- Added as a specialization of the dangerous instance above, for colimits indexed in Type 0.
noncomputable instance (priority := 120) PreservesColimitsOfSize.Zero.preservesFiniteColimits
    (F : C ⥤ D) [PreservesColimitsOfSize.{0, 0} F] : PreservesFiniteColimits F :=
  PreservesColimitsOfSize.preservesFiniteColimits F
#align category_theory.limits.preserves_colimits_of_size.zero.preserves_finite_colimits CategoryTheory.Limits.PreservesColimitsOfSize.Zero.preservesFiniteColimits

#print CategoryTheory.Limits.PreservesColimits.preservesFiniteColimits /-
-- An alternative specialization of the dangerous instance for small colimits.
noncomputable instance (priority := 120) PreservesColimits.preservesFiniteColimits (F : C ⥤ D)
    [PreservesColimits F] : PreservesFiniteColimits F :=
  PreservesColimitsOfSize.preservesFiniteColimits F
#align category_theory.limits.preserves_colimits.preserves_finite_colimits CategoryTheory.Limits.PreservesColimits.preservesFiniteColimits
-/

#print CategoryTheory.Limits.preservesFiniteColimitsOfPreservesFiniteColimitsOfSize /-
/-- We can always derive `preserves_finite_limits C` by showing that we are preserving limits at an
arbitrary universe. -/
def preservesFiniteColimitsOfPreservesFiniteColimitsOfSize (F : C ⥤ D)
    (h :
      ∀ (J : Type w) {𝒥 : SmallCategory J} (hJ : @FinCategory J 𝒥), by skip;
        exact preserves_colimits_of_shape J F) :
    PreservesFiniteColimits F :=
  ⟨fun J hJ hhJ => by
    skip
    let this.1 : Category.{w, w} (ULiftHom.{w} (ULift.{w, 0} J)) := by apply ULiftHom.category.{0};
      exact CategoryTheory.uliftCategory J
    haveI := h (ULiftHom.{w} (ULift.{w} J)) CategoryTheory.finCategoryUlift
    exact preserves_colimits_of_shape_of_equiv (ULiftHomULiftCategory.equiv.{w, w} J).symm F⟩
#align category_theory.limits.preserves_finite_colimits_of_preserves_finite_colimits_of_size CategoryTheory.Limits.preservesFiniteColimitsOfPreservesFiniteColimitsOfSize
-/

#print CategoryTheory.Limits.idPreservesFiniteColimits /-
instance idPreservesFiniteColimits : PreservesFiniteColimits (𝟭 C) where
#align category_theory.limits.id_preserves_finite_colimits CategoryTheory.Limits.idPreservesFiniteColimits
-/

#print CategoryTheory.Limits.compPreservesFiniteColimits /-
/-- The composition of two right exact functors is right exact. -/
def compPreservesFiniteColimits (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteColimits F]
    [PreservesFiniteColimits G] : PreservesFiniteColimits (F ⋙ G) :=
  ⟨fun _ _ _ => by skip; infer_instance⟩
#align category_theory.limits.comp_preserves_finite_colimits CategoryTheory.Limits.compPreservesFiniteColimits
-/

end CategoryTheory.Limits

