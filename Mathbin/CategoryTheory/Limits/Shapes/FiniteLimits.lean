/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import CategoryTheory.FinCategory.Basic
import CategoryTheory.Limits.Shapes.BinaryProducts
import CategoryTheory.Limits.Shapes.Equalizers
import CategoryTheory.Limits.Shapes.WidePullbacks
import CategoryTheory.Limits.Shapes.Pullback.Cospan
import Data.Fintype.Option

#align_import category_theory.limits.shapes.finite_limits from "leanprover-community/mathlib"@"f47581155c818e6361af4e4fda60d27d020c226b"

/-!
# Categories with finite limits.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A typeclass for categories with all finite (co)limits.
-/


universe w' w v' u' v u

noncomputable section

open CategoryTheory

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]

#print CategoryTheory.Limits.HasFiniteLimits /-
-- We can't just made this an `abbreviation`
-- because of https://github.com/leanprover-community/lean/issues/429
/-- A category has all finite limits if every functor `J ⥤ C` with a `fin_category J`
instance and `J : Type` has a limit.

This is often called 'finitely complete'.
-/
class HasFiniteLimits : Prop where
  out (J : Type) [𝒥 : SmallCategory J] [@FinCategory J 𝒥] : @HasLimitsOfShape J 𝒥 C _
#align category_theory.limits.has_finite_limits CategoryTheory.Limits.HasFiniteLimits
-/

#print CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits /-
instance (priority := 100) hasLimitsOfShape_of_hasFiniteLimits (J : Type w) [SmallCategory J]
    [FinCategory J] [HasFiniteLimits C] : HasLimitsOfShape J C :=
  by
  apply has_limits_of_shape_of_equivalence (fin_category.equiv_as_type J)
  apply has_finite_limits.out
#align category_theory.limits.has_limits_of_shape_of_has_finite_limits CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits
-/

#print CategoryTheory.Limits.hasFiniteLimits_of_hasLimitsOfSize /-
instance (priority := 100) hasFiniteLimits_of_hasLimitsOfSize [HasLimitsOfSize.{v', u'} C] :
    HasFiniteLimits C :=
  ⟨fun J hJ hJ' =>
    haveI := hasLimitsOfSizeShrink.{0, 0} C
    has_limits_of_shape_of_equivalence (fin_category.equiv_as_type J)⟩
#align category_theory.limits.has_finite_limits_of_has_limits_of_size CategoryTheory.Limits.hasFiniteLimits_of_hasLimitsOfSize
-/

#print CategoryTheory.Limits.hasFiniteLimits_of_hasLimits /-
/-- If `C` has all limits, it has finite limits. -/
instance (priority := 100) hasFiniteLimits_of_hasLimits [HasLimits C] : HasFiniteLimits C :=
  inferInstance
#align category_theory.limits.has_finite_limits_of_has_limits CategoryTheory.Limits.hasFiniteLimits_of_hasLimits
-/

#print CategoryTheory.Limits.hasFiniteLimits_of_hasFiniteLimits_of_size /-
/-- We can always derive `has_finite_limits C` by providing limits at an
arbitrary universe. -/
theorem hasFiniteLimits_of_hasFiniteLimits_of_size
    (h :
      ∀ (J : Type w) {𝒥 : SmallCategory J} (hJ : @FinCategory J 𝒥), by skip;
        exact has_limits_of_shape J C) :
    HasFiniteLimits C :=
  ⟨fun J hJ hhJ => by
    skip
    let this.1 : Category.{w, w} (ULiftHom.{w} (ULift.{w, 0} J)) := by apply ULiftHom.category.{0};
      exact CategoryTheory.uliftCategory J
    haveI := h (ULiftHom.{w} (ULift.{w} J)) CategoryTheory.finCategoryUlift
    exact has_limits_of_shape_of_equivalence (ULiftHomULiftCategory.equiv.{w, w} J).symm⟩
#align category_theory.limits.has_finite_limits_of_has_finite_limits_of_size CategoryTheory.Limits.hasFiniteLimits_of_hasFiniteLimits_of_size
-/

#print CategoryTheory.Limits.HasFiniteColimits /-
/-- A category has all finite colimits if every functor `J ⥤ C` with a `fin_category J`
instance and `J : Type` has a colimit.

This is often called 'finitely cocomplete'.
-/
class HasFiniteColimits : Prop where
  out (J : Type) [𝒥 : SmallCategory J] [@FinCategory J 𝒥] : @HasColimitsOfShape J 𝒥 C _
#align category_theory.limits.has_finite_colimits CategoryTheory.Limits.HasFiniteColimits
-/

#print CategoryTheory.Limits.hasColimitsOfShape_of_hasFiniteColimits /-
instance (priority := 100) hasColimitsOfShape_of_hasFiniteColimits (J : Type w) [SmallCategory J]
    [FinCategory J] [HasFiniteColimits C] : HasColimitsOfShape J C :=
  by
  apply has_colimits_of_shape_of_equivalence (fin_category.equiv_as_type J)
  apply has_finite_colimits.out
#align category_theory.limits.has_colimits_of_shape_of_has_finite_colimits CategoryTheory.Limits.hasColimitsOfShape_of_hasFiniteColimits
-/

#print CategoryTheory.Limits.hasFiniteColimits_of_hasColimitsOfSize /-
instance (priority := 100) hasFiniteColimits_of_hasColimitsOfSize [HasColimitsOfSize.{v', u'} C] :
    HasFiniteColimits C :=
  ⟨fun J hJ hJ' =>
    haveI := hasColimitsOfSizeShrink.{0, 0} C
    has_colimits_of_shape_of_equivalence (fin_category.equiv_as_type J)⟩
#align category_theory.limits.has_finite_colimits_of_has_colimits_of_size CategoryTheory.Limits.hasFiniteColimits_of_hasColimitsOfSize
-/

#print CategoryTheory.Limits.hasFiniteColimits_of_hasFiniteColimits_of_size /-
/-- We can always derive `has_finite_colimits C` by providing colimits at an
arbitrary universe. -/
theorem hasFiniteColimits_of_hasFiniteColimits_of_size
    (h :
      ∀ (J : Type w) {𝒥 : SmallCategory J} (hJ : @FinCategory J 𝒥), by skip;
        exact has_colimits_of_shape J C) :
    HasFiniteColimits C :=
  ⟨fun J hJ hhJ => by
    skip
    let this.1 : Category.{w, w} (ULiftHom.{w} (ULift.{w, 0} J)) := by apply ULiftHom.category.{0};
      exact CategoryTheory.uliftCategory J
    haveI := h (ULiftHom.{w} (ULift.{w} J)) CategoryTheory.finCategoryUlift
    exact has_colimits_of_shape_of_equivalence (ULiftHomULiftCategory.equiv.{w, w} J).symm⟩
#align category_theory.limits.has_finite_colimits_of_has_finite_colimits_of_size CategoryTheory.Limits.hasFiniteColimits_of_hasFiniteColimits_of_size
-/

section

open WalkingParallelPair WalkingParallelPairHom

#print CategoryTheory.Limits.fintypeWalkingParallelPair /-
instance fintypeWalkingParallelPair : Fintype WalkingParallelPair
    where
  elems := [WalkingParallelPair.zero, WalkingParallelPair.one].toFinset
  complete x := by cases x <;> simp
#align category_theory.limits.fintype_walking_parallel_pair CategoryTheory.Limits.fintypeWalkingParallelPair
-/

attribute [local tidy] tactic.case_bash

instance (j j' : WalkingParallelPair) : Fintype (WalkingParallelPairHom j j')
    where
  elems :=
    WalkingParallelPair.recOn j
      (WalkingParallelPair.recOn j' [WalkingParallelPairHom.id zero].toFinset
        [left, right].toFinset)
      (WalkingParallelPair.recOn j' ∅ [WalkingParallelPairHom.id one].toFinset)
  complete := by tidy

end

instance : FinCategory WalkingParallelPair where

/-- Equalizers are finite limits, so if `C` has all finite limits, it also has all equalizers -/
example [HasFiniteLimits C] : HasEqualizers C := by infer_instance

/-- Coequalizers are finite colimits, of if `C` has all finite colimits, it also has all
    coequalizers -/
example [HasFiniteColimits C] : HasCoequalizers C := by infer_instance

variable {J : Type v}

attribute [local tidy] tactic.case_bash

namespace WidePullbackShape

#print CategoryTheory.Limits.WidePullbackShape.fintypeObj /-
instance fintypeObj [Fintype J] : Fintype (WidePullbackShape J) := by rw [wide_pullback_shape];
  infer_instance
#align category_theory.limits.wide_pullback_shape.fintype_obj CategoryTheory.Limits.WidePullbackShape.fintypeObj
-/

#print CategoryTheory.Limits.WidePullbackShape.fintypeHom /-
instance fintypeHom (j j' : WidePullbackShape J) : Fintype (j ⟶ j')
    where
  elems := by
    cases j'
    · cases j
      · exact {hom.id none}
      · exact {hom.term j}
    · by_cases some j' = j
      · rw [h]
        exact {hom.id j}
      · exact ∅
  complete := by tidy
#align category_theory.limits.wide_pullback_shape.fintype_hom CategoryTheory.Limits.WidePullbackShape.fintypeHom
-/

end WidePullbackShape

namespace WidePushoutShape

#print CategoryTheory.Limits.WidePushoutShape.fintypeObj /-
instance fintypeObj [Fintype J] : Fintype (WidePushoutShape J) := by rw [wide_pushout_shape];
  infer_instance
#align category_theory.limits.wide_pushout_shape.fintype_obj CategoryTheory.Limits.WidePushoutShape.fintypeObj
-/

#print CategoryTheory.Limits.WidePushoutShape.fintypeHom /-
instance fintypeHom (j j' : WidePushoutShape J) : Fintype (j ⟶ j')
    where
  elems := by
    cases j
    · cases j'
      · exact {hom.id none}
      · exact {hom.init j'}
    · by_cases some j = j'
      · rw [h]
        exact {hom.id j'}
      · exact ∅
  complete := by tidy
#align category_theory.limits.wide_pushout_shape.fintype_hom CategoryTheory.Limits.WidePushoutShape.fintypeHom
-/

end WidePushoutShape

#print CategoryTheory.Limits.finCategoryWidePullback /-
instance finCategoryWidePullback [Fintype J] : FinCategory (WidePullbackShape J)
    where fintypeHom := WidePullbackShape.fintypeHom
#align category_theory.limits.fin_category_wide_pullback CategoryTheory.Limits.finCategoryWidePullback
-/

#print CategoryTheory.Limits.finCategoryWidePushout /-
instance finCategoryWidePushout [Fintype J] : FinCategory (WidePushoutShape J)
    where fintypeHom := WidePushoutShape.fintypeHom
#align category_theory.limits.fin_category_wide_pushout CategoryTheory.Limits.finCategoryWidePushout
-/

#print CategoryTheory.Limits.HasFiniteWidePullbacks /-
-- We can't just made this an `abbreviation`
-- because of https://github.com/leanprover-community/lean/issues/429
/-- `has_finite_wide_pullbacks` represents a choice of wide pullback
for every finite collection of morphisms
-/
class HasFiniteWidePullbacks : Prop where
  out (J : Type) [Fintype J] : HasLimitsOfShape (WidePullbackShape J) C
#align category_theory.limits.has_finite_wide_pullbacks CategoryTheory.Limits.HasFiniteWidePullbacks
-/

#print CategoryTheory.Limits.hasLimitsOfShape_widePullbackShape /-
instance hasLimitsOfShape_widePullbackShape (J : Type) [Finite J] [HasFiniteWidePullbacks C] :
    HasLimitsOfShape (WidePullbackShape J) C := by cases nonempty_fintype J;
  haveI := @has_finite_wide_pullbacks.out C _ _ J; infer_instance
#align category_theory.limits.has_limits_of_shape_wide_pullback_shape CategoryTheory.Limits.hasLimitsOfShape_widePullbackShape
-/

#print CategoryTheory.Limits.HasFiniteWidePushouts /-
/-- `has_finite_wide_pushouts` represents a choice of wide pushout
for every finite collection of morphisms
-/
class HasFiniteWidePushouts : Prop where
  out (J : Type) [Fintype J] : HasColimitsOfShape (WidePushoutShape J) C
#align category_theory.limits.has_finite_wide_pushouts CategoryTheory.Limits.HasFiniteWidePushouts
-/

#print CategoryTheory.Limits.hasColimitsOfShape_widePushoutShape /-
instance hasColimitsOfShape_widePushoutShape (J : Type) [Finite J] [HasFiniteWidePushouts C] :
    HasColimitsOfShape (WidePushoutShape J) C := by cases nonempty_fintype J;
  haveI := @has_finite_wide_pushouts.out C _ _ J; infer_instance
#align category_theory.limits.has_colimits_of_shape_wide_pushout_shape CategoryTheory.Limits.hasColimitsOfShape_widePushoutShape
-/

#print CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits /-
/-- Finite wide pullbacks are finite limits, so if `C` has all finite limits,
it also has finite wide pullbacks
-/
theorem hasFiniteWidePullbacks_of_hasFiniteLimits [HasFiniteLimits C] : HasFiniteWidePullbacks C :=
  ⟨fun J _ => has_finite_limits.out _⟩
#align category_theory.limits.has_finite_wide_pullbacks_of_has_finite_limits CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits
-/

#print CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits /-
/-- Finite wide pushouts are finite colimits, so if `C` has all finite colimits,
it also has finite wide pushouts
-/
theorem hasFiniteWidePushouts_of_has_finite_limits [HasFiniteColimits C] :
    HasFiniteWidePushouts C :=
  ⟨fun J _ => has_finite_colimits.out _⟩
#align category_theory.limits.has_finite_wide_pushouts_of_has_finite_limits CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits
-/

#print CategoryTheory.Limits.fintypeWalkingPair /-
instance fintypeWalkingPair : Fintype WalkingPair
    where
  elems := {WalkingPair.left, WalkingPair.right}
  complete x := by cases x <;> simp
#align category_theory.limits.fintype_walking_pair CategoryTheory.Limits.fintypeWalkingPair
-/

/-- Pullbacks are finite limits, so if `C` has all finite limits, it also has all pullbacks -/
example [HasFiniteWidePullbacks C] : HasPullbacks C := by infer_instance

/-- Pushouts are finite colimits, so if `C` has all finite colimits, it also has all pushouts -/
example [HasFiniteWidePushouts C] : HasPushouts C := by infer_instance

end CategoryTheory.Limits

