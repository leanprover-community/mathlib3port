/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.FinCategory
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Limits.Shapes.Equalizers
import Mathbin.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks
import Mathbin.Data.Fintype.Basic

/-!
# Categories with finite limits.

A typeclass for categories with all finite (co)limits.
-/


universe v' u' v u

open CategoryTheory

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]

/-- A category has all finite limits if every functor `J ⥤ C` with a `fin_category J` instance
has a limit.

This is often called 'finitely complete'.
-/
-- We can't just made this an `abbreviation`
-- because of https://github.com/leanprover-community/lean/issues/429
class HasFiniteLimits : Prop where
  out (J : Type v) [𝒥 : SmallCategory J] [@FinCategory J 𝒥] : @HasLimitsOfShape J 𝒥 C _

instance (priority := 100) has_limits_of_shape_of_has_finite_limits (J : Type v) [SmallCategory J] [FinCategory J]
    [HasFiniteLimits C] : HasLimitsOfShape J C :=
  HasFiniteLimits.out J

instance (priority := 100) has_finite_limits_of_has_limits_of_size [HasLimitsOfSize.{v', u'} C] : HasFiniteLimits C :=
  ⟨fun J hJ hJ' =>
    have := has_limits_of_size_shrink.{0, 0} C
    has_limits_of_shape_of_equivalence (fin_category.equiv_as_type J)⟩

/-- If `C` has all limits, it has finite limits. -/
instance (priority := 100) has_finite_limits_of_has_limits [HasLimits C] : HasFiniteLimits C :=
  inferInstance

/-- A category has all finite colimits if every functor `J ⥤ C` with a `fin_category J` instance
has a colimit.

This is often called 'finitely cocomplete'.
-/
class HasFiniteColimits : Prop where
  out (J : Type v) [𝒥 : SmallCategory J] [@FinCategory J 𝒥] : @HasColimitsOfShape J 𝒥 C _

instance (priority := 100) has_limits_of_shape_of_has_finite_colimits (J : Type v) [SmallCategory J] [FinCategory J]
    [HasFiniteColimits C] : HasColimitsOfShape J C :=
  HasFiniteColimits.out J

instance (priority := 100) has_finite_colimits_of_has_colimits_of_size [HasColimitsOfSize.{v', u'} C] :
    HasFiniteColimits C :=
  ⟨fun J hJ hJ' =>
    have := has_colimits_of_size_shrink.{0, 0} C
    has_colimits_of_shape_of_equivalence (fin_category.equiv_as_type J)⟩

/-- If `C` has all colimits, it has finite colimits. -/
instance (priority := 100) has_finite_colimits_of_has_colimits [HasColimits C] : HasFiniteColimits C :=
  inferInstance

section

open WalkingParallelPair WalkingParallelPairHom

instance fintypeWalkingParallelPair : Fintype WalkingParallelPair where
  elems := [WalkingParallelPair.zero, WalkingParallelPair.one].toFinset
  complete := fun x => by
    cases x <;> simp

attribute [local tidy] tactic.case_bash

instance (j j' : WalkingParallelPair) : Fintype (WalkingParallelPairHom j j') where
  elems :=
    WalkingParallelPair.recOn j
      (WalkingParallelPair.recOn j' [WalkingParallelPairHom.id zero].toFinset [left, right].toFinset)
      (WalkingParallelPair.recOn j' ∅ [WalkingParallelPairHom.id one].toFinset)
  complete := by
    tidy

end

instance : FinCategory WalkingParallelPair :=
  {  }

/-- Equalizers are finite limits, so if `C` has all finite limits, it also has all equalizers -/
example [HasFiniteLimits C] : HasEqualizers C := by
  infer_instance

/-- Coequalizers are finite colimits, of if `C` has all finite colimits, it also has all
    coequalizers -/
example [HasFiniteColimits C] : HasCoequalizers C := by
  infer_instance

variable {J : Type v}

attribute [local tidy] tactic.case_bash

namespace WidePullbackShape

instance fintypeObj [Fintype J] : Fintype (WidePullbackShape J) := by
  rw [wide_pullback_shape]
  infer_instance

instance fintypeHom [DecidableEq J] (j j' : WidePullbackShape J) : Fintype (j ⟶ j') where
  elems := by
    cases j'
    · cases j
      · exact {hom.id none}
        
      · exact {hom.term j}
        
      
    · by_cases' some j' = j
      · rw [h]
        exact {hom.id j}
        
      · exact ∅
        
      
  complete := by
    tidy

end WidePullbackShape

namespace WidePushoutShape

instance fintypeObj [Fintype J] : Fintype (WidePushoutShape J) := by
  rw [wide_pushout_shape]
  infer_instance

instance fintypeHom [DecidableEq J] (j j' : WidePushoutShape J) : Fintype (j ⟶ j') where
  elems := by
    cases j
    · cases j'
      · exact {hom.id none}
        
      · exact {hom.init j'}
        
      
    · by_cases' some j = j'
      · rw [h]
        exact {hom.id j'}
        
      · exact ∅
        
      
  complete := by
    tidy

end WidePushoutShape

instance finCategoryWidePullback [DecidableEq J] [Fintype J] : FinCategory (WidePullbackShape J) where
  fintypeHom := WidePullbackShape.fintypeHom

instance finCategoryWidePushout [DecidableEq J] [Fintype J] : FinCategory (WidePushoutShape J) where
  fintypeHom := WidePushoutShape.fintypeHom

/-- `has_finite_wide_pullbacks` represents a choice of wide pullback
for every finite collection of morphisms
-/
-- We can't just made this an `abbreviation`
-- because of https://github.com/leanprover-community/lean/issues/429
class HasFiniteWidePullbacks : Prop where
  out (J : Type v) [DecidableEq J] [Fintype J] : HasLimitsOfShape (WidePullbackShape J) C

instance has_limits_of_shape_wide_pullback_shape (J : Type v) [Fintype J] [HasFiniteWidePullbacks C] :
    HasLimitsOfShape (WidePullbackShape J) C := by
  have := @has_finite_wide_pullbacks.out C _ _ J (Classical.decEq _)
  infer_instance

/-- `has_finite_wide_pushouts` represents a choice of wide pushout
for every finite collection of morphisms
-/
class HasFiniteWidePushouts : Prop where
  out (J : Type v) [DecidableEq J] [Fintype J] : HasColimitsOfShape (WidePushoutShape J) C

instance has_colimits_of_shape_wide_pushout_shape (J : Type v) [Fintype J] [HasFiniteWidePushouts C] :
    HasColimitsOfShape (WidePushoutShape J) C := by
  have := @has_finite_wide_pushouts.out C _ _ J (Classical.decEq _)
  infer_instance

/-- Finite wide pullbacks are finite limits, so if `C` has all finite limits,
it also has finite wide pullbacks
-/
theorem has_finite_wide_pullbacks_of_has_finite_limits [HasFiniteLimits C] : HasFiniteWidePullbacks C :=
  ⟨fun J _ _ => has_finite_limits.out _⟩

/-- Finite wide pushouts are finite colimits, so if `C` has all finite colimits,
it also has finite wide pushouts
-/
theorem has_finite_wide_pushouts_of_has_finite_limits [HasFiniteColimits C] : HasFiniteWidePushouts C :=
  ⟨fun J _ _ => has_finite_colimits.out _⟩

instance fintypeWalkingPair : Fintype WalkingPair where
  elems := {WalkingPair.left, WalkingPair.right}
  complete := fun x => by
    cases x <;> simp

/-- Pullbacks are finite limits, so if `C` has all finite limits, it also has all pullbacks -/
example [HasFiniteWidePullbacks C] : HasPullbacks C := by
  infer_instance

/-- Pushouts are finite colimits, so if `C` has all finite colimits, it also has all pushouts -/
example [HasFiniteWidePushouts C] : HasPushouts C := by
  infer_instance

end CategoryTheory.Limits

