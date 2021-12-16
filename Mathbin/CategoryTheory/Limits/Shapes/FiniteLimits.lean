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

variable (C : Type u) [category.{v} C]

/--
A category has all finite limits if every functor `J ⥤ C` with a `fin_category J` instance
has a limit.

This is often called 'finitely complete'.
-/
class has_finite_limits : Prop where 
  out (J : Type v) [𝒥 : small_category J] [@fin_category J 𝒥] : @has_limits_of_shape J 𝒥 C _

instance (priority := 100) has_limits_of_shape_of_has_finite_limits (J : Type v) [small_category J] [fin_category J]
  [has_finite_limits C] : has_limits_of_shape J C :=
  has_finite_limits.out J

instance (priority := 100) has_finite_limits_of_has_limits_of_size [has_limits_of_size.{v', u'} C] :
  has_finite_limits C :=
  ⟨fun J hJ hJ' =>
      by 
        have  := has_limits_of_size_shrink.{0, 0} C 
        exact has_limits_of_shape_of_equivalence (fin_category.equiv_as_type J)⟩

/-- If `C` has all limits, it has finite limits. -/
instance (priority := 100) has_finite_limits_of_has_limits [has_limits C] : has_finite_limits C :=
  inferInstance

/--
A category has all finite colimits if every functor `J ⥤ C` with a `fin_category J` instance
has a colimit.

This is often called 'finitely cocomplete'.
-/
class has_finite_colimits : Prop where 
  out (J : Type v) [𝒥 : small_category J] [@fin_category J 𝒥] : @has_colimits_of_shape J 𝒥 C _

instance (priority := 100) has_limits_of_shape_of_has_finite_colimits (J : Type v) [small_category J] [fin_category J]
  [has_finite_colimits C] : has_colimits_of_shape J C :=
  has_finite_colimits.out J

instance (priority := 100) has_finite_colimits_of_has_colimits_of_size [has_colimits_of_size.{v', u'} C] :
  has_finite_colimits C :=
  ⟨fun J hJ hJ' =>
      by 
        have  := has_colimits_of_size_shrink.{0, 0} C 
        exact has_colimits_of_shape_of_equivalence (fin_category.equiv_as_type J)⟩

/-- If `C` has all colimits, it has finite colimits. -/
instance (priority := 100) has_finite_colimits_of_has_colimits [has_colimits C] : has_finite_colimits C :=
  inferInstance

section 

open WalkingParallelPair WalkingParallelPairHom

instance fintype_walking_parallel_pair : Fintype walking_parallel_pair :=
  { elems := [walking_parallel_pair.zero, walking_parallel_pair.one].toFinset,
    complete :=
      fun x =>
        by 
          cases x <;> simp  }

attribute [local tidy] tactic.case_bash

instance (j j' : walking_parallel_pair) : Fintype (walking_parallel_pair_hom j j') :=
  { elems :=
      walking_parallel_pair.rec_on j
        (walking_parallel_pair.rec_on j' [walking_parallel_pair_hom.id zero].toFinset [left, right].toFinset)
        (walking_parallel_pair.rec_on j' ∅ [walking_parallel_pair_hom.id one].toFinset),
    complete :=
      by 
        tidy }

end 

instance : fin_category walking_parallel_pair :=
  {  }

/-- Equalizers are finite limits, so if `C` has all finite limits, it also has all equalizers -/
example [has_finite_limits C] : has_equalizers C :=
  by 
    infer_instance

/-- Coequalizers are finite colimits, of if `C` has all finite colimits, it also has all
    coequalizers -/
example [has_finite_colimits C] : has_coequalizers C :=
  by 
    infer_instance

variable {J : Type v}

attribute [local tidy] tactic.case_bash

namespace WidePullbackShape

instance fintype_obj [Fintype J] : Fintype (wide_pullback_shape J) :=
  by 
    rw [wide_pullback_shape]
    infer_instance

instance fintype_hom [DecidableEq J] (j j' : wide_pullback_shape J) : Fintype (j ⟶ j') :=
  { elems :=
      by 
        cases j'
        ·
          cases j
          ·
            exact {hom.id none}
          ·
            exact {hom.term j}
        ·
          byCases' some j' = j
          ·
            rw [h]
            exact {hom.id j}
          ·
            exact ∅,
    complete :=
      by 
        tidy }

end WidePullbackShape

namespace WidePushoutShape

instance fintype_obj [Fintype J] : Fintype (wide_pushout_shape J) :=
  by 
    rw [wide_pushout_shape]
    infer_instance

instance fintype_hom [DecidableEq J] (j j' : wide_pushout_shape J) : Fintype (j ⟶ j') :=
  { elems :=
      by 
        cases j
        ·
          cases j'
          ·
            exact {hom.id none}
          ·
            exact {hom.init j'}
        ·
          byCases' some j = j'
          ·
            rw [h]
            exact {hom.id j'}
          ·
            exact ∅,
    complete :=
      by 
        tidy }

end WidePushoutShape

instance fin_category_wide_pullback [DecidableEq J] [Fintype J] : fin_category (wide_pullback_shape J) :=
  { fintypeHom := wide_pullback_shape.fintype_hom }

instance fin_category_wide_pushout [DecidableEq J] [Fintype J] : fin_category (wide_pushout_shape J) :=
  { fintypeHom := wide_pushout_shape.fintype_hom }

/--
`has_finite_wide_pullbacks` represents a choice of wide pullback
for every finite collection of morphisms
-/
class has_finite_wide_pullbacks : Prop where 
  out (J : Type v) [DecidableEq J] [Fintype J] : has_limits_of_shape (wide_pullback_shape J) C

instance has_limits_of_shape_wide_pullback_shape (J : Type v) [Fintype J] [has_finite_wide_pullbacks C] :
  has_limits_of_shape (wide_pullback_shape J) C :=
  by 
    have  := @has_finite_wide_pullbacks.out C _ _ J (Classical.decEq _)
    infer_instance

/--
`has_finite_wide_pushouts` represents a choice of wide pushout
for every finite collection of morphisms
-/
class has_finite_wide_pushouts : Prop where 
  out (J : Type v) [DecidableEq J] [Fintype J] : has_colimits_of_shape (wide_pushout_shape J) C

instance has_colimits_of_shape_wide_pushout_shape (J : Type v) [Fintype J] [has_finite_wide_pushouts C] :
  has_colimits_of_shape (wide_pushout_shape J) C :=
  by 
    have  := @has_finite_wide_pushouts.out C _ _ J (Classical.decEq _)
    infer_instance

/--
Finite wide pullbacks are finite limits, so if `C` has all finite limits,
it also has finite wide pullbacks
-/
theorem has_finite_wide_pullbacks_of_has_finite_limits [has_finite_limits C] : has_finite_wide_pullbacks C :=
  ⟨fun J _ _ =>
      by 
        exact has_finite_limits.out _⟩

/--
Finite wide pushouts are finite colimits, so if `C` has all finite colimits,
it also has finite wide pushouts
-/
theorem has_finite_wide_pushouts_of_has_finite_limits [has_finite_colimits C] : has_finite_wide_pushouts C :=
  ⟨fun J _ _ =>
      by 
        exact has_finite_colimits.out _⟩

instance fintype_walking_pair : Fintype walking_pair :=
  { elems := {walking_pair.left, walking_pair.right},
    complete :=
      fun x =>
        by 
          cases x <;> simp  }

/-- Pullbacks are finite limits, so if `C` has all finite limits, it also has all pullbacks -/
example [has_finite_wide_pullbacks C] : has_pullbacks C :=
  by 
    infer_instance

/-- Pushouts are finite colimits, so if `C` has all finite colimits, it also has all pushouts -/
example [has_finite_wide_pushouts C] : has_pushouts C :=
  by 
    infer_instance

end CategoryTheory.Limits

