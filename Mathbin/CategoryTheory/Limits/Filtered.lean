/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module category_theory.limits.filtered
! leanprover-community/mathlib commit 0743cc5d9d86bcd1bba10f480e948a257d65056f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Filtered
import Mathbin.CategoryTheory.Limits.HasLimits

/-!
# Possession of filtered colimits
-/


universe w' w v u

noncomputable section

open CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory.Limits

section

variable (C)

/-- Class for having all cofiltered limits of a given size. -/
class HasCofilteredLimitsOfSize : Prop where
  HasLimitsOfShape : ∀ (I : Type w) [Category.{w'} I] [IsCofiltered I], HasLimitsOfShape I C
#align
  category_theory.limits.has_cofiltered_limits_of_size CategoryTheory.Limits.HasCofilteredLimitsOfSize

/-- Class for having all filtered colimits of a given size. -/
class HasFilteredColimitsOfSize : Prop where
  HasColimitsOfShape : ∀ (I : Type w) [Category.{w'} I] [IsFiltered I], HasColimitsOfShape I C
#align
  category_theory.limits.has_filtered_colimits_of_size CategoryTheory.Limits.HasFilteredColimitsOfSize

end

instance (priority := 100) hasLimitsOfShapeOfHasCofilteredLimits
    [HasCofilteredLimitsOfSize.{w', w} C] (I : Type w) [Category.{w'} I] [IsCofiltered I] :
    HasLimitsOfShape I C :=
  HasCofilteredLimitsOfSize.hasLimitsOfShape _
#align
  category_theory.limits.has_limits_of_shape_of_has_cofiltered_limits CategoryTheory.Limits.hasLimitsOfShapeOfHasCofilteredLimits

instance (priority := 100) hasColimitsOfShapeOfHasFilteredColimits
    [HasFilteredColimitsOfSize.{w', w} C] (I : Type w) [Category.{w'} I] [IsFiltered I] :
    HasColimitsOfShape I C :=
  HasFilteredColimitsOfSize.hasColimitsOfShape _
#align
  category_theory.limits.has_colimits_of_shape_of_has_filtered_colimits CategoryTheory.Limits.hasColimitsOfShapeOfHasFilteredColimits

end CategoryTheory.Limits

