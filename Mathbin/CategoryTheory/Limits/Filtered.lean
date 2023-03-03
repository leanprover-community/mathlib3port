/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module category_theory.limits.filtered
! leanprover-community/mathlib commit 832f7b9162039c28b9361289c8681f155cae758f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Filtered
import Mathbin.CategoryTheory.Limits.HasLimits

/-!
# Possession of filtered colimits

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


universe w' w v u

noncomputable section

open CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory.Limits

section

variable (C)

#print CategoryTheory.Limits.HasCofilteredLimitsOfSize /-
/-- Class for having all cofiltered limits of a given size. -/
class HasCofilteredLimitsOfSize : Prop where
  HasLimitsOfShape : ∀ (I : Type w) [Category.{w'} I] [IsCofiltered I], HasLimitsOfShape I C
#align category_theory.limits.has_cofiltered_limits_of_size CategoryTheory.Limits.HasCofilteredLimitsOfSize
-/

#print CategoryTheory.Limits.HasFilteredColimitsOfSize /-
/-- Class for having all filtered colimits of a given size. -/
class HasFilteredColimitsOfSize : Prop where
  HasColimitsOfShape : ∀ (I : Type w) [Category.{w'} I] [IsFiltered I], HasColimitsOfShape I C
#align category_theory.limits.has_filtered_colimits_of_size CategoryTheory.Limits.HasFilteredColimitsOfSize
-/

end

#print CategoryTheory.Limits.hasLimitsOfShape_of_has_cofiltered_limits /-
instance (priority := 100) hasLimitsOfShape_of_has_cofiltered_limits
    [HasCofilteredLimitsOfSize.{w', w} C] (I : Type w) [Category.{w'} I] [IsCofiltered I] :
    HasLimitsOfShape I C :=
  HasCofilteredLimitsOfSize.hasLimitsOfShape _
#align category_theory.limits.has_limits_of_shape_of_has_cofiltered_limits CategoryTheory.Limits.hasLimitsOfShape_of_has_cofiltered_limits
-/

#print CategoryTheory.Limits.hasColimitsOfShape_of_has_filtered_colimits /-
instance (priority := 100) hasColimitsOfShape_of_has_filtered_colimits
    [HasFilteredColimitsOfSize.{w', w} C] (I : Type w) [Category.{w'} I] [IsFiltered I] :
    HasColimitsOfShape I C :=
  HasFilteredColimitsOfSize.hasColimitsOfShape _
#align category_theory.limits.has_colimits_of_shape_of_has_filtered_colimits CategoryTheory.Limits.hasColimitsOfShape_of_has_filtered_colimits
-/

end CategoryTheory.Limits

