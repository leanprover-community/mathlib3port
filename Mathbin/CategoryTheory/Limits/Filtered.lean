/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
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

/-- Class for having all filtered colimits of a given size. -/
class HasFilteredColimitsOfSize : Prop where
  HasColimitsOfShape : ∀ (I : Type w) [Category.{w'} I] [IsFiltered I], HasColimitsOfShape I C

end

instance (priority := 100) has_limits_of_shape_of_has_cofiltered_limits [HasCofilteredLimitsOfSize.{w', w} C]
    (I : Type w) [Category.{w'} I] [IsCofiltered I] : HasLimitsOfShape I C :=
  HasCofilteredLimitsOfSize.has_limits_of_shape _

instance (priority := 100) has_colimits_of_shape_of_has_filtered_colimits [HasFilteredColimitsOfSize.{w', w} C]
    (I : Type w) [Category.{w'} I] [IsFiltered I] : HasColimitsOfShape I C :=
  HasFilteredColimitsOfSize.has_colimits_of_shape _

end CategoryTheory.Limits

