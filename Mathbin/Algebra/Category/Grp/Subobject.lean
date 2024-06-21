/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Algebra.Category.Grp.ZModuleEquivalence
import Algebra.Category.ModuleCat.Subobject

#align_import algebra.category.Group.subobject from "leanprover-community/mathlib"@"d07a9c875ed7139abfde6a333b2be205c5bd404e"

/-!
# The category of abelian groups is well-powered

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open CategoryTheory

universe u

namespace AddCommGrp

#print AddCommGrp.wellPowered_addCommGrp /-
instance wellPowered_addCommGrp : WellPowered AddCommGrp.{u} :=
  wellPowered_of_equiv (forget₂ (ModuleCat.{u} ℤ) AddCommGrp.{u}).asEquivalence
#align AddCommGroup.well_powered_AddCommGroup AddCommGrp.wellPowered_addCommGrp
-/

end AddCommGrp

