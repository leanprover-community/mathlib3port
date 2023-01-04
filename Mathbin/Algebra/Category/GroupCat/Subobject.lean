/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module algebra.category.Group.subobject
! leanprover-community/mathlib commit d3e8e0a0237c10c2627bf52c246b15ff8e7df4c0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.GroupCat.ZModuleEquivalence
import Mathbin.Algebra.Category.ModuleCat.Subobject

/-!
# The category of abelian groups is well-powered
-/


open CategoryTheory

universe u

namespace AddCommGroupCat

instance well_powered_AddCommGroup : WellPowered AddCommGroupCat.{u} :=
  well_powered_of_equiv (forget₂ (ModuleCat.{u} ℤ) AddCommGroupCat.{u}).asEquivalence
#align AddCommGroup.well_powered_AddCommGroup AddCommGroupCat.well_powered_AddCommGroup

end AddCommGroupCat

