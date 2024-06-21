/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Algebra.Category.Grp.ZModuleEquivalence
import Algebra.Category.Grp.Limits
import Algebra.Category.Grp.Colimits
import Algebra.Category.ModuleCat.Abelian
import CategoryTheory.Abelian.Basic

#align_import algebra.category.Group.abelian from "leanprover-community/mathlib"@"0b7c740e25651db0ba63648fbae9f9d6f941e31b"

/-!
# The category of abelian groups is abelian

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open CategoryTheory

open CategoryTheory.Limits

universe u

noncomputable section

namespace AddCommGrp

section

variable {X Y : AddCommGrp.{u}} (f : X ⟶ Y)

#print AddCommGrp.normalMono /-
/-- In the category of abelian groups, every monomorphism is normal. -/
def normalMono (hf : Mono f) : NormalMono f :=
  equivalenceReflectsNormalMono (forget₂ (ModuleCat.{u} ℤ) AddCommGrp.{u}).inv <|
    ModuleCat.normalMono _ inferInstance
#align AddCommGroup.normal_mono AddCommGrp.normalMono
-/

#print AddCommGrp.normalEpi /-
/-- In the category of abelian groups, every epimorphism is normal. -/
def normalEpi (hf : Epi f) : NormalEpi f :=
  equivalenceReflectsNormalEpi (forget₂ (ModuleCat.{u} ℤ) AddCommGrp.{u}).inv <|
    ModuleCat.normalEpi _ inferInstance
#align AddCommGroup.normal_epi AddCommGrp.normalEpi
-/

end

/-- The category of abelian groups is abelian. -/
instance : Abelian AddCommGrp.{u}
    where
  HasFiniteProducts := ⟨by infer_instance⟩
  normalMonoOfMono X Y := normalMono
  normalEpiOfEpi X Y := normalEpi
  add_comp := by intros; simp only [preadditive.add_comp]
  comp_add := by intros; simp only [preadditive.comp_add]

end AddCommGrp

