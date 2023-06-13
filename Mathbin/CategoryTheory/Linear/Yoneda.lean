/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.linear.yoneda
! leanprover-community/mathlib commit 9d2f0748e6c50d7a2657c564b1ff2c695b39148d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Module.Basic
import Mathbin.CategoryTheory.Linear.Basic
import Mathbin.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# The Yoneda embedding for `R`-linear categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The Yoneda embedding for `R`-linear categories `C`,
sends an object `X : C` to the `Module R`-valued presheaf on `C`,
with value on `Y : Cᵒᵖ` given by `Module.of R (unop Y ⟶ X)`.

TODO: `linear_yoneda R C` is `R`-linear.
TODO: In fact, `linear_yoneda` itself is additive and `R`-linear.
-/


universe w v u

open Opposite

namespace CategoryTheory

variable (R : Type w) [Ring R] (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C]

#print CategoryTheory.linearYoneda /-
/-- The Yoneda embedding for `R`-linear categories `C`,
sending an object `X : C` to the `Module R`-valued presheaf on `C`,
with value on `Y : Cᵒᵖ` given by `Module.of R (unop Y ⟶ X)`. -/
@[simps]
def linearYoneda : C ⥤ Cᵒᵖ ⥤ ModuleCat R
    where
  obj X :=
    { obj := fun Y => ModuleCat.of R (unop Y ⟶ X)
      map := fun Y Y' f => Linear.leftComp R _ f.unop
      map_comp' := fun _ _ _ f g => LinearMap.ext fun _ => Category.assoc _ _ _
      map_id' := fun Y => LinearMap.ext fun _ => Category.id_comp _ }
  map X X' f :=
    { app := fun Y => Linear.rightComp R _ f
      naturality' := fun X Y f =>
        LinearMap.ext fun x => by
          simp only [category.assoc, ModuleCat.coe_comp, Function.comp_apply,
            linear.left_comp_apply, linear.right_comp_apply] }
  map_id' X :=
    NatTrans.ext _ _ <|
      funext fun _ =>
        LinearMap.ext fun _ => by
          simp only [linear.right_comp_apply, category.comp_id, nat_trans.id_app,
            ModuleCat.id_apply]
  map_comp' _ _ _ f g :=
    NatTrans.ext _ _ <|
      funext fun _ =>
        LinearMap.ext fun _ => by
          simp only [category.assoc, linear.right_comp_apply, nat_trans.comp_app,
            ModuleCat.coe_comp, Function.comp_apply]
#align category_theory.linear_yoneda CategoryTheory.linearYoneda
-/

#print CategoryTheory.linearCoyoneda /-
/-- The Yoneda embedding for `R`-linear categories `C`,
sending an object `Y : Cᵒᵖ` to the `Module R`-valued copresheaf on `C`,
with value on `X : C` given by `Module.of R (unop Y ⟶ X)`. -/
@[simps]
def linearCoyoneda : Cᵒᵖ ⥤ C ⥤ ModuleCat R
    where
  obj Y :=
    { obj := fun X => ModuleCat.of R (unop Y ⟶ X)
      map := fun Y Y' => Linear.rightComp _ _
      map_id' := fun Y => LinearMap.ext fun _ => Category.comp_id _
      map_comp' := fun _ _ _ f g => LinearMap.ext fun _ => Eq.symm (Category.assoc _ _ _) }
  map Y Y' f :=
    { app := fun X => Linear.leftComp _ _ f.unop
      naturality' := fun X Y f =>
        LinearMap.ext fun x => by
          simp only [category.assoc, ModuleCat.coe_comp, Function.comp_apply,
            linear.right_comp_apply, linear.left_comp_apply] }
  map_id' X :=
    NatTrans.ext _ _ <|
      funext fun _ =>
        LinearMap.ext fun _ => by
          simp only [linear.left_comp_apply, unop_id, category.id_comp, nat_trans.id_app,
            ModuleCat.id_apply]
  map_comp' _ _ _ f g :=
    NatTrans.ext _ _ <|
      funext fun _ =>
        LinearMap.ext fun _ => by
          simp only [category.assoc, ModuleCat.coe_comp, Function.comp_apply,
            linear.left_comp_apply, unop_comp, nat_trans.comp_app]
#align category_theory.linear_coyoneda CategoryTheory.linearCoyoneda
-/

#print CategoryTheory.linearYoneda_obj_additive /-
instance linearYoneda_obj_additive (X : C) : ((linearYoneda R C).obj X).Additive where
#align category_theory.linear_yoneda_obj_additive CategoryTheory.linearYoneda_obj_additive
-/

#print CategoryTheory.linearCoyoneda_obj_additive /-
instance linearCoyoneda_obj_additive (Y : Cᵒᵖ) : ((linearCoyoneda R C).obj Y).Additive where
#align category_theory.linear_coyoneda_obj_additive CategoryTheory.linearCoyoneda_obj_additive
-/

#print CategoryTheory.whiskering_linearYoneda /-
@[simp]
theorem whiskering_linearYoneda :
    linearYoneda R C ⋙ (whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R)) = yoneda :=
  rfl
#align category_theory.whiskering_linear_yoneda CategoryTheory.whiskering_linearYoneda
-/

#print CategoryTheory.whiskering_linearYoneda₂ /-
@[simp]
theorem whiskering_linearYoneda₂ :
    linearYoneda R C ⋙ (whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{v} R) AddCommGroupCat.{v}) =
      preadditiveYoneda :=
  rfl
#align category_theory.whiskering_linear_yoneda₂ CategoryTheory.whiskering_linearYoneda₂
-/

#print CategoryTheory.whiskering_linearCoyoneda /-
@[simp]
theorem whiskering_linearCoyoneda :
    linearCoyoneda R C ⋙ (whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R)) = coyoneda :=
  rfl
#align category_theory.whiskering_linear_coyoneda CategoryTheory.whiskering_linearCoyoneda
-/

#print CategoryTheory.whiskering_linearCoyoneda₂ /-
@[simp]
theorem whiskering_linearCoyoneda₂ :
    linearCoyoneda R C ⋙
        (whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{v} R) AddCommGroupCat.{v}) =
      preadditiveCoyoneda :=
  rfl
#align category_theory.whiskering_linear_coyoneda₂ CategoryTheory.whiskering_linearCoyoneda₂
-/

#print CategoryTheory.full_linearYoneda /-
instance full_linearYoneda : Full (linearYoneda R C) :=
  let yoneda_full :
    Full (linearYoneda R C ⋙ (whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R))) :=
    Yoneda.yonedaFull
  full.of_comp_faithful (linear_yoneda R C)
    ((whiskering_right _ _ _).obj (forget (ModuleCat.{v} R)))
#align category_theory.linear_yoneda_full CategoryTheory.full_linearYoneda
-/

#print CategoryTheory.full_linearCoyoneda /-
instance full_linearCoyoneda : Full (linearCoyoneda R C) :=
  let coyoneda_full :
    Full (linearCoyoneda R C ⋙ (whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R))) :=
    Coyoneda.coyonedaFull
  full.of_comp_faithful (linear_coyoneda R C)
    ((whiskering_right _ _ _).obj (forget (ModuleCat.{v} R)))
#align category_theory.linear_coyoneda_full CategoryTheory.full_linearCoyoneda
-/

#print CategoryTheory.faithful_linearYoneda /-
instance faithful_linearYoneda : Faithful (linearYoneda R C) :=
  Faithful.of_comp_eq (whiskering_linearYoneda R C)
#align category_theory.linear_yoneda_faithful CategoryTheory.faithful_linearYoneda
-/

#print CategoryTheory.faithful_linearCoyoneda /-
instance faithful_linearCoyoneda : Faithful (linearCoyoneda R C) :=
  Faithful.of_comp_eq (whiskering_linearCoyoneda R C)
#align category_theory.linear_coyoneda_faithful CategoryTheory.faithful_linearCoyoneda
-/

end CategoryTheory

