/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Category.Module.Basic
import Mathbin.CategoryTheory.Linear.Default
import Mathbin.CategoryTheory.Preadditive.AdditiveFunctor
import Mathbin.CategoryTheory.Preadditive.Yoneda

/-!
# The Yoneda embedding for `R`-linear categories

The Yoneda embedding for `R`-linear categories `C`,
sends an object `X : C` to the `Module R`-valued presheaf on `C`,
with value on `Y : Cᵒᵖ` given by `Module.of R (unop Y ⟶ X)`.

TODO: `linear_yoneda R C` is `R`-linear.
TODO: In fact, `linear_yoneda` itself is additive and `R`-linear.
-/


universe w v u

open Opposite

namespace CategoryTheory

variable (R : Type w) [Ringₓ R] (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C]

/-- The Yoneda embedding for `R`-linear categories `C`,
sending an object `X : C` to the `Module R`-valued presheaf on `C`,
with value on `Y : Cᵒᵖ` given by `Module.of R (unop Y ⟶ X)`. -/
@[simps]
def linearYoneda : C ⥤ Cᵒᵖ ⥤ ModuleCat R where
  obj := fun X =>
    { obj := fun Y => ModuleCat.of R (unop Y ⟶ X), map := fun Y Y' f => Linear.leftComp R _ f.unop,
      map_comp' := fun _ _ _ f g => LinearMap.ext fun _ => Category.assoc _ _ _,
      map_id' := fun Y => LinearMap.ext fun _ => Category.id_comp _ }
  map := fun X X' f =>
    { app := fun Y => Linear.rightComp R _ f,
      naturality' := fun X Y f =>
        LinearMap.ext fun x => by
          simp only [category.assoc, ModuleCat.coe_comp, Function.comp_app, linear.left_comp_apply,
            linear.right_comp_apply] }
  map_id' := fun X =>
    NatTrans.ext _ _ <|
      funext fun _ =>
        LinearMap.ext fun _ => by
          simp only [linear.right_comp_apply, category.comp_id, nat_trans.id_app, ModuleCat.id_apply]
  map_comp' := fun _ _ _ f g =>
    NatTrans.ext _ _ <|
      funext fun _ =>
        LinearMap.ext fun _ => by
          simp only [category.assoc, linear.right_comp_apply, nat_trans.comp_app, ModuleCat.coe_comp, Function.comp_app]

/-- The Yoneda embedding for `R`-linear categories `C`,
sending an object `Y : Cᵒᵖ` to the `Module R`-valued copresheaf on `C`,
with value on `X : C` given by `Module.of R (unop Y ⟶ X)`. -/
@[simps]
def linearCoyoneda : Cᵒᵖ ⥤ C ⥤ ModuleCat R where
  obj := fun Y =>
    { obj := fun X => ModuleCat.of R (unop Y ⟶ X), map := fun Y Y' => Linear.rightComp _ _,
      map_id' := fun Y => LinearMap.ext fun _ => Category.comp_id _,
      map_comp' := fun _ _ _ f g => LinearMap.ext fun _ => Eq.symm (Category.assoc _ _ _) }
  map := fun Y Y' f =>
    { app := fun X => Linear.leftComp _ _ f.unop,
      naturality' := fun X Y f =>
        LinearMap.ext fun x => by
          simp only [category.assoc, ModuleCat.coe_comp, Function.comp_app, linear.right_comp_apply,
            linear.left_comp_apply] }
  map_id' := fun X =>
    NatTrans.ext _ _ <|
      funext fun _ =>
        LinearMap.ext fun _ => by
          simp only [linear.left_comp_apply, unop_id, category.id_comp, nat_trans.id_app, ModuleCat.id_apply]
  map_comp' := fun _ _ _ f g =>
    NatTrans.ext _ _ <|
      funext fun _ =>
        LinearMap.ext fun _ => by
          simp only [category.assoc, ModuleCat.coe_comp, Function.comp_app, linear.left_comp_apply, unop_comp,
            nat_trans.comp_app]

instance linear_yoneda_obj_additive (X : C) : ((linearYoneda R C).obj X).Additive where

instance linear_coyoneda_obj_additive (Y : Cᵒᵖ) : ((linearCoyoneda R C).obj Y).Additive where

@[simp]
theorem whiskering_linear_yoneda : linearYoneda R C ⋙ (whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R)) = yoneda :=
  rfl

@[simp]
theorem whiskering_linear_yoneda₂ :
    linearYoneda R C ⋙ (whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{v} R) AddCommGroupₓₓ.{v}) =
      preadditive_yoneda :=
  rfl

@[simp]
theorem whiskering_linear_coyoneda :
    linearCoyoneda R C ⋙ (whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R)) = coyoneda :=
  rfl

@[simp]
theorem whiskering_linear_coyoneda₂ :
    linearCoyoneda R C ⋙ (whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{v} R) AddCommGroupₓₓ.{v}) =
      preadditive_coyoneda :=
  rfl

instance linearYonedaFull : Full (linearYoneda R C) :=
  let yoneda_full : Full (linearYoneda R C ⋙ (whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R))) :=
    yoneda.yonedaFull
  full.of_comp_faithful (linear_yoneda R C) ((whiskering_right _ _ _).obj (forget (ModuleCat.{v} R)))

instance linearCoyonedaFull : Full (linearCoyoneda R C) :=
  let coyoneda_full : Full (linearCoyoneda R C ⋙ (whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R))) :=
    coyoneda.coyonedaFull
  full.of_comp_faithful (linear_coyoneda R C) ((whiskering_right _ _ _).obj (forget (ModuleCat.{v} R)))

instance linear_yoneda_faithful : Faithful (linearYoneda R C) :=
  Faithful.of_comp_eq (whiskering_linear_yoneda R C)

instance linear_coyoneda_faithful : Faithful (linearCoyoneda R C) :=
  Faithful.of_comp_eq (whiskering_linear_coyoneda R C)

end CategoryTheory

