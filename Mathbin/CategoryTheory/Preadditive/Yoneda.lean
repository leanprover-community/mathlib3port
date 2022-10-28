/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathbin.CategoryTheory.Limits.Yoneda
import Mathbin.CategoryTheory.Preadditive.Opposite
import Mathbin.Algebra.Category.ModuleCat.Abelian
import Mathbin.Algebra.Category.GroupCat.Preadditive

/-!
# The Yoneda embedding for preadditive categories

The Yoneda embedding for preadditive categories sends an object `Y` to the presheaf sending an
object `X` to the group of morphisms `X ⟶ Y`. At each point, we get an additional `End Y`-module
structure.

We also show that this presheaf is additive and that it is compatible with the normal Yoneda
embedding in the expected way and deduce that the preadditive Yoneda embedding is fully faithful.

## TODO
* The Yoneda embedding is additive itself

-/


universe v u

open CategoryTheory.Preadditive Opposite CategoryTheory.Limits

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The Yoneda embedding for preadditive categories sends an object `Y` to the presheaf sending an
object `X` to the `End Y`-module of morphisms `X ⟶ Y`.
-/
@[simps]
def preadditiveYonedaObj (Y : C) : Cᵒᵖ ⥤ ModuleCat.{v} (EndCat Y) where
  obj X := ModuleCat.of _ (X.unop ⟶ Y)
  map X X' f :=
    { toFun := fun g => f.unop ≫ g, map_add' := fun g g' => comp_add _ _ _ _ _ _,
      map_smul' := fun r g => Eq.symm <| Category.assoc _ _ _ }

/-- The Yoneda embedding for preadditive categories sends an object `Y` to the presheaf sending an
object `X` to the group of morphisms `X ⟶ Y`. At each point, we get an additional `End Y`-module
structure, see `preadditive_yoneda_obj`.
-/
@[simps]
def preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGroupCat.{v} where
  obj Y := preadditiveYonedaObj Y ⋙ forget₂ _ _
  map Y Y' f :=
    { app := fun X =>
        { toFun := fun g => g ≫ f, map_zero' := Limits.zero_comp, map_add' := fun g g' => add_comp _ _ _ _ _ _ },
      naturality' := fun X X' g => (AddCommGroupCat.ext _ _ _ _) fun x => Category.assoc _ _ _ }
  map_id' X := by
    ext
    simp
  map_comp' X Y Z f g := by
    ext
    simp

/-- The Yoneda embedding for preadditive categories sends an object `X` to the copresheaf sending an
object `Y` to the `End X`-module of morphisms `X ⟶ Y`.
-/
@[simps]
def preadditiveCoyonedaObj (X : Cᵒᵖ) : C ⥤ ModuleCat.{v} (EndCat X) where
  obj Y := ModuleCat.of _ (unop X ⟶ Y)
  map Y Y' f :=
    { toFun := fun g => g ≫ f, map_add' := fun g g' => add_comp _ _ _ _ _ _,
      map_smul' := fun r g => Category.assoc _ _ _ }

/-- The Yoneda embedding for preadditive categories sends an object `X` to the copresheaf sending an
object `Y` to the group of morphisms `X ⟶ Y`. At each point, we get an additional `End X`-module
structure, see `preadditive_coyoneda_obj`.
-/
@[simps]
def preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGroupCat.{v} where
  obj X := preadditiveCoyonedaObj X ⋙ forget₂ _ _
  map X X' f :=
    { app := fun Y =>
        { toFun := fun g => f.unop ≫ g, map_zero' := Limits.comp_zero, map_add' := fun g g' => comp_add _ _ _ _ _ _ },
      naturality' := fun Y Y' g => (AddCommGroupCat.ext _ _ _ _) fun x => Eq.symm <| Category.assoc _ _ _ }
  map_id' X := by
    ext
    simp
  map_comp' X Y Z f g := by
    ext
    simp

instance additive_yoneda_obj (X : C) : Functor.Additive (preadditiveYonedaObj X) where

instance additive_yoneda_obj' (X : C) : Functor.Additive (preadditiveYoneda.obj X) where

instance additive_coyoneda_obj (X : Cᵒᵖ) : Functor.Additive (preadditiveCoyonedaObj X) where

instance additive_coyoneda_obj' (X : Cᵒᵖ) : Functor.Additive (preadditiveCoyoneda.obj X) where

/-- Composing the preadditive yoneda embedding with the forgetful functor yields the regular
Yoneda embedding.
-/
@[simp]
theorem whiskering_preadditive_yoneda :
    preadditive_yoneda ⋙ (whiskeringRight Cᵒᵖ AddCommGroupCat (Type v)).obj (forget AddCommGroupCat) = yoneda :=
  rfl

/-- Composing the preadditive yoneda embedding with the forgetful functor yields the regular
Yoneda embedding.
-/
@[simp]
theorem whiskering_preadditive_coyoneda :
    preadditive_coyoneda ⋙ (whiskeringRight C AddCommGroupCat (Type v)).obj (forget AddCommGroupCat) = coyoneda :=
  rfl

instance preadditiveYonedaFull : Full (preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGroupCat) :=
  let yoneda_full :
    Full (preadditive_yoneda ⋙ (whiskeringRight Cᵒᵖ AddCommGroupCat (Type v)).obj (forget AddCommGroupCat)) :=
    yoneda.yonedaFull
  full.of_comp_faithful preadditive_yoneda
    ((whiskering_right Cᵒᵖ AddCommGroupCat (Type v)).obj (forget AddCommGroupCat))

instance preadditiveCoyonedaFull : Full (preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGroupCat) :=
  let coyoneda_full :
    Full (preadditive_coyoneda ⋙ (whiskeringRight C AddCommGroupCat (Type v)).obj (forget AddCommGroupCat)) :=
    coyoneda.coyonedaFull
  full.of_comp_faithful preadditive_coyoneda
    ((whiskering_right C AddCommGroupCat (Type v)).obj (forget AddCommGroupCat))

instance preadditive_yoneda_faithful : Faithful (preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGroupCat) :=
  Faithful.of_comp_eq whiskering_preadditive_yoneda

instance preadditive_coyoneda_faithful : Faithful (preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGroupCat) :=
  Faithful.of_comp_eq whiskering_preadditive_coyoneda

instance preservesLimitsPreadditiveYonedaObj (X : C) : PreservesLimits (preadditiveYonedaObj X) :=
  have : PreservesLimits (preadditiveYonedaObj X ⋙ forget _) := (inferInstance : PreservesLimits (yoneda.obj X))
  preserves_limits_of_reflects_of_preserves _ (forget _)

instance preservesLimitsPreadditiveCoyonedaObj (X : Cᵒᵖ) : PreservesLimits (preadditiveCoyonedaObj X) :=
  have : PreservesLimits (preadditiveCoyonedaObj X ⋙ forget _) := (inferInstance : PreservesLimits (coyoneda.obj X))
  preserves_limits_of_reflects_of_preserves _ (forget _)

instance PreservesLimitsPreadditiveYoneda.obj (X : C) : PreservesLimits (preadditiveYoneda.obj X) :=
  show PreservesLimits (preadditiveYonedaObj X ⋙ forget₂ _ _) from inferInstance

instance PreservesLimitsPreadditiveCoyoneda.obj (X : Cᵒᵖ) : PreservesLimits (preadditiveCoyoneda.obj X) :=
  show PreservesLimits (preadditiveCoyonedaObj X ⋙ forget₂ _ _) from inferInstance

end CategoryTheory

