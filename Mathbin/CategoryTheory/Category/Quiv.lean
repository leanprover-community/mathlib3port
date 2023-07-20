/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Adjunction.Basic
import Mathbin.CategoryTheory.Category.Cat
import Mathbin.CategoryTheory.PathCategory

#align_import category_theory.category.Quiv from "leanprover-community/mathlib"@"10bf4f825ad729c5653adc039dafa3622e7f93c9"

/-!
# The category of quivers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The category of (bundled) quivers, and the free/forgetful adjunction between `Cat` and `Quiv`.

-/


universe v u

namespace CategoryTheory

#print CategoryTheory.QuivCat /-
-- intended to be used with explicit universe parameters
/-- Category of quivers. -/
@[nolint check_univs]
def QuivCat :=
  Bundled Quiver.{v + 1, u}
#align category_theory.Quiv CategoryTheory.QuivCat
-/

namespace Quiv

instance : CoeSort QuivCat (Type u) where coe := Bundled.α

#print CategoryTheory.QuivCat.str' /-
instance str' (C : QuivCat.{v, u}) : Quiver.{v + 1, u} C :=
  C.str
#align category_theory.Quiv.str CategoryTheory.QuivCat.str'
-/

#print CategoryTheory.QuivCat.of /-
/-- Construct a bundled `Quiv` from the underlying type and the typeclass. -/
def of (C : Type u) [Quiver.{v + 1} C] : QuivCat.{v, u} :=
  Bundled.of C
#align category_theory.Quiv.of CategoryTheory.QuivCat.of
-/

instance : Inhabited QuivCat :=
  ⟨QuivCat.of (Quiver.Empty PEmpty)⟩

#print CategoryTheory.QuivCat.category /-
/-- Category structure on `Quiv` -/
instance category : LargeCategory.{max v u} QuivCat.{v, u}
    where
  Hom C D := Prefunctor C D
  id C := Prefunctor.id C
  comp C D E F G := Prefunctor.comp F G
  id_comp' C D F := by cases F <;> rfl
  comp_id' C D F := by cases F <;> rfl
  assoc' := by intros <;> rfl
#align category_theory.Quiv.category CategoryTheory.QuivCat.category
-/

#print CategoryTheory.QuivCat.forget /-
/-- The forgetful functor from categories to quivers. -/
@[simps]
def forget : Cat.{v, u} ⥤ QuivCat.{v, u}
    where
  obj C := QuivCat.of C
  map C D F := F.toPrefunctor
#align category_theory.Quiv.forget CategoryTheory.QuivCat.forget
-/

end Quiv

namespace Cat

#print CategoryTheory.Cat.free /-
/-- The functor sending each quiver to its path category. -/
@[simps]
def free : QuivCat.{v, u} ⥤ Cat.{max u v, u}
    where
  obj V := Cat.of (Paths V)
  map V W F :=
    { obj := fun X => F.obj X
      map := fun X Y f => F.mapPath f
      map_comp' := fun X Y Z f g => F.mapPath_comp f g }
  map_id' V := by change (show paths V ⥤ _ from _) = _; ext; apply eq_conj_eq_to_hom; rfl
  map_comp' U V W F G := by change (show paths U ⥤ _ from _) = _; ext; apply eq_conj_eq_to_hom; rfl
#align category_theory.Cat.free CategoryTheory.Cat.free
-/

end Cat

namespace Quiv

#print CategoryTheory.QuivCat.lift /-
/-- Any prefunctor into a category lifts to a functor from the path category. -/
@[simps]
def lift {V : Type u} [Quiver.{v + 1} V] {C : Type _} [Category C] (F : Prefunctor V C) :
    Paths V ⥤ C where
  obj X := F.obj X
  map X Y f := composePath (F.mapPath f)
#align category_theory.Quiv.lift CategoryTheory.QuivCat.lift
-/

#print CategoryTheory.QuivCat.adj /-
-- We might construct `of_lift_iso_self : paths.of ⋙ lift F ≅ F`
-- (and then show that `lift F` is initial amongst such functors)
-- but it would require lifting quite a bit of machinery to quivers!
/--
The adjunction between forming the free category on a quiver, and forgetting a category to a quiver.
-/
def adj : Cat.free ⊣ QuivCat.forget :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun V C =>
        { toFun := fun F => Paths.of.comp F.toPrefunctor
          invFun := fun F => lift F
          left_inv := fun F => by ext; · erw [(eq_conj_eq_to_hom _).symm]; apply category.id_comp;
            rfl
          right_inv := by
            rintro ⟨obj, map⟩
            dsimp only [Prefunctor.comp]
            congr
            ext X Y f
            exact category.id_comp _ }
      homEquiv_naturality_left_symm := fun V W C f g => by change (show paths V ⥤ _ from _) = _;
        ext; apply eq_conj_eq_to_hom; rfl }
#align category_theory.Quiv.adj CategoryTheory.QuivCat.adj
-/

end Quiv

end CategoryTheory

