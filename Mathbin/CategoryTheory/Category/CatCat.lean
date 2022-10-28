/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.CategoryTheory.ConcreteCategory.Bundled
import Mathbin.CategoryTheory.DiscreteCategory
import Mathbin.CategoryTheory.Types
import Mathbin.CategoryTheory.Bicategory.Strict

/-!
# Category of categories

This file contains the definition of the category `Cat` of all categories.
In this category objects are categories and
morphisms are functors between these categories.

## Implementation notes

Though `Cat` is not a concrete category, we use `bundled` to define
its carrier type.
-/


universe v u

namespace CategoryTheory

-- intended to be used with explicit universe parameters
/-- Category of categories. -/
@[nolint check_univs]
def CatCat :=
  Bundled Category.{v, u}

namespace CatCat

instance : Inhabited CatCat :=
  ⟨⟨Type u, CategoryTheory.types⟩⟩

instance : CoeSort CatCat (Type u) :=
  ⟨Bundled.α⟩

instance str (C : CatCat.{v, u}) : Category.{v, u} C :=
  C.str

/-- Construct a bundled `Cat` from the underlying type and the typeclass. -/
def of (C : Type u) [Category.{v} C] : CatCat.{v, u} :=
  Bundled.of C

/-- Bicategory structure on `Cat` -/
instance bicategory : Bicategory.{max v u, max v u} CatCat.{v, u} where
  Hom C D := C ⥤ D
  id C := 𝟭 C
  comp C D E F G := F ⋙ G
  homCategory C D := Functor.category C D
  whiskerLeft C D E F G H η := whiskerLeft F η
  whiskerRight C D E F G η H := whiskerRight η H
  associator A B C D := Functor.associator
  leftUnitor A B := Functor.leftUnitor
  rightUnitor A B := Functor.rightUnitor
  pentagon' A B C D E := Functor.pentagon
  triangle' A B C := Functor.triangle

/-- `Cat` is a strict bicategory. -/
instance bicategory.strict : Bicategory.Strict CatCat.{v, u} where
  id_comp' C D F := by cases F <;> rfl
  comp_id' C D F := by cases F <;> rfl
  assoc' := by intros <;> rfl

/-- Category structure on `Cat` -/
instance category : LargeCategory.{max v u} CatCat.{v, u} :=
  StrictBicategory.category CatCat.{v, u}

@[simp]
theorem id_map {C : CatCat} {X Y : C} (f : X ⟶ Y) : (𝟙 C : C ⥤ C).map f = f :=
  Functor.id_map f

@[simp]
theorem comp_obj {C D E : CatCat} (F : C ⟶ D) (G : D ⟶ E) (X : C) : (F ≫ G).obj X = G.obj (F.obj X) :=
  Functor.comp_obj F G X

@[simp]
theorem comp_map {C D E : CatCat} (F : C ⟶ D) (G : D ⟶ E) {X Y : C} (f : X ⟶ Y) : (F ≫ G).map f = G.map (F.map f) :=
  Functor.comp_map F G f

/-- Functor that gets the set of objects of a category. It is not
called `forget`, because it is not a faithful functor. -/
def objects : Cat.{v, u} ⥤ Type u where
  obj C := C
  map C D F := F.obj

section

attribute [local simp] eq_to_hom_map

/-- Any isomorphism in `Cat` induces an equivalence of the underlying categories. -/
def equivOfIso {C D : CatCat} (γ : C ≅ D) : C ≌ D where
  Functor := γ.Hom
  inverse := γ.inv
  unitIso := eq_to_iso <| Eq.symm γ.hom_inv_id
  counitIso := eqToIso γ.inv_hom_id

end

end CatCat

/-- Embedding `Type` into `Cat` as discrete categories.

This ought to be modelled as a 2-functor!
-/
@[simps]
def typeToCat : Type u ⥤ Cat where
  obj X := CatCat.of (Discrete X)
  map X Y f := Discrete.functor (discrete.mk ∘ f)
  map_id' X := by
    apply Functor.ext
    tidy
  map_comp' X Y Z f g := by
    apply Functor.ext
    tidy

instance :
    Faithful
      typeToCat.{u} where map_injective' X Y f g h := funext fun x => congr_arg Discrete.as (Functor.congr_obj h ⟨x⟩)

instance : Full typeToCat.{u} where
  preimage X Y F := discrete.as ∘ F.obj ∘ discrete.mk
  witness' := by
    intro X Y F
    apply Functor.ext
    · intro x y f
      dsimp
      ext
      
    · rintro ⟨x⟩
      ext
      rfl
      

end CategoryTheory

