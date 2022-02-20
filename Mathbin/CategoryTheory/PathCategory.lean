/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.EqToHom
import Mathbin.Combinatorics.Quiver.Path

/-!
# The category paths on a quiver.
-/


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

/-- A type synonym for the category of paths in a quiver.
-/
def Paths (V : Type u₁) : Type u₁ :=
  V

instance (V : Type u₁) [Inhabited V] : Inhabited (Paths V) :=
  ⟨(default : V)⟩

variable (V : Type u₁) [Quiver.{v₁ + 1} V]

namespace Paths

instance categoryPaths : Category.{max u₁ v₁} (Paths V) where
  Hom := fun X Y : V => Quiver.Path X Y
  id := fun X => Quiver.Path.nil
  comp := fun X Y Z f g => Quiver.Path.comp f g

variable {V}

/-- The inclusion of a quiver `V` into its path category, as a prefunctor.
-/
@[simps]
def of : Prefunctor V (Paths V) where
  obj := fun X => X
  map := fun X Y f => f.toPath

attribute [local ext] Functor.ext

/-- Two functors out of a path category are equal when they agree on singleton paths. -/
@[ext]
theorem ext_functor {C} [Category C] {F G : Paths V ⥤ C} (h_obj : F.obj = G.obj)
    (h :
      ∀ a b : V e : a ⟶ b,
        F.map e.toPath = eqToHom (congr_funₓ h_obj a) ≫ G.map e.toPath ≫ eqToHom (congr_funₓ h_obj.symm b)) :
    F = G := by
  ext X Y f
  · induction' f with Y' Z' g e ih
    · erw [F.map_id, G.map_id, category.id_comp, eq_to_hom_trans, eq_to_hom_refl]
      
    · erw [F.map_comp g e.to_path, G.map_comp g e.to_path, ih, h]
      simp only [category.id_comp, eq_to_hom_refl, eq_to_hom_trans_assoc, category.assoc]
      
    
  · intro X
    rw [h_obj]
    

end Paths

variable (W : Type u₂) [Quiver.{v₂ + 1} W]

-- A restatement of `prefunctor.map_path_comp` using `f ≫ g` instead of `f.comp g`.
@[simp]
theorem Prefunctor.map_path_comp' (F : Prefunctor V W) {X Y Z : Paths V} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.mapPath (f ≫ g) = (F.mapPath f).comp (F.mapPath g) :=
  Prefunctor.map_path_comp _ _ _

end

section

variable {C : Type u₁} [Category.{v₁} C]

open Quiver

/-- A path in a category can be composed to a single morphism. -/
@[simp]
def composePathₓ {X : C} : ∀ {Y : C} p : Path X Y, X ⟶ Y
  | _, path.nil => 𝟙 X
  | _, path.cons p e => compose_path p ≫ e

@[simp]
theorem compose_path_comp {X Y Z : C} (f : Path X Y) (g : Path Y Z) :
    composePathₓ (f.comp g) = composePathₓ f ≫ composePathₓ g := by
  induction' g with Y' Z' g e ih
  · simp
    
  · simp [ih]
    

end

end CategoryTheory

