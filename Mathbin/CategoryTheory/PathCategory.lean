import Mathbin.CategoryTheory.EqToHom

/-!
# The category paths on a quiver.
-/


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

/-- 
A type synonym for the category of paths in a quiver.
-/
def paths (V : Type u₁) : Type u₁ :=
  V

instance (V : Type u₁) [Inhabited V] : Inhabited (paths V) :=
  ⟨(default V : V)⟩

variable (V : Type u₁) [Quiver.{v₁ + 1} V]

namespace Paths

-- failed to format: format: uncaught backtrack exception
instance
  category_paths
  : category .{ max u₁ v₁ } ( paths V )
  where Hom X Y : V := Quiver.Path X Y id X := Quiver.Path.nil comp X Y Z f g := Quiver.Path.comp f g

variable {V}

/-- 
The inclusion of a quiver `V` into its path category, as a prefunctor.
-/
@[simps]
def of : Prefunctor V (paths V) :=
  { obj := fun X => X, map := fun X Y f => f.to_path }

attribute [local ext] Functor.ext

/--  Two functors out of a path category are equal when they agree on singleton paths. -/
@[ext]
theorem ext_functor {C} [category C] {F G : paths V ⥤ C} (h_obj : F.obj = G.obj)
    (h :
      ∀ a b : V e : a ⟶ b,
        F.map e.to_path = eq_to_hom (congr_funₓ h_obj a) ≫ G.map e.to_path ≫ eq_to_hom (congr_funₓ h_obj.symm b)) :
    F = G := by
  ext X Y f
  ·
    induction' f with Y' Z' g e ih
    ·
      erw [F.map_id, G.map_id, category.id_comp, eq_to_hom_trans, eq_to_hom_refl]
    ·
      erw [F.map_comp g e.to_path, G.map_comp g e.to_path, ih, h]
      simp only [category.id_comp, eq_to_hom_refl, eq_to_hom_trans_assoc, category.assoc]
  ·
    intro X
    rw [h_obj]

end Paths

variable (W : Type u₂) [Quiver.{v₂ + 1} W]

@[simp]
theorem prefunctor.map_path_comp' (F : Prefunctor V W) {X Y Z : paths V} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map_path (f ≫ g) = (F.map_path f).comp (F.map_path g) :=
  Prefunctor.map_path_comp _ _ _

end

section

variable {C : Type u₁} [category.{v₁} C]

open Quiver

/--  A path in a category can be composed to a single morphism. -/
@[simp]
def compose_path {X : C} : ∀ {Y : C} p : path X Y, X ⟶ Y
  | _, path.nil => 𝟙 X
  | _, path.cons p e => compose_path p ≫ e

@[simp]
theorem compose_path_comp {X Y Z : C} (f : path X Y) (g : path Y Z) :
    compose_path (f.comp g) = compose_path f ≫ compose_path g := by
  induction' g with Y' Z' g e ih
  ·
    simp
  ·
    simp [ih]

end

end CategoryTheory

