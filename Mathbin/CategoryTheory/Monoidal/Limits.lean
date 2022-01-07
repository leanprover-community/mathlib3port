import Mathbin.CategoryTheory.Monoidal.Functorial
import Mathbin.CategoryTheory.Monoidal.FunctorCategory
import Mathbin.CategoryTheory.Limits.HasLimits

/-!
# `lim : (J ⥤ C) ⥤ C` is lax monoidal when `C` is a monoidal category.

When `C` is a monoidal category, the functorial association `F ↦ limit F` is lax monoidal,
i.e. there are morphisms
* `lim_lax.ε : (𝟙_ C) → limit (𝟙_ (J ⥤ C))`
* `lim_lax.μ : limit F ⊗ limit G ⟶ limit (F ⊗ G)`
satisfying the laws of a lax monoidal functor.
-/


open CategoryTheory

open CategoryTheory.MonoidalCategory

namespace CategoryTheory.Limits

universe v u

noncomputable section

variable {J : Type v} [small_category J]

variable {C : Type u} [category.{v} C] [has_limits C]

instance limit_functorial : functorial fun F : J ⥤ C => limit F :=
  { limits.lim with }

@[simp]
theorem limit_functorial_map {F G : J ⥤ C} (α : F ⟶ G) : map (fun F : J ⥤ C => limit F) α = limits.lim.map α :=
  rfl

variable [monoidal_category.{v} C]

@[simps]
instance limit_lax_monoidal : lax_monoidal fun F : J ⥤ C => limit F where
  ε := limit.lift _ { x := _, π := { app := fun j => 𝟙 _ } }
  μ := fun F G =>
    limit.lift (F ⊗ G)
      { x := limit F ⊗ limit G,
        π :=
          { app := fun j => limit.π F j ⊗ limit.π G j,
            naturality' := fun j j' f => by
              dsimp
              simp only [category.id_comp, ← tensor_comp, limit.w] } }
  μ_natural' := fun X Y X' Y' f g => by
    ext
    dsimp
    simp only [limit.lift_π, cones.postcompose_obj_π, monoidal.tensor_hom_app, limit.lift_map, nat_trans.comp_app,
      category.assoc, ← tensor_comp, lim_map_π]
  associativity' := fun X Y Z => by
    ext
    dsimp
    simp only [limit.lift_π, cones.postcompose_obj_π, monoidal.associator_hom_app, limit.lift_map, nat_trans.comp_app,
      category.assoc]
    slice_lhs 2 2 => rw [← tensor_id_comp_id_tensor]
    slice_lhs 1 2 => rw [← comp_tensor_id, limit.lift_π]dsimp
    slice_lhs 1 2 => rw [tensor_id_comp_id_tensor]
    conv_lhs => rw [associator_naturality]
    conv_rhs => rw [← id_tensor_comp_tensor_id (limit.π (Y ⊗ Z) j)]
    slice_rhs 2 3 => rw [← id_tensor_comp, limit.lift_π]dsimp
    dsimp
    simp
  left_unitality' := fun X => by
    ext
    dsimp
    simp
    conv_rhs => rw [← tensor_id_comp_id_tensor (limit.π X j)]
    slice_rhs 1 2 => rw [← comp_tensor_id]erw [limit.lift_π]dsimp
    slice_rhs 2 3 => rw [left_unitor_naturality]
    simp
  right_unitality' := fun X => by
    ext
    dsimp
    simp
    conv_rhs => rw [← id_tensor_comp_tensor_id _ (limit.π X j)]
    slice_rhs 1 2 => rw [← id_tensor_comp]erw [limit.lift_π]dsimp
    slice_rhs 2 3 => rw [right_unitor_naturality]
    simp

/-- The limit functor `F ↦ limit F` bundled as a lax monoidal functor. -/
def lim_lax : lax_monoidal_functor (J ⥤ C) C :=
  lax_monoidal_functor.of fun F : J ⥤ C => limit F

@[simp]
theorem lim_lax_obj (F : J ⥤ C) : lim_lax.obj F = limit F :=
  rfl

theorem lim_lax_obj' (F : J ⥤ C) : lim_lax.obj F = lim.obj F :=
  rfl

@[simp]
theorem lim_lax_map {F G : J ⥤ C} (α : F ⟶ G) : lim_lax.map α = lim.map α :=
  rfl

@[simp]
theorem lim_lax_ε : (@lim_lax J _ C _ _ _).ε = limit.lift _ { x := _, π := { app := fun j => 𝟙 _ } } :=
  rfl

@[simp]
theorem lim_lax_μ (F G : J ⥤ C) :
    (@lim_lax J _ C _ _ _).μ F G =
      limit.lift (F ⊗ G)
        { x := limit F ⊗ limit G,
          π :=
            { app := fun j => limit.π F j ⊗ limit.π G j,
              naturality' := fun j j' f => by
                dsimp
                simp only [category.id_comp, ← tensor_comp, limit.w] } } :=
  rfl

end CategoryTheory.Limits

