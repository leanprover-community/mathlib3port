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

noncomputable theory

variable{J : Type v}[small_category J]

variable{C : Type u}[category.{v} C][has_limits C]

-- error in CategoryTheory.Monoidal.Limits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
instance limit_functorial : functorial (λ F : «expr ⥤ »(J, C), limit F) := { ..limits.lim }

-- error in CategoryTheory.Monoidal.Limits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[simp]
theorem limit_functorial_map
{F G : «expr ⥤ »(J, C)}
(α : «expr ⟶ »(F, G)) : «expr = »(map (λ F : «expr ⥤ »(J, C), limit F) α, limits.lim.map α) :=
rfl

variable[monoidal_category.{v} C]

-- error in CategoryTheory.Monoidal.Limits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[simps #[]] instance limit_lax_monoidal : lax_monoidal (λ F : «expr ⥤ »(J, C), limit F) :=
{ ε := limit.lift _ { X := _, π := { app := λ j, «expr𝟙»() _ } },
  μ := λ
  F
  G, limit.lift [«expr ⊗ »/«expr ⊗ »/«expr ⊗ »](F, G) { X := [«expr ⊗ »/«expr ⊗ »/«expr ⊗ »](limit F, limit G),
    π := { app := λ j, [«expr ⊗ »/«expr ⊗ »/«expr ⊗ »](limit.π F j, limit.π G j),
      naturality' := λ j j' f, begin
        dsimp [] [] [] [],
        simp [] [] ["only"] ["[", expr category.id_comp, ",", "<-", expr tensor_comp, ",", expr limit.w, "]"] [] []
      end } },
  μ_natural' := λ X Y X' Y' f g, begin
    ext [] [] [],
    dsimp [] [] [] [],
    simp [] [] ["only"] ["[", expr limit.lift_π, ",", expr cones.postcompose_obj_π, ",", expr monoidal.tensor_hom_app, ",", expr limit.lift_map, ",", expr nat_trans.comp_app, ",", expr category.assoc, ",", "<-", expr tensor_comp, ",", expr lim_map_π, "]"] [] []
  end,
  associativity' := λ X Y Z, begin
    ext [] [] [],
    dsimp [] [] [] [],
    simp [] [] ["only"] ["[", expr limit.lift_π, ",", expr cones.postcompose_obj_π, ",", expr monoidal.associator_hom_app, ",", expr limit.lift_map, ",", expr nat_trans.comp_app, ",", expr category.assoc, "]"] [] [],
    slice_lhs [2] [2] { rw ["[", "<-", expr tensor_id_comp_id_tensor, "]"] },
    slice_lhs [1] [2] { rw ["[", "<-", expr comp_tensor_id, ",", expr limit.lift_π, "]"],
      dsimp [] [] [] },
    slice_lhs [1] [2] { rw ["[", expr tensor_id_comp_id_tensor, "]"] },
    conv_lhs [] [] { rw ["[", expr associator_naturality, "]"] },
    conv_rhs [] [] { rw ["[", "<-", expr id_tensor_comp_tensor_id (limit.π [«expr ⊗ »/«expr ⊗ »/«expr ⊗ »](Y, Z) j), "]"] },
    slice_rhs [2] [3] { rw ["[", "<-", expr id_tensor_comp, ",", expr limit.lift_π, "]"],
      dsimp [] [] [] },
    dsimp [] [] [] [],
    simp [] [] [] [] [] []
  end,
  left_unitality' := λ X, begin
    ext [] [] [],
    dsimp [] [] [] [],
    simp [] [] [] [] [] [],
    conv_rhs [] [] { rw ["[", "<-", expr tensor_id_comp_id_tensor (limit.π X j), "]"] },
    slice_rhs [1] [2] { rw ["[", "<-", expr comp_tensor_id, "]"],
      erw ["[", expr limit.lift_π, "]"],
      dsimp [] [] [] },
    slice_rhs [2] [3] { rw ["[", expr left_unitor_naturality, "]"] },
    simp [] [] [] [] [] []
  end,
  right_unitality' := λ X, begin
    ext [] [] [],
    dsimp [] [] [] [],
    simp [] [] [] [] [] [],
    conv_rhs [] [] { rw ["[", "<-", expr id_tensor_comp_tensor_id _ (limit.π X j), "]"] },
    slice_rhs [1] [2] { rw ["[", "<-", expr id_tensor_comp, "]"],
      erw ["[", expr limit.lift_π, "]"],
      dsimp [] [] [] },
    slice_rhs [2] [3] { rw ["[", expr right_unitor_naturality, "]"] },
    simp [] [] [] [] [] []
  end }

-- error in CategoryTheory.Monoidal.Limits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The limit functor `F ↦ limit F` bundled as a lax monoidal functor. -/
def lim_lax : lax_monoidal_functor «expr ⥤ »(J, C) C :=
lax_monoidal_functor.of (λ F : «expr ⥤ »(J, C), limit F)

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
            naturality' :=
              fun j j' f =>
                by 
                  dsimp 
                  simp only [category.id_comp, ←tensor_comp, limit.w] } } :=
  rfl

end CategoryTheory.Limits

