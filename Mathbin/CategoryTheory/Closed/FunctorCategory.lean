/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import Mathbin.CategoryTheory.Closed.Monoidal
import Mathbin.CategoryTheory.Monoidal.FunctorCategory

/-!
# Functors from a groupoid into a monoidal closed category form a monoidal closed category.

(Using the pointwise monoidal structure on the functor category.)
-/


noncomputable section

open CategoryTheory

open CategoryTheory.MonoidalCategory

open CategoryTheory.MonoidalClosed

namespace CategoryTheory.Functor

variable {C D : Type _} [Groupoid D] [Category C] [MonoidalCategory C] [MonoidalClosed C]

/-- Auxiliary definition for `category_theory.monoidal_closed.functor_closed`.
The internal hom functor `F ⟶[C] -` -/
@[simps]
def closedIhom (F : D ⥤ C) : (D ⥤ C) ⥤ D ⥤ C :=
  ((whiskeringRight₂ D Cᵒᵖ C C).obj internalHom).obj (Groupoid.invFunctor D ⋙ F.op)

/-- Auxiliary definition for `category_theory.monoidal_closed.functor_closed`.
The unit for the adjunction `(tensor_left F) ⊣ (ihom F)`. -/
@[simps]
def closedUnit (F : D ⥤ C) :
    𝟭 (D ⥤ C) ⟶
      tensorLeft F ⋙
        closedIhom F where app G :=
    { app := fun X => (ihom.coev (F.obj X)).app (G.obj X),
      naturality' := by
        intro X Y f
        dsimp
        simp only [ihom.coev_naturality, closed_ihom_obj_map, monoidal.tensor_obj_map]
        dsimp
        rw [coev_app_comp_pre_app_assoc, ← functor.map_comp]
        simp }

/-- Auxiliary definition for `category_theory.monoidal_closed.functor_closed`.
The counit for the adjunction `(tensor_left F) ⊣ (ihom F)`. -/
@[simps]
def closedCounit (F : D ⥤ C) :
    closedIhom F ⋙ tensorLeft F ⟶
      𝟭 (D ⥤ C) where app G :=
    { app := fun X => (ihom.ev (F.obj X)).app (G.obj X),
      naturality' := by
        intro X Y f
        dsimp
        simp only [closed_ihom_obj_map, pre_comm_ihom_map]
        rw [← tensor_id_comp_id_tensor, id_tensor_comp]
        simp }

/-- If `C` is a monoidal closed category and `D` is groupoid, then every functor `F : D ⥤ C` is
closed in the functor category `F : D ⥤ C` with the pointwise monoidal structure. -/
@[simps]
instance closed (F : D ⥤ C) :
    Closed
      F where isAdj :=
    { right := closedIhom F, adj := Adjunction.mkOfUnitCounit { Unit := closedUnit F, counit := closedCounit F } }

/-- If `C` is a monoidal closed category and `D` is groupoid, then the functor category `D ⥤ C`,
with the pointwise monoidal structure, is monoidal closed. -/
@[simps]
instance monoidalClosed : MonoidalClosed (D ⥤ C) where closed' := by infer_instance

end CategoryTheory.Functor

