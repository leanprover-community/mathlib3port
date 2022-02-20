/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Transport a monoidal structure along an equivalence.

When `C` and `D` are equivalent as categories,
we can transport a monoidal structure on `C` along the equivalence,
obtaining a monoidal structure on `D`.

We don't yet prove anything about this transported structure!
The next step would be to show that the original functor can be upgraded
to a monoidal functor with respect to this new structure.
-/


universe v₁ v₂ u₁ u₂

open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.MonoidalCategory

namespace CategoryTheory.Monoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D]

/-- Transport a monoidal structure along an equivalence of (plain) categories.
-/
@[simps]
def transport (e : C ≌ D) : MonoidalCategory.{v₂} D where
  tensorObj := fun X Y => e.Functor.obj (e.inverse.obj X ⊗ e.inverse.obj Y)
  tensorHom := fun W X Y Z f g => e.Functor.map (e.inverse.map f ⊗ e.inverse.map g)
  tensorUnit := e.Functor.obj (𝟙_ C)
  associator := fun X Y Z =>
    e.Functor.mapIso
      (((e.unitIso.app _).symm ⊗ Iso.refl _) ≪≫
        α_ (e.inverse.obj X) (e.inverse.obj Y) (e.inverse.obj Z) ≪≫ (Iso.refl _ ⊗ e.unitIso.app _))
  leftUnitor := fun X =>
    e.Functor.mapIso (((e.unitIso.app _).symm ⊗ Iso.refl _) ≪≫ λ_ (e.inverse.obj X)) ≪≫ e.counitIso.app _
  rightUnitor := fun X =>
    e.Functor.mapIso ((Iso.refl _ ⊗ (e.unitIso.app _).symm) ≪≫ ρ_ (e.inverse.obj X)) ≪≫ e.counitIso.app _
  triangle' := fun X Y => by
    dsimp
    simp only [iso.hom_inv_id_app_assoc, comp_tensor_id, equivalence.unit_inverse_comp, assoc, equivalence.inv_fun_map,
      comp_id, functor.map_comp, id_tensor_comp, e.inverse.map_id]
    simp only [← e.functor.map_comp]
    congr 2
    slice_lhs 2 3 => rw [← id_tensor_comp]simp dsimp rw [tensor_id]
    rw [category.id_comp, ← associator_naturality_assoc, triangle]
  pentagon' := fun W X Y Z => by
    dsimp
    simp only [iso.hom_inv_id_app_assoc, comp_tensor_id, assoc, equivalence.inv_fun_map, functor.map_comp,
      id_tensor_comp, e.inverse.map_id]
    simp only [← e.functor.map_comp]
    congr 2
    slice_lhs 4 5 => rw [← comp_tensor_id, iso.hom_inv_id_app]dsimp rw [tensor_id]
    simp only [category.id_comp, category.assoc]
    slice_lhs 5 6 => rw [← id_tensor_comp, iso.hom_inv_id_app]dsimp rw [tensor_id]
    simp only [category.id_comp, category.assoc]
    slice_rhs 2 3 => rw [id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
    slice_rhs 1 2 => rw [← tensor_id, ← associator_naturality]
    slice_rhs 3 4 => rw [← tensor_id, associator_naturality]
    slice_rhs 2 3 => rw [← pentagon]
    simp only [category.assoc]
    congr 2
    slice_lhs 1 2 => rw [associator_naturality]
    simp only [category.assoc]
    congr 1
    slice_lhs 1 2 => rw [← id_tensor_comp, ← comp_tensor_id, iso.hom_inv_id_app]dsimp rw [tensor_id, tensor_id]
    simp only [category.id_comp, category.assoc]
  left_unitor_naturality' := fun X Y f => by
    dsimp
    simp only [functor.map_comp, Functor.map_id, category.assoc]
    erw [← e.counit_iso.hom.naturality]
    simp only [functor.comp_map, ← e.functor.map_comp_assoc]
    congr 2
    rw [e.inverse.map_id, id_tensor_comp_tensor_id_assoc, ← tensor_id_comp_id_tensor_assoc, left_unitor_naturality]
  right_unitor_naturality' := fun X Y f => by
    dsimp
    simp only [functor.map_comp, Functor.map_id, category.assoc]
    erw [← e.counit_iso.hom.naturality]
    simp only [functor.comp_map, ← e.functor.map_comp_assoc]
    congr 2
    rw [e.inverse.map_id, tensor_id_comp_id_tensor_assoc, ← id_tensor_comp_tensor_id_assoc, right_unitor_naturality]
  associator_naturality' := fun X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃ => by
    dsimp
    simp only [equivalence.inv_fun_map, functor.map_comp, category.assoc]
    simp only [← e.functor.map_comp]
    congr 1
    conv_lhs => rw [← tensor_id_comp_id_tensor]
    slice_lhs 2 3 => rw [id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor, ← tensor_id]
    simp only [category.assoc]
    slice_lhs 3 4 => rw [associator_naturality]
    conv_lhs => simp only [comp_tensor_id]
    slice_lhs 3 4 => rw [← comp_tensor_id, iso.hom_inv_id_app]dsimp rw [tensor_id]
    simp only [category.id_comp, category.assoc]
    slice_lhs 2 3 => rw [associator_naturality]
    simp only [category.assoc]
    congr 2
    slice_lhs 1 1 => rw [← tensor_id_comp_id_tensor]
    slice_lhs 2 3 => rw [← id_tensor_comp, tensor_id_comp_id_tensor]
    slice_lhs 1 2 => rw [tensor_id_comp_id_tensor]
    conv_rhs => congr skip rw [← id_tensor_comp_tensor_id, id_tensor_comp]
    simp only [category.assoc]
    slice_rhs 1 2 => rw [← id_tensor_comp, iso.hom_inv_id_app]dsimp rw [tensor_id]
    simp only [category.id_comp, category.assoc]
    conv_rhs => rw [id_tensor_comp]
    slice_rhs 2 3 => rw [id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
    slice_rhs 1 2 => rw [id_tensor_comp_tensor_id]

/-- A type synonym for `D`, which will carry the transported monoidal structure. -/
@[nolint unused_arguments]
def Transported (e : C ≌ D) :=
  D deriving Category

instance (e : C ≌ D) : MonoidalCategory (Transported e) :=
  transport e

instance (e : C ≌ D) : Inhabited (Transported e) :=
  ⟨𝟙_ _⟩

/-- We can upgrade `e.functor` to a lax monoidal functor from `C` to `D` with the transported structure.
-/
@[simps]
def laxToTransported (e : C ≌ D) : LaxMonoidalFunctor C (Transported e) :=
  { e.Functor with ε := 𝟙 (e.Functor.obj (𝟙_ C)), μ := fun X Y => e.Functor.map (e.unitInv.app X ⊗ e.unitInv.app Y),
    μ_natural' := fun X Y X' Y' f g => by
      dsimp
      simp only [equivalence.inv_fun_map, functor.map_comp, tensor_comp, category.assoc]
      simp only [← e.functor.map_comp]
      congr 1
      rw [← tensor_comp, iso.hom_inv_id_app, iso.hom_inv_id_app, ← tensor_comp]
      dsimp
      rw [comp_id, comp_id],
    associativity' := fun X Y Z => by
      dsimp
      simp only [comp_tensor_id, assoc, equivalence.inv_fun_map, functor.map_comp, id_tensor_comp, e.inverse.map_id]
      simp only [← e.functor.map_comp]
      congr 2
      slice_lhs 3 3 => rw [← tensor_id_comp_id_tensor]
      slice_lhs 2 3 => rw [← comp_tensor_id, iso.hom_inv_id_app]dsimp rw [tensor_id]
      simp only [id_comp]
      slice_rhs 2 3 => rw [← id_tensor_comp, iso.hom_inv_id_app]dsimp rw [tensor_id]
      simp only [id_comp]
      conv_rhs => rw [← id_tensor_comp_tensor_id _ (e.unit_inv.app X)]
      dsimp only [functor.comp_obj]
      slice_rhs 3 4 => rw [← id_tensor_comp, iso.hom_inv_id_app]dsimp rw [tensor_id]
      simp only [id_comp]
      simp [associator_naturality],
    left_unitality' := fun X => by
      dsimp
      simp only [tensor_id, assoc, id_comp, functor.map_comp, e.inverse.map_id]
      rw [equivalence.counit_app_functor]
      simp only [← e.functor.map_comp]
      congr 1
      rw [← left_unitor_naturality]
      simp ,
    right_unitality' := fun X => by
      dsimp
      simp only [tensor_id, assoc, id_comp, functor.map_comp, e.inverse.map_id]
      rw [equivalence.counit_app_functor]
      simp only [← e.functor.map_comp]
      congr 1
      rw [← right_unitor_naturality]
      simp }

/-- We can upgrade `e.functor` to a monoidal functor from `C` to `D` with the transported structure.
-/
@[simps]
def toTransported (e : C ≌ D) : MonoidalFunctor C (Transported e) :=
  { laxToTransported e with
    ε_is_iso := by
      dsimp
      infer_instance,
    μ_is_iso := fun X Y => by
      dsimp
      infer_instance }

/-- We can upgrade `e.inverse` to a lax monoidal functor from `D` with the transported structure to `C`.
-/
@[simps]
def laxFromTransported (e : C ≌ D) : LaxMonoidalFunctor (Transported e) C :=
  { e.inverse with ε := e.Unit.app (𝟙_ C), μ := fun X Y => e.Unit.app (e.inverse.obj X ⊗ e.inverse.obj Y),
    μ_natural' := fun X Y X' Y' f g => by
      dsimp
      simp only [iso.hom_inv_id_app_assoc, equivalence.inv_fun_map],
    associativity' := fun X Y Z => by
      dsimp
      simp only [iso.hom_inv_id_app_assoc, assoc, equivalence.inv_fun_map, functor.map_comp]
      slice_lhs 1 2 => rw [← comp_tensor_id, iso.hom_inv_id_app]dsimp rw [tensor_id]
      simp ,
    left_unitality' := fun X => by
      dsimp
      simp only [iso.hom_inv_id_app_assoc, equivalence.unit_inverse_comp, assoc, equivalence.inv_fun_map, comp_id,
        functor.map_comp]
      slice_rhs 1 2 => rw [← comp_tensor_id, iso.hom_inv_id_app]dsimp rw [tensor_id]
      simp ,
    right_unitality' := fun X => by
      dsimp
      simp only [iso.hom_inv_id_app_assoc, equivalence.unit_inverse_comp, assoc, equivalence.inv_fun_map, comp_id,
        functor.map_comp]
      slice_rhs 1 2 => rw [← id_tensor_comp, iso.hom_inv_id_app]dsimp rw [tensor_id]
      simp }

/-- We can upgrade `e.inverse` to a monoidal functor from `D` with the transported structure to `C`.
-/
@[simps]
def fromTransported (e : C ≌ D) : MonoidalFunctor (Transported e) C :=
  { laxFromTransported e with
    ε_is_iso := by
      dsimp
      infer_instance,
    μ_is_iso := fun X Y => by
      dsimp
      infer_instance }

/-- The unit isomorphism upgrades to a monoidal isomorphism. -/
@[simps]
def transportedMonoidalUnitIso (e : C ≌ D) : LaxMonoidalFunctor.id C ≅ laxToTransported e ⊗⋙ laxFromTransported e :=
  MonoidalNatIso.ofComponents (fun X => e.unitIso.app X) (fun X Y f => e.Unit.naturality f)
    (by
      dsimp
      simp )
    fun X Y => by
    dsimp
    simp only [iso.hom_inv_id_app_assoc, id_comp, equivalence.inv_fun_map]
    slice_rhs 1 2 => rw [← tensor_comp, iso.hom_inv_id_app, iso.hom_inv_id_app]dsimp rw [tensor_id]
    simp

/-- The counit isomorphism upgrades to a monoidal isomorphism. -/
@[simps]
def transportedMonoidalCounitIso (e : C ≌ D) :
    laxFromTransported e ⊗⋙ laxToTransported e ≅ LaxMonoidalFunctor.id (Transported e) :=
  MonoidalNatIso.ofComponents (fun X => e.counitIso.app X) (fun X Y f => e.counit.naturality f)
    (by
      dsimp
      simp )
    fun X Y => by
    dsimp
    simp only [iso.hom_inv_id_app_assoc, id_comp, equivalence.inv_fun_map]
    simp only [equivalence.counit_app_functor, ← e.functor.map_id, ← e.functor.map_comp]
    congr 1
    simp [equivalence.unit_inv_app_inverse]
    dsimp
    simp

-- See note [dsimp, simp].
-- We could put these together as an equivalence of monoidal categories,
-- but I don't want to do this quite yet.
-- Etingof-Gelaki-Nikshych-Ostrik "Tensor categories" define an equivalence of monoidal categories
-- as a monoidal functor which, as a functor, is an equivalence.
-- Presumably one can show that the inverse functor can be upgraded to a monoidal
-- functor in a unique way, such that the unit and counit are monoidal natural isomorphisms,
-- but I've never seen this explained or worked it out.
end CategoryTheory.Monoidal

