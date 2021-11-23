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

variable{C : Type u₁}[category.{v₁} C][monoidal_category.{v₁} C]

variable{D : Type u₂}[category.{v₂} D]

/--
Transport a monoidal structure along an equivalence of (plain) categories.
-/
@[simps]
def transport (e : C ≌ D) : monoidal_category.{v₂} D :=
  { tensorObj := fun X Y => e.functor.obj (e.inverse.obj X ⊗ e.inverse.obj Y),
    tensorHom := fun W X Y Z f g => e.functor.map (e.inverse.map f ⊗ e.inverse.map g),
    tensorUnit := e.functor.obj (𝟙_ C),
    associator :=
      fun X Y Z =>
        e.functor.map_iso
          (((e.unit_iso.app _).symm ⊗ iso.refl _) ≪≫
            α_ (e.inverse.obj X) (e.inverse.obj Y) (e.inverse.obj Z) ≪≫ (iso.refl _ ⊗ e.unit_iso.app _)),
    leftUnitor :=
      fun X => e.functor.map_iso (((e.unit_iso.app _).symm ⊗ iso.refl _) ≪≫ λ_ (e.inverse.obj X)) ≪≫ e.counit_iso.app _,
    rightUnitor :=
      fun X => e.functor.map_iso ((iso.refl _ ⊗ (e.unit_iso.app _).symm) ≪≫ ρ_ (e.inverse.obj X)) ≪≫ e.counit_iso.app _,
    triangle' :=
      fun X Y =>
        by 
          dsimp 
          simp only [iso.hom_inv_id_app_assoc, comp_tensor_id, equivalence.unit_inverse_comp, assoc,
            equivalence.inv_fun_map, comp_id, functor.map_comp, id_tensor_comp, e.inverse.map_id]
          simp only [←e.functor.map_comp]
          congr 2
          sliceLHS 2 3 => rw [←id_tensor_comp]simp dsimp rw [tensor_id]
          rw [category.id_comp, ←associator_naturality_assoc, triangle],
    pentagon' :=
      fun W X Y Z =>
        by 
          dsimp 
          simp only [iso.hom_inv_id_app_assoc, comp_tensor_id, assoc, equivalence.inv_fun_map, functor.map_comp,
            id_tensor_comp, e.inverse.map_id]
          simp only [←e.functor.map_comp]
          congr 2
          sliceLHS 4 5 => rw [←comp_tensor_id, iso.hom_inv_id_app]dsimp rw [tensor_id]
          simp only [category.id_comp, category.assoc]
          sliceLHS 5 6 => rw [←id_tensor_comp, iso.hom_inv_id_app]dsimp rw [tensor_id]
          simp only [category.id_comp, category.assoc]
          sliceRHS 2 3 => rw [id_tensor_comp_tensor_id, ←tensor_id_comp_id_tensor]
          sliceRHS 1 2 => rw [←tensor_id, ←associator_naturality]
          sliceRHS 3 4 => rw [←tensor_id, associator_naturality]
          sliceRHS 2 3 => rw [←pentagon]
          simp only [category.assoc]
          congr 2
          sliceLHS 1 2 => rw [associator_naturality]
          simp only [category.assoc]
          congr 1
          sliceLHS 1 2 => rw [←id_tensor_comp, ←comp_tensor_id, iso.hom_inv_id_app]dsimp rw [tensor_id, tensor_id]
          simp only [category.id_comp, category.assoc],
    left_unitor_naturality' :=
      fun X Y f =>
        by 
          dsimp 
          simp only [functor.map_comp, Functor.map_id, category.assoc]
          erw [←e.counit_iso.hom.naturality]
          simp only [functor.comp_map, ←e.functor.map_comp_assoc]
          congr 2
          rw [e.inverse.map_id, id_tensor_comp_tensor_id_assoc, ←tensor_id_comp_id_tensor_assoc,
            left_unitor_naturality],
    right_unitor_naturality' :=
      fun X Y f =>
        by 
          dsimp 
          simp only [functor.map_comp, Functor.map_id, category.assoc]
          erw [←e.counit_iso.hom.naturality]
          simp only [functor.comp_map, ←e.functor.map_comp_assoc]
          congr 2
          rw [e.inverse.map_id, tensor_id_comp_id_tensor_assoc, ←id_tensor_comp_tensor_id_assoc,
            right_unitor_naturality],
    associator_naturality' :=
      fun X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃ =>
        by 
          dsimp 
          simp only [equivalence.inv_fun_map, functor.map_comp, category.assoc]
          simp only [←e.functor.map_comp]
          congr 1
          convLHS => rw [←tensor_id_comp_id_tensor]
          sliceLHS 2 3 => rw [id_tensor_comp_tensor_id, ←tensor_id_comp_id_tensor, ←tensor_id]
          simp only [category.assoc]
          sliceLHS 3 4 => rw [associator_naturality]
          convLHS => simp only [comp_tensor_id]
          sliceLHS 3 4 => rw [←comp_tensor_id, iso.hom_inv_id_app]dsimp rw [tensor_id]
          simp only [category.id_comp, category.assoc]
          sliceLHS 2 3 => rw [associator_naturality]
          simp only [category.assoc]
          congr 2
          sliceLHS 1 1 => rw [←tensor_id_comp_id_tensor]
          sliceLHS 2 3 => rw [←id_tensor_comp, tensor_id_comp_id_tensor]
          sliceLHS 1 2 => rw [tensor_id_comp_id_tensor]
          convRHS => congr skip rw [←id_tensor_comp_tensor_id, id_tensor_comp]
          simp only [category.assoc]
          sliceRHS 1 2 => rw [←id_tensor_comp, iso.hom_inv_id_app]dsimp rw [tensor_id]
          simp only [category.id_comp, category.assoc]
          convRHS => rw [id_tensor_comp]
          sliceRHS 2 3 => rw [id_tensor_comp_tensor_id, ←tensor_id_comp_id_tensor]
          sliceRHS 1 2 => rw [id_tensor_comp_tensor_id] }

-- error in CategoryTheory.Monoidal.Transport: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler category
/-- A type synonym for `D`, which will carry the transported monoidal structure. -/
@[derive #[expr category], nolint #[ident unused_arguments]]
def transported (e : «expr ≌ »(C, D)) :=
D

instance  (e : C ≌ D) : monoidal_category (transported e) :=
  transport e

instance  (e : C ≌ D) : Inhabited (transported e) :=
  ⟨𝟙_ _⟩

/--
We can upgrade `e.functor` to a lax monoidal functor from `C` to `D` with the transported structure.
-/
@[simps]
def lax_to_transported (e : C ≌ D) : lax_monoidal_functor C (transported e) :=
  { e.functor with ε := 𝟙 (e.functor.obj (𝟙_ C)), μ := fun X Y => e.functor.map (e.unit_inv.app X ⊗ e.unit_inv.app Y),
    μ_natural' :=
      fun X Y X' Y' f g =>
        by 
          dsimp 
          simp only [equivalence.inv_fun_map, functor.map_comp, tensor_comp, category.assoc]
          simp only [←e.functor.map_comp]
          congr 1
          rw [←tensor_comp, iso.hom_inv_id_app, iso.hom_inv_id_app, ←tensor_comp]
          dsimp 
          rw [comp_id, comp_id],
    associativity' :=
      fun X Y Z =>
        by 
          dsimp 
          simp only [comp_tensor_id, assoc, equivalence.inv_fun_map, functor.map_comp, id_tensor_comp, e.inverse.map_id]
          simp only [←e.functor.map_comp]
          congr 2
          sliceLHS 3 3 => rw [←tensor_id_comp_id_tensor]
          sliceLHS 2 3 => rw [←comp_tensor_id, iso.hom_inv_id_app]dsimp rw [tensor_id]
          simp only [id_comp]
          sliceRHS 2 3 => rw [←id_tensor_comp, iso.hom_inv_id_app]dsimp rw [tensor_id]
          simp only [id_comp]
          convRHS => rw [←id_tensor_comp_tensor_id _ (e.unit_inv.app X)]
          dsimp only [functor.comp_obj]
          sliceRHS 3 4 => rw [←id_tensor_comp, iso.hom_inv_id_app]dsimp rw [tensor_id]
          simp only [id_comp]
          simp [associator_naturality],
    left_unitality' :=
      fun X =>
        by 
          dsimp 
          simp only [tensor_id, assoc, id_comp, functor.map_comp, e.inverse.map_id]
          rw [equivalence.counit_app_functor]
          simp only [←e.functor.map_comp]
          congr 1
          rw [←left_unitor_naturality]
          simp ,
    right_unitality' :=
      fun X =>
        by 
          dsimp 
          simp only [tensor_id, assoc, id_comp, functor.map_comp, e.inverse.map_id]
          rw [equivalence.counit_app_functor]
          simp only [←e.functor.map_comp]
          congr 1
          rw [←right_unitor_naturality]
          simp  }

/--
We can upgrade `e.functor` to a monoidal functor from `C` to `D` with the transported structure.
-/
@[simps]
def to_transported (e : C ≌ D) : monoidal_functor C (transported e) :=
  { lax_to_transported e with
    ε_is_iso :=
      by 
        dsimp 
        infer_instance,
    μ_is_iso :=
      fun X Y =>
        by 
          dsimp 
          infer_instance }

/--
We can upgrade `e.inverse` to a lax monoidal functor from `D` with the transported structure to `C`.
-/
@[simps]
def lax_from_transported (e : C ≌ D) : lax_monoidal_functor (transported e) C :=
  { e.inverse with ε := e.unit.app (𝟙_ C), μ := fun X Y => e.unit.app (e.inverse.obj X ⊗ e.inverse.obj Y),
    μ_natural' :=
      fun X Y X' Y' f g =>
        by 
          dsimp 
          simp only [iso.hom_inv_id_app_assoc, equivalence.inv_fun_map],
    associativity' :=
      fun X Y Z =>
        by 
          dsimp 
          simp only [iso.hom_inv_id_app_assoc, assoc, equivalence.inv_fun_map, functor.map_comp]
          sliceLHS 1 2 => rw [←comp_tensor_id, iso.hom_inv_id_app]dsimp rw [tensor_id]
          simp ,
    left_unitality' :=
      fun X =>
        by 
          dsimp 
          simp only [iso.hom_inv_id_app_assoc, equivalence.unit_inverse_comp, assoc, equivalence.inv_fun_map, comp_id,
            functor.map_comp]
          sliceRHS 1 2 => rw [←comp_tensor_id, iso.hom_inv_id_app]dsimp rw [tensor_id]
          simp ,
    right_unitality' :=
      fun X =>
        by 
          dsimp 
          simp only [iso.hom_inv_id_app_assoc, equivalence.unit_inverse_comp, assoc, equivalence.inv_fun_map, comp_id,
            functor.map_comp]
          sliceRHS 1 2 => rw [←id_tensor_comp, iso.hom_inv_id_app]dsimp rw [tensor_id]
          simp  }

/--
We can upgrade `e.inverse` to a monoidal functor from `D` with the transported structure to `C`.
-/
@[simps]
def from_transported (e : C ≌ D) : monoidal_functor (transported e) C :=
  { lax_from_transported e with
    ε_is_iso :=
      by 
        dsimp 
        infer_instance,
    μ_is_iso :=
      fun X Y =>
        by 
          dsimp 
          infer_instance }

/-- The unit isomorphism upgrades to a monoidal isomorphism. -/
@[simps]
def transported_monoidal_unit_iso (e : C ≌ D) :
  lax_monoidal_functor.id C ≅ lax_to_transported e ⊗⋙ lax_from_transported e :=
  monoidal_nat_iso.of_components (fun X => e.unit_iso.app X) (fun X Y f => e.unit.naturality f)
    (by 
      dsimp 
      simp )
    fun X Y =>
      by 
        dsimp 
        simp only [iso.hom_inv_id_app_assoc, id_comp, equivalence.inv_fun_map]
        sliceRHS 1 2 => rw [←tensor_comp, iso.hom_inv_id_app, iso.hom_inv_id_app]dsimp rw [tensor_id]
        simp 

/-- The counit isomorphism upgrades to a monoidal isomorphism. -/
@[simps]
def transported_monoidal_counit_iso (e : C ≌ D) :
  lax_from_transported e ⊗⋙ lax_to_transported e ≅ lax_monoidal_functor.id (transported e) :=
  monoidal_nat_iso.of_components (fun X => e.counit_iso.app X) (fun X Y f => e.counit.naturality f)
    (by 
      dsimp 
      simp )
    fun X Y =>
      by 
        dsimp 
        simp only [iso.hom_inv_id_app_assoc, id_comp, equivalence.inv_fun_map]
        simp only [equivalence.counit_app_functor, ←e.functor.map_id, ←e.functor.map_comp]
        congr 1
        simp [equivalence.unit_inv_app_inverse]
        dsimp 
        simp 

end CategoryTheory.Monoidal

