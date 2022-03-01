/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathbin.CategoryTheory.Limits.Shapes.Zero

/-!
# Preservation of zero objects and zero morphisms

We define the class `preserves_zero_morphisms` and show basic properties.

## Main results

We provide the following results:
* Left adjoints and right adjoints preserve zero morphisms;
* full functors preserve zero morphisms;
* if both categories involved have a zero object, then a functor preserves zero morphisms if and
  only if it preserves the zero object;
* functors which preserve initial or terminal objects preserve zero morphisms.

-/


universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

section ZeroMorphisms

variable [HasZeroMorphisms C] [HasZeroMorphisms D]

/-- A functor preserves zero morphisms if it sends zero morphisms to zero morphisms. -/
class PreservesZeroMorphisms (F : C ⥤ D) : Prop where
  map_zero' : ∀ X Y : C, F.map (0 : X ⟶ Y) = 0 := by
    run_tac
      obviously

@[simp]
protected theorem map_zero (F : C ⥤ D) [PreservesZeroMorphisms F] (X Y : C) : F.map (0 : X ⟶ Y) = 0 :=
  PreservesZeroMorphisms.map_zero' _ _

instance (priority := 100) preserves_zero_morphisms_of_is_left_adjoint (F : C ⥤ D) [IsLeftAdjoint F] :
    PreservesZeroMorphisms F where
  map_zero' := fun X Y => by
    let adj := Adjunction.ofLeftAdjoint F
    calc F.map (0 : X ⟶ Y) = F.map 0 ≫ F.map (adj.unit.app Y) ≫ adj.counit.app (F.obj Y) :=
        _ _ = F.map 0 ≫ F.map ((right_adjoint F).map (0 : F.obj X ⟶ _)) ≫ adj.counit.app (F.obj Y) := _ _ = 0 := _
    · rw [adjunction.left_triangle_components]
      exact (category.comp_id _).symm
      
    · simp only [← category.assoc, ← F.map_comp, zero_comp]
      
    · simp only [adjunction.counit_naturality, comp_zero]
      

instance (priority := 100) preserves_zero_morphisms_of_is_right_adjoint (G : C ⥤ D) [IsRightAdjoint G] :
    PreservesZeroMorphisms G where
  map_zero' := fun X Y => by
    let adj := Adjunction.ofRightAdjoint G
    calc G.map (0 : X ⟶ Y) = adj.unit.app (G.obj X) ≫ G.map (adj.counit.app X) ≫ G.map 0 :=
        _ _ = adj.unit.app (G.obj X) ≫ G.map ((left_adjoint G).map (0 : _ ⟶ G.obj X)) ≫ G.map 0 := _ _ = 0 := _
    · rw [adjunction.right_triangle_components_assoc]
      
    · simp only [← G.map_comp, comp_zero]
      
    · simp only [adjunction.unit_naturality_assoc, zero_comp]
      

instance (priority := 100) preserves_zero_morphisms_of_full (F : C ⥤ D) [Full F] : PreservesZeroMorphisms F where
  map_zero' := fun X Y =>
    calc
      F.map (0 : X ⟶ Y) = F.map (0 ≫ F.Preimage (0 : F.obj Y ⟶ F.obj Y)) := by
        rw [zero_comp]
      _ = 0 := by
        rw [F.map_comp, F.image_preimage, comp_zero]
      

end ZeroMorphisms

section ZeroObject

variable [HasZeroObject C] [HasZeroObject D]

open_locale ZeroObject

variable [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D)

/-- A functor that preserves zero morphisms also preserves the zero object. -/
@[simps]
def mapZeroObject [PreservesZeroMorphisms F] : F.obj 0 ≅ 0 where
  Hom := 0
  inv := 0
  hom_inv_id' := by
    rw [← F.map_id, id_zero, F.map_zero, zero_comp]
  inv_hom_id' := by
    rw [id_zero, comp_zero]

variable {F}

theorem preserves_zero_morphisms_of_map_zero_object (i : F.obj 0 ≅ 0) : PreservesZeroMorphisms F :=
  { map_zero' := fun X Y =>
      calc
        F.map (0 : X ⟶ Y) = F.map (0 : X ⟶ 0) ≫ F.map 0 := by
          rw [← functor.map_comp, comp_zero]
        _ = F.map 0 ≫ (i.Hom ≫ i.inv) ≫ F.map 0 := by
          rw [iso.hom_inv_id, category.id_comp]
        _ = 0 := by
          simp only [zero_of_to_zero i.hom, zero_comp, comp_zero]
         }

instance (priority := 100) preserves_zero_morphisms_of_preserves_initial_object
    [PreservesColimit (Functor.empty.{v₁} C) F] : PreservesZeroMorphisms F :=
  preserves_zero_morphisms_of_map_zero_object <|
    (F.mapIso HasZeroObject.zeroIsoInitial).trans <| (PreservesInitial.iso F).trans HasZeroObject.zeroIsoInitial.symm

instance (priority := 100) preserves_zero_morphisms_of_preserves_terminal_object
    [PreservesLimit (Functor.empty.{v₁} C) F] : PreservesZeroMorphisms F :=
  preserves_zero_morphisms_of_map_zero_object <|
    (F.mapIso HasZeroObject.zeroIsoTerminal).trans <| (PreservesTerminal.iso F).trans HasZeroObject.zeroIsoTerminal.symm

end ZeroObject

end CategoryTheory.Functor

