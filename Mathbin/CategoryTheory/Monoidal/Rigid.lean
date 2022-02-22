/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathbin.CategoryTheory.Monoidal.Category

/-!
# Rigid (autonomous) monoidal categories

This file defines rigid (autonomous) monoidal categories and the necessary theory about
exact pairings and duals.

## Main definitions

* `exact_pairing` of two objects of a monoidal category
* Type classes `has_left_dual` and `has_right_dual` that capture that a pairing exists
* The `right_adjoint_mate f` as a morphism `fᘁ : Yᘁ ⟶ Xᘁ` for a morphism `f : X ⟶ Y`
* The classes of `right_rigid_category`, `left_rigid_category` and `rigid_category`

## Main statements

* `comp_right_adjoint_mate`: The adjoint mates of the composition is the composition of
  adjoint mates.

## Notations

* `η_` and `ε_` denote the coevaluation and evaluation morphism of an exact pairing.
* `Xᘁ` and `ᘁX` denote the right and left dual of an object, as well as the adjoint
  mate of a morphism.

## Future work

* Show that `X ⊗ Y` and `Yᘁ ⊗ Xᘁ` form an exact pairing.
* Show that the left adjoint mate of the right adjoint mate of a morphism is the morphism itself.
* Simplify constructions in the case where a symmetry or braiding is present.

## References

* <https://ncatlab.org/nlab/show/rigid+monoidal+category>

## Tags

rigid category, monoidal category

-/


open CategoryTheory

universe v v₁ v₂ v₃ u u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

/-- An exact pairing is a pair of objects `X Y : C` which admit
  a coevaluation and evaluation morphism which fulfill two triangle equalities. -/
class ExactPairing (X Y : C) where
  coevaluation {} : 𝟙_ C ⟶ X ⊗ Y
  evaluation {} : Y ⊗ X ⟶ 𝟙_ C
  coevaluation_evaluation' {} :
    (𝟙 Y ⊗ coevaluation) ≫ (α_ _ _ _).inv ≫ (evaluation ⊗ 𝟙 Y) = (ρ_ Y).Hom ≫ (λ_ Y).inv := by
    run_tac
      obviously
  evaluation_coevaluation' {} :
    (coevaluation ⊗ 𝟙 X) ≫ (α_ _ _ _).Hom ≫ (𝟙 X ⊗ evaluation) = (λ_ X).Hom ≫ (ρ_ X).inv := by
    run_tac
      obviously

open ExactPairing

-- mathport name: «exprη_»
notation "η_" => ExactPairing.coevaluation

-- mathport name: «exprε_»
notation "ε_" => ExactPairing.evaluation

restate_axiom coevaluation_evaluation'

attribute [reassoc, simp] exact_pairing.coevaluation_evaluation

restate_axiom evaluation_coevaluation'

attribute [reassoc, simp] exact_pairing.evaluation_coevaluation

instance exactPairingUnit : ExactPairing (𝟙_ C) (𝟙_ C) where
  coevaluation := (ρ_ _).inv
  evaluation := (ρ_ _).Hom
  coevaluation_evaluation' := by
    rw [monoidal_category.triangle_assoc_comp_right, monoidal_category.unitors_inv_equal,
      monoidal_category.unitors_equal]
    simp
  evaluation_coevaluation' := by
    rw [monoidal_category.triangle_assoc_comp_right_inv_assoc, monoidal_category.unitors_inv_equal,
      monoidal_category.unitors_equal]
    simp

/-- A class of objects which have a right dual. -/
class HasRightDual (X : C) where
  rightDual : C
  [exact : ExactPairing X right_dual]

/-- A class of objects with have a left dual. -/
class HasLeftDual (Y : C) where
  leftDual : C
  [exact : ExactPairing left_dual Y]

attribute [instance] has_right_dual.exact

attribute [instance] has_left_dual.exact

open ExactPairing HasRightDual HasLeftDual MonoidalCategory

-- mathport name: «exprᘁ »
prefix:1024 "ᘁ" => leftDual

-- mathport name: «expr ᘁ»
postfix:1024 "ᘁ" => rightDual

instance hasRightDualUnit : HasRightDual (𝟙_ C) where
  rightDual := 𝟙_ C

instance hasLeftDualUnit : HasLeftDual (𝟙_ C) where
  leftDual := 𝟙_ C

instance hasRightDualLeftDual {X : C} [HasLeftDual X] : HasRightDual ᘁX where
  rightDual := X

instance hasLeftDualRightDual {X : C} [HasRightDual X] : HasLeftDual Xᘁ where
  leftDual := X

@[simp]
theorem left_dual_right_dual {X : C} [HasRightDual X] : ᘁXᘁ = X :=
  rfl

@[simp]
theorem right_dual_left_dual {X : C} [HasLeftDual X] : (ᘁX)ᘁ = X :=
  rfl

/-- The right adjoint mate `fᘁ : Xᘁ ⟶ Yᘁ` of a morphism `f : X ⟶ Y`. -/
def rightAdjointMate {X Y : C} [HasRightDual X] [HasRightDual Y] (f : X ⟶ Y) : Yᘁ ⟶ Xᘁ :=
  (ρ_ _).inv ≫ (𝟙 _ ⊗ η_ _ _) ≫ (𝟙 _ ⊗ f ⊗ 𝟙 _) ≫ (α_ _ _ _).inv ≫ (ε_ _ _ ⊗ 𝟙 _) ≫ (λ_ _).Hom

/-- The left adjoint mate `ᘁf : ᘁY ⟶ ᘁX` of a morphism `f : X ⟶ Y`. -/
def leftAdjointMate {X Y : C} [HasLeftDual X] [HasLeftDual Y] (f : X ⟶ Y) : ᘁY ⟶ ᘁX :=
  (λ_ _).inv ≫ (η_ (ᘁX) X ⊗ 𝟙 _) ≫ ((𝟙 _ ⊗ f) ⊗ 𝟙 _) ≫ (α_ _ _ _).Hom ≫ (𝟙 _ ⊗ ε_ _ _) ≫ (ρ_ _).Hom

-- mathport name: «expr ᘁ»
notation f "ᘁ" => rightAdjointMate f

-- mathport name: «exprᘁ »
notation "ᘁ" f => leftAdjointMate f

@[simp]
theorem right_adjoint_mate_id {X : C} [HasRightDual X] : 𝟙 Xᘁ = 𝟙 (Xᘁ) := by
  simp only [right_adjoint_mate, monoidal_category.tensor_id, category.id_comp, coevaluation_evaluation_assoc,
    category.comp_id, iso.inv_hom_id]

@[simp]
theorem left_adjoint_mate_id {X : C} [HasLeftDual X] : (ᘁ𝟙 X) = 𝟙 (ᘁX) := by
  simp only [left_adjoint_mate, monoidal_category.tensor_id, category.id_comp, evaluation_coevaluation_assoc,
    category.comp_id, iso.inv_hom_id]

theorem right_adjoint_mate_comp {X Y Z : C} [HasRightDual X] [HasRightDual Y] {f : X ⟶ Y} {g : Xᘁ ⟶ Z} :
    fᘁ ≫ g = (ρ_ (Yᘁ)).inv ≫ (𝟙 _ ⊗ η_ X (Xᘁ)) ≫ (𝟙 _ ⊗ f ⊗ g) ≫ (α_ (Yᘁ) Y Z).inv ≫ (ε_ Y (Yᘁ) ⊗ 𝟙 _) ≫ (λ_ Z).Hom :=
  by
  dunfold right_adjoint_mate
  rw [category.assoc, category.assoc, associator_inv_naturality_assoc, associator_inv_naturality_assoc, ←
    tensor_id_comp_id_tensor g, category.assoc, category.assoc, category.assoc, category.assoc,
    id_tensor_comp_tensor_id_assoc, ← left_unitor_naturality, tensor_id_comp_id_tensor_assoc]

theorem left_adjoint_mate_comp {X Y Z : C} [HasLeftDual X] [HasLeftDual Y] {f : X ⟶ Y} {g : (ᘁX) ⟶ Z} :
    (ᘁf) ≫ g = (λ_ _).inv ≫ (η_ (ᘁX) X ⊗ 𝟙 _) ≫ ((g ⊗ f) ⊗ 𝟙 _) ≫ (α_ _ _ _).Hom ≫ (𝟙 _ ⊗ ε_ _ _) ≫ (ρ_ _).Hom := by
  dunfold left_adjoint_mate
  rw [category.assoc, category.assoc, associator_naturality_assoc, associator_naturality_assoc, ←
    id_tensor_comp_tensor_id _ g, category.assoc, category.assoc, category.assoc, category.assoc,
    tensor_id_comp_id_tensor_assoc, ← right_unitor_naturality, id_tensor_comp_tensor_id_assoc]

/-- The composition of right adjoint mates is the adjoint mate of the composition. -/
@[reassoc]
theorem comp_right_adjoint_mate {X Y Z : C} [HasRightDual X] [HasRightDual Y] [HasRightDual Z] {f : X ⟶ Y} {g : Y ⟶ Z} :
    (f ≫ g)ᘁ = gᘁ ≫ fᘁ := by
  rw [right_adjoint_mate_comp]
  simp only [right_adjoint_mate, comp_tensor_id, iso.cancel_iso_inv_left, id_tensor_comp, category.assoc]
  symm
  iterate 5 
    trans
    rw [← category.id_comp g, tensor_comp]
  rw [← category.assoc]
  symm
  iterate 2 
    trans
    rw [← category.assoc]
  apply eq_whisker
  repeat'
    rw [← id_tensor_comp]
  congr 1
  rw [← id_tensor_comp_tensor_id (λ_ (Xᘁ)).Hom g, id_tensor_right_unitor_inv, category.assoc, category.assoc,
    right_unitor_inv_naturality_assoc, ← associator_naturality_assoc, tensor_id, tensor_id_comp_id_tensor_assoc, ←
    associator_naturality_assoc]
  slice_rhs 2 3 => rw [← tensor_comp, tensor_id, category.comp_id, ← category.id_comp (η_ Y (Yᘁ)), tensor_comp]
  rw [← id_tensor_comp_tensor_id _ (η_ Y (Yᘁ)), ← tensor_id]
  repeat'
    rw [category.assoc]
  rw [pentagon_hom_inv_assoc, ← associator_naturality_assoc, associator_inv_naturality_assoc]
  slice_rhs 5 7 => rw [← comp_tensor_id, ← comp_tensor_id, evaluation_coevaluation, comp_tensor_id]
  rw [associator_inv_naturality_assoc]
  slice_rhs 4 5 => rw [← tensor_comp, left_unitor_naturality, tensor_comp]
  repeat'
    rw [category.assoc]
  rw [triangle_assoc_comp_right_inv_assoc, ← left_unitor_tensor_assoc, left_unitor_naturality_assoc, unitors_equal, ←
    category.assoc, ← category.assoc]
  simp

/-- The composition of left adjoint mates is the adjoint mate of the composition. -/
@[reassoc]
theorem comp_left_adjoint_mate {X Y Z : C} [HasLeftDual X] [HasLeftDual Y] [HasLeftDual Z] {f : X ⟶ Y} {g : Y ⟶ Z} :
    (ᘁf ≫ g) = (ᘁg) ≫ ᘁf := by
  rw [left_adjoint_mate_comp]
  simp only [left_adjoint_mate, id_tensor_comp, iso.cancel_iso_inv_left, comp_tensor_id, category.assoc]
  symm
  iterate 5 
    trans
    rw [← category.id_comp g, tensor_comp]
  rw [← category.assoc]
  symm
  iterate 2 
    trans
    rw [← category.assoc]
  apply eq_whisker
  repeat'
    rw [← comp_tensor_id]
  congr 1
  rw [← tensor_id_comp_id_tensor g (ρ_ (ᘁX)).Hom, left_unitor_inv_tensor_id, category.assoc, category.assoc,
    left_unitor_inv_naturality_assoc, ← associator_inv_naturality_assoc, tensor_id, id_tensor_comp_tensor_id_assoc, ←
    associator_inv_naturality_assoc]
  slice_rhs 2 3 => rw [← tensor_comp, tensor_id, category.comp_id, ← category.id_comp (η_ (ᘁY) Y), tensor_comp]
  rw [← tensor_id_comp_id_tensor (η_ (ᘁY) Y), ← tensor_id]
  repeat'
    rw [category.assoc]
  rw [pentagon_inv_hom_assoc, ← associator_inv_naturality_assoc, associator_naturality_assoc]
  slice_rhs 5 7 => rw [← id_tensor_comp, ← id_tensor_comp, coevaluation_evaluation, id_tensor_comp]
  rw [associator_naturality_assoc]
  slice_rhs 4 5 => rw [← tensor_comp, right_unitor_naturality, tensor_comp]
  repeat'
    rw [category.assoc]
  rw [triangle_assoc_comp_left_inv_assoc, ← right_unitor_tensor_assoc, right_unitor_naturality_assoc, ← unitors_equal, ←
    category.assoc, ← category.assoc]
  simp

/-- Right duals are isomorphic. -/
def rightDualIso {X Y₁ Y₂ : C} (_ : ExactPairing X Y₁) (_ : ExactPairing X Y₂) : Y₁ ≅ Y₂ where
  Hom := @rightAdjointMate C _ _ X X ⟨Y₂⟩ ⟨Y₁⟩ (𝟙 X)
  inv := @rightAdjointMate C _ _ X X ⟨Y₁⟩ ⟨Y₂⟩ (𝟙 X)
  hom_inv_id' := by
    rw [← comp_right_adjoint_mate, category.comp_id, right_adjoint_mate_id]
  inv_hom_id' := by
    rw [← comp_right_adjoint_mate, category.comp_id, right_adjoint_mate_id]

/-- Left duals are isomorphic. -/
def leftDualIso {X₁ X₂ Y : C} (p₁ : ExactPairing X₁ Y) (p₂ : ExactPairing X₂ Y) : X₁ ≅ X₂ where
  Hom := @leftAdjointMate C _ _ Y Y ⟨X₂⟩ ⟨X₁⟩ (𝟙 Y)
  inv := @leftAdjointMate C _ _ Y Y ⟨X₁⟩ ⟨X₂⟩ (𝟙 Y)
  hom_inv_id' := by
    rw [← comp_left_adjoint_mate, category.comp_id, left_adjoint_mate_id]
  inv_hom_id' := by
    rw [← comp_left_adjoint_mate, category.comp_id, left_adjoint_mate_id]

@[simp]
theorem right_dual_iso_id {X Y : C} (p : ExactPairing X Y) : rightDualIso p p = Iso.refl Y := by
  ext
  simp only [right_dual_iso, iso.refl_hom, right_adjoint_mate_id]

@[simp]
theorem left_dual_iso_id {X Y : C} (p : ExactPairing X Y) : leftDualIso p p = Iso.refl X := by
  ext
  simp only [left_dual_iso, iso.refl_hom, left_adjoint_mate_id]

/-- A right rigid monoidal category is one in which every object has a right dual. -/
class RightRigidCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] where
  [rightDual : ∀ X : C, HasRightDual X]

/-- A left rigid monoidal category is one in which every object has a right dual. -/
class LeftRigidCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] where
  [leftDual : ∀ X : C, HasLeftDual X]

attribute [instance] right_rigid_category.right_dual

attribute [instance] left_rigid_category.left_dual

/-- A rigid monoidal category is a monoidal category which is left rigid and right rigid. -/
class RigidCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] extends RightRigidCategory C,
  LeftRigidCategory C

end CategoryTheory

