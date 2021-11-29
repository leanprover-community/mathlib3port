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

noncomputable theory

namespace CategoryTheory

variable{C : Type u₁}[category.{v₁} C][monoidal_category C]

/-- An exact pairing is a pair of objects `X Y : C` which admit
  a coevaluation and evaluation morphism which fulfill two triangle equalities. -/
class exact_pairing(X Y : C) where 
  coevaluation{} : 𝟙_ C ⟶ X ⊗ Y 
  evaluation{} : Y ⊗ X ⟶ 𝟙_ C 
  coevaluation_evaluation'{} : (𝟙 Y ⊗ coevaluation) ≫ (α_ _ _ _).inv ≫ (evaluation ⊗ 𝟙 Y) = (ρ_ Y).Hom ≫ (λ_ Y).inv :=
   by 
  runTac 
    obviously 
  evaluation_coevaluation'{} : (coevaluation ⊗ 𝟙 X) ≫ (α_ _ _ _).Hom ≫ (𝟙 X ⊗ evaluation) = (λ_ X).Hom ≫ (ρ_ X).inv :=
   by 
  runTac 
    obviously

open ExactPairing

notation "η_" => exact_pairing.coevaluation

notation "ε_" => exact_pairing.evaluation

restate_axiom coevaluation_evaluation'

attribute [reassoc, simp] exact_pairing.coevaluation_evaluation

restate_axiom evaluation_coevaluation'

attribute [reassoc, simp] exact_pairing.evaluation_coevaluation

instance exact_pairing_unit : exact_pairing (𝟙_ C) (𝟙_ C) :=
  { coevaluation := (ρ_ _).inv, evaluation := (ρ_ _).Hom,
    coevaluation_evaluation' :=
      by 
        rw [monoidal_category.triangle_assoc_comp_right, monoidal_category.unitors_inv_equal,
          monoidal_category.unitors_equal]
        simp ,
    evaluation_coevaluation' :=
      by 
        rw [monoidal_category.triangle_assoc_comp_right_inv_assoc, monoidal_category.unitors_inv_equal,
          monoidal_category.unitors_equal]
        simp  }

/-- A class of objects which have a right dual. -/
class has_right_dual(X : C) where 
  rightDual : C
  [exact : exact_pairing X right_dual]

/-- A class of objects with have a left dual. -/
class has_left_dual(Y : C) where 
  leftDual : C
  [exact : exact_pairing left_dual Y]

attribute [instance] has_right_dual.exact

attribute [instance] has_left_dual.exact

open ExactPairing HasRightDual HasLeftDual MonoidalCategory

prefix:1025 "ᘁ" => left_dual

postfix:1025 "ᘁ" => right_dual

instance has_right_dual_unit : has_right_dual (𝟙_ C) :=
  { rightDual := 𝟙_ C }

instance has_left_dual_unit : has_left_dual (𝟙_ C) :=
  { leftDual := 𝟙_ C }

instance has_right_dual_left_dual {X : C} [has_left_dual X] : has_right_dual ᘁ(X) :=
  { rightDual := X }

instance has_left_dual_right_dual {X : C} [has_right_dual X] : has_left_dual (X)ᘁ :=
  { leftDual := X }

@[simp]
theorem left_dual_right_dual {X : C} [has_right_dual X] : ᘁ(X)ᘁ = X :=
  rfl

@[simp]
theorem right_dual_left_dual {X : C} [has_left_dual X] : (ᘁ(X))ᘁ = X :=
  rfl

/-- The right adjoint mate `fᘁ : Xᘁ ⟶ Yᘁ` of a morphism `f : X ⟶ Y`. -/
def right_adjoint_mate {X Y : C} [has_right_dual X] [has_right_dual Y] (f : X ⟶ Y) : (Y)ᘁ ⟶ (X)ᘁ :=
  (ρ_ _).inv ≫ (𝟙 _ ⊗ η_ _ _) ≫ (𝟙 _ ⊗ f ⊗ 𝟙 _) ≫ (α_ _ _ _).inv ≫ (ε_ _ _ ⊗ 𝟙 _) ≫ (λ_ _).Hom

/-- The left adjoint mate `ᘁf : ᘁY ⟶ ᘁX` of a morphism `f : X ⟶ Y`. -/
def left_adjoint_mate {X Y : C} [has_left_dual X] [has_left_dual Y] (f : X ⟶ Y) : ᘁ(Y) ⟶ ᘁ(X) :=
  (λ_ _).inv ≫ (η_ ᘁ(X) X ⊗ 𝟙 _) ≫ ((𝟙 _ ⊗ f) ⊗ 𝟙 _) ≫ (α_ _ _ _).Hom ≫ (𝟙 _ ⊗ ε_ _ _) ≫ (ρ_ _).Hom

notation f "ᘁ" => right_adjoint_mate f

notation "ᘁ" f => left_adjoint_mate f

@[simp]
theorem right_adjoint_mate_id {X : C} [has_right_dual X] : 𝟙 Xᘁ = 𝟙 (Xᘁ) :=
  by 
    simp only [right_adjoint_mate, monoidal_category.tensor_id, category.id_comp, coevaluation_evaluation_assoc,
      category.comp_id, iso.inv_hom_id]

@[simp]
theorem left_adjoint_mate_id {X : C} [has_left_dual X] : (ᘁ𝟙 X) = 𝟙 (ᘁX) :=
  by 
    simp only [left_adjoint_mate, monoidal_category.tensor_id, category.id_comp, evaluation_coevaluation_assoc,
      category.comp_id, iso.inv_hom_id]

theorem right_adjoint_mate_comp {X Y Z : C} [has_right_dual X] [has_right_dual Y] {f : X ⟶ Y} {g : Xᘁ ⟶ Z} :
  fᘁ ≫ g = (ρ_ (Yᘁ)).inv ≫ (𝟙 _ ⊗ η_ X (Xᘁ)) ≫ (𝟙 _ ⊗ f ⊗ g) ≫ (α_ (Yᘁ) Y Z).inv ≫ (ε_ Y (Yᘁ) ⊗ 𝟙 _) ≫ (λ_ Z).Hom :=
  by 
    dunfold right_adjoint_mate 
    rw [category.assoc, category.assoc, associator_inv_naturality_assoc, associator_inv_naturality_assoc,
      ←tensor_id_comp_id_tensor g, category.assoc, category.assoc, category.assoc, category.assoc,
      id_tensor_comp_tensor_id_assoc, ←left_unitor_naturality, tensor_id_comp_id_tensor_assoc]

theorem left_adjoint_mate_comp {X Y Z : C} [has_left_dual X] [has_left_dual Y] {f : X ⟶ Y} {g : (ᘁX) ⟶ Z} :
  (ᘁf) ≫ g = (λ_ _).inv ≫ (η_ (ᘁX) X ⊗ 𝟙 _) ≫ ((g ⊗ f) ⊗ 𝟙 _) ≫ (α_ _ _ _).Hom ≫ (𝟙 _ ⊗ ε_ _ _) ≫ (ρ_ _).Hom :=
  by 
    dunfold left_adjoint_mate 
    rw [category.assoc, category.assoc, associator_naturality_assoc, associator_naturality_assoc,
      ←id_tensor_comp_tensor_id _ g, category.assoc, category.assoc, category.assoc, category.assoc,
      tensor_id_comp_id_tensor_assoc, ←right_unitor_naturality, id_tensor_comp_tensor_id_assoc]

/-- The composition of right adjoint mates is the adjoint mate of the composition. -/
@[reassoc]
theorem comp_right_adjoint_mate {X Y Z : C} [has_right_dual X] [has_right_dual Y] [has_right_dual Z] {f : X ⟶ Y}
  {g : Y ⟶ Z} : (f ≫ g)ᘁ = gᘁ ≫ fᘁ :=
  by 
    rw [right_adjoint_mate_comp]
    simp only [right_adjoint_mate, comp_tensor_id, iso.cancel_iso_inv_left, id_tensor_comp, category.assoc]
    symm 
    iterate 5
      trans 
      rw [←category.id_comp g, tensor_comp]
    rw [←category.assoc]
    symm 
    iterate 2
      trans 
      rw [←category.assoc]
    apply eq_whisker 
    repeat' 
      rw [←id_tensor_comp]
    congr 1
    rw [←id_tensor_comp_tensor_id (λ_ (Xᘁ)).Hom g, id_tensor_right_unitor_inv, category.assoc, category.assoc,
      right_unitor_inv_naturality_assoc, ←associator_naturality_assoc, tensor_id, tensor_id_comp_id_tensor_assoc,
      ←associator_naturality_assoc]
    sliceRHS 2 3 => rw [←tensor_comp, tensor_id, category.comp_id, ←category.id_comp (η_ Y (Yᘁ)), tensor_comp]
    rw [←id_tensor_comp_tensor_id _ (η_ Y (Yᘁ)), ←tensor_id]
    repeat' 
      rw [category.assoc]
    rw [pentagon_hom_inv_assoc, ←associator_naturality_assoc, associator_inv_naturality_assoc]
    sliceRHS 5 7 => rw [←comp_tensor_id, ←comp_tensor_id, evaluation_coevaluation, comp_tensor_id]
    rw [associator_inv_naturality_assoc]
    sliceRHS 4 5 => rw [←tensor_comp, left_unitor_naturality, tensor_comp]
    repeat' 
      rw [category.assoc]
    rw [triangle_assoc_comp_right_inv_assoc, ←left_unitor_tensor_assoc, left_unitor_naturality_assoc, unitors_equal,
      ←category.assoc, ←category.assoc]
    simp 

/-- The composition of left adjoint mates is the adjoint mate of the composition. -/
@[reassoc]
theorem comp_left_adjoint_mate {X Y Z : C} [has_left_dual X] [has_left_dual Y] [has_left_dual Z] {f : X ⟶ Y}
  {g : Y ⟶ Z} : (ᘁf ≫ g) = (ᘁg) ≫ ᘁf :=
  by 
    rw [left_adjoint_mate_comp]
    simp only [left_adjoint_mate, id_tensor_comp, iso.cancel_iso_inv_left, comp_tensor_id, category.assoc]
    symm 
    iterate 5
      trans 
      rw [←category.id_comp g, tensor_comp]
    rw [←category.assoc]
    symm 
    iterate 2
      trans 
      rw [←category.assoc]
    apply eq_whisker 
    repeat' 
      rw [←comp_tensor_id]
    congr 1
    rw [←tensor_id_comp_id_tensor g (ρ_ (ᘁX)).Hom, left_unitor_inv_tensor_id, category.assoc, category.assoc,
      left_unitor_inv_naturality_assoc, ←associator_inv_naturality_assoc, tensor_id, id_tensor_comp_tensor_id_assoc,
      ←associator_inv_naturality_assoc]
    sliceRHS 2 3 => rw [←tensor_comp, tensor_id, category.comp_id, ←category.id_comp (η_ (ᘁY) Y), tensor_comp]
    rw [←tensor_id_comp_id_tensor (η_ (ᘁY) Y), ←tensor_id]
    repeat' 
      rw [category.assoc]
    rw [pentagon_inv_hom_assoc, ←associator_inv_naturality_assoc, associator_naturality_assoc]
    sliceRHS 5 7 => rw [←id_tensor_comp, ←id_tensor_comp, coevaluation_evaluation, id_tensor_comp]
    rw [associator_naturality_assoc]
    sliceRHS 4 5 => rw [←tensor_comp, right_unitor_naturality, tensor_comp]
    repeat' 
      rw [category.assoc]
    rw [triangle_assoc_comp_left_inv_assoc, ←right_unitor_tensor_assoc, right_unitor_naturality_assoc, ←unitors_equal,
      ←category.assoc, ←category.assoc]
    simp 

/-- Right duals are isomorphic. -/
def right_dual_iso {X Y₁ Y₂ : C} (_ : exact_pairing X Y₁) (_ : exact_pairing X Y₂) : Y₁ ≅ Y₂ :=
  { Hom := @right_adjoint_mate C _ _ X X ⟨Y₂⟩ ⟨Y₁⟩ (𝟙 X), inv := @right_adjoint_mate C _ _ X X ⟨Y₁⟩ ⟨Y₂⟩ (𝟙 X),
    hom_inv_id' :=
      by 
        rw [←comp_right_adjoint_mate, category.comp_id, right_adjoint_mate_id],
    inv_hom_id' :=
      by 
        rw [←comp_right_adjoint_mate, category.comp_id, right_adjoint_mate_id] }

/-- Left duals are isomorphic. -/
def left_dual_iso {X₁ X₂ Y : C} (p₁ : exact_pairing X₁ Y) (p₂ : exact_pairing X₂ Y) : X₁ ≅ X₂ :=
  { Hom := @left_adjoint_mate C _ _ Y Y ⟨X₂⟩ ⟨X₁⟩ (𝟙 Y), inv := @left_adjoint_mate C _ _ Y Y ⟨X₁⟩ ⟨X₂⟩ (𝟙 Y),
    hom_inv_id' :=
      by 
        rw [←comp_left_adjoint_mate, category.comp_id, left_adjoint_mate_id],
    inv_hom_id' :=
      by 
        rw [←comp_left_adjoint_mate, category.comp_id, left_adjoint_mate_id] }

@[simp]
theorem right_dual_iso_id {X Y : C} (p : exact_pairing X Y) : right_dual_iso p p = iso.refl Y :=
  by 
    ext 
    simp only [right_dual_iso, iso.refl_hom, right_adjoint_mate_id]

@[simp]
theorem left_dual_iso_id {X Y : C} (p : exact_pairing X Y) : left_dual_iso p p = iso.refl X :=
  by 
    ext 
    simp only [left_dual_iso, iso.refl_hom, left_adjoint_mate_id]

/-- A right rigid monoidal category is one in which every object has a right dual. -/
class right_rigid_category(C : Type u)[category.{v} C][monoidal_category.{v} C] where 
  [rightDual : ∀ (X : C), has_right_dual X]

/-- A left rigid monoidal category is one in which every object has a right dual. -/
class left_rigid_category(C : Type u)[category.{v} C][monoidal_category.{v} C] where 
  [leftDual : ∀ (X : C), has_left_dual X]

attribute [instance] right_rigid_category.right_dual

attribute [instance] left_rigid_category.left_dual

/-- A rigid monoidal category is a monoidal category which is left rigid and right rigid. -/
class rigid_category(C : Type u)[category.{v} C][monoidal_category.{v} C] extends right_rigid_category C,
  left_rigid_category C

end CategoryTheory

