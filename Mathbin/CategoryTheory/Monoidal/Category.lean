/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Scott Morrison, Bhavik Mehta, Jakob von Raumer
-/
import Mathbin.CategoryTheory.Products.Basic

/-!
# Monoidal categories

A monoidal category is a category equipped with a tensor product, unitors, and an associator.
In the definition, we provide the tensor product as a pair of functions
* `tensor_obj : C → C → C`
* `tensor_hom : (X₁ ⟶ Y₁) → (X₂ ⟶ Y₂) → ((X₁ ⊗ X₂) ⟶ (Y₁ ⊗ Y₂))`
and allow use of the overloaded notation `⊗` for both.
The unitors and associator are provided componentwise.

The tensor product can be expressed as a functor via `tensor : C × C ⥤ C`.
The unitors and associator are gathered together as natural
isomorphisms in `left_unitor_nat_iso`, `right_unitor_nat_iso` and `associator_nat_iso`.

Some consequences of the definition are proved in other files,
e.g. `(λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom` in `category_theory.monoidal.unitors_equal`.

## Implementation
Dealing with unitors and associators is painful, and at this stage we do not have a useful
implementation of coherence for monoidal categories.

In an effort to lessen the pain, we put some effort into choosing the right `simp` lemmas.
Generally, the rule is that the component index of a natural transformation "weighs more"
in considering the complexity of an expression than does a structural isomorphism (associator, etc).

As an example when we prove Proposition 2.2.4 of
<http://www-math.mit.edu/~etingof/egnobookfinal.pdf>
we state it as a `@[simp]` lemma as
```
(λ_ (X ⊗ Y)).hom = (α_ (𝟙_ C) X Y).inv ≫ (λ_ X).hom ⊗ (𝟙 Y)
```

This is far from completely effective, but seems to prove a useful principle.

## References
* Tensor categories, Etingof, Gelaki, Nikshych, Ostrik,
  http://www-math.mit.edu/~etingof/egnobookfinal.pdf
* https://stacks.math.columbia.edu/tag/0FFK.
-/


open CategoryTheory

universe v u

open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.Iso

namespace CategoryTheory

-- ././Mathport/Syntax/Translate/Basic.lean:1272:24: unsupported: (notation) in structure
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«expr ⊗ »
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«expr ⊗ »
-- ././Mathport/Syntax/Translate/Basic.lean:1272:24: unsupported: (notation) in structure
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«expr ⊗' »
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«expr ⊗ »
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«expr ⊗' »
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«expr ⊗' »
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«expr ⊗' »
-- ././Mathport/Syntax/Translate/Basic.lean:1272:24: unsupported: (notation) in structure
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«expr ⊗ »
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«expr ⊗ »
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«expr ⊗ »
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«expr ⊗ »
-- ././Mathport/Syntax/Translate/Basic.lean:1272:24: unsupported: (notation) in structure
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«expr ⊗' »
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«expr ⊗' »
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `exprα_
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `exprα_
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«expr ⊗' »
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«expr ⊗' »
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«expr ⊗ »
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«expr𝟙_»
-- ././Mathport/Syntax/Translate/Basic.lean:1272:24: unsupported: (notation) in structure
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«expr ⊗' »
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«expr𝟙_»
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«exprλ_»
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«exprλ_»
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«expr ⊗ »
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«expr𝟙_»
-- ././Mathport/Syntax/Translate/Basic.lean:1272:24: unsupported: (notation) in structure
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«expr ⊗' »
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«expr𝟙_»
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `exprρ_
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `exprρ_
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«expr ⊗' »
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `exprα_
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `exprα_
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«expr ⊗ »
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«expr ⊗' »
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `exprα_
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `exprα_
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«expr ⊗ »
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `exprα_
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«expr ⊗ »
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `exprα_
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«expr𝟙_»
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«expr ⊗' »
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«exprλ_»
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `«expr ⊗' »
-- ././Mathport/Syntax/Translate/Basic.lean:825:4: warning: unsupported notation `exprρ_
/-- In a monoidal category, we can take the tensor product of objects, `X ⊗ Y` and of morphisms `f ⊗ g`.
Tensor product does not need to be strictly associative on objects, but there is a
specified associator, `α_ X Y Z : (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)`. There is a tensor unit `𝟙_ C`,
with specified left and right unitor isomorphisms `λ_ X : 𝟙_ C ⊗ X ≅ X` and `ρ_ X : X ⊗ 𝟙_ C ≅ X`.
These associators and unitors satisfy the pentagon and triangle equations.

See https://stacks.math.columbia.edu/tag/0FFK.
-/
class MonoidalCategory (C : Type u) [𝒞 : Category.{v} C] where
  -- curried tensor product of objects:
  tensorObj : C → C → C
  -- This notation is only temporary
  -- curried tensor product of morphisms:
  tensorHom : ∀ {X₁ Y₁ X₂ Y₂ : C}, (X₁ ⟶ Y₁) → (X₂ ⟶ Y₂) → («expr ⊗ » X₁ X₂ ⟶ «expr ⊗ » Y₁ Y₂)
  -- This notation is only temporary
  -- tensor product laws:
  tensor_id' : ∀ X₁ X₂ : C, «expr ⊗' » (𝟙 X₁) (𝟙 X₂) = 𝟙 («expr ⊗ » X₁ X₂) := by
    run_tac
      obviously
  tensor_comp' :
    ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} f₁ : X₁ ⟶ Y₁ f₂ : X₂ ⟶ Y₂ g₁ : Y₁ ⟶ Z₁ g₂ : Y₂ ⟶ Z₂,
      «expr ⊗' » (f₁ ≫ g₁) (f₂ ≫ g₂) = «expr ⊗' » f₁ f₂ ≫ «expr ⊗' » g₁ g₂ := by
    run_tac
      obviously
  -- tensor unit:
  tensorUnit {} : C
  -- associator:
  associator : ∀ X Y Z : C, «expr ⊗ » («expr ⊗ » X Y) Z ≅ «expr ⊗ » X («expr ⊗ » Y Z)
  associator_naturality' :
    ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} f₁ : X₁ ⟶ Y₁ f₂ : X₂ ⟶ Y₂ f₃ : X₃ ⟶ Y₃,
      «expr ⊗' » («expr ⊗' » f₁ f₂) f₃ ≫ ((exprα_) Y₁ Y₂ Y₃).Hom =
        ((exprα_) X₁ X₂ X₃).Hom ≫ «expr ⊗' » f₁ («expr ⊗' » f₂ f₃) := by
    run_tac
      obviously
  -- left unitor:
  leftUnitor : ∀ X : C, «expr ⊗ » («expr𝟙_») X ≅ X
  left_unitor_naturality' :
    ∀ {X Y : C} f : X ⟶ Y, «expr ⊗' » (𝟙 («expr𝟙_»)) f ≫ ((«exprλ_») Y).Hom = ((«exprλ_») X).Hom ≫ f := by
    run_tac
      obviously
  -- right unitor:
  rightUnitor : ∀ X : C, «expr ⊗ » X («expr𝟙_») ≅ X
  right_unitor_naturality' :
    ∀ {X Y : C} f : X ⟶ Y, «expr ⊗' » f (𝟙 («expr𝟙_»)) ≫ ((exprρ_) Y).Hom = ((exprρ_) X).Hom ≫ f := by
    run_tac
      obviously
  -- pentagon identity:
  pentagon' :
    ∀ W X Y Z : C,
      «expr ⊗' » ((exprα_) W X Y).Hom (𝟙 Z) ≫
          ((exprα_) W («expr ⊗ » X Y) Z).Hom ≫ «expr ⊗' » (𝟙 W) ((exprα_) X Y Z).Hom =
        ((exprα_) («expr ⊗ » W X) Y Z).Hom ≫ ((exprα_) W X («expr ⊗ » Y Z)).Hom := by
    run_tac
      obviously
  -- triangle identity:
  triangle' :
    ∀ X Y : C,
      ((exprα_) X («expr𝟙_») Y).Hom ≫ «expr ⊗' » (𝟙 X) ((«exprλ_») Y).Hom = «expr ⊗' » ((exprρ_) X).Hom (𝟙 Y) := by
    run_tac
      obviously

restate_axiom monoidal_category.tensor_id'

attribute [simp] monoidal_category.tensor_id

restate_axiom monoidal_category.tensor_comp'

attribute [reassoc] monoidal_category.tensor_comp

-- This would be redundant in the simp set.
attribute [simp] monoidal_category.tensor_comp

restate_axiom monoidal_category.associator_naturality'

attribute [reassoc] monoidal_category.associator_naturality

restate_axiom monoidal_category.left_unitor_naturality'

attribute [reassoc] monoidal_category.left_unitor_naturality

restate_axiom monoidal_category.right_unitor_naturality'

attribute [reassoc] monoidal_category.right_unitor_naturality

restate_axiom monoidal_category.pentagon'

restate_axiom monoidal_category.triangle'

attribute [reassoc] monoidal_category.pentagon

attribute [simp, reassoc] monoidal_category.triangle

open MonoidalCategory

-- mathport name: «expr ⊗ »
infixr:70 " ⊗ " => tensorObj

-- mathport name: «expr ⊗ »
infixr:70 " ⊗ " => tensorHom

-- mathport name: «expr𝟙_»
notation "𝟙_" => tensorUnit

-- mathport name: «exprα_»
notation "α_" => associator

-- mathport name: «exprλ_»
notation "λ_" => leftUnitor

-- mathport name: «exprρ_»
notation "ρ_" => rightUnitor

/-- The tensor product of two isomorphisms is an isomorphism. -/
@[simps]
def tensorIso {C : Type u} {X Y X' Y' : C} [Category.{v} C] [MonoidalCategory.{v} C] (f : X ≅ Y) (g : X' ≅ Y') :
    X ⊗ X' ≅ Y ⊗ Y' where
  Hom := f.Hom ⊗ g.Hom
  inv := f.inv ⊗ g.inv
  hom_inv_id' := by
    rw [← tensor_comp, iso.hom_inv_id, iso.hom_inv_id, ← tensor_id]
  inv_hom_id' := by
    rw [← tensor_comp, iso.inv_hom_id, iso.inv_hom_id, ← tensor_id]

-- mathport name: «expr ⊗ »
infixr:70 " ⊗ " => tensorIso

namespace MonoidalCategory

section

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

instance tensor_is_iso {W X Y Z : C} (f : W ⟶ X) [IsIso f] (g : Y ⟶ Z) [IsIso g] : IsIso (f ⊗ g) :=
  IsIso.of_iso (asIso f ⊗ asIso g)

@[simp]
theorem inv_tensor {W X Y Z : C} (f : W ⟶ X) [IsIso f] (g : Y ⟶ Z) [IsIso g] : inv (f ⊗ g) = inv f ⊗ inv g := by
  ext
  simp [← tensor_comp]

variable {U V W X Y Z : C}

-- When `rewrite_search` lands, add @[search] attributes to
-- monoidal_category.tensor_id monoidal_category.tensor_comp monoidal_category.associator_naturality
-- monoidal_category.left_unitor_naturality monoidal_category.right_unitor_naturality
-- monoidal_category.pentagon monoidal_category.triangle
-- tensor_comp_id tensor_id_comp comp_id_tensor_tensor_id
-- triangle_assoc_comp_left triangle_assoc_comp_right
-- triangle_assoc_comp_left_inv triangle_assoc_comp_right_inv
-- left_unitor_tensor left_unitor_tensor_inv
-- right_unitor_tensor right_unitor_tensor_inv
-- pentagon_inv
-- associator_inv_naturality
-- left_unitor_inv_naturality
-- right_unitor_inv_naturality
@[reassoc, simp]
theorem comp_tensor_id (f : W ⟶ X) (g : X ⟶ Y) : f ≫ g ⊗ 𝟙 Z = (f ⊗ 𝟙 Z) ≫ (g ⊗ 𝟙 Z) := by
  rw [← tensor_comp]
  simp

@[reassoc, simp]
theorem id_tensor_comp (f : W ⟶ X) (g : X ⟶ Y) : 𝟙 Z ⊗ f ≫ g = (𝟙 Z ⊗ f) ≫ (𝟙 Z ⊗ g) := by
  rw [← tensor_comp]
  simp

@[simp, reassoc]
theorem id_tensor_comp_tensor_id (f : W ⟶ X) (g : Y ⟶ Z) : (𝟙 Y ⊗ f) ≫ (g ⊗ 𝟙 X) = g ⊗ f := by
  rw [← tensor_comp]
  simp

@[simp, reassoc]
theorem tensor_id_comp_id_tensor (f : W ⟶ X) (g : Y ⟶ Z) : (g ⊗ 𝟙 W) ≫ (𝟙 Z ⊗ f) = g ⊗ f := by
  rw [← tensor_comp]
  simp

@[reassoc]
theorem left_unitor_inv_naturality {X X' : C} (f : X ⟶ X') : f ≫ (λ_ X').inv = (λ_ X).inv ≫ (𝟙 _ ⊗ f) := by
  apply (cancel_mono (λ_ X').Hom).1
  simp only [assoc, comp_id, iso.inv_hom_id]
  rw [left_unitor_naturality, ← category.assoc, iso.inv_hom_id, category.id_comp]

@[reassoc]
theorem right_unitor_inv_naturality {X X' : C} (f : X ⟶ X') : f ≫ (ρ_ X').inv = (ρ_ X).inv ≫ (f ⊗ 𝟙 _) := by
  apply (cancel_mono (ρ_ X').Hom).1
  simp only [assoc, comp_id, iso.inv_hom_id]
  rw [right_unitor_naturality, ← category.assoc, iso.inv_hom_id, category.id_comp]

@[simp]
theorem right_unitor_conjugation {X Y : C} (f : X ⟶ Y) : (ρ_ X).inv ≫ (f ⊗ 𝟙 (𝟙_ C)) ≫ (ρ_ Y).Hom = f := by
  rw [right_unitor_naturality, ← category.assoc, iso.inv_hom_id, category.id_comp]

@[simp]
theorem left_unitor_conjugation {X Y : C} (f : X ⟶ Y) : (λ_ X).inv ≫ (𝟙 (𝟙_ C) ⊗ f) ≫ (λ_ Y).Hom = f := by
  rw [left_unitor_naturality, ← category.assoc, iso.inv_hom_id, category.id_comp]

@[simp]
theorem tensor_left_iff {X Y : C} (f g : X ⟶ Y) : 𝟙 (𝟙_ C) ⊗ f = 𝟙 (𝟙_ C) ⊗ g ↔ f = g := by
  rw [← cancel_mono (λ_ Y).Hom, left_unitor_naturality, left_unitor_naturality]
  simp

@[simp]
theorem tensor_right_iff {X Y : C} (f g : X ⟶ Y) : f ⊗ 𝟙 (𝟙_ C) = g ⊗ 𝟙 (𝟙_ C) ↔ f = g := by
  rw [← cancel_mono (ρ_ Y).Hom, right_unitor_naturality, right_unitor_naturality]
  simp

-- See Proposition 2.2.4 of <http://www-math.mit.edu/~etingof/egnobookfinal.pdf>
@[reassoc]
theorem left_unitor_tensor' (X Y : C) : (α_ (𝟙_ C) X Y).Hom ≫ (λ_ (X ⊗ Y)).Hom = (λ_ X).Hom ⊗ 𝟙 Y := by
  rw [← tensor_left_iff, id_tensor_comp, ← cancel_epi (α_ (𝟙_ C) (𝟙_ C ⊗ X) Y).Hom, ←
    cancel_epi ((α_ (𝟙_ C) (𝟙_ C) X).Hom ⊗ 𝟙 Y), pentagon_assoc, triangle, ← associator_naturality, ←
    comp_tensor_id_assoc, triangle, associator_naturality, tensor_id]

@[reassoc, simp]
theorem left_unitor_tensor (X Y : C) : (λ_ (X ⊗ Y)).Hom = (α_ (𝟙_ C) X Y).inv ≫ ((λ_ X).Hom ⊗ 𝟙 Y) := by
  rw [← left_unitor_tensor']
  simp

theorem left_unitor_tensor_inv' (X Y : C) : (λ_ (X ⊗ Y)).inv ≫ (α_ (𝟙_ C) X Y).inv = (λ_ X).inv ⊗ 𝟙 Y :=
  eq_of_inv_eq_inv
    (by
      simp )

@[reassoc, simp]
theorem left_unitor_tensor_inv (X Y : C) : (λ_ (X ⊗ Y)).inv = ((λ_ X).inv ⊗ 𝟙 Y) ≫ (α_ (𝟙_ C) X Y).Hom := by
  rw [← left_unitor_tensor_inv']
  simp

@[reassoc, simp]
theorem right_unitor_tensor (X Y : C) : (ρ_ (X ⊗ Y)).Hom = (α_ X Y (𝟙_ C)).Hom ≫ (𝟙 X ⊗ (ρ_ Y).Hom) := by
  rw [← tensor_right_iff, comp_tensor_id, ← cancel_mono (α_ X Y (𝟙_ C)).Hom, assoc, associator_naturality, ←
    triangle_assoc, ← triangle, id_tensor_comp, pentagon_assoc, ← associator_naturality, tensor_id]

@[reassoc, simp]
theorem right_unitor_tensor_inv (X Y : C) : (ρ_ (X ⊗ Y)).inv = (𝟙 X ⊗ (ρ_ Y).inv) ≫ (α_ X Y (𝟙_ C)).inv :=
  eq_of_inv_eq_inv
    (by
      simp )

@[reassoc]
theorem id_tensor_right_unitor_inv (X Y : C) : 𝟙 X ⊗ (ρ_ Y).inv = (ρ_ _).inv ≫ (α_ _ _ _).Hom := by
  simp only [right_unitor_tensor_inv, category.comp_id, iso.inv_hom_id, category.assoc]

@[reassoc]
theorem left_unitor_inv_tensor_id (X Y : C) : (λ_ X).inv ⊗ 𝟙 Y = (λ_ _).inv ≫ (α_ _ _ _).inv := by
  simp only [left_unitor_tensor_inv, assoc, comp_id, hom_inv_id]

@[reassoc]
theorem associator_inv_naturality {X Y Z X' Y' Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    (f ⊗ g ⊗ h) ≫ (α_ X' Y' Z').inv = (α_ X Y Z).inv ≫ ((f ⊗ g) ⊗ h) := by
  rw [comp_inv_eq, assoc, associator_naturality]
  simp

@[reassoc]
theorem id_tensor_associator_naturality {X Y Z Z' : C} (h : Z ⟶ Z') :
    (𝟙 (X ⊗ Y) ⊗ h) ≫ (α_ X Y Z').Hom = (α_ X Y Z).Hom ≫ (𝟙 X ⊗ 𝟙 Y ⊗ h) := by
  rw [← tensor_id, associator_naturality]

@[reassoc]
theorem id_tensor_associator_inv_naturality {X Y Z X' : C} (f : X ⟶ X') :
    (f ⊗ 𝟙 (Y ⊗ Z)) ≫ (α_ X' Y Z).inv = (α_ X Y Z).inv ≫ ((f ⊗ 𝟙 Y) ⊗ 𝟙 Z) := by
  rw [← tensor_id, associator_inv_naturality]

@[reassoc]
theorem associator_conjugation {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    (α_ X Y Z).Hom ≫ (f ⊗ g ⊗ h) ≫ (α_ X' Y' Z').inv = (f ⊗ g) ⊗ h := by
  rw [associator_inv_naturality, hom_inv_id_assoc]

@[reassoc]
theorem associator_inv_conjugation {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    (α_ X Y Z).inv ≫ ((f ⊗ g) ⊗ h) ≫ (α_ X' Y' Z').Hom = f ⊗ g ⊗ h := by
  rw [associator_naturality, inv_hom_id_assoc]

@[reassoc]
theorem pentagon_inv (W X Y Z : C) :
    (𝟙 W ⊗ (α_ X Y Z).inv) ≫ (α_ W (X ⊗ Y) Z).inv ≫ ((α_ W X Y).inv ⊗ 𝟙 Z) =
      (α_ W X (Y ⊗ Z)).inv ≫ (α_ (W ⊗ X) Y Z).inv :=
  CategoryTheory.eq_of_inv_eq_inv
    (by
      simp [pentagon])

@[reassoc]
theorem pentagon_inv_inv_hom (W X Y Z : C) :
    (α_ W (X ⊗ Y) Z).inv ≫ ((α_ W X Y).inv ⊗ 𝟙 Z) ≫ (α_ (W ⊗ X) Y Z).Hom =
      (𝟙 W ⊗ (α_ X Y Z).Hom) ≫ (α_ W X (Y ⊗ Z)).inv :=
  by
  rw [← (iso.eq_comp_inv _).mp (pentagon_inv W X Y Z)]
  slice_rhs 1 2 => rw [← id_tensor_comp, iso.hom_inv_id]
  simp only [tensor_id, assoc, id_comp]

theorem triangle_assoc_comp_left (X Y : C) : (α_ X (𝟙_ C) Y).Hom ≫ (𝟙 X ⊗ (λ_ Y).Hom) = (ρ_ X).Hom ⊗ 𝟙 Y :=
  MonoidalCategory.triangle X Y

@[simp, reassoc]
theorem triangle_assoc_comp_right (X Y : C) : (α_ X (𝟙_ C) Y).inv ≫ ((ρ_ X).Hom ⊗ 𝟙 Y) = 𝟙 X ⊗ (λ_ Y).Hom := by
  rw [← triangle_assoc_comp_left, iso.inv_hom_id_assoc]

@[simp, reassoc]
theorem triangle_assoc_comp_right_inv (X Y : C) : ((ρ_ X).inv ⊗ 𝟙 Y) ≫ (α_ X (𝟙_ C) Y).Hom = 𝟙 X ⊗ (λ_ Y).inv := by
  apply (cancel_mono (𝟙 X ⊗ (λ_ Y).Hom)).1
  simp only [assoc, triangle_assoc_comp_left]
  rw [← comp_tensor_id, iso.inv_hom_id, ← id_tensor_comp, iso.inv_hom_id]

@[simp, reassoc]
theorem triangle_assoc_comp_left_inv (X Y : C) : (𝟙 X ⊗ (λ_ Y).inv) ≫ (α_ X (𝟙_ C) Y).inv = (ρ_ X).inv ⊗ 𝟙 Y := by
  apply (cancel_mono ((ρ_ X).Hom ⊗ 𝟙 Y)).1
  simp only [triangle_assoc_comp_right, assoc]
  rw [← id_tensor_comp, iso.inv_hom_id, ← comp_tensor_id, iso.inv_hom_id]

theorem unitors_equal : (λ_ (𝟙_ C)).Hom = (ρ_ (𝟙_ C)).Hom := by
  rw [← tensor_left_iff, ← cancel_epi (α_ (𝟙_ C) (𝟙_ _) (𝟙_ _)).Hom, ← cancel_mono (ρ_ (𝟙_ C)).Hom, triangle, ←
    right_unitor_tensor, right_unitor_naturality]

theorem unitors_inv_equal : (λ_ (𝟙_ C)).inv = (ρ_ (𝟙_ C)).inv := by
  ext
  simp [← unitors_equal]

@[reassoc]
theorem right_unitor_inv_comp_tensor (f : W ⟶ X) (g : 𝟙_ C ⟶ Z) : (ρ_ _).inv ≫ (f ⊗ g) = f ≫ (ρ_ _).inv ≫ (𝟙 _ ⊗ g) :=
  by
  slice_rhs 1 2 => rw [right_unitor_inv_naturality]
  simp

@[reassoc]
theorem left_unitor_inv_comp_tensor (f : W ⟶ X) (g : 𝟙_ C ⟶ Z) : (λ_ _).inv ≫ (g ⊗ f) = f ≫ (λ_ _).inv ≫ (g ⊗ 𝟙 _) := by
  slice_rhs 1 2 => rw [left_unitor_inv_naturality]
  simp

@[simp, reassoc]
theorem hom_inv_id_tensor {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f.Hom ⊗ g) ≫ (f.inv ⊗ h) = 𝟙 V ⊗ g ≫ h := by
  rw [← tensor_comp, f.hom_inv_id]

@[simp, reassoc]
theorem inv_hom_id_tensor {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f.inv ⊗ g) ≫ (f.Hom ⊗ h) = 𝟙 W ⊗ g ≫ h := by
  rw [← tensor_comp, f.inv_hom_id]

@[simp, reassoc]
theorem tensor_hom_inv_id {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ f.Hom) ≫ (h ⊗ f.inv) = g ≫ h ⊗ 𝟙 V := by
  rw [← tensor_comp, f.hom_inv_id]

@[simp, reassoc]
theorem tensor_inv_hom_id {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ f.inv) ≫ (h ⊗ f.Hom) = g ≫ h ⊗ 𝟙 W := by
  rw [← tensor_comp, f.inv_hom_id]

@[reassoc]
theorem pentagon_hom_inv {W X Y Z : C} :
    (α_ W X (Y ⊗ Z)).Hom ≫ (𝟙 W ⊗ (α_ X Y Z).inv) =
      (α_ (W ⊗ X) Y Z).inv ≫ ((α_ W X Y).Hom ⊗ 𝟙 Z) ≫ (α_ W (X ⊗ Y) Z).Hom :=
  by
  have pent := pentagon W X Y Z
  rw [← iso.comp_inv_eq] at pent
  rw [iso.eq_inv_comp, ← pent]
  simp only [tensor_hom_inv_id, iso.inv_hom_id_assoc, tensor_id, category.comp_id, category.assoc]

@[reassoc]
theorem pentagon_inv_hom (W X Y Z : C) :
    (α_ (W ⊗ X) Y Z).inv ≫ ((α_ W X Y).Hom ⊗ 𝟙 Z) =
      (α_ W X (Y ⊗ Z)).Hom ≫ (𝟙 W ⊗ (α_ X Y Z).inv) ≫ (α_ W (X ⊗ Y) Z).inv :=
  by
  have pent := pentagon W X Y Z
  rw [← iso.inv_comp_eq] at pent
  rw [← pent]
  simp only [tensor_id, assoc, id_comp, comp_id, hom_inv_id, tensor_hom_inv_id_assoc]

@[reassoc]
theorem pentagon_comp_id_tensor {W X Y Z : C} :
    (α_ W (X ⊗ Y) Z).Hom ≫ (𝟙 W ⊗ (α_ X Y Z).Hom) =
      ((α_ W X Y).inv ⊗ 𝟙 Z) ≫ (α_ (W ⊗ X) Y Z).Hom ≫ (α_ W X (Y ⊗ Z)).Hom :=
  by
  rw [← pentagon W X Y Z]
  simp

end

section

variable (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]

/-- The tensor product expressed as a functor. -/
def tensor : C × C ⥤ C where
  obj := fun X => X.1 ⊗ X.2
  map := fun f : X ⟶ Y => f.1 ⊗ f.2

/-- The left-associated triple tensor product as a functor. -/
def leftAssocTensor : C × C × C ⥤ C where
  obj := fun X => (X.1 ⊗ X.2.1) ⊗ X.2.2
  map := fun f : X ⟶ Y => (f.1 ⊗ f.2.1) ⊗ f.2.2

@[simp]
theorem left_assoc_tensor_obj X : (leftAssocTensor C).obj X = (X.1 ⊗ X.2.1) ⊗ X.2.2 :=
  rfl

@[simp]
theorem left_assoc_tensor_map {X Y} (f : X ⟶ Y) : (leftAssocTensor C).map f = (f.1 ⊗ f.2.1) ⊗ f.2.2 :=
  rfl

/-- The right-associated triple tensor product as a functor. -/
def rightAssocTensor : C × C × C ⥤ C where
  obj := fun X => X.1 ⊗ X.2.1 ⊗ X.2.2
  map := fun f : X ⟶ Y => f.1 ⊗ f.2.1 ⊗ f.2.2

@[simp]
theorem right_assoc_tensor_obj X : (rightAssocTensor C).obj X = X.1 ⊗ X.2.1 ⊗ X.2.2 :=
  rfl

@[simp]
theorem right_assoc_tensor_map {X Y} (f : X ⟶ Y) : (rightAssocTensor C).map f = f.1 ⊗ f.2.1 ⊗ f.2.2 :=
  rfl

/-- The functor `λ X, 𝟙_ C ⊗ X`. -/
def tensorUnitLeft : C ⥤ C where
  obj := fun X => 𝟙_ C ⊗ X
  map := fun f : X ⟶ Y => 𝟙 (𝟙_ C) ⊗ f

/-- The functor `λ X, X ⊗ 𝟙_ C`. -/
def tensorUnitRight : C ⥤ C where
  obj := fun X => X ⊗ 𝟙_ C
  map := fun f : X ⟶ Y => f ⊗ 𝟙 (𝟙_ C)

/-- The associator as a natural isomorphism. -/
-- We can express the associator and the unitors, given componentwise above,
-- as natural isomorphisms.
@[simps]
def associatorNatIso : leftAssocTensor C ≅ rightAssocTensor C :=
  NatIso.ofComponents
    (by
      intros
      apply monoidal_category.associator)
    (by
      intros
      apply monoidal_category.associator_naturality)

/-- The left unitor as a natural isomorphism. -/
@[simps]
def leftUnitorNatIso : tensorUnitLeft C ≅ 𝟭 C :=
  NatIso.ofComponents
    (by
      intros
      apply monoidal_category.left_unitor)
    (by
      intros
      apply monoidal_category.left_unitor_naturality)

/-- The right unitor as a natural isomorphism. -/
@[simps]
def rightUnitorNatIso : tensorUnitRight C ≅ 𝟭 C :=
  NatIso.ofComponents
    (by
      intros
      apply monoidal_category.right_unitor)
    (by
      intros
      apply monoidal_category.right_unitor_naturality)

section

variable {C}

/-- Tensoring on the left with a fixed object, as a functor. -/
@[simps]
def tensorLeft (X : C) : C ⥤ C where
  obj := fun Y => X ⊗ Y
  map := fun Y Y' f => 𝟙 X ⊗ f

/-- Tensoring on the left with `X ⊗ Y` is naturally isomorphic to
tensoring on the left with `Y`, and then again with `X`.
-/
def tensorLeftTensor (X Y : C) : tensorLeft (X ⊗ Y) ≅ tensorLeft Y ⋙ tensorLeft X :=
  NatIso.ofComponents (associator _ _) fun Z Z' f => by
    dsimp
    rw [← tensor_id]
    apply associator_naturality

@[simp]
theorem tensor_left_tensor_hom_app (X Y Z : C) : (tensorLeftTensor X Y).Hom.app Z = (associator X Y Z).Hom :=
  rfl

@[simp]
theorem tensor_left_tensor_inv_app (X Y Z : C) : (tensorLeftTensor X Y).inv.app Z = (associator X Y Z).inv := by
  simp [tensor_left_tensor]

/-- Tensoring on the right with a fixed object, as a functor. -/
@[simps]
def tensorRight (X : C) : C ⥤ C where
  obj := fun Y => Y ⊗ X
  map := fun Y Y' f => f ⊗ 𝟙 X

variable (C)

/-- Tensoring on the left, as a functor from `C` into endofunctors of `C`.

TODO: show this is a op-monoidal functor.
-/
@[simps]
def tensoringLeft : C ⥤ C ⥤ C where
  obj := tensorLeft
  map := fun X Y f => { app := fun Z => f ⊗ 𝟙 Z }

instance : Faithful (tensoringLeft C) where
  map_injective' := fun X Y f g h => by
    injections with h
    replace h := congr_funₓ h (𝟙_ C)
    simpa using h

/-- Tensoring on the right, as a functor from `C` into endofunctors of `C`.

We later show this is a monoidal functor.
-/
@[simps]
def tensoringRight : C ⥤ C ⥤ C where
  obj := tensorRight
  map := fun X Y f => { app := fun Z => 𝟙 Z ⊗ f }

instance : Faithful (tensoringRight C) where
  map_injective' := fun X Y f g h => by
    injections with h
    replace h := congr_funₓ h (𝟙_ C)
    simpa using h

variable {C}

/-- Tensoring on the right with `X ⊗ Y` is naturally isomorphic to
tensoring on the right with `X`, and then again with `Y`.
-/
def tensorRightTensor (X Y : C) : tensorRight (X ⊗ Y) ≅ tensorRight X ⋙ tensorRight Y :=
  NatIso.ofComponents (fun Z => (associator Z X Y).symm) fun Z Z' f => by
    dsimp
    rw [← tensor_id]
    apply associator_inv_naturality

@[simp]
theorem tensor_right_tensor_hom_app (X Y Z : C) : (tensorRightTensor X Y).Hom.app Z = (associator Z X Y).inv :=
  rfl

@[simp]
theorem tensor_right_tensor_inv_app (X Y Z : C) : (tensorRightTensor X Y).inv.app Z = (associator Z X Y).Hom := by
  simp [tensor_right_tensor]

variable {C}

/-- Any property closed under `𝟙_` and `⊗` induces a full monoidal subcategory of `C`, where
the category on the subtype is given by `full_subcategory`.
-/
def fullMonoidalSubcategory (P : C → Prop) (h_id : P (𝟙_ C)) (h_tensor : ∀ {X Y}, P X → P Y → P (X ⊗ Y)) :
    MonoidalCategory { X : C // P X } where
  tensorObj := fun X Y => ⟨X ⊗ Y, h_tensor X.2 Y.2⟩
  tensorHom := fun X₁ Y₁ X₂ Y₂ f g => by
    change X₁.1 ⊗ X₂.1 ⟶ Y₁.1 ⊗ Y₂.1
    change X₁.1 ⟶ Y₁.1 at f
    change X₂.1 ⟶ Y₂.1 at g
    exact f ⊗ g
  tensorUnit := ⟨𝟙_ C, h_id⟩
  associator := fun X Y Z =>
    ⟨(α_ X.1 Y.1 Z.1).Hom, (α_ X.1 Y.1 Z.1).inv, hom_inv_id (α_ X.1 Y.1 Z.1), inv_hom_id (α_ X.1 Y.1 Z.1)⟩
  leftUnitor := fun X => ⟨(λ_ X.1).Hom, (λ_ X.1).inv, hom_inv_id (λ_ X.1), inv_hom_id (λ_ X.1)⟩
  rightUnitor := fun X => ⟨(ρ_ X.1).Hom, (ρ_ X.1).inv, hom_inv_id (ρ_ X.1), inv_hom_id (ρ_ X.1)⟩
  tensor_id' := fun X Y => tensor_id X.1 Y.1
  tensor_comp' := fun X₁ Y₁ Z₁ X₂ Y₂ Z₂ f₁ f₂ g₁ g₂ => tensor_comp f₁ f₂ g₁ g₂
  associator_naturality' := fun X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃ => associator_naturality f₁ f₂ f₃
  left_unitor_naturality' := fun X Y f => left_unitor_naturality f
  right_unitor_naturality' := fun X Y f => right_unitor_naturality f
  pentagon' := fun W X Y Z => pentagon W.1 X.1 Y.1 Z.1
  triangle' := fun X Y => triangle X.1 Y.1

end

end

end MonoidalCategory

end CategoryTheory

