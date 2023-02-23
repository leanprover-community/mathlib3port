/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Scott Morrison, Bhavik Mehta, Jakob von Raumer

! This file was ported from Lean 3 source module category_theory.monoidal.category
! leanprover-community/mathlib commit 23aa88e32dcc9d2a24cca7bc23268567ed4cd7d6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Products.Basic

/-!
# Monoidal categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
* <https://stacks.math.columbia.edu/tag/0FFK>.
-/


open CategoryTheory

universe v u

open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.Iso

namespace CategoryTheory

#print CategoryTheory.MonoidalCategory /-
/- ./././Mathport/Syntax/Translate/Command.lean:401:24: unsupported: (notation) in structure -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `tensor_obj -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `tensor_obj -/
/- ./././Mathport/Syntax/Translate/Command.lean:401:24: unsupported: (notation) in structure -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr ⊗' » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `tensor_obj -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr ⊗' » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr ⊗' » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr ⊗' » -/
/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`tensorUnit] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:401:24: unsupported: (notation) in structure -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `tensor_obj -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `tensor_obj -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `tensor_obj -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `tensor_obj -/
/- ./././Mathport/Syntax/Translate/Command.lean:401:24: unsupported: (notation) in structure -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr ⊗' » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr ⊗' » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `exprα_ -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `exprα_ -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr ⊗' » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr ⊗' » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `tensor_obj -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr𝟙_» -/
/- ./././Mathport/Syntax/Translate/Command.lean:401:24: unsupported: (notation) in structure -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr ⊗' » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr𝟙_» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«exprλ_» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«exprλ_» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `tensor_obj -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr𝟙_» -/
/- ./././Mathport/Syntax/Translate/Command.lean:401:24: unsupported: (notation) in structure -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr ⊗' » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr𝟙_» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `exprρ_ -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `exprρ_ -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr ⊗' » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `exprα_ -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `exprα_ -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `tensor_obj -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr ⊗' » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `exprα_ -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `exprα_ -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `tensor_obj -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `exprα_ -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `tensor_obj -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `exprα_ -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr𝟙_» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr ⊗' » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«exprλ_» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr ⊗' » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `exprρ_ -/
/--
In a monoidal category, we can take the tensor product of objects, `X ⊗ Y` and of morphisms `f ⊗ g`.
Tensor product does not need to be strictly associative on objects, but there is a
specified associator, `α_ X Y Z : (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)`. There is a tensor unit `𝟙_ C`,
with specified left and right unitor isomorphisms `λ_ X : 𝟙_ C ⊗ X ≅ X` and `ρ_ X : X ⊗ 𝟙_ C ≅ X`.
These associators and unitors satisfy the pentagon and triangle equations.

See <https://stacks.math.columbia.edu/tag/0FFK>.
-/
class MonoidalCategory (C : Type u) [𝒞 : Category.{v} C] where
  -- curried tensor product of objects:
  tensorObj : C → C → C
  -- This notation is only temporary
  -- curried tensor product of morphisms:
  tensorHom : ∀ {X₁ Y₁ X₂ Y₂ : C}, (X₁ ⟶ Y₁) → (X₂ ⟶ Y₂) → (tensor_obj X₁ X₂ ⟶ tensor_obj Y₁ Y₂)
  -- This notation is only temporary
  -- tensor product laws:
  tensor_id' : ∀ X₁ X₂ : C, «expr ⊗' » (𝟙 X₁) (𝟙 X₂) = 𝟙 (tensor_obj X₁ X₂) := by obviously
  tensor_comp' :
    ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
      «expr ⊗' » (f₁ ≫ g₁) (f₂ ≫ g₂) = «expr ⊗' » f₁ f₂ ≫ «expr ⊗' » g₁ g₂ := by
    obviously
  -- tensor unit:
  tensorUnit : C
  -- associator:
  associator : ∀ X Y Z : C, tensor_obj (tensor_obj X Y) Z ≅ tensor_obj X (tensor_obj Y Z)
  associator_naturality' :
    ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
      «expr ⊗' » («expr ⊗' » f₁ f₂) f₃ ≫ ((exprα_) Y₁ Y₂ Y₃).Hom =
        ((exprα_) X₁ X₂ X₃).Hom ≫ «expr ⊗' » f₁ («expr ⊗' » f₂ f₃) := by
    obviously
  -- left unitor:
  leftUnitor : ∀ X : C, tensor_obj («expr𝟙_») X ≅ X
  leftUnitor_naturality' :
    ∀ {X Y : C} (f : X ⟶ Y),
      «expr ⊗' » (𝟙 («expr𝟙_»)) f ≫ ((«exprλ_») Y).Hom = ((«exprλ_») X).Hom ≫ f := by
    obviously
  -- right unitor:
  rightUnitor : ∀ X : C, tensor_obj X («expr𝟙_») ≅ X
  rightUnitor_naturality' :
    ∀ {X Y : C} (f : X ⟶ Y),
      «expr ⊗' » f (𝟙 («expr𝟙_»)) ≫ ((exprρ_) Y).Hom = ((exprρ_) X).Hom ≫ f := by
    obviously
  -- pentagon identity:
  pentagon' :
    ∀ W X Y Z : C,
      «expr ⊗' » ((exprα_) W X Y).Hom (𝟙 Z) ≫
          ((exprα_) W (tensor_obj X Y) Z).Hom ≫ «expr ⊗' » (𝟙 W) ((exprα_) X Y Z).Hom =
        ((exprα_) (tensor_obj W X) Y Z).Hom ≫ ((exprα_) W X (tensor_obj Y Z)).Hom := by
    obviously
  -- triangle identity:
  triangle' :
    ∀ X Y : C,
      ((exprα_) X («expr𝟙_») Y).Hom ≫ «expr ⊗' » (𝟙 X) ((«exprλ_») Y).Hom =
        «expr ⊗' » ((exprρ_) X).Hom (𝟙 Y) := by
    obviously
#align category_theory.monoidal_category CategoryTheory.MonoidalCategory
-/

restate_axiom monoidal_category.tensor_id'

attribute [simp] monoidal_category.tensor_id

restate_axiom monoidal_category.tensor_comp'

attribute [reassoc.1] monoidal_category.tensor_comp

-- This would be redundant in the simp set.
attribute [simp] monoidal_category.tensor_comp

restate_axiom monoidal_category.associator_naturality'

attribute [reassoc.1] monoidal_category.associator_naturality

restate_axiom monoidal_category.left_unitor_naturality'

attribute [reassoc.1] monoidal_category.left_unitor_naturality

restate_axiom monoidal_category.right_unitor_naturality'

attribute [reassoc.1] monoidal_category.right_unitor_naturality

restate_axiom monoidal_category.pentagon'

restate_axiom monoidal_category.triangle'

attribute [reassoc.1] monoidal_category.pentagon

attribute [simp, reassoc.1] monoidal_category.triangle

open MonoidalCategory

-- mathport name: tensor_obj
infixr:70 " ⊗ " => tensorObj

-- mathport name: tensor_hom
infixr:70 " ⊗ " => tensorHom

-- mathport name: «expr𝟙_»
notation "𝟙_" => tensorUnit

-- mathport name: exprα_
notation "α_" => associator

-- mathport name: «exprλ_»
notation "λ_" => leftUnitor

-- mathport name: exprρ_
notation "ρ_" => rightUnitor

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.tensorIso /-
/-- The tensor product of two isomorphisms is an isomorphism. -/
@[simps]
def tensorIso {C : Type u} {X Y X' Y' : C} [Category.{v} C] [MonoidalCategory.{v} C] (f : X ≅ Y)
    (g : X' ≅ Y') : X ⊗ X' ≅ Y ⊗ Y' where
  Hom := f.Hom ⊗ g.Hom
  inv := f.inv ⊗ g.inv
  hom_inv_id' := by rw [← tensor_comp, iso.hom_inv_id, iso.hom_inv_id, ← tensor_id]
  inv_hom_id' := by rw [← tensor_comp, iso.inv_hom_id, iso.inv_hom_id, ← tensor_id]
#align category_theory.tensor_iso CategoryTheory.tensorIso
-/

-- mathport name: tensor_iso
infixr:70 " ⊗ " => tensorIso

namespace MonoidalCategory

section

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.tensor_isIso /-
instance tensor_isIso {W X Y Z : C} (f : W ⟶ X) [IsIso f] (g : Y ⟶ Z) [IsIso g] : IsIso (f ⊗ g) :=
  IsIso.of_iso (asIso f ⊗ asIso g)
#align category_theory.monoidal_category.tensor_is_iso CategoryTheory.MonoidalCategory.tensor_isIso
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.inv_tensor /-
@[simp]
theorem inv_tensor {W X Y Z : C} (f : W ⟶ X) [IsIso f] (g : Y ⟶ Z) [IsIso g] :
    inv (f ⊗ g) = inv f ⊗ inv g := by
  ext
  simp [← tensor_comp]
#align category_theory.monoidal_category.inv_tensor CategoryTheory.MonoidalCategory.inv_tensor
-/

variable {U V W X Y Z : C}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.tensor_dite /-
theorem tensor_dite {P : Prop} [Decidable P] {W X Y Z : C} (f : W ⟶ X) (g : P → (Y ⟶ Z))
    (g' : ¬P → (Y ⟶ Z)) : (f ⊗ if h : P then g h else g' h) = if h : P then f ⊗ g h else f ⊗ g' h :=
  by split_ifs <;> rfl
#align category_theory.monoidal_category.tensor_dite CategoryTheory.MonoidalCategory.tensor_dite
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.dite_tensor /-
theorem dite_tensor {P : Prop} [Decidable P] {W X Y Z : C} (f : W ⟶ X) (g : P → (Y ⟶ Z))
    (g' : ¬P → (Y ⟶ Z)) : (if h : P then g h else g' h) ⊗ f = if h : P then g h ⊗ f else g' h ⊗ f :=
  by split_ifs <;> rfl
#align category_theory.monoidal_category.dite_tensor CategoryTheory.MonoidalCategory.dite_tensor
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.comp_tensor_id /-
@[reassoc.1, simp]
theorem comp_tensor_id (f : W ⟶ X) (g : X ⟶ Y) : f ≫ g ⊗ 𝟙 Z = (f ⊗ 𝟙 Z) ≫ (g ⊗ 𝟙 Z) :=
  by
  rw [← tensor_comp]
  simp
#align category_theory.monoidal_category.comp_tensor_id CategoryTheory.MonoidalCategory.comp_tensor_id
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.id_tensor_comp /-
@[reassoc.1, simp]
theorem id_tensor_comp (f : W ⟶ X) (g : X ⟶ Y) : 𝟙 Z ⊗ f ≫ g = (𝟙 Z ⊗ f) ≫ (𝟙 Z ⊗ g) :=
  by
  rw [← tensor_comp]
  simp
#align category_theory.monoidal_category.id_tensor_comp CategoryTheory.MonoidalCategory.id_tensor_comp
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.id_tensor_comp_tensor_id /-
@[simp, reassoc.1]
theorem id_tensor_comp_tensor_id (f : W ⟶ X) (g : Y ⟶ Z) : (𝟙 Y ⊗ f) ≫ (g ⊗ 𝟙 X) = g ⊗ f :=
  by
  rw [← tensor_comp]
  simp
#align category_theory.monoidal_category.id_tensor_comp_tensor_id CategoryTheory.MonoidalCategory.id_tensor_comp_tensor_id
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.tensor_id_comp_id_tensor /-
@[simp, reassoc.1]
theorem tensor_id_comp_id_tensor (f : W ⟶ X) (g : Y ⟶ Z) : (g ⊗ 𝟙 W) ≫ (𝟙 Z ⊗ f) = g ⊗ f :=
  by
  rw [← tensor_comp]
  simp
#align category_theory.monoidal_category.tensor_id_comp_id_tensor CategoryTheory.MonoidalCategory.tensor_id_comp_id_tensor
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.rightUnitor_conjugation /-
@[simp]
theorem rightUnitor_conjugation {X Y : C} (f : X ⟶ Y) :
    f ⊗ 𝟙 (𝟙_ C) = (ρ_ X).Hom ≫ f ≫ (ρ_ Y).inv := by
  rw [← right_unitor_naturality_assoc, iso.hom_inv_id, category.comp_id]
#align category_theory.monoidal_category.right_unitor_conjugation CategoryTheory.MonoidalCategory.rightUnitor_conjugation
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.leftUnitor_conjugation /-
@[simp]
theorem leftUnitor_conjugation {X Y : C} (f : X ⟶ Y) : 𝟙 (𝟙_ C) ⊗ f = (λ_ X).Hom ≫ f ≫ (λ_ Y).inv :=
  by rw [← left_unitor_naturality_assoc, iso.hom_inv_id, category.comp_id]
#align category_theory.monoidal_category.left_unitor_conjugation CategoryTheory.MonoidalCategory.leftUnitor_conjugation
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.leftUnitor_inv_naturality /-
@[reassoc.1]
theorem leftUnitor_inv_naturality {X X' : C} (f : X ⟶ X') :
    f ≫ (λ_ X').inv = (λ_ X).inv ≫ (𝟙 _ ⊗ f) := by simp
#align category_theory.monoidal_category.left_unitor_inv_naturality CategoryTheory.MonoidalCategory.leftUnitor_inv_naturality
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.rightUnitor_inv_naturality /-
@[reassoc.1]
theorem rightUnitor_inv_naturality {X X' : C} (f : X ⟶ X') :
    f ≫ (ρ_ X').inv = (ρ_ X).inv ≫ (f ⊗ 𝟙 _) := by simp
#align category_theory.monoidal_category.right_unitor_inv_naturality CategoryTheory.MonoidalCategory.rightUnitor_inv_naturality
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.tensor_left_iff /-
theorem tensor_left_iff {X Y : C} (f g : X ⟶ Y) : 𝟙 (𝟙_ C) ⊗ f = 𝟙 (𝟙_ C) ⊗ g ↔ f = g := by simp
#align category_theory.monoidal_category.tensor_left_iff CategoryTheory.MonoidalCategory.tensor_left_iff
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.tensor_right_iff /-
theorem tensor_right_iff {X Y : C} (f g : X ⟶ Y) : f ⊗ 𝟙 (𝟙_ C) = g ⊗ 𝟙 (𝟙_ C) ↔ f = g := by simp
#align category_theory.monoidal_category.tensor_right_iff CategoryTheory.MonoidalCategory.tensor_right_iff
-/

/-! The lemmas in the next section are true by coherence,
but we prove them directly as they are used in proving the coherence theorem. -/


section

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.pentagon_inv /-
@[reassoc.1]
theorem pentagon_inv (W X Y Z : C) :
    (𝟙 W ⊗ (α_ X Y Z).inv) ≫ (α_ W (X ⊗ Y) Z).inv ≫ ((α_ W X Y).inv ⊗ 𝟙 Z) =
      (α_ W X (Y ⊗ Z)).inv ≫ (α_ (W ⊗ X) Y Z).inv :=
  CategoryTheory.eq_of_inv_eq_inv (by simp [pentagon])
#align category_theory.monoidal_category.pentagon_inv CategoryTheory.MonoidalCategory.pentagon_inv
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.rightUnitor_tensor /-
@[reassoc.1, simp]
theorem rightUnitor_tensor (X Y : C) :
    (ρ_ (X ⊗ Y)).Hom = (α_ X Y (𝟙_ C)).Hom ≫ (𝟙 X ⊗ (ρ_ Y).Hom) := by
  rw [← tensor_right_iff, comp_tensor_id, ← cancel_mono (α_ X Y (𝟙_ C)).Hom, assoc,
    associator_naturality, ← triangle_assoc, ← triangle, id_tensor_comp, pentagon_assoc, ←
    associator_naturality, tensor_id]
#align category_theory.monoidal_category.right_unitor_tensor CategoryTheory.MonoidalCategory.rightUnitor_tensor
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.rightUnitor_tensor_inv /-
@[reassoc.1, simp]
theorem rightUnitor_tensor_inv (X Y : C) :
    (ρ_ (X ⊗ Y)).inv = (𝟙 X ⊗ (ρ_ Y).inv) ≫ (α_ X Y (𝟙_ C)).inv :=
  eq_of_inv_eq_inv (by simp)
#align category_theory.monoidal_category.right_unitor_tensor_inv CategoryTheory.MonoidalCategory.rightUnitor_tensor_inv
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.triangle_assoc_comp_right /-
@[simp, reassoc.1]
theorem triangle_assoc_comp_right (X Y : C) :
    (α_ X (𝟙_ C) Y).inv ≫ ((ρ_ X).Hom ⊗ 𝟙 Y) = 𝟙 X ⊗ (λ_ Y).Hom := by
  rw [← triangle, iso.inv_hom_id_assoc]
#align category_theory.monoidal_category.triangle_assoc_comp_right CategoryTheory.MonoidalCategory.triangle_assoc_comp_right
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.triangle_assoc_comp_left_inv /-
@[simp, reassoc.1]
theorem triangle_assoc_comp_left_inv (X Y : C) :
    (𝟙 X ⊗ (λ_ Y).inv) ≫ (α_ X (𝟙_ C) Y).inv = (ρ_ X).inv ⊗ 𝟙 Y :=
  by
  apply (cancel_mono ((ρ_ X).Hom ⊗ 𝟙 Y)).1
  simp only [triangle_assoc_comp_right, assoc]
  rw [← id_tensor_comp, iso.inv_hom_id, ← comp_tensor_id, iso.inv_hom_id]
#align category_theory.monoidal_category.triangle_assoc_comp_left_inv CategoryTheory.MonoidalCategory.triangle_assoc_comp_left_inv
-/

end

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.associator_inv_naturality /-
@[reassoc.1]
theorem associator_inv_naturality {X Y Z X' Y' Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    (f ⊗ g ⊗ h) ≫ (α_ X' Y' Z').inv = (α_ X Y Z).inv ≫ ((f ⊗ g) ⊗ h) :=
  by
  rw [comp_inv_eq, assoc, associator_naturality]
  simp
#align category_theory.monoidal_category.associator_inv_naturality CategoryTheory.MonoidalCategory.associator_inv_naturality
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.associator_conjugation /-
@[reassoc.1, simp]
theorem associator_conjugation {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    (f ⊗ g) ⊗ h = (α_ X Y Z).Hom ≫ (f ⊗ g ⊗ h) ≫ (α_ X' Y' Z').inv := by
  rw [associator_inv_naturality, hom_inv_id_assoc]
#align category_theory.monoidal_category.associator_conjugation CategoryTheory.MonoidalCategory.associator_conjugation
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.associator_inv_conjugation /-
@[reassoc.1]
theorem associator_inv_conjugation {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    f ⊗ g ⊗ h = (α_ X Y Z).inv ≫ ((f ⊗ g) ⊗ h) ≫ (α_ X' Y' Z').Hom := by
  rw [associator_naturality, inv_hom_id_assoc]
#align category_theory.monoidal_category.associator_inv_conjugation CategoryTheory.MonoidalCategory.associator_inv_conjugation
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.id_tensor_associator_naturality /-
-- TODO these next two lemmas aren't so fundamental, and perhaps could be removed
-- (replacing their usages by their proofs).
@[reassoc.1]
theorem id_tensor_associator_naturality {X Y Z Z' : C} (h : Z ⟶ Z') :
    (𝟙 (X ⊗ Y) ⊗ h) ≫ (α_ X Y Z').Hom = (α_ X Y Z).Hom ≫ (𝟙 X ⊗ 𝟙 Y ⊗ h) := by
  rw [← tensor_id, associator_naturality]
#align category_theory.monoidal_category.id_tensor_associator_naturality CategoryTheory.MonoidalCategory.id_tensor_associator_naturality
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.id_tensor_associator_inv_naturality /-
@[reassoc.1]
theorem id_tensor_associator_inv_naturality {X Y Z X' : C} (f : X ⟶ X') :
    (f ⊗ 𝟙 (Y ⊗ Z)) ≫ (α_ X' Y Z).inv = (α_ X Y Z).inv ≫ ((f ⊗ 𝟙 Y) ⊗ 𝟙 Z) := by
  rw [← tensor_id, associator_inv_naturality]
#align category_theory.monoidal_category.id_tensor_associator_inv_naturality CategoryTheory.MonoidalCategory.id_tensor_associator_inv_naturality
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.hom_inv_id_tensor /-
@[simp, reassoc.1]
theorem hom_inv_id_tensor {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f.Hom ⊗ g) ≫ (f.inv ⊗ h) = (𝟙 V ⊗ g) ≫ (𝟙 V ⊗ h) := by
  rw [← tensor_comp, f.hom_inv_id, id_tensor_comp]
#align category_theory.monoidal_category.hom_inv_id_tensor CategoryTheory.MonoidalCategory.hom_inv_id_tensor
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.inv_hom_id_tensor /-
@[simp, reassoc.1]
theorem inv_hom_id_tensor {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f.inv ⊗ g) ≫ (f.Hom ⊗ h) = (𝟙 W ⊗ g) ≫ (𝟙 W ⊗ h) := by
  rw [← tensor_comp, f.inv_hom_id, id_tensor_comp]
#align category_theory.monoidal_category.inv_hom_id_tensor CategoryTheory.MonoidalCategory.inv_hom_id_tensor
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.tensorHom_inv_id /-
@[simp, reassoc.1]
theorem tensorHom_inv_id {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ f.Hom) ≫ (h ⊗ f.inv) = (g ⊗ 𝟙 V) ≫ (h ⊗ 𝟙 V) := by
  rw [← tensor_comp, f.hom_inv_id, comp_tensor_id]
#align category_theory.monoidal_category.tensor_hom_inv_id CategoryTheory.MonoidalCategory.tensorHom_inv_id
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.tensor_inv_hom_id /-
@[simp, reassoc.1]
theorem tensor_inv_hom_id {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ f.inv) ≫ (h ⊗ f.Hom) = (g ⊗ 𝟙 W) ≫ (h ⊗ 𝟙 W) := by
  rw [← tensor_comp, f.inv_hom_id, comp_tensor_id]
#align category_theory.monoidal_category.tensor_inv_hom_id CategoryTheory.MonoidalCategory.tensor_inv_hom_id
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.hom_inv_id_tensor' /-
@[simp, reassoc.1]
theorem hom_inv_id_tensor' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f ⊗ g) ≫ (inv f ⊗ h) = (𝟙 V ⊗ g) ≫ (𝟙 V ⊗ h) := by
  rw [← tensor_comp, is_iso.hom_inv_id, id_tensor_comp]
#align category_theory.monoidal_category.hom_inv_id_tensor' CategoryTheory.MonoidalCategory.hom_inv_id_tensor'
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.inv_hom_id_tensor' /-
@[simp, reassoc.1]
theorem inv_hom_id_tensor' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (inv f ⊗ g) ≫ (f ⊗ h) = (𝟙 W ⊗ g) ≫ (𝟙 W ⊗ h) := by
  rw [← tensor_comp, is_iso.inv_hom_id, id_tensor_comp]
#align category_theory.monoidal_category.inv_hom_id_tensor' CategoryTheory.MonoidalCategory.inv_hom_id_tensor'
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.tensorHom_inv_id' /-
@[simp, reassoc.1]
theorem tensorHom_inv_id' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ f) ≫ (h ⊗ inv f) = (g ⊗ 𝟙 V) ≫ (h ⊗ 𝟙 V) := by
  rw [← tensor_comp, is_iso.hom_inv_id, comp_tensor_id]
#align category_theory.monoidal_category.tensor_hom_inv_id' CategoryTheory.MonoidalCategory.tensorHom_inv_id'
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.tensor_inv_hom_id' /-
@[simp, reassoc.1]
theorem tensor_inv_hom_id' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ inv f) ≫ (h ⊗ f) = (g ⊗ 𝟙 W) ≫ (h ⊗ 𝟙 W) := by
  rw [← tensor_comp, is_iso.inv_hom_id, comp_tensor_id]
#align category_theory.monoidal_category.tensor_inv_hom_id' CategoryTheory.MonoidalCategory.tensor_inv_hom_id'
-/

end

section

variable (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.tensor /-
/-- The tensor product expressed as a functor. -/
@[simps]
def tensor : C × C ⥤ C where
  obj X := X.1 ⊗ X.2
  map {X Y : C × C} (f : X ⟶ Y) := f.1 ⊗ f.2
#align category_theory.monoidal_category.tensor CategoryTheory.MonoidalCategory.tensor
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.leftAssocTensor /-
/-- The left-associated triple tensor product as a functor. -/
def leftAssocTensor : C × C × C ⥤ C
    where
  obj X := (X.1 ⊗ X.2.1) ⊗ X.2.2
  map {X Y : C × C × C} (f : X ⟶ Y) := (f.1 ⊗ f.2.1) ⊗ f.2.2
#align category_theory.monoidal_category.left_assoc_tensor CategoryTheory.MonoidalCategory.leftAssocTensor
-/

/- warning: category_theory.monoidal_category.left_assoc_tensor_obj -> CategoryTheory.MonoidalCategory.leftAssocTensor_obj is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.MonoidalCategory.{u1, u2} C _inst_1] (X : Prod.{u2, u2} C (Prod.{u2, u2} C C)), Eq.{succ u2} C (CategoryTheory.Functor.obj.{u1, u1, u2, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1)) C _inst_1 (CategoryTheory.MonoidalCategory.leftAssocTensor.{u1, u2} C _inst_1 _inst_2) X) (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) X) (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X))) (Prod.snd.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X)))
but is expected to have type
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.MonoidalCategory.{u1, u2} C _inst_1] (X : Prod.{u2, u2} C (Prod.{u2, u2} C C)), Eq.{succ u2} C (Prefunctor.obj.{succ u1, succ u1, u2, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1)))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1)) C _inst_1 (CategoryTheory.MonoidalCategory.leftAssocTensor.{u1, u2} C _inst_1 _inst_2)) X) (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) X) (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X))) (Prod.snd.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X)))
Case conversion may be inaccurate. Consider using '#align category_theory.monoidal_category.left_assoc_tensor_obj CategoryTheory.MonoidalCategory.leftAssocTensor_objₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem leftAssocTensor_obj (X) : (leftAssocTensor C).obj X = (X.1 ⊗ X.2.1) ⊗ X.2.2 :=
  rfl
#align category_theory.monoidal_category.left_assoc_tensor_obj CategoryTheory.MonoidalCategory.leftAssocTensor_obj

/- warning: category_theory.monoidal_category.left_assoc_tensor_map -> CategoryTheory.MonoidalCategory.leftAssocTensor_map is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.MonoidalCategory.{u1, u2} C _inst_1] {X : Prod.{u2, u2} C (Prod.{u2, u2} C C)} {Y : Prod.{u2, u2} C (Prod.{u2, u2} C C)} (f : Quiver.Hom.{succ u1, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1)))) X Y), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1)) C _inst_1 (CategoryTheory.MonoidalCategory.leftAssocTensor.{u1, u2} C _inst_1 _inst_2) X) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1)) C _inst_1 (CategoryTheory.MonoidalCategory.leftAssocTensor.{u1, u2} C _inst_1 _inst_2) Y)) (CategoryTheory.Functor.map.{u1, u1, u2, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1)) C _inst_1 (CategoryTheory.MonoidalCategory.leftAssocTensor.{u1, u2} C _inst_1 _inst_2) X Y f) (CategoryTheory.MonoidalCategory.tensorHom.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) X) (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X))) (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) Y) (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y))) (Prod.snd.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X)) (Prod.snd.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y)) (CategoryTheory.MonoidalCategory.tensorHom.{u1, u2} C _inst_1 _inst_2 (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) X) (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) Y) (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X)) (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y)) (Prod.fst.{u1, u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) X) (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) Y)) (Quiver.Hom.{succ u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1))) (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X) (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y)) f) (Prod.fst.{u1, u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X)) (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y))) (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prod.snd.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X)) (Prod.snd.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y))) (Prod.snd.{u1, u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) X) (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) Y)) (Quiver.Hom.{succ u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1))) (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X) (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y)) f))) (Prod.snd.{u1, u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X)) (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y))) (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prod.snd.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X)) (Prod.snd.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y))) (Prod.snd.{u1, u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) X) (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) Y)) (Quiver.Hom.{succ u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1))) (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X) (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y)) f)))
but is expected to have type
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.MonoidalCategory.{u1, u2} C _inst_1] {X : Prod.{u2, u2} C (Prod.{u2, u2} C C)} {Y : Prod.{u2, u2} C (Prod.{u2, u2} C C)} (f : Quiver.Hom.{succ u1, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1)))) X Y), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{succ u1, succ u1, u2, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1)))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1)) C _inst_1 (CategoryTheory.MonoidalCategory.leftAssocTensor.{u1, u2} C _inst_1 _inst_2)) X) (Prefunctor.obj.{succ u1, succ u1, u2, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1)))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1)) C _inst_1 (CategoryTheory.MonoidalCategory.leftAssocTensor.{u1, u2} C _inst_1 _inst_2)) Y)) (Prefunctor.map.{succ u1, succ u1, u2, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1)))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1)) C _inst_1 (CategoryTheory.MonoidalCategory.leftAssocTensor.{u1, u2} C _inst_1 _inst_2)) X Y f) (CategoryTheory.MonoidalCategory.tensorHom.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) X) (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X))) (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) Y) (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y))) (Prod.snd.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X)) (Prod.snd.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y)) (CategoryTheory.MonoidalCategory.tensorHom.{u1, u2} C _inst_1 _inst_2 (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) X) (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) Y) (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X)) (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y)) (Prod.fst.{u1, u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) X) (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) Y)) (Quiver.Hom.{succ u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1))) (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X) (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y)) f) (Prod.fst.{u1, u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X)) (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y))) (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prod.snd.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X)) (Prod.snd.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y))) (Prod.snd.{u1, u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) X) (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) Y)) (Quiver.Hom.{succ u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1))) (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X) (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y)) f))) (Prod.snd.{u1, u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X)) (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y))) (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prod.snd.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X)) (Prod.snd.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y))) (Prod.snd.{u1, u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) X) (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) Y)) (Quiver.Hom.{succ u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1))) (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X) (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y)) f)))
Case conversion may be inaccurate. Consider using '#align category_theory.monoidal_category.left_assoc_tensor_map CategoryTheory.MonoidalCategory.leftAssocTensor_mapₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem leftAssocTensor_map {X Y} (f : X ⟶ Y) : (leftAssocTensor C).map f = (f.1 ⊗ f.2.1) ⊗ f.2.2 :=
  rfl
#align category_theory.monoidal_category.left_assoc_tensor_map CategoryTheory.MonoidalCategory.leftAssocTensor_map

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.rightAssocTensor /-
/-- The right-associated triple tensor product as a functor. -/
def rightAssocTensor : C × C × C ⥤ C
    where
  obj X := X.1 ⊗ X.2.1 ⊗ X.2.2
  map {X Y : C × C × C} (f : X ⟶ Y) := f.1 ⊗ f.2.1 ⊗ f.2.2
#align category_theory.monoidal_category.right_assoc_tensor CategoryTheory.MonoidalCategory.rightAssocTensor
-/

/- warning: category_theory.monoidal_category.right_assoc_tensor_obj -> CategoryTheory.MonoidalCategory.rightAssocTensor_obj is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.MonoidalCategory.{u1, u2} C _inst_1] (X : Prod.{u2, u2} C (Prod.{u2, u2} C C)), Eq.{succ u2} C (CategoryTheory.Functor.obj.{u1, u1, u2, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1)) C _inst_1 (CategoryTheory.MonoidalCategory.rightAssocTensor.{u1, u2} C _inst_1 _inst_2) X) (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) X) (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X)) (Prod.snd.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X))))
but is expected to have type
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.MonoidalCategory.{u1, u2} C _inst_1] (X : Prod.{u2, u2} C (Prod.{u2, u2} C C)), Eq.{succ u2} C (Prefunctor.obj.{succ u1, succ u1, u2, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1)))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1)) C _inst_1 (CategoryTheory.MonoidalCategory.rightAssocTensor.{u1, u2} C _inst_1 _inst_2)) X) (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) X) (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X)) (Prod.snd.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X))))
Case conversion may be inaccurate. Consider using '#align category_theory.monoidal_category.right_assoc_tensor_obj CategoryTheory.MonoidalCategory.rightAssocTensor_objₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem rightAssocTensor_obj (X) : (rightAssocTensor C).obj X = X.1 ⊗ X.2.1 ⊗ X.2.2 :=
  rfl
#align category_theory.monoidal_category.right_assoc_tensor_obj CategoryTheory.MonoidalCategory.rightAssocTensor_obj

/- warning: category_theory.monoidal_category.right_assoc_tensor_map -> CategoryTheory.MonoidalCategory.rightAssocTensor_map is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.MonoidalCategory.{u1, u2} C _inst_1] {X : Prod.{u2, u2} C (Prod.{u2, u2} C C)} {Y : Prod.{u2, u2} C (Prod.{u2, u2} C C)} (f : Quiver.Hom.{succ u1, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1)))) X Y), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1)) C _inst_1 (CategoryTheory.MonoidalCategory.rightAssocTensor.{u1, u2} C _inst_1 _inst_2) X) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1)) C _inst_1 (CategoryTheory.MonoidalCategory.rightAssocTensor.{u1, u2} C _inst_1 _inst_2) Y)) (CategoryTheory.Functor.map.{u1, u1, u2, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1)) C _inst_1 (CategoryTheory.MonoidalCategory.rightAssocTensor.{u1, u2} C _inst_1 _inst_2) X Y f) (CategoryTheory.MonoidalCategory.tensorHom.{u1, u2} C _inst_1 _inst_2 (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) X) (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) Y) (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X)) (Prod.snd.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X))) (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y)) (Prod.snd.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y))) (Prod.fst.{u1, u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) X) (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) Y)) (Quiver.Hom.{succ u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1))) (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X) (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y)) f) (CategoryTheory.MonoidalCategory.tensorHom.{u1, u2} C _inst_1 _inst_2 (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X)) (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y)) (Prod.snd.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X)) (Prod.snd.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y)) (Prod.fst.{u1, u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X)) (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y))) (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prod.snd.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X)) (Prod.snd.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y))) (Prod.snd.{u1, u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) X) (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) Y)) (Quiver.Hom.{succ u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1))) (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X) (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y)) f)) (Prod.snd.{u1, u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X)) (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y))) (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prod.snd.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X)) (Prod.snd.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y))) (Prod.snd.{u1, u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) X) (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) Y)) (Quiver.Hom.{succ u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1))) (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X) (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y)) f))))
but is expected to have type
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.MonoidalCategory.{u1, u2} C _inst_1] {X : Prod.{u2, u2} C (Prod.{u2, u2} C C)} {Y : Prod.{u2, u2} C (Prod.{u2, u2} C C)} (f : Quiver.Hom.{succ u1, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1)))) X Y), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{succ u1, succ u1, u2, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1)))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1)) C _inst_1 (CategoryTheory.MonoidalCategory.rightAssocTensor.{u1, u2} C _inst_1 _inst_2)) X) (Prefunctor.obj.{succ u1, succ u1, u2, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1)))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1)) C _inst_1 (CategoryTheory.MonoidalCategory.rightAssocTensor.{u1, u2} C _inst_1 _inst_2)) Y)) (Prefunctor.map.{succ u1, succ u1, u2, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1)))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} (Prod.{u2, u2} C (Prod.{u2, u2} C C)) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1)) C _inst_1 (CategoryTheory.MonoidalCategory.rightAssocTensor.{u1, u2} C _inst_1 _inst_2)) X Y f) (CategoryTheory.MonoidalCategory.tensorHom.{u1, u2} C _inst_1 _inst_2 (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) X) (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) Y) (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X)) (Prod.snd.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X))) (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y)) (Prod.snd.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y))) (Prod.fst.{u1, u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) X) (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) Y)) (Quiver.Hom.{succ u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1))) (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X) (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y)) f) (CategoryTheory.MonoidalCategory.tensorHom.{u1, u2} C _inst_1 _inst_2 (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X)) (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y)) (Prod.snd.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X)) (Prod.snd.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y)) (Prod.fst.{u1, u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X)) (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y))) (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prod.snd.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X)) (Prod.snd.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y))) (Prod.snd.{u1, u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) X) (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) Y)) (Quiver.Hom.{succ u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1))) (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X) (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y)) f)) (Prod.snd.{u1, u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X)) (Prod.fst.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y))) (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prod.snd.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X)) (Prod.snd.{u2, u2} C C (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y))) (Prod.snd.{u1, u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) X) (Prod.fst.{u2, u2} C (Prod.{u2, u2} C C) Y)) (Quiver.Hom.{succ u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Prod.{u2, u2} C C) (CategoryTheory.uniformProd.{u1, u2} C _inst_1 C _inst_1))) (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) X) (Prod.snd.{u2, u2} C (Prod.{u2, u2} C C) Y)) f))))
Case conversion may be inaccurate. Consider using '#align category_theory.monoidal_category.right_assoc_tensor_map CategoryTheory.MonoidalCategory.rightAssocTensor_mapₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem rightAssocTensor_map {X Y} (f : X ⟶ Y) : (rightAssocTensor C).map f = f.1 ⊗ f.2.1 ⊗ f.2.2 :=
  rfl
#align category_theory.monoidal_category.right_assoc_tensor_map CategoryTheory.MonoidalCategory.rightAssocTensor_map

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.tensorUnitLeft /-
/-- The functor `λ X, 𝟙_ C ⊗ X`. -/
def tensorUnitLeft : C ⥤ C where
  obj X := 𝟙_ C ⊗ X
  map {X Y : C} (f : X ⟶ Y) := 𝟙 (𝟙_ C) ⊗ f
#align category_theory.monoidal_category.tensor_unit_left CategoryTheory.MonoidalCategory.tensorUnitLeft
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.tensorUnitRight /-
/-- The functor `λ X, X ⊗ 𝟙_ C`. -/
def tensorUnitRight : C ⥤ C where
  obj X := X ⊗ 𝟙_ C
  map {X Y : C} (f : X ⟶ Y) := f ⊗ 𝟙 (𝟙_ C)
#align category_theory.monoidal_category.tensor_unit_right CategoryTheory.MonoidalCategory.tensorUnitRight
-/

#print CategoryTheory.MonoidalCategory.associatorNatIso /-
-- We can express the associator and the unitors, given componentwise above,
-- as natural isomorphisms.
/-- The associator as a natural isomorphism. -/
@[simps]
def associatorNatIso : leftAssocTensor C ≅ rightAssocTensor C :=
  NatIso.ofComponents
    (by
      intros
      apply monoidal_category.associator)
    (by
      intros
      apply monoidal_category.associator_naturality)
#align category_theory.monoidal_category.associator_nat_iso CategoryTheory.MonoidalCategory.associatorNatIso
-/

#print CategoryTheory.MonoidalCategory.leftUnitorNatIso /-
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
#align category_theory.monoidal_category.left_unitor_nat_iso CategoryTheory.MonoidalCategory.leftUnitorNatIso
-/

#print CategoryTheory.MonoidalCategory.rightUnitorNatIso /-
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
#align category_theory.monoidal_category.right_unitor_nat_iso CategoryTheory.MonoidalCategory.rightUnitorNatIso
-/

section

variable {C}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.tensorLeft /-
/-- Tensoring on the left with a fixed object, as a functor. -/
@[simps]
def tensorLeft (X : C) : C ⥤ C where
  obj Y := X ⊗ Y
  map Y Y' f := 𝟙 X ⊗ f
#align category_theory.monoidal_category.tensor_left CategoryTheory.MonoidalCategory.tensorLeft
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.tensorLeftTensor /-
/-- Tensoring on the left with `X ⊗ Y` is naturally isomorphic to
tensoring on the left with `Y`, and then again with `X`.
-/
def tensorLeftTensor (X Y : C) : tensorLeft (X ⊗ Y) ≅ tensorLeft Y ⋙ tensorLeft X :=
  NatIso.ofComponents (associator _ _) fun Z Z' f =>
    by
    dsimp
    rw [← tensor_id]
    apply associator_naturality
#align category_theory.monoidal_category.tensor_left_tensor CategoryTheory.MonoidalCategory.tensorLeftTensor
-/

/- warning: category_theory.monoidal_category.tensor_left_tensor_hom_app -> CategoryTheory.MonoidalCategory.tensorLeftTensor_hom_app is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.MonoidalCategory.{u1, u2} C _inst_1] (X : C) (Y : C) (Z : C), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X Y)) Z) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.comp.{u1, u1, u1, u2, u2, u2} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 Y) (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 X)) Z)) (CategoryTheory.NatTrans.app.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X Y)) (CategoryTheory.Functor.comp.{u1, u1, u1, u2, u2, u2} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 Y) (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 X)) (CategoryTheory.Iso.hom.{max u2 u1, max u1 u2} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X Y)) (CategoryTheory.Functor.comp.{u1, u1, u1, u2, u2, u2} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 Y) (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 X)) (CategoryTheory.MonoidalCategory.tensorLeftTensor.{u1, u2} C _inst_1 _inst_2 X Y)) Z) (CategoryTheory.Iso.hom.{u1, u2} C _inst_1 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X Y) Z) (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 Y Z)) (CategoryTheory.MonoidalCategory.associator.{u1, u2} C _inst_1 _inst_2 X Y Z))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.MonoidalCategory.{u1, u2} C _inst_1] (X : C) (Y : C) (Z : C), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X Y))) Z) (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.comp.{u1, u1, u1, u2, u2, u2} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 Y) (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 X))) Z)) (CategoryTheory.NatTrans.app.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X Y)) (CategoryTheory.Functor.comp.{u1, u1, u1, u2, u2, u2} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 Y) (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 X)) (CategoryTheory.Iso.hom.{max u2 u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X Y)) (CategoryTheory.Functor.comp.{u1, u1, u1, u2, u2, u2} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 Y) (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 X)) (CategoryTheory.MonoidalCategory.tensorLeftTensor.{u1, u2} C _inst_1 _inst_2 X Y)) Z) (CategoryTheory.Iso.hom.{u1, u2} C _inst_1 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X Y) Z) (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 Y Z)) (CategoryTheory.MonoidalCategory.associator.{u1, u2} C _inst_1 _inst_2 X Y Z))
Case conversion may be inaccurate. Consider using '#align category_theory.monoidal_category.tensor_left_tensor_hom_app CategoryTheory.MonoidalCategory.tensorLeftTensor_hom_appₓ'. -/
@[simp]
theorem tensorLeftTensor_hom_app (X Y Z : C) :
    (tensorLeftTensor X Y).Hom.app Z = (associator X Y Z).Hom :=
  rfl
#align category_theory.monoidal_category.tensor_left_tensor_hom_app CategoryTheory.MonoidalCategory.tensorLeftTensor_hom_app

/- warning: category_theory.monoidal_category.tensor_left_tensor_inv_app -> CategoryTheory.MonoidalCategory.tensorLeftTensor_inv_app is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.MonoidalCategory.{u1, u2} C _inst_1] (X : C) (Y : C) (Z : C), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.comp.{u1, u1, u1, u2, u2, u2} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 Y) (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 X)) Z) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X Y)) Z)) (CategoryTheory.NatTrans.app.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.comp.{u1, u1, u1, u2, u2, u2} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 Y) (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 X)) (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X Y)) (CategoryTheory.Iso.inv.{max u2 u1, max u1 u2} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X Y)) (CategoryTheory.Functor.comp.{u1, u1, u1, u2, u2, u2} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 Y) (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 X)) (CategoryTheory.MonoidalCategory.tensorLeftTensor.{u1, u2} C _inst_1 _inst_2 X Y)) Z) (CategoryTheory.Iso.inv.{u1, u2} C _inst_1 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X Y) Z) (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 Y Z)) (CategoryTheory.MonoidalCategory.associator.{u1, u2} C _inst_1 _inst_2 X Y Z))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.MonoidalCategory.{u1, u2} C _inst_1] (X : C) (Y : C) (Z : C), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.comp.{u1, u1, u1, u2, u2, u2} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 Y) (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 X))) Z) (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X Y))) Z)) (CategoryTheory.NatTrans.app.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.comp.{u1, u1, u1, u2, u2, u2} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 Y) (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 X)) (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X Y)) (CategoryTheory.Iso.inv.{max u2 u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X Y)) (CategoryTheory.Functor.comp.{u1, u1, u1, u2, u2, u2} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 Y) (CategoryTheory.MonoidalCategory.tensorLeft.{u1, u2} C _inst_1 _inst_2 X)) (CategoryTheory.MonoidalCategory.tensorLeftTensor.{u1, u2} C _inst_1 _inst_2 X Y)) Z) (CategoryTheory.Iso.inv.{u1, u2} C _inst_1 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X Y) Z) (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 Y Z)) (CategoryTheory.MonoidalCategory.associator.{u1, u2} C _inst_1 _inst_2 X Y Z))
Case conversion may be inaccurate. Consider using '#align category_theory.monoidal_category.tensor_left_tensor_inv_app CategoryTheory.MonoidalCategory.tensorLeftTensor_inv_appₓ'. -/
@[simp]
theorem tensorLeftTensor_inv_app (X Y Z : C) :
    (tensorLeftTensor X Y).inv.app Z = (associator X Y Z).inv := by simp [tensor_left_tensor]
#align category_theory.monoidal_category.tensor_left_tensor_inv_app CategoryTheory.MonoidalCategory.tensorLeftTensor_inv_app

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.tensorRight /-
/-- Tensoring on the right with a fixed object, as a functor. -/
@[simps]
def tensorRight (X : C) : C ⥤ C where
  obj Y := Y ⊗ X
  map Y Y' f := f ⊗ 𝟙 X
#align category_theory.monoidal_category.tensor_right CategoryTheory.MonoidalCategory.tensorRight
-/

variable (C)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.tensoringLeft /-
/-- Tensoring on the left, as a functor from `C` into endofunctors of `C`.

TODO: show this is a op-monoidal functor.
-/
@[simps]
def tensoringLeft : C ⥤ C ⥤ C where
  obj := tensorLeft
  map X Y f := { app := fun Z => f ⊗ 𝟙 Z }
#align category_theory.monoidal_category.tensoring_left CategoryTheory.MonoidalCategory.tensoringLeft
-/

instance : Faithful (tensoringLeft C)
    where map_injective' X Y f g h := by
    injections h
    replace h := congr_fun h (𝟙_ C)
    simpa using h

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.tensoringRight /-
/-- Tensoring on the right, as a functor from `C` into endofunctors of `C`.

We later show this is a monoidal functor.
-/
@[simps]
def tensoringRight : C ⥤ C ⥤ C where
  obj := tensorRight
  map X Y f := { app := fun Z => 𝟙 Z ⊗ f }
#align category_theory.monoidal_category.tensoring_right CategoryTheory.MonoidalCategory.tensoringRight
-/

instance : Faithful (tensoringRight C)
    where map_injective' X Y f g h := by
    injections h
    replace h := congr_fun h (𝟙_ C)
    simpa using h

variable {C}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.tensorRightTensor /-
/-- Tensoring on the right with `X ⊗ Y` is naturally isomorphic to
tensoring on the right with `X`, and then again with `Y`.
-/
def tensorRightTensor (X Y : C) : tensorRight (X ⊗ Y) ≅ tensorRight X ⋙ tensorRight Y :=
  NatIso.ofComponents (fun Z => (associator Z X Y).symm) fun Z Z' f =>
    by
    dsimp
    rw [← tensor_id]
    apply associator_inv_naturality
#align category_theory.monoidal_category.tensor_right_tensor CategoryTheory.MonoidalCategory.tensorRightTensor
-/

/- warning: category_theory.monoidal_category.tensor_right_tensor_hom_app -> CategoryTheory.MonoidalCategory.tensorRightTensor_hom_app is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.MonoidalCategory.{u1, u2} C _inst_1] (X : C) (Y : C) (Z : C), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X Y)) Z) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.comp.{u1, u1, u1, u2, u2, u2} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 X) (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 Y)) Z)) (CategoryTheory.NatTrans.app.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X Y)) (CategoryTheory.Functor.comp.{u1, u1, u1, u2, u2, u2} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 X) (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 Y)) (CategoryTheory.Iso.hom.{max u2 u1, max u1 u2} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X Y)) (CategoryTheory.Functor.comp.{u1, u1, u1, u2, u2, u2} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 X) (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 Y)) (CategoryTheory.MonoidalCategory.tensorRightTensor.{u1, u2} C _inst_1 _inst_2 X Y)) Z) (CategoryTheory.Iso.inv.{u1, u2} C _inst_1 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 Z X) Y) (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 Z (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X Y)) (CategoryTheory.MonoidalCategory.associator.{u1, u2} C _inst_1 _inst_2 Z X Y))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.MonoidalCategory.{u1, u2} C _inst_1] (X : C) (Y : C) (Z : C), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X Y))) Z) (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.comp.{u1, u1, u1, u2, u2, u2} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 X) (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 Y))) Z)) (CategoryTheory.NatTrans.app.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X Y)) (CategoryTheory.Functor.comp.{u1, u1, u1, u2, u2, u2} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 X) (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 Y)) (CategoryTheory.Iso.hom.{max u2 u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X Y)) (CategoryTheory.Functor.comp.{u1, u1, u1, u2, u2, u2} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 X) (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 Y)) (CategoryTheory.MonoidalCategory.tensorRightTensor.{u1, u2} C _inst_1 _inst_2 X Y)) Z) (CategoryTheory.Iso.inv.{u1, u2} C _inst_1 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 Z X) Y) (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 Z (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X Y)) (CategoryTheory.MonoidalCategory.associator.{u1, u2} C _inst_1 _inst_2 Z X Y))
Case conversion may be inaccurate. Consider using '#align category_theory.monoidal_category.tensor_right_tensor_hom_app CategoryTheory.MonoidalCategory.tensorRightTensor_hom_appₓ'. -/
@[simp]
theorem tensorRightTensor_hom_app (X Y Z : C) :
    (tensorRightTensor X Y).Hom.app Z = (associator Z X Y).inv :=
  rfl
#align category_theory.monoidal_category.tensor_right_tensor_hom_app CategoryTheory.MonoidalCategory.tensorRightTensor_hom_app

/- warning: category_theory.monoidal_category.tensor_right_tensor_inv_app -> CategoryTheory.MonoidalCategory.tensorRightTensor_inv_app is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.MonoidalCategory.{u1, u2} C _inst_1] (X : C) (Y : C) (Z : C), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.comp.{u1, u1, u1, u2, u2, u2} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 X) (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 Y)) Z) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X Y)) Z)) (CategoryTheory.NatTrans.app.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.comp.{u1, u1, u1, u2, u2, u2} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 X) (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 Y)) (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X Y)) (CategoryTheory.Iso.inv.{max u2 u1, max u1 u2} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X Y)) (CategoryTheory.Functor.comp.{u1, u1, u1, u2, u2, u2} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 X) (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 Y)) (CategoryTheory.MonoidalCategory.tensorRightTensor.{u1, u2} C _inst_1 _inst_2 X Y)) Z) (CategoryTheory.Iso.hom.{u1, u2} C _inst_1 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 Z X) Y) (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 Z (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X Y)) (CategoryTheory.MonoidalCategory.associator.{u1, u2} C _inst_1 _inst_2 Z X Y))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.MonoidalCategory.{u1, u2} C _inst_1] (X : C) (Y : C) (Z : C), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.comp.{u1, u1, u1, u2, u2, u2} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 X) (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 Y))) Z) (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X Y))) Z)) (CategoryTheory.NatTrans.app.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.comp.{u1, u1, u1, u2, u2, u2} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 X) (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 Y)) (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X Y)) (CategoryTheory.Iso.inv.{max u2 u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X Y)) (CategoryTheory.Functor.comp.{u1, u1, u1, u2, u2, u2} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 X) (CategoryTheory.MonoidalCategory.tensorRight.{u1, u2} C _inst_1 _inst_2 Y)) (CategoryTheory.MonoidalCategory.tensorRightTensor.{u1, u2} C _inst_1 _inst_2 X Y)) Z) (CategoryTheory.Iso.hom.{u1, u2} C _inst_1 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 Z X) Y) (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 Z (CategoryTheory.MonoidalCategory.tensorObj.{u1, u2} C _inst_1 _inst_2 X Y)) (CategoryTheory.MonoidalCategory.associator.{u1, u2} C _inst_1 _inst_2 Z X Y))
Case conversion may be inaccurate. Consider using '#align category_theory.monoidal_category.tensor_right_tensor_inv_app CategoryTheory.MonoidalCategory.tensorRightTensor_inv_appₓ'. -/
@[simp]
theorem tensorRightTensor_inv_app (X Y Z : C) :
    (tensorRightTensor X Y).inv.app Z = (associator Z X Y).Hom := by simp [tensor_right_tensor]
#align category_theory.monoidal_category.tensor_right_tensor_inv_app CategoryTheory.MonoidalCategory.tensorRightTensor_inv_app

end

end

section

universe v₁ v₂ u₁ u₂

variable (C₁ : Type u₁) [Category.{v₁} C₁] [MonoidalCategory.{v₁} C₁]

variable (C₂ : Type u₂) [Category.{v₂} C₂] [MonoidalCategory.{v₂} C₂]

attribute [local simp] associator_naturality left_unitor_naturality right_unitor_naturality pentagon

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.prodMonoidal /-
@[simps tensorObj tensorHom tensorUnit associator]
instance prodMonoidal : MonoidalCategory (C₁ × C₂)
    where
  tensorObj X Y := (X.1 ⊗ Y.1, X.2 ⊗ Y.2)
  tensorHom _ _ _ _ f g := (f.1 ⊗ g.1, f.2 ⊗ g.2)
  tensorUnit := (𝟙_ C₁, 𝟙_ C₂)
  associator X Y Z := (α_ X.1 Y.1 Z.1).Prod (α_ X.2 Y.2 Z.2)
  leftUnitor := fun ⟨X₁, X₂⟩ => (λ_ X₁).Prod (λ_ X₂)
  rightUnitor := fun ⟨X₁, X₂⟩ => (ρ_ X₁).Prod (ρ_ X₂)
#align category_theory.monoidal_category.prod_monoidal CategoryTheory.MonoidalCategory.prodMonoidal
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.prodMonoidal_leftUnitor_hom_fst /-
@[simp]
theorem prodMonoidal_leftUnitor_hom_fst (X : C₁ × C₂) :
    ((λ_ X).Hom : 𝟙_ _ ⊗ X ⟶ X).1 = (λ_ X.1).Hom :=
  by
  cases X
  rfl
#align category_theory.monoidal_category.prod_monoidal_left_unitor_hom_fst CategoryTheory.MonoidalCategory.prodMonoidal_leftUnitor_hom_fst
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.prodMonoidal_leftUnitor_hom_snd /-
@[simp]
theorem prodMonoidal_leftUnitor_hom_snd (X : C₁ × C₂) :
    ((λ_ X).Hom : 𝟙_ _ ⊗ X ⟶ X).2 = (λ_ X.2).Hom :=
  by
  cases X
  rfl
#align category_theory.monoidal_category.prod_monoidal_left_unitor_hom_snd CategoryTheory.MonoidalCategory.prodMonoidal_leftUnitor_hom_snd
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.prodMonoidal_leftUnitor_inv_fst /-
@[simp]
theorem prodMonoidal_leftUnitor_inv_fst (X : C₁ × C₂) :
    ((λ_ X).inv : X ⟶ 𝟙_ _ ⊗ X).1 = (λ_ X.1).inv :=
  by
  cases X
  rfl
#align category_theory.monoidal_category.prod_monoidal_left_unitor_inv_fst CategoryTheory.MonoidalCategory.prodMonoidal_leftUnitor_inv_fst
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.prodMonoidal_leftUnitor_inv_snd /-
@[simp]
theorem prodMonoidal_leftUnitor_inv_snd (X : C₁ × C₂) :
    ((λ_ X).inv : X ⟶ 𝟙_ _ ⊗ X).2 = (λ_ X.2).inv :=
  by
  cases X
  rfl
#align category_theory.monoidal_category.prod_monoidal_left_unitor_inv_snd CategoryTheory.MonoidalCategory.prodMonoidal_leftUnitor_inv_snd
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.prodMonoidal_rightUnitor_hom_fst /-
@[simp]
theorem prodMonoidal_rightUnitor_hom_fst (X : C₁ × C₂) :
    ((ρ_ X).Hom : X ⊗ 𝟙_ _ ⟶ X).1 = (ρ_ X.1).Hom :=
  by
  cases X
  rfl
#align category_theory.monoidal_category.prod_monoidal_right_unitor_hom_fst CategoryTheory.MonoidalCategory.prodMonoidal_rightUnitor_hom_fst
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.prodMonoidal_rightUnitor_hom_snd /-
@[simp]
theorem prodMonoidal_rightUnitor_hom_snd (X : C₁ × C₂) :
    ((ρ_ X).Hom : X ⊗ 𝟙_ _ ⟶ X).2 = (ρ_ X.2).Hom :=
  by
  cases X
  rfl
#align category_theory.monoidal_category.prod_monoidal_right_unitor_hom_snd CategoryTheory.MonoidalCategory.prodMonoidal_rightUnitor_hom_snd
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.prodMonoidal_rightUnitor_inv_fst /-
@[simp]
theorem prodMonoidal_rightUnitor_inv_fst (X : C₁ × C₂) :
    ((ρ_ X).inv : X ⟶ X ⊗ 𝟙_ _).1 = (ρ_ X.1).inv :=
  by
  cases X
  rfl
#align category_theory.monoidal_category.prod_monoidal_right_unitor_inv_fst CategoryTheory.MonoidalCategory.prodMonoidal_rightUnitor_inv_fst
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalCategory.prodMonoidal_rightUnitor_inv_snd /-
@[simp]
theorem prodMonoidal_rightUnitor_inv_snd (X : C₁ × C₂) :
    ((ρ_ X).inv : X ⟶ X ⊗ 𝟙_ _).2 = (ρ_ X.2).inv :=
  by
  cases X
  rfl
#align category_theory.monoidal_category.prod_monoidal_right_unitor_inv_snd CategoryTheory.MonoidalCategory.prodMonoidal_rightUnitor_inv_snd
-/

end

end MonoidalCategory

end CategoryTheory

