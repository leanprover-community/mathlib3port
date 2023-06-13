/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Simon Hudon

! This file was ported from Lean 3 source module category_theory.monoidal.of_chosen_finite_products.basic
! leanprover-community/mathlib commit 33c67ae661dd8988516ff7f247b0be3018cdd952
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Monoidal.Category
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Pempty

/-!
# The monoidal structure on a category with chosen finite products.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This is a variant of the development in `category_theory.monoidal.of_has_finite_products`,
which uses specified choices of the terminal object and binary product,
enabling the construction of a cartesian category with specific definitions of the tensor unit
and tensor product.

(Because the construction in `category_theory.monoidal.of_has_finite_products` uses `has_limit`
classes, the actual definitions there are opaque behind `classical.choice`.)

We use this in `category_theory.monoidal.types` to construct the monoidal category of types
so that the tensor product is the usual cartesian product of types.

For now we only do the construction from products, and not from coproducts,
which seems less often useful.
-/


universe v u

noncomputable section

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] {X Y : C}

namespace Limits

section

variable {C}

#print CategoryTheory.Limits.BinaryFan.swap /-
/-- Swap the two sides of a `binary_fan`. -/
def BinaryFan.swap {P Q : C} (t : BinaryFan P Q) : BinaryFan Q P :=
  BinaryFan.mk t.snd t.fst
#align category_theory.limits.binary_fan.swap CategoryTheory.Limits.BinaryFan.swap
-/

#print CategoryTheory.Limits.BinaryFan.swap_fst /-
@[simp]
theorem BinaryFan.swap_fst {P Q : C} (t : BinaryFan P Q) : t.symm.fst = t.snd :=
  rfl
#align category_theory.limits.binary_fan.swap_fst CategoryTheory.Limits.BinaryFan.swap_fst
-/

#print CategoryTheory.Limits.BinaryFan.swap_snd /-
@[simp]
theorem BinaryFan.swap_snd {P Q : C} (t : BinaryFan P Q) : t.symm.snd = t.fst :=
  rfl
#align category_theory.limits.binary_fan.swap_snd CategoryTheory.Limits.BinaryFan.swap_snd
-/

#print CategoryTheory.Limits.IsLimit.swapBinaryFan /-
/-- If a cone `t` over `P Q` is a limit cone, then `t.swap` is a limit cone over `Q P`.
-/
@[simps]
def IsLimit.swapBinaryFan {P Q : C} {t : BinaryFan P Q} (I : IsLimit t) : IsLimit t.symm
    where
  lift s := I.lift (BinaryFan.swap s)
  fac s := by rintro ⟨⟨⟩⟩ <;> simp
  uniq s m w := by
    have h := I.uniq (binary_fan.swap s) m
    rw [h]
    rintro ⟨j⟩
    specialize w ⟨j.swap⟩
    cases j <;> exact w
#align category_theory.limits.is_limit.swap_binary_fan CategoryTheory.Limits.IsLimit.swapBinaryFan
-/

#print CategoryTheory.Limits.HasBinaryProduct.swap /-
/-- Construct `has_binary_product Q P` from `has_binary_product P Q`.
This can't be an instance, as it would cause a loop in typeclass search.
-/
theorem HasBinaryProduct.swap (P Q : C) [HasBinaryProduct P Q] : HasBinaryProduct Q P :=
  HasLimit.mk ⟨BinaryFan.swap (limit.cone (pair P Q)), (limit.isLimit (pair P Q)).swapBinaryFan⟩
#align category_theory.limits.has_binary_product.swap CategoryTheory.Limits.HasBinaryProduct.swap
-/

#print CategoryTheory.Limits.BinaryFan.braiding /-
/-- Given a limit cone over `X` and `Y`, and another limit cone over `Y` and `X`, we can construct
an isomorphism between the cone points. Relative to some fixed choice of limits cones for every
pair, these isomorphisms constitute a braiding.
-/
def BinaryFan.braiding {X Y : C} {s : BinaryFan X Y} (P : IsLimit s) {t : BinaryFan Y X}
    (Q : IsLimit t) : s.pt ≅ t.pt :=
  IsLimit.conePointUniqueUpToIso P Q.swapBinaryFan
#align category_theory.limits.binary_fan.braiding CategoryTheory.Limits.BinaryFan.braiding
-/

#print CategoryTheory.Limits.BinaryFan.assoc /-
/-- Given binary fans `sXY` over `X Y`, and `sYZ` over `Y Z`, and `s` over `sXY.X Z`,
if `sYZ` is a limit cone we can construct a binary fan over `X sYZ.X`.

This is an ingredient of building the associator for a cartesian category.
-/
def BinaryFan.assoc {X Y Z : C} {sXY : BinaryFan X Y} {sYZ : BinaryFan Y Z} (Q : IsLimit sYZ)
    (s : BinaryFan sXY.pt Z) : BinaryFan X sYZ.pt :=
  BinaryFan.mk (s.fst ≫ sXY.fst) (Q.lift (BinaryFan.mk (s.fst ≫ sXY.snd) s.snd))
#align category_theory.limits.binary_fan.assoc CategoryTheory.Limits.BinaryFan.assoc
-/

#print CategoryTheory.Limits.BinaryFan.assoc_fst /-
@[simp]
theorem BinaryFan.assoc_fst {X Y Z : C} {sXY : BinaryFan X Y} {sYZ : BinaryFan Y Z}
    (Q : IsLimit sYZ) (s : BinaryFan sXY.pt Z) : (s.and_assoc Q).fst = s.fst ≫ sXY.fst :=
  rfl
#align category_theory.limits.binary_fan.assoc_fst CategoryTheory.Limits.BinaryFan.assoc_fst
-/

#print CategoryTheory.Limits.BinaryFan.assoc_snd /-
@[simp]
theorem BinaryFan.assoc_snd {X Y Z : C} {sXY : BinaryFan X Y} {sYZ : BinaryFan Y Z}
    (Q : IsLimit sYZ) (s : BinaryFan sXY.pt Z) :
    (s.and_assoc Q).snd = Q.lift (BinaryFan.mk (s.fst ≫ sXY.snd) s.snd) :=
  rfl
#align category_theory.limits.binary_fan.assoc_snd CategoryTheory.Limits.BinaryFan.assoc_snd
-/

#print CategoryTheory.Limits.BinaryFan.assocInv /-
/-- Given binary fans `sXY` over `X Y`, and `sYZ` over `Y Z`, and `s` over `X sYZ.X`,
if `sYZ` is a limit cone we can construct a binary fan over `sXY.X Z`.

This is an ingredient of building the associator for a cartesian category.
-/
def BinaryFan.assocInv {X Y Z : C} {sXY : BinaryFan X Y} (P : IsLimit sXY) {sYZ : BinaryFan Y Z}
    (s : BinaryFan X sYZ.pt) : BinaryFan sXY.pt Z :=
  BinaryFan.mk (P.lift (BinaryFan.mk s.fst (s.snd ≫ sYZ.fst))) (s.snd ≫ sYZ.snd)
#align category_theory.limits.binary_fan.assoc_inv CategoryTheory.Limits.BinaryFan.assocInv
-/

#print CategoryTheory.Limits.BinaryFan.assocInv_fst /-
@[simp]
theorem BinaryFan.assocInv_fst {X Y Z : C} {sXY : BinaryFan X Y} (P : IsLimit sXY)
    {sYZ : BinaryFan Y Z} (s : BinaryFan X sYZ.pt) :
    (s.assocInv P).fst = P.lift (BinaryFan.mk s.fst (s.snd ≫ sYZ.fst)) :=
  rfl
#align category_theory.limits.binary_fan.assoc_inv_fst CategoryTheory.Limits.BinaryFan.assocInv_fst
-/

#print CategoryTheory.Limits.BinaryFan.assocInv_snd /-
@[simp]
theorem BinaryFan.assocInv_snd {X Y Z : C} {sXY : BinaryFan X Y} (P : IsLimit sXY)
    {sYZ : BinaryFan Y Z} (s : BinaryFan X sYZ.pt) : (s.assocInv P).snd = s.snd ≫ sYZ.snd :=
  rfl
#align category_theory.limits.binary_fan.assoc_inv_snd CategoryTheory.Limits.BinaryFan.assocInv_snd
-/

#print CategoryTheory.Limits.IsLimit.assoc /-
/-- If all the binary fans involved a limit cones, `binary_fan.assoc` produces another limit cone.
-/
@[simps]
def IsLimit.assoc {X Y Z : C} {sXY : BinaryFan X Y} (P : IsLimit sXY) {sYZ : BinaryFan Y Z}
    (Q : IsLimit sYZ) {s : BinaryFan sXY.pt Z} (R : IsLimit s) : IsLimit (s.and_assoc Q)
    where
  lift t := R.lift (BinaryFan.assocInv P t)
  fac t := by
    rintro ⟨⟨⟩⟩ <;> simp
    apply Q.hom_ext
    rintro ⟨⟨⟩⟩ <;> simp
  uniq t m w := by
    have h := R.uniq (binary_fan.assoc_inv P t) m
    rw [h]
    rintro ⟨⟨⟩⟩ <;> simp
    apply P.hom_ext
    rintro ⟨⟨⟩⟩ <;> simp
    · exact w ⟨walking_pair.left⟩
    · specialize w ⟨walking_pair.right⟩
      simp at w 
      rw [← w]; simp
    · specialize w ⟨walking_pair.right⟩
      simp at w 
      rw [← w]; simp
#align category_theory.limits.is_limit.assoc CategoryTheory.Limits.IsLimit.assoc
-/

#print CategoryTheory.Limits.BinaryFan.associator /-
/-- Given two pairs of limit cones corresponding to the parenthesisations of `X × Y × Z`,
we obtain an isomorphism between the cone points.
-/
@[reducible]
def BinaryFan.associator {X Y Z : C} {sXY : BinaryFan X Y} (P : IsLimit sXY) {sYZ : BinaryFan Y Z}
    (Q : IsLimit sYZ) {s : BinaryFan sXY.pt Z} (R : IsLimit s) {t : BinaryFan X sYZ.pt}
    (S : IsLimit t) : s.pt ≅ t.pt :=
  IsLimit.conePointUniqueUpToIso (IsLimit.assoc P Q R) S
#align category_theory.limits.binary_fan.associator CategoryTheory.Limits.BinaryFan.associator
-/

#print CategoryTheory.Limits.BinaryFan.associatorOfLimitCone /-
/-- Given a fixed family of limit data for every pair `X Y`, we obtain an associator.
-/
@[reducible]
def BinaryFan.associatorOfLimitCone (L : ∀ X Y : C, LimitCone (pair X Y)) (X Y Z : C) :
    (L (L X Y).Cone.pt Z).Cone.pt ≅ (L X (L Y Z).Cone.pt).Cone.pt :=
  BinaryFan.associator (L X Y).IsLimit (L Y Z).IsLimit (L (L X Y).Cone.pt Z).IsLimit
    (L X (L Y Z).Cone.pt).IsLimit
#align category_theory.limits.binary_fan.associator_of_limit_cone CategoryTheory.Limits.BinaryFan.associatorOfLimitCone
-/

attribute [local tidy] tactic.discrete_cases

#print CategoryTheory.Limits.BinaryFan.leftUnitor /-
/-- Construct a left unitor from specified limit cones.
-/
@[simps]
def BinaryFan.leftUnitor {X : C} {s : Cone (Functor.empty.{v} C)} (P : IsLimit s)
    {t : BinaryFan s.pt X} (Q : IsLimit t) : t.pt ≅ X
    where
  Hom := t.snd
  inv :=
    Q.lift
      (BinaryFan.mk
        (P.lift
          { pt
            π := { app := Discrete.rec (PEmpty.rec _) } })
        (𝟙 X))
  hom_inv_id' := by apply Q.hom_ext; rintro ⟨⟨⟩⟩; · apply P.hom_ext; rintro ⟨⟨⟩⟩; · simp
#align category_theory.limits.binary_fan.left_unitor CategoryTheory.Limits.BinaryFan.leftUnitor
-/

#print CategoryTheory.Limits.BinaryFan.rightUnitor /-
/-- Construct a right unitor from specified limit cones.
-/
@[simps]
def BinaryFan.rightUnitor {X : C} {s : Cone (Functor.empty.{v} C)} (P : IsLimit s)
    {t : BinaryFan X s.pt} (Q : IsLimit t) : t.pt ≅ X
    where
  Hom := t.fst
  inv :=
    Q.lift
      (BinaryFan.mk (𝟙 X)
        (P.lift
          { pt
            π := { app := Discrete.rec (PEmpty.rec _) } }))
  hom_inv_id' := by apply Q.hom_ext; rintro ⟨⟨⟩⟩; · simp; · apply P.hom_ext; rintro ⟨⟨⟩⟩
#align category_theory.limits.binary_fan.right_unitor CategoryTheory.Limits.BinaryFan.rightUnitor
-/

end

end Limits

open CategoryTheory.Limits

section

attribute [local tidy] tactic.case_bash

variable {C}

variable (𝒯 : LimitCone (Functor.empty.{v} C))

variable (ℬ : ∀ X Y : C, LimitCone (pair X Y))

namespace MonoidalOfChosenFiniteProducts

#print CategoryTheory.MonoidalOfChosenFiniteProducts.tensorObj /-
/-- Implementation of the tensor product for `monoidal_of_chosen_finite_products`. -/
@[reducible]
def tensorObj (X Y : C) : C :=
  (ℬ X Y).Cone.pt
#align category_theory.monoidal_of_chosen_finite_products.tensor_obj CategoryTheory.MonoidalOfChosenFiniteProducts.tensorObj
-/

#print CategoryTheory.MonoidalOfChosenFiniteProducts.tensorHom /-
/-- Implementation of the tensor product of morphisms for `monoidal_of_chosen_finite_products`. -/
@[reducible]
def tensorHom {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : tensorObj ℬ W Y ⟶ tensorObj ℬ X Z :=
  (BinaryFan.IsLimit.lift' (ℬ X Z).IsLimit ((ℬ W Y).Cone.π.app ⟨WalkingPair.left⟩ ≫ f)
      (((ℬ W Y).Cone.π.app ⟨WalkingPair.right⟩ : (ℬ W Y).Cone.pt ⟶ Y) ≫ g)).val
#align category_theory.monoidal_of_chosen_finite_products.tensor_hom CategoryTheory.MonoidalOfChosenFiniteProducts.tensorHom
-/

#print CategoryTheory.MonoidalOfChosenFiniteProducts.tensor_id /-
theorem tensor_id (X₁ X₂ : C) : tensorHom ℬ (𝟙 X₁) (𝟙 X₂) = 𝟙 (tensorObj ℬ X₁ X₂) := by
  apply is_limit.hom_ext (ℬ _ _).IsLimit; rintro ⟨⟨⟩⟩ <;> · dsimp [tensor_hom]; simp
#align category_theory.monoidal_of_chosen_finite_products.tensor_id CategoryTheory.MonoidalOfChosenFiniteProducts.tensor_id
-/

#print CategoryTheory.MonoidalOfChosenFiniteProducts.tensor_comp /-
theorem tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁)
    (g₂ : Y₂ ⟶ Z₂) : tensorHom ℬ (f₁ ≫ g₁) (f₂ ≫ g₂) = tensorHom ℬ f₁ f₂ ≫ tensorHom ℬ g₁ g₂ := by
  apply is_limit.hom_ext (ℬ _ _).IsLimit; rintro ⟨⟨⟩⟩ <;> · dsimp [tensor_hom]; simp
#align category_theory.monoidal_of_chosen_finite_products.tensor_comp CategoryTheory.MonoidalOfChosenFiniteProducts.tensor_comp
-/

#print CategoryTheory.MonoidalOfChosenFiniteProducts.pentagon /-
theorem pentagon (W X Y Z : C) :
    tensorHom ℬ (BinaryFan.associatorOfLimitCone ℬ W X Y).Hom (𝟙 Z) ≫
        (BinaryFan.associatorOfLimitCone ℬ W (tensorObj ℬ X Y) Z).Hom ≫
          tensorHom ℬ (𝟙 W) (BinaryFan.associatorOfLimitCone ℬ X Y Z).Hom =
      (BinaryFan.associatorOfLimitCone ℬ (tensorObj ℬ W X) Y Z).Hom ≫
        (BinaryFan.associatorOfLimitCone ℬ W X (tensorObj ℬ Y Z)).Hom :=
  by
  dsimp [tensor_hom]
  apply is_limit.hom_ext (ℬ _ _).IsLimit; rintro ⟨⟨⟩⟩
  · simp
  · apply is_limit.hom_ext (ℬ _ _).IsLimit; rintro ⟨⟨⟩⟩
    · simp
    apply is_limit.hom_ext (ℬ _ _).IsLimit; rintro ⟨⟨⟩⟩
    · simp
    · simp
#align category_theory.monoidal_of_chosen_finite_products.pentagon CategoryTheory.MonoidalOfChosenFiniteProducts.pentagon
-/

#print CategoryTheory.MonoidalOfChosenFiniteProducts.triangle /-
theorem triangle (X Y : C) :
    (BinaryFan.associatorOfLimitCone ℬ X 𝒯.Cone.pt Y).Hom ≫
        tensorHom ℬ (𝟙 X) (BinaryFan.leftUnitor 𝒯.IsLimit (ℬ 𝒯.Cone.pt Y).IsLimit).Hom =
      tensorHom ℬ (BinaryFan.rightUnitor 𝒯.IsLimit (ℬ X 𝒯.Cone.pt).IsLimit).Hom (𝟙 Y) :=
  by
  dsimp [tensor_hom]
  apply is_limit.hom_ext (ℬ _ _).IsLimit; rintro ⟨⟨⟩⟩ <;> simp
#align category_theory.monoidal_of_chosen_finite_products.triangle CategoryTheory.MonoidalOfChosenFiniteProducts.triangle
-/

#print CategoryTheory.MonoidalOfChosenFiniteProducts.leftUnitor_naturality /-
theorem leftUnitor_naturality {X₁ X₂ : C} (f : X₁ ⟶ X₂) :
    tensorHom ℬ (𝟙 𝒯.Cone.pt) f ≫ (BinaryFan.leftUnitor 𝒯.IsLimit (ℬ 𝒯.Cone.pt X₂).IsLimit).Hom =
      (BinaryFan.leftUnitor 𝒯.IsLimit (ℬ 𝒯.Cone.pt X₁).IsLimit).Hom ≫ f :=
  by
  dsimp [tensor_hom]
  simp
#align category_theory.monoidal_of_chosen_finite_products.left_unitor_naturality CategoryTheory.MonoidalOfChosenFiniteProducts.leftUnitor_naturality
-/

#print CategoryTheory.MonoidalOfChosenFiniteProducts.rightUnitor_naturality /-
theorem rightUnitor_naturality {X₁ X₂ : C} (f : X₁ ⟶ X₂) :
    tensorHom ℬ f (𝟙 𝒯.Cone.pt) ≫ (BinaryFan.rightUnitor 𝒯.IsLimit (ℬ X₂ 𝒯.Cone.pt).IsLimit).Hom =
      (BinaryFan.rightUnitor 𝒯.IsLimit (ℬ X₁ 𝒯.Cone.pt).IsLimit).Hom ≫ f :=
  by
  dsimp [tensor_hom]
  simp
#align category_theory.monoidal_of_chosen_finite_products.right_unitor_naturality CategoryTheory.MonoidalOfChosenFiniteProducts.rightUnitor_naturality
-/

#print CategoryTheory.MonoidalOfChosenFiniteProducts.associator_naturality /-
theorem associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    tensorHom ℬ (tensorHom ℬ f₁ f₂) f₃ ≫ (BinaryFan.associatorOfLimitCone ℬ Y₁ Y₂ Y₃).Hom =
      (BinaryFan.associatorOfLimitCone ℬ X₁ X₂ X₃).Hom ≫ tensorHom ℬ f₁ (tensorHom ℬ f₂ f₃) :=
  by
  dsimp [tensor_hom]
  apply is_limit.hom_ext (ℬ _ _).IsLimit; rintro ⟨⟨⟩⟩
  · simp
  · apply is_limit.hom_ext (ℬ _ _).IsLimit; rintro ⟨⟨⟩⟩
    · simp
    · simp
#align category_theory.monoidal_of_chosen_finite_products.associator_naturality CategoryTheory.MonoidalOfChosenFiniteProducts.associator_naturality
-/

end MonoidalOfChosenFiniteProducts

open MonoidalOfChosenFiniteProducts

#print CategoryTheory.monoidalOfChosenFiniteProducts /-
/-- A category with a terminal object and binary products has a natural monoidal structure. -/
def monoidalOfChosenFiniteProducts : MonoidalCategory C
    where
  tensorUnit := 𝒯.Cone.pt
  tensorObj X Y := tensorObj ℬ X Y
  tensorHom _ _ _ _ f g := tensorHom ℬ f g
  tensor_id' := tensor_id ℬ
  tensor_comp' _ _ _ _ _ _ f₁ f₂ g₁ g₂ := tensor_comp ℬ f₁ f₂ g₁ g₂
  associator X Y Z := BinaryFan.associatorOfLimitCone ℬ X Y Z
  leftUnitor X := BinaryFan.leftUnitor 𝒯.IsLimit (ℬ 𝒯.Cone.pt X).IsLimit
  rightUnitor X := BinaryFan.rightUnitor 𝒯.IsLimit (ℬ X 𝒯.Cone.pt).IsLimit
  pentagon' := pentagon ℬ
  triangle' := triangle 𝒯 ℬ
  leftUnitor_naturality' _ _ f := leftUnitor_naturality 𝒯 ℬ f
  rightUnitor_naturality' _ _ f := rightUnitor_naturality 𝒯 ℬ f
  associator_naturality' _ _ _ _ _ _ f₁ f₂ f₃ := associator_naturality ℬ f₁ f₂ f₃
#align category_theory.monoidal_of_chosen_finite_products CategoryTheory.monoidalOfChosenFiniteProducts
-/

namespace MonoidalOfChosenFiniteProducts

open MonoidalCategory

#print CategoryTheory.MonoidalOfChosenFiniteProducts.MonoidalOfChosenFiniteProductsSynonym /-
/-- A type synonym for `C` carrying a monoidal category structure corresponding to
a fixed choice of limit data for the empty functor, and for `pair X Y` for every `X Y : C`.

This is an implementation detail for `symmetric_of_chosen_finite_products`.
-/
@[nolint unused_arguments has_nonempty_instance]
def MonoidalOfChosenFiniteProductsSynonym (𝒯 : LimitCone (Functor.empty.{v} C))
    (ℬ : ∀ X Y : C, LimitCone (pair X Y)) :=
  C
deriving Category
#align category_theory.monoidal_of_chosen_finite_products.monoidal_of_chosen_finite_products_synonym CategoryTheory.MonoidalOfChosenFiniteProducts.MonoidalOfChosenFiniteProductsSynonym
-/

instance : MonoidalCategory (MonoidalOfChosenFiniteProductsSynonym 𝒯 ℬ) :=
  monoidalOfChosenFiniteProducts 𝒯 ℬ

end MonoidalOfChosenFiniteProducts

end

end CategoryTheory

