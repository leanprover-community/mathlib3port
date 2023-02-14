/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Scott Morrison, Floris van Doorn

! This file was ported from Lean 3 source module category_theory.isomorphism
! leanprover-community/mathlib commit 48085f140e684306f9e7da907cd5932056d1aded
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Functor.Basic

/-!
# Isomorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines isomorphisms between objects of a category.

## Main definitions

- `structure iso` : a bundled isomorphism between two objects of a category;
- `class is_iso` : an unbundled version of `iso`;
  note that `is_iso f` is a `Prop`, and only asserts the existence of an inverse.
  Of course, this inverse is unique, so it doesn't cost us much to use choice to retrieve it.
- `inv f`, for the inverse of a morphism with `[is_iso f]`
- `as_iso` : convert from `is_iso` to `iso` (noncomputable);
- `of_iso` : convert from `iso` to `is_iso`;
- standard operations on isomorphisms (composition, inverse etc)

## Notations

- `X ≅ Y` : same as `iso X Y`;
- `α ≪≫ β` : composition of two isomorphisms; it is called `iso.trans`

## Tags

category, category theory, isomorphism
-/


universe v u

-- morphism levels before object levels. See note [category_theory universes].
namespace CategoryTheory

open Category

#print CategoryTheory.Iso /-
/-- An isomorphism (a.k.a. an invertible morphism) between two objects of a category.
The inverse morphism is bundled.

See also `category_theory.core` for the category with the same objects and isomorphisms playing
the role of morphisms.

See <https://stacks.math.columbia.edu/tag/0017>.
-/
structure Iso {C : Type u} [Category.{v} C] (X Y : C) where
  Hom : X ⟶ Y
  inv : Y ⟶ X
  hom_inv_id' : hom ≫ inv = 𝟙 X := by obviously
  inv_hom_id' : inv ≫ hom = 𝟙 Y := by obviously
#align category_theory.iso CategoryTheory.Iso
-/

restate_axiom iso.hom_inv_id'

restate_axiom iso.inv_hom_id'

attribute [simp, reassoc.1] iso.hom_inv_id iso.inv_hom_id

-- mathport name: «expr ≅ »
infixr:10 " ≅ " => Iso

-- type as \cong or \iso
variable {C : Type u} [Category.{v} C]

variable {X Y Z : C}

namespace Iso

#print CategoryTheory.Iso.ext /-
@[ext]
theorem ext ⦃α β : X ≅ Y⦄ (w : α.Hom = β.Hom) : α = β :=
  suffices α.inv = β.inv by cases α <;> cases β <;> cc
  calc
    α.inv = α.inv ≫ β.Hom ≫ β.inv := by rw [iso.hom_inv_id, category.comp_id]
    _ = (α.inv ≫ α.Hom) ≫ β.inv := by rw [category.assoc, ← w]
    _ = β.inv := by rw [iso.inv_hom_id, category.id_comp]
    
#align category_theory.iso.ext CategoryTheory.Iso.ext
-/

#print CategoryTheory.Iso.symm /-
/-- Inverse isomorphism. -/
@[symm]
def symm (I : X ≅ Y) : Y ≅ X where
  Hom := I.inv
  inv := I.Hom
  hom_inv_id' := I.inv_hom_id'
  inv_hom_id' := I.hom_inv_id'
#align category_theory.iso.symm CategoryTheory.Iso.symm
-/

#print CategoryTheory.Iso.symm_hom /-
@[simp]
theorem symm_hom (α : X ≅ Y) : α.symm.Hom = α.inv :=
  rfl
#align category_theory.iso.symm_hom CategoryTheory.Iso.symm_hom
-/

#print CategoryTheory.Iso.symm_inv /-
@[simp]
theorem symm_inv (α : X ≅ Y) : α.symm.inv = α.Hom :=
  rfl
#align category_theory.iso.symm_inv CategoryTheory.Iso.symm_inv
-/

#print CategoryTheory.Iso.symm_mk /-
@[simp]
theorem symm_mk {X Y : C} (hom : X ⟶ Y) (inv : Y ⟶ X) (hom_inv_id) (inv_hom_id) :
    Iso.symm
        { Hom
          inv
          hom_inv_id' := hom_inv_id
          inv_hom_id' := inv_hom_id } =
      { Hom := inv
        inv := hom
        hom_inv_id' := inv_hom_id
        inv_hom_id' := hom_inv_id } :=
  rfl
#align category_theory.iso.symm_mk CategoryTheory.Iso.symm_mk
-/

#print CategoryTheory.Iso.symm_symm_eq /-
@[simp]
theorem symm_symm_eq {X Y : C} (α : X ≅ Y) : α.symm.symm = α := by cases α <;> rfl
#align category_theory.iso.symm_symm_eq CategoryTheory.Iso.symm_symm_eq
-/

#print CategoryTheory.Iso.symm_eq_iff /-
@[simp]
theorem symm_eq_iff {X Y : C} {α β : X ≅ Y} : α.symm = β.symm ↔ α = β :=
  ⟨fun h => symm_symm_eq α ▸ symm_symm_eq β ▸ congr_arg symm h, congr_arg symm⟩
#align category_theory.iso.symm_eq_iff CategoryTheory.Iso.symm_eq_iff
-/

#print CategoryTheory.Iso.nonempty_iso_symm /-
theorem nonempty_iso_symm (X Y : C) : Nonempty (X ≅ Y) ↔ Nonempty (Y ≅ X) :=
  ⟨fun h => ⟨h.some.symm⟩, fun h => ⟨h.some.symm⟩⟩
#align category_theory.iso.nonempty_iso_symm CategoryTheory.Iso.nonempty_iso_symm
-/

#print CategoryTheory.Iso.refl /-
/-- Identity isomorphism. -/
@[refl, simps]
def refl (X : C) : X ≅ X where
  Hom := 𝟙 X
  inv := 𝟙 X
#align category_theory.iso.refl CategoryTheory.Iso.refl
-/

instance : Inhabited (X ≅ X) :=
  ⟨Iso.refl X⟩

#print CategoryTheory.Iso.refl_symm /-
@[simp]
theorem refl_symm (X : C) : (Iso.refl X).symm = Iso.refl X :=
  rfl
#align category_theory.iso.refl_symm CategoryTheory.Iso.refl_symm
-/

#print CategoryTheory.Iso.trans /-
/-- Composition of two isomorphisms -/
@[trans, simps]
def trans (α : X ≅ Y) (β : Y ≅ Z) : X ≅ Z
    where
  Hom := α.Hom ≫ β.Hom
  inv := β.inv ≫ α.inv
#align category_theory.iso.trans CategoryTheory.Iso.trans
-/

-- mathport name: «expr ≪≫ »
infixr:80 " ≪≫ " => Iso.trans

#print CategoryTheory.Iso.trans_mk /-
-- type as `\ll \gg`.
@[simp]
theorem trans_mk {X Y Z : C} (hom : X ⟶ Y) (inv : Y ⟶ X) (hom_inv_id) (inv_hom_id) (hom' : Y ⟶ Z)
    (inv' : Z ⟶ Y) (hom_inv_id') (inv_hom_id') (hom_inv_id'') (inv_hom_id'') :
    Iso.trans
        { Hom
          inv
          hom_inv_id' := hom_inv_id
          inv_hom_id' := inv_hom_id }
        { Hom := hom'
          inv := inv'
          hom_inv_id'
          inv_hom_id' } =
      { Hom := hom ≫ hom'
        inv := inv' ≫ inv
        hom_inv_id' := hom_inv_id''
        inv_hom_id' := inv_hom_id'' } :=
  rfl
#align category_theory.iso.trans_mk CategoryTheory.Iso.trans_mk
-/

#print CategoryTheory.Iso.trans_symm /-
@[simp]
theorem trans_symm (α : X ≅ Y) (β : Y ≅ Z) : (α ≪≫ β).symm = β.symm ≪≫ α.symm :=
  rfl
#align category_theory.iso.trans_symm CategoryTheory.Iso.trans_symm
-/

#print CategoryTheory.Iso.trans_assoc /-
@[simp]
theorem trans_assoc {Z' : C} (α : X ≅ Y) (β : Y ≅ Z) (γ : Z ≅ Z') : (α ≪≫ β) ≪≫ γ = α ≪≫ β ≪≫ γ :=
  by ext <;> simp only [trans_hom, category.assoc]
#align category_theory.iso.trans_assoc CategoryTheory.Iso.trans_assoc
-/

#print CategoryTheory.Iso.refl_trans /-
@[simp]
theorem refl_trans (α : X ≅ Y) : Iso.refl X ≪≫ α = α := by ext <;> apply category.id_comp
#align category_theory.iso.refl_trans CategoryTheory.Iso.refl_trans
-/

#print CategoryTheory.Iso.trans_refl /-
@[simp]
theorem trans_refl (α : X ≅ Y) : α ≪≫ Iso.refl Y = α := by ext <;> apply category.comp_id
#align category_theory.iso.trans_refl CategoryTheory.Iso.trans_refl
-/

#print CategoryTheory.Iso.symm_self_id /-
@[simp]
theorem symm_self_id (α : X ≅ Y) : α.symm ≪≫ α = Iso.refl Y :=
  ext α.inv_hom_id
#align category_theory.iso.symm_self_id CategoryTheory.Iso.symm_self_id
-/

#print CategoryTheory.Iso.self_symm_id /-
@[simp]
theorem self_symm_id (α : X ≅ Y) : α ≪≫ α.symm = Iso.refl X :=
  ext α.hom_inv_id
#align category_theory.iso.self_symm_id CategoryTheory.Iso.self_symm_id
-/

#print CategoryTheory.Iso.symm_self_id_assoc /-
@[simp]
theorem symm_self_id_assoc (α : X ≅ Y) (β : Y ≅ Z) : α.symm ≪≫ α ≪≫ β = β := by
  rw [← trans_assoc, symm_self_id, refl_trans]
#align category_theory.iso.symm_self_id_assoc CategoryTheory.Iso.symm_self_id_assoc
-/

#print CategoryTheory.Iso.self_symm_id_assoc /-
@[simp]
theorem self_symm_id_assoc (α : X ≅ Y) (β : X ≅ Z) : α ≪≫ α.symm ≪≫ β = β := by
  rw [← trans_assoc, self_symm_id, refl_trans]
#align category_theory.iso.self_symm_id_assoc CategoryTheory.Iso.self_symm_id_assoc
-/

#print CategoryTheory.Iso.inv_comp_eq /-
theorem inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g : Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.Hom ≫ g :=
  ⟨fun H => by simp [H.symm], fun H => by simp [H]⟩
#align category_theory.iso.inv_comp_eq CategoryTheory.Iso.inv_comp_eq
-/

#print CategoryTheory.Iso.eq_inv_comp /-
theorem eq_inv_comp (α : X ≅ Y) {f : X ⟶ Z} {g : Y ⟶ Z} : g = α.inv ≫ f ↔ α.Hom ≫ g = f :=
  (inv_comp_eq α.symm).symm
#align category_theory.iso.eq_inv_comp CategoryTheory.Iso.eq_inv_comp
-/

#print CategoryTheory.Iso.comp_inv_eq /-
theorem comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g : Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.Hom :=
  ⟨fun H => by simp [H.symm], fun H => by simp [H]⟩
#align category_theory.iso.comp_inv_eq CategoryTheory.Iso.comp_inv_eq
-/

#print CategoryTheory.Iso.eq_comp_inv /-
theorem eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g : Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.Hom = f :=
  (comp_inv_eq α.symm).symm
#align category_theory.iso.eq_comp_inv CategoryTheory.Iso.eq_comp_inv
-/

#print CategoryTheory.Iso.inv_eq_inv /-
theorem inv_eq_inv (f g : X ≅ Y) : f.inv = g.inv ↔ f.Hom = g.Hom :=
  have : ∀ {X Y : C} (f g : X ≅ Y), f.Hom = g.Hom → f.inv = g.inv := fun X Y f g h => by rw [ext h]
  ⟨this f.symm g.symm, this f g⟩
#align category_theory.iso.inv_eq_inv CategoryTheory.Iso.inv_eq_inv
-/

#print CategoryTheory.Iso.hom_comp_eq_id /-
theorem hom_comp_eq_id (α : X ≅ Y) {f : Y ⟶ X} : α.Hom ≫ f = 𝟙 X ↔ f = α.inv := by
  rw [← eq_inv_comp, comp_id]
#align category_theory.iso.hom_comp_eq_id CategoryTheory.Iso.hom_comp_eq_id
-/

#print CategoryTheory.Iso.comp_hom_eq_id /-
theorem comp_hom_eq_id (α : X ≅ Y) {f : Y ⟶ X} : f ≫ α.Hom = 𝟙 Y ↔ f = α.inv := by
  rw [← eq_comp_inv, id_comp]
#align category_theory.iso.comp_hom_eq_id CategoryTheory.Iso.comp_hom_eq_id
-/

#print CategoryTheory.Iso.inv_comp_eq_id /-
theorem inv_comp_eq_id (α : X ≅ Y) {f : X ⟶ Y} : α.inv ≫ f = 𝟙 Y ↔ f = α.Hom :=
  hom_comp_eq_id α.symm
#align category_theory.iso.inv_comp_eq_id CategoryTheory.Iso.inv_comp_eq_id
-/

#print CategoryTheory.Iso.comp_inv_eq_id /-
theorem comp_inv_eq_id (α : X ≅ Y) {f : X ⟶ Y} : f ≫ α.inv = 𝟙 X ↔ f = α.Hom :=
  comp_hom_eq_id α.symm
#align category_theory.iso.comp_inv_eq_id CategoryTheory.Iso.comp_inv_eq_id
-/

#print CategoryTheory.Iso.hom_eq_inv /-
theorem hom_eq_inv (α : X ≅ Y) (β : Y ≅ X) : α.Hom = β.inv ↔ β.Hom = α.inv :=
  by
  erw [inv_eq_inv α.symm β, eq_comm]
  rfl
#align category_theory.iso.hom_eq_inv CategoryTheory.Iso.hom_eq_inv
-/

end Iso

#print CategoryTheory.IsIso /-
/-- `is_iso` typeclass expressing that a morphism is invertible. -/
class IsIso (f : X ⟶ Y) : Prop where
  out : ∃ inv : Y ⟶ X, f ≫ inv = 𝟙 X ∧ inv ≫ f = 𝟙 Y
#align category_theory.is_iso CategoryTheory.IsIso
-/

#print CategoryTheory.inv /-
/-- The inverse of a morphism `f` when we have `[is_iso f]`.
-/
noncomputable def inv (f : X ⟶ Y) [I : IsIso f] :=
  Classical.choose I.1
#align category_theory.inv CategoryTheory.inv
-/

namespace IsIso

#print CategoryTheory.IsIso.hom_inv_id /-
@[simp, reassoc.1]
theorem hom_inv_id (f : X ⟶ Y) [I : IsIso f] : f ≫ inv f = 𝟙 X :=
  (Classical.choose_spec I.1).left
#align category_theory.is_iso.hom_inv_id CategoryTheory.IsIso.hom_inv_id
-/

#print CategoryTheory.IsIso.inv_hom_id /-
@[simp, reassoc.1]
theorem inv_hom_id (f : X ⟶ Y) [I : IsIso f] : inv f ≫ f = 𝟙 Y :=
  (Classical.choose_spec I.1).right
#align category_theory.is_iso.inv_hom_id CategoryTheory.IsIso.inv_hom_id
-/

end IsIso

open IsIso

#print CategoryTheory.asIso /-
/-- Reinterpret a morphism `f` with an `is_iso f` instance as an `iso`. -/
noncomputable def asIso (f : X ⟶ Y) [h : IsIso f] : X ≅ Y :=
  ⟨f, inv f, hom_inv_id f, inv_hom_id f⟩
#align category_theory.as_iso CategoryTheory.asIso
-/

#print CategoryTheory.asIso_hom /-
@[simp]
theorem asIso_hom (f : X ⟶ Y) [IsIso f] : (asIso f).Hom = f :=
  rfl
#align category_theory.as_iso_hom CategoryTheory.asIso_hom
-/

#print CategoryTheory.asIso_inv /-
@[simp]
theorem asIso_inv (f : X ⟶ Y) [IsIso f] : (asIso f).inv = inv f :=
  rfl
#align category_theory.as_iso_inv CategoryTheory.asIso_inv
-/

namespace IsIso

#print CategoryTheory.IsIso.epi_of_iso /-
-- see Note [lower instance priority]
instance (priority := 100) epi_of_iso (f : X ⟶ Y) [IsIso f] : Epi f
    where left_cancellation Z g h
    w :=-- This is an interesting test case for better rewrite automation.
  by rw [← is_iso.inv_hom_id_assoc f g, w, is_iso.inv_hom_id_assoc f h]
#align category_theory.is_iso.epi_of_iso CategoryTheory.IsIso.epi_of_iso
-/

#print CategoryTheory.IsIso.mono_of_iso /-
-- see Note [lower instance priority]
instance (priority := 100) mono_of_iso (f : X ⟶ Y) [IsIso f] : Mono f
    where right_cancellation Z g h w := by
    rw [← category.comp_id g, ← category.comp_id h, ← is_iso.hom_inv_id f, ← category.assoc, w, ←
      category.assoc]
#align category_theory.is_iso.mono_of_iso CategoryTheory.IsIso.mono_of_iso
-/

#print CategoryTheory.IsIso.inv_eq_of_hom_inv_id /-
@[ext]
theorem inv_eq_of_hom_inv_id {f : X ⟶ Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) :
    inv f = g := by
  apply (cancel_epi f).mp
  simp [hom_inv_id]
#align category_theory.is_iso.inv_eq_of_hom_inv_id CategoryTheory.IsIso.inv_eq_of_hom_inv_id
-/

#print CategoryTheory.IsIso.inv_eq_of_inv_hom_id /-
theorem inv_eq_of_inv_hom_id {f : X ⟶ Y} [IsIso f] {g : Y ⟶ X} (inv_hom_id : g ≫ f = 𝟙 Y) :
    inv f = g := by
  apply (cancel_mono f).mp
  simp [inv_hom_id]
#align category_theory.is_iso.inv_eq_of_inv_hom_id CategoryTheory.IsIso.inv_eq_of_inv_hom_id
-/

#print CategoryTheory.IsIso.eq_inv_of_hom_inv_id /-
@[ext]
theorem eq_inv_of_hom_inv_id {f : X ⟶ Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) :
    g = inv f :=
  (inv_eq_of_hom_inv_id hom_inv_id).symm
#align category_theory.is_iso.eq_inv_of_hom_inv_id CategoryTheory.IsIso.eq_inv_of_hom_inv_id
-/

#print CategoryTheory.IsIso.eq_inv_of_inv_hom_id /-
theorem eq_inv_of_inv_hom_id {f : X ⟶ Y} [IsIso f] {g : Y ⟶ X} (inv_hom_id : g ≫ f = 𝟙 Y) :
    g = inv f :=
  (inv_eq_of_inv_hom_id inv_hom_id).symm
#align category_theory.is_iso.eq_inv_of_inv_hom_id CategoryTheory.IsIso.eq_inv_of_inv_hom_id
-/

#print CategoryTheory.IsIso.id /-
instance id (X : C) : IsIso (𝟙 X) :=
  ⟨⟨𝟙 X, by simp⟩⟩
#align category_theory.is_iso.id CategoryTheory.IsIso.id
-/

#print CategoryTheory.IsIso.of_iso /-
instance of_iso (f : X ≅ Y) : IsIso f.Hom :=
  ⟨⟨f.inv, by simp⟩⟩
#align category_theory.is_iso.of_iso CategoryTheory.IsIso.of_iso
-/

#print CategoryTheory.IsIso.of_iso_inv /-
instance of_iso_inv (f : X ≅ Y) : IsIso f.inv :=
  IsIso.of_iso f.symm
#align category_theory.is_iso.of_iso_inv CategoryTheory.IsIso.of_iso_inv
-/

variable {f g : X ⟶ Y} {h : Y ⟶ Z}

#print CategoryTheory.IsIso.inv_isIso /-
instance inv_isIso [IsIso f] : IsIso (inv f) :=
  IsIso.of_iso_inv (asIso f)
#align category_theory.is_iso.inv_is_iso CategoryTheory.IsIso.inv_isIso
-/

#print CategoryTheory.IsIso.comp_isIso /-
/- The following instance has lower priority for the following reason:
Suppose we are given `f : X ≅ Y` with `X Y : Type u`.
Without the lower priority, typeclass inference cannot deduce `is_iso f.hom`
because `f.hom` is defeq to `(λ x, x) ≫ f.hom`, triggering a loop. -/
instance (priority := 900) comp_isIso [IsIso f] [IsIso h] : IsIso (f ≫ h) :=
  IsIso.of_iso <| asIso f ≪≫ asIso h
#align category_theory.is_iso.comp_is_iso CategoryTheory.IsIso.comp_isIso
-/

#print CategoryTheory.IsIso.inv_id /-
@[simp]
theorem inv_id : inv (𝟙 X) = 𝟙 X := by
  ext
  simp
#align category_theory.is_iso.inv_id CategoryTheory.IsIso.inv_id
-/

#print CategoryTheory.IsIso.inv_comp /-
@[simp]
theorem inv_comp [IsIso f] [IsIso h] : inv (f ≫ h) = inv h ≫ inv f :=
  by
  ext
  simp
#align category_theory.is_iso.inv_comp CategoryTheory.IsIso.inv_comp
-/

#print CategoryTheory.IsIso.inv_inv /-
@[simp]
theorem inv_inv [IsIso f] : inv (inv f) = f := by
  ext
  simp
#align category_theory.is_iso.inv_inv CategoryTheory.IsIso.inv_inv
-/

#print CategoryTheory.IsIso.Iso.inv_inv /-
@[simp]
theorem Iso.inv_inv (f : X ≅ Y) : inv f.inv = f.Hom :=
  by
  ext
  simp
#align category_theory.is_iso.iso.inv_inv CategoryTheory.IsIso.Iso.inv_inv
-/

#print CategoryTheory.IsIso.Iso.inv_hom /-
@[simp]
theorem Iso.inv_hom (f : X ≅ Y) : inv f.Hom = f.inv :=
  by
  ext
  simp
#align category_theory.is_iso.iso.inv_hom CategoryTheory.IsIso.Iso.inv_hom
-/

#print CategoryTheory.IsIso.inv_comp_eq /-
@[simp]
theorem inv_comp_eq (α : X ⟶ Y) [IsIso α] {f : X ⟶ Z} {g : Y ⟶ Z} : inv α ≫ f = g ↔ f = α ≫ g :=
  (asIso α).inv_comp_eq
#align category_theory.is_iso.inv_comp_eq CategoryTheory.IsIso.inv_comp_eq
-/

#print CategoryTheory.IsIso.eq_inv_comp /-
@[simp]
theorem eq_inv_comp (α : X ⟶ Y) [IsIso α] {f : X ⟶ Z} {g : Y ⟶ Z} : g = inv α ≫ f ↔ α ≫ g = f :=
  (asIso α).eq_inv_comp
#align category_theory.is_iso.eq_inv_comp CategoryTheory.IsIso.eq_inv_comp
-/

#print CategoryTheory.IsIso.comp_inv_eq /-
@[simp]
theorem comp_inv_eq (α : X ⟶ Y) [IsIso α] {f : Z ⟶ Y} {g : Z ⟶ X} : f ≫ inv α = g ↔ f = g ≫ α :=
  (asIso α).comp_inv_eq
#align category_theory.is_iso.comp_inv_eq CategoryTheory.IsIso.comp_inv_eq
-/

#print CategoryTheory.IsIso.eq_comp_inv /-
@[simp]
theorem eq_comp_inv (α : X ⟶ Y) [IsIso α] {f : Z ⟶ Y} {g : Z ⟶ X} : g = f ≫ inv α ↔ g ≫ α = f :=
  (asIso α).eq_comp_inv
#align category_theory.is_iso.eq_comp_inv CategoryTheory.IsIso.eq_comp_inv
-/

#print CategoryTheory.IsIso.of_isIso_comp_left /-
theorem of_isIso_comp_left {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [IsIso (f ≫ g)] :
    IsIso g := by
  rw [← id_comp g, ← inv_hom_id f, assoc]
  infer_instance
#align category_theory.is_iso.of_is_iso_comp_left CategoryTheory.IsIso.of_isIso_comp_left
-/

#print CategoryTheory.IsIso.of_isIso_comp_right /-
theorem of_isIso_comp_right {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] [IsIso (f ≫ g)] :
    IsIso f := by
  rw [← comp_id f, ← hom_inv_id g, ← assoc]
  infer_instance
#align category_theory.is_iso.of_is_iso_comp_right CategoryTheory.IsIso.of_isIso_comp_right
-/

#print CategoryTheory.IsIso.of_isIso_fac_left /-
theorem of_isIso_fac_left {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [IsIso f] [hh : IsIso h]
    (w : f ≫ g = h) : IsIso g := by
  rw [← w] at hh
  haveI := hh
  exact of_is_iso_comp_left f g
#align category_theory.is_iso.of_is_iso_fac_left CategoryTheory.IsIso.of_isIso_fac_left
-/

#print CategoryTheory.IsIso.of_isIso_fac_right /-
theorem of_isIso_fac_right {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [IsIso g] [hh : IsIso h]
    (w : f ≫ g = h) : IsIso f := by
  rw [← w] at hh
  haveI := hh
  exact of_is_iso_comp_right f g
#align category_theory.is_iso.of_is_iso_fac_right CategoryTheory.IsIso.of_isIso_fac_right
-/

end IsIso

open IsIso

#print CategoryTheory.eq_of_inv_eq_inv /-
theorem eq_of_inv_eq_inv {f g : X ⟶ Y} [IsIso f] [IsIso g] (p : inv f = inv g) : f = g :=
  by
  apply (cancel_epi (inv f)).1
  erw [inv_hom_id, p, inv_hom_id]
#align category_theory.eq_of_inv_eq_inv CategoryTheory.eq_of_inv_eq_inv
-/

#print CategoryTheory.IsIso.inv_eq_inv /-
theorem IsIso.inv_eq_inv {f g : X ⟶ Y} [IsIso f] [IsIso g] : inv f = inv g ↔ f = g :=
  Iso.inv_eq_inv (asIso f) (asIso g)
#align category_theory.is_iso.inv_eq_inv CategoryTheory.IsIso.inv_eq_inv
-/

#print CategoryTheory.hom_comp_eq_id /-
theorem hom_comp_eq_id (g : X ⟶ Y) [IsIso g] {f : Y ⟶ X} : g ≫ f = 𝟙 X ↔ f = inv g :=
  (asIso g).hom_comp_eq_id
#align category_theory.hom_comp_eq_id CategoryTheory.hom_comp_eq_id
-/

#print CategoryTheory.comp_hom_eq_id /-
theorem comp_hom_eq_id (g : X ⟶ Y) [IsIso g] {f : Y ⟶ X} : f ≫ g = 𝟙 Y ↔ f = inv g :=
  (asIso g).comp_hom_eq_id
#align category_theory.comp_hom_eq_id CategoryTheory.comp_hom_eq_id
-/

#print CategoryTheory.inv_comp_eq_id /-
theorem inv_comp_eq_id (g : X ⟶ Y) [IsIso g] {f : X ⟶ Y} : inv g ≫ f = 𝟙 Y ↔ f = g :=
  (asIso g).inv_comp_eq_id
#align category_theory.inv_comp_eq_id CategoryTheory.inv_comp_eq_id
-/

#print CategoryTheory.comp_inv_eq_id /-
theorem comp_inv_eq_id (g : X ⟶ Y) [IsIso g] {f : X ⟶ Y} : f ≫ inv g = 𝟙 X ↔ f = g :=
  (asIso g).comp_inv_eq_id
#align category_theory.comp_inv_eq_id CategoryTheory.comp_inv_eq_id
-/

#print CategoryTheory.isIso_of_hom_comp_eq_id /-
theorem isIso_of_hom_comp_eq_id (g : X ⟶ Y) [IsIso g] {f : Y ⟶ X} (h : g ≫ f = 𝟙 X) : IsIso f :=
  by
  rw [(hom_comp_eq_id _).mp h]
  infer_instance
#align category_theory.is_iso_of_hom_comp_eq_id CategoryTheory.isIso_of_hom_comp_eq_id
-/

#print CategoryTheory.isIso_of_comp_hom_eq_id /-
theorem isIso_of_comp_hom_eq_id (g : X ⟶ Y) [IsIso g] {f : Y ⟶ X} (h : f ≫ g = 𝟙 Y) : IsIso f :=
  by
  rw [(comp_hom_eq_id _).mp h]
  infer_instance
#align category_theory.is_iso_of_comp_hom_eq_id CategoryTheory.isIso_of_comp_hom_eq_id
-/

namespace Iso

#print CategoryTheory.Iso.inv_ext /-
@[ext]
theorem inv_ext {f : X ≅ Y} {g : Y ⟶ X} (hom_inv_id : f.Hom ≫ g = 𝟙 X) : f.inv = g :=
  ((hom_comp_eq_id f).1 hom_inv_id).symm
#align category_theory.iso.inv_ext CategoryTheory.Iso.inv_ext
-/

#print CategoryTheory.Iso.inv_ext' /-
@[ext]
theorem inv_ext' {f : X ≅ Y} {g : Y ⟶ X} (hom_inv_id : f.Hom ≫ g = 𝟙 X) : g = f.inv :=
  (hom_comp_eq_id f).1 hom_inv_id
#align category_theory.iso.inv_ext' CategoryTheory.Iso.inv_ext'
-/

/-!
All these cancellation lemmas can be solved by `simp [cancel_mono]` (or `simp [cancel_epi]`),
but with the current design `cancel_mono` is not a good `simp` lemma,
because it generates a typeclass search.

When we can see syntactically that a morphism is a `mono` or an `epi`
because it came from an isomorphism, it's fine to do the cancellation via `simp`.

In the longer term, it might be worth exploring making `mono` and `epi` structures,
rather than typeclasses, with coercions back to `X ⟶ Y`.
Presumably we could write `X ↪ Y` and `X ↠ Y`.
-/


#print CategoryTheory.Iso.cancel_iso_hom_left /-
@[simp]
theorem cancel_iso_hom_left {X Y Z : C} (f : X ≅ Y) (g g' : Y ⟶ Z) :
    f.Hom ≫ g = f.Hom ≫ g' ↔ g = g' := by simp only [cancel_epi]
#align category_theory.iso.cancel_iso_hom_left CategoryTheory.Iso.cancel_iso_hom_left
-/

#print CategoryTheory.Iso.cancel_iso_inv_left /-
@[simp]
theorem cancel_iso_inv_left {X Y Z : C} (f : Y ≅ X) (g g' : Y ⟶ Z) :
    f.inv ≫ g = f.inv ≫ g' ↔ g = g' := by simp only [cancel_epi]
#align category_theory.iso.cancel_iso_inv_left CategoryTheory.Iso.cancel_iso_inv_left
-/

#print CategoryTheory.Iso.cancel_iso_hom_right /-
@[simp]
theorem cancel_iso_hom_right {X Y Z : C} (f f' : X ⟶ Y) (g : Y ≅ Z) :
    f ≫ g.Hom = f' ≫ g.Hom ↔ f = f' := by simp only [cancel_mono]
#align category_theory.iso.cancel_iso_hom_right CategoryTheory.Iso.cancel_iso_hom_right
-/

#print CategoryTheory.Iso.cancel_iso_inv_right /-
@[simp]
theorem cancel_iso_inv_right {X Y Z : C} (f f' : X ⟶ Y) (g : Z ≅ Y) :
    f ≫ g.inv = f' ≫ g.inv ↔ f = f' := by simp only [cancel_mono]
#align category_theory.iso.cancel_iso_inv_right CategoryTheory.Iso.cancel_iso_inv_right
-/

#print CategoryTheory.Iso.cancel_iso_hom_right_assoc /-
/-
Unfortunately cancelling an isomorphism from the right of a chain of compositions is awkward.
We would need separate lemmas for each chain length (worse: for each pair of chain lengths).

We provide two more lemmas, for case of three morphisms, because this actually comes up in practice,
but then stop.
-/
@[simp]
theorem cancel_iso_hom_right_assoc {W X X' Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X')
    (g' : X' ⟶ Y) (h : Y ≅ Z) : f ≫ g ≫ h.Hom = f' ≫ g' ≫ h.Hom ↔ f ≫ g = f' ≫ g' := by
  simp only [← category.assoc, cancel_mono]
#align category_theory.iso.cancel_iso_hom_right_assoc CategoryTheory.Iso.cancel_iso_hom_right_assoc
-/

#print CategoryTheory.Iso.cancel_iso_inv_right_assoc /-
@[simp]
theorem cancel_iso_inv_right_assoc {W X X' Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X')
    (g' : X' ⟶ Y) (h : Z ≅ Y) : f ≫ g ≫ h.inv = f' ≫ g' ≫ h.inv ↔ f ≫ g = f' ≫ g' := by
  simp only [← category.assoc, cancel_mono]
#align category_theory.iso.cancel_iso_inv_right_assoc CategoryTheory.Iso.cancel_iso_inv_right_assoc
-/

end Iso

namespace Functor

universe u₁ v₁ u₂ v₂

variable {D : Type u₂}

variable [Category.{v₂} D]

/- warning: category_theory.functor.map_iso -> CategoryTheory.Functor.mapIso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} D] (F : CategoryTheory.Functor.{u1, u4, u2, u3} C _inst_1 D _inst_2) {X : C} {Y : C}, (CategoryTheory.Iso.{u1, u2} C _inst_1 X Y) -> (CategoryTheory.Iso.{u4, u3} D _inst_2 (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 F Y))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} D] (F : CategoryTheory.Functor.{u1, u4, u2, u3} C _inst_1 D _inst_2) {X : C} {Y : C}, (CategoryTheory.Iso.{u1, u2} C _inst_1 X Y) -> (CategoryTheory.Iso.{u4, u3} D _inst_2 (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) Y))
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_iso CategoryTheory.Functor.mapIsoₓ'. -/
/-- A functor `F : C ⥤ D` sends isomorphisms `i : X ≅ Y` to isomorphisms `F.obj X ≅ F.obj Y` -/
@[simps]
def mapIso (F : C ⥤ D) {X Y : C} (i : X ≅ Y) : F.obj X ≅ F.obj Y
    where
  Hom := F.map i.Hom
  inv := F.map i.inv
  hom_inv_id' := by rw [← map_comp, iso.hom_inv_id, ← map_id]
  inv_hom_id' := by rw [← map_comp, iso.inv_hom_id, ← map_id]
#align category_theory.functor.map_iso CategoryTheory.Functor.mapIso

/- warning: category_theory.functor.map_iso_symm -> CategoryTheory.Functor.mapIso_symm is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} D] (F : CategoryTheory.Functor.{u1, u4, u2, u3} C _inst_1 D _inst_2) {X : C} {Y : C} (i : CategoryTheory.Iso.{u1, u2} C _inst_1 X Y), Eq.{succ u4} (CategoryTheory.Iso.{u4, u3} D _inst_2 (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 F X)) (CategoryTheory.Functor.mapIso.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y X (CategoryTheory.Iso.symm.{u1, u2} C _inst_1 X Y i)) (CategoryTheory.Iso.symm.{u4, u3} D _inst_2 (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.mapIso.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y i))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} D] (F : CategoryTheory.Functor.{u1, u4, u2, u3} C _inst_1 D _inst_2) {X : C} {Y : C} (i : CategoryTheory.Iso.{u1, u2} C _inst_1 X Y), Eq.{succ u4} (CategoryTheory.Iso.{u4, u3} D _inst_2 (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) Y) (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) X)) (CategoryTheory.Functor.mapIso.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y X (CategoryTheory.Iso.symm.{u1, u2} C _inst_1 X Y i)) (CategoryTheory.Iso.symm.{u4, u3} D _inst_2 (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) Y) (CategoryTheory.Functor.mapIso.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y i))
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_iso_symm CategoryTheory.Functor.mapIso_symmₓ'. -/
@[simp]
theorem mapIso_symm (F : C ⥤ D) {X Y : C} (i : X ≅ Y) : F.mapIso i.symm = (F.mapIso i).symm :=
  rfl
#align category_theory.functor.map_iso_symm CategoryTheory.Functor.mapIso_symm

/- warning: category_theory.functor.map_iso_trans -> CategoryTheory.Functor.mapIso_trans is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} D] (F : CategoryTheory.Functor.{u1, u4, u2, u3} C _inst_1 D _inst_2) {X : C} {Y : C} {Z : C} (i : CategoryTheory.Iso.{u1, u2} C _inst_1 X Y) (j : CategoryTheory.Iso.{u1, u2} C _inst_1 Y Z), Eq.{succ u4} (CategoryTheory.Iso.{u4, u3} D _inst_2 (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 F Z)) (CategoryTheory.Functor.mapIso.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Z (CategoryTheory.Iso.trans.{u1, u2} C _inst_1 X Y Z i j)) (CategoryTheory.Iso.trans.{u4, u3} D _inst_2 (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 F Z) (CategoryTheory.Functor.mapIso.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y i) (CategoryTheory.Functor.mapIso.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y Z j))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} D] (F : CategoryTheory.Functor.{u1, u4, u2, u3} C _inst_1 D _inst_2) {X : C} {Y : C} {Z : C} (i : CategoryTheory.Iso.{u1, u2} C _inst_1 X Y) (j : CategoryTheory.Iso.{u1, u2} C _inst_1 Y Z), Eq.{succ u4} (CategoryTheory.Iso.{u4, u3} D _inst_2 (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) Z)) (CategoryTheory.Functor.mapIso.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Z (CategoryTheory.Iso.trans.{u1, u2} C _inst_1 X Y Z i j)) (CategoryTheory.Iso.trans.{u4, u3} D _inst_2 (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) Y) (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) Z) (CategoryTheory.Functor.mapIso.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y i) (CategoryTheory.Functor.mapIso.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y Z j))
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_iso_trans CategoryTheory.Functor.mapIso_transₓ'. -/
@[simp]
theorem mapIso_trans (F : C ⥤ D) {X Y Z : C} (i : X ≅ Y) (j : Y ≅ Z) :
    F.mapIso (i ≪≫ j) = F.mapIso i ≪≫ F.mapIso j := by ext <;> apply functor.map_comp
#align category_theory.functor.map_iso_trans CategoryTheory.Functor.mapIso_trans

/- warning: category_theory.functor.map_iso_refl -> CategoryTheory.Functor.mapIso_refl is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} D] (F : CategoryTheory.Functor.{u1, u4, u2, u3} C _inst_1 D _inst_2) (X : C), Eq.{succ u4} (CategoryTheory.Iso.{u4, u3} D _inst_2 (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 F X)) (CategoryTheory.Functor.mapIso.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X X (CategoryTheory.Iso.refl.{u1, u2} C _inst_1 X)) (CategoryTheory.Iso.refl.{u4, u3} D _inst_2 (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 F X))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} D] (F : CategoryTheory.Functor.{u1, u4, u2, u3} C _inst_1 D _inst_2) (X : C), Eq.{succ u4} (CategoryTheory.Iso.{u4, u3} D _inst_2 (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) X)) (CategoryTheory.Functor.mapIso.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X X (CategoryTheory.Iso.refl.{u1, u2} C _inst_1 X)) (CategoryTheory.Iso.refl.{u4, u3} D _inst_2 (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) X))
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_iso_refl CategoryTheory.Functor.mapIso_reflₓ'. -/
@[simp]
theorem mapIso_refl (F : C ⥤ D) (X : C) : F.mapIso (Iso.refl X) = Iso.refl (F.obj X) :=
  Iso.ext <| F.map_id X
#align category_theory.functor.map_iso_refl CategoryTheory.Functor.mapIso_refl

/- warning: category_theory.functor.map_is_iso -> CategoryTheory.Functor.map_isIso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} D] (F : CategoryTheory.Functor.{u1, u4, u2, u3} C _inst_1 D _inst_2) (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) [_inst_3 : CategoryTheory.IsIso.{u1, u2} C _inst_1 X Y f], CategoryTheory.IsIso.{u4, u3} D _inst_2 (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.map.{u1, u4, u2, u3} C _inst_1 D _inst_2 F X Y f)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} D] (F : CategoryTheory.Functor.{u1, u4, u2, u3} C _inst_1 D _inst_2) (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) [_inst_3 : CategoryTheory.IsIso.{u1, u2} C _inst_1 X Y f], CategoryTheory.IsIso.{u4, u3} D _inst_2 (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) Y) (Prefunctor.map.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) X Y f)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_is_iso CategoryTheory.Functor.map_isIsoₓ'. -/
instance map_isIso (F : C ⥤ D) (f : X ⟶ Y) [IsIso f] : IsIso (F.map f) :=
  IsIso.of_iso <| F.mapIso (asIso f)
#align category_theory.functor.map_is_iso CategoryTheory.Functor.map_isIso

/- warning: category_theory.functor.map_inv -> CategoryTheory.Functor.map_inv is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} D] (F : CategoryTheory.Functor.{u1, u4, u2, u3} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) [_inst_3 : CategoryTheory.IsIso.{u1, u2} C _inst_1 X Y f], Eq.{succ u4} (Quiver.Hom.{succ u4, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 F X)) (CategoryTheory.Functor.map.{u1, u4, u2, u3} C _inst_1 D _inst_2 F Y X (CategoryTheory.inv.{u1, u2} C _inst_1 X Y f _inst_3)) (CategoryTheory.inv.{u4, u3} D _inst_2 (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.map.{u1, u4, u2, u3} C _inst_1 D _inst_2 F X Y f) (CategoryTheory.Functor.map_isIso.{u1, u2, u3, u4} C _inst_1 X Y D _inst_2 F f _inst_3))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} D] (F : CategoryTheory.Functor.{u1, u4, u2, u3} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) [_inst_3 : CategoryTheory.IsIso.{u1, u2} C _inst_1 X Y f], Eq.{succ u4} (Quiver.Hom.{succ u4, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) Y) (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) X)) (Prefunctor.map.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) Y X (CategoryTheory.inv.{u1, u2} C _inst_1 X Y f _inst_3)) (CategoryTheory.inv.{u4, u3} D _inst_2 (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) Y) (Prefunctor.map.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) X Y f) (CategoryTheory.Functor.map_isIso.{u1, u2, u3, u4} C _inst_1 X Y D _inst_2 F f _inst_3))
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_inv CategoryTheory.Functor.map_invₓ'. -/
@[simp]
theorem map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [IsIso f] : F.map (inv f) = inv (F.map f) :=
  by
  ext
  simp [← F.map_comp]
#align category_theory.functor.map_inv CategoryTheory.Functor.map_inv

/- warning: category_theory.functor.map_hom_inv -> CategoryTheory.Functor.map_hom_inv is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} D] (F : CategoryTheory.Functor.{u1, u4, u2, u3} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) [_inst_3 : CategoryTheory.IsIso.{u1, u2} C _inst_1 X Y f], Eq.{succ u4} (Quiver.Hom.{succ u4, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 F X)) (CategoryTheory.CategoryStruct.comp.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2) (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.map.{u1, u4, u2, u3} C _inst_1 D _inst_2 F X Y f) (CategoryTheory.Functor.map.{u1, u4, u2, u3} C _inst_1 D _inst_2 F Y X (CategoryTheory.inv.{u1, u2} C _inst_1 X Y f _inst_3))) (CategoryTheory.CategoryStruct.id.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2) (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 F X))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} D] (F : CategoryTheory.Functor.{u1, u4, u2, u3} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) [_inst_3 : CategoryTheory.IsIso.{u1, u2} C _inst_1 X Y f], Eq.{succ u4} (Quiver.Hom.{succ u4, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) X)) (CategoryTheory.CategoryStruct.comp.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2) (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) Y) (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) X) (Prefunctor.map.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) X Y f) (Prefunctor.map.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) Y X (CategoryTheory.inv.{u1, u2} C _inst_1 X Y f _inst_3))) (CategoryTheory.CategoryStruct.id.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2) (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) X))
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_hom_inv CategoryTheory.Functor.map_hom_invₓ'. -/
theorem map_hom_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [IsIso f] :
    F.map f ≫ F.map (inv f) = 𝟙 (F.obj X) := by simp
#align category_theory.functor.map_hom_inv CategoryTheory.Functor.map_hom_inv

/- warning: category_theory.functor.map_inv_hom -> CategoryTheory.Functor.map_inv_hom is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} D] (F : CategoryTheory.Functor.{u1, u4, u2, u3} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) [_inst_3 : CategoryTheory.IsIso.{u1, u2} C _inst_1 X Y f], Eq.{succ u4} (Quiver.Hom.{succ u4, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 F Y)) (CategoryTheory.CategoryStruct.comp.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2) (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.map.{u1, u4, u2, u3} C _inst_1 D _inst_2 F Y X (CategoryTheory.inv.{u1, u2} C _inst_1 X Y f _inst_3)) (CategoryTheory.Functor.map.{u1, u4, u2, u3} C _inst_1 D _inst_2 F X Y f)) (CategoryTheory.CategoryStruct.id.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2) (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 F Y))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} D] (F : CategoryTheory.Functor.{u1, u4, u2, u3} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) [_inst_3 : CategoryTheory.IsIso.{u1, u2} C _inst_1 X Y f], Eq.{succ u4} (Quiver.Hom.{succ u4, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) Y) (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) Y)) (CategoryTheory.CategoryStruct.comp.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2) (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) Y) (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) Y) (Prefunctor.map.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) Y X (CategoryTheory.inv.{u1, u2} C _inst_1 X Y f _inst_3)) (Prefunctor.map.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) X Y f)) (CategoryTheory.CategoryStruct.id.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2) (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) Y))
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_inv_hom CategoryTheory.Functor.map_inv_homₓ'. -/
theorem map_inv_hom (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [IsIso f] :
    F.map (inv f) ≫ F.map f = 𝟙 (F.obj Y) := by simp
#align category_theory.functor.map_inv_hom CategoryTheory.Functor.map_inv_hom

end Functor

end CategoryTheory

