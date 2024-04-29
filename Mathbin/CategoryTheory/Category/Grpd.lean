/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import CategoryTheory.SingleObj
import CategoryTheory.Limits.Shapes.Products
import CategoryTheory.Pi.Basic
import CategoryTheory.Limits.IsLimit

#align_import category_theory.category.Groupoid from "leanprover-community/mathlib"@"fe8d0ff42c3c24d789f491dc2622b6cac3d61564"

/-!
# Category of groupoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains the definition of the category `Groupoid` of all groupoids.
In this category objects are groupoids and morphisms are functors
between these groupoids.

We also provide two “forgetting” functors: `objects : Groupoid ⥤ Type`
and `forget_to_Cat : Groupoid ⥤ Cat`.

## Implementation notes

Though `Groupoid` is not a concrete category, we use `bundled` to define
its carrier type.
-/


universe v u

namespace CategoryTheory

#print CategoryTheory.Grpd /-
-- intended to be used with explicit universe parameters
/-- Category of groupoids -/
@[nolint check_univs]
def Grpd :=
  Bundled Groupoid.{v, u}
#align category_theory.Groupoid CategoryTheory.Grpd
-/

namespace Groupoid

instance : Inhabited Grpd :=
  ⟨Bundled.of (SingleObj PUnit)⟩

#print CategoryTheory.Grpd.str' /-
instance str' (C : Grpd.{v, u}) : Groupoid.{v, u} C.α :=
  C.str
#align category_theory.Groupoid.str CategoryTheory.Grpd.str'
-/

instance : CoeSort Grpd (Type _) :=
  Bundled.hasCoeToSort

#print CategoryTheory.Grpd.of /-
/-- Construct a bundled `Groupoid` from the underlying type and the typeclass. -/
def of (C : Type u) [Groupoid.{v} C] : Grpd.{v, u} :=
  Bundled.of C
#align category_theory.Groupoid.of CategoryTheory.Grpd.of
-/

#print CategoryTheory.Grpd.coe_of /-
@[simp]
theorem coe_of (C : Type u) [Groupoid C] : (of C : Type u) = C :=
  rfl
#align category_theory.Groupoid.coe_of CategoryTheory.Grpd.coe_of
-/

#print CategoryTheory.Grpd.category /-
/-- Category structure on `Groupoid` -/
instance category : LargeCategory.{max v u} Grpd.{v, u}
    where
  Hom C D := C ⥤ D
  id C := 𝟭 C
  comp C D E F G := F ⋙ G
  id_comp' C D F := by cases F <;> rfl
  comp_id' C D F := by cases F <;> rfl
  assoc' := by intros <;> rfl
#align category_theory.Groupoid.category CategoryTheory.Grpd.category
-/

#print CategoryTheory.Grpd.objects /-
/-- Functor that gets the set of objects of a groupoid. It is not
called `forget`, because it is not a faithful functor. -/
def objects : Grpd.{v, u} ⥤ Type u where
  obj := Bundled.α
  map C D F := F.obj
#align category_theory.Groupoid.objects CategoryTheory.Grpd.objects
-/

#print CategoryTheory.Grpd.forgetToCat /-
/-- Forgetting functor to `Cat` -/
def forgetToCat : Grpd.{v, u} ⥤ Cat.{v, u}
    where
  obj C := Cat.of C
  map C D := id
#align category_theory.Groupoid.forget_to_Cat CategoryTheory.Grpd.forgetToCat
-/

#print CategoryTheory.Grpd.forgetToCat_full /-
instance forgetToCat_full : CategoryTheory.Functor.Full forgetToCat where preimage C D := id
#align category_theory.Groupoid.forget_to_Cat_full CategoryTheory.Grpd.forgetToCat_full
-/

#print CategoryTheory.Grpd.forgetToCat_faithful /-
instance forgetToCat_faithful : CategoryTheory.Functor.Faithful forgetToCat where
#align category_theory.Groupoid.forget_to_Cat_faithful CategoryTheory.Grpd.forgetToCat_faithful
-/

#print CategoryTheory.Grpd.hom_to_functor /-
/-- Convert arrows in the category of groupoids to functors,
which sometimes helps in applying simp lemmas -/
theorem hom_to_functor {C D E : Grpd.{v, u}} (f : C ⟶ D) (g : D ⟶ E) : f ≫ g = f ⋙ g :=
  rfl
#align category_theory.Groupoid.hom_to_functor CategoryTheory.Grpd.hom_to_functor
-/

#print CategoryTheory.Grpd.id_to_functor /-
/-- Converts identity in the category of groupoids to the functor identity -/
theorem id_to_functor {C : Grpd.{v, u}} : 𝟭 C = 𝟙 C :=
  rfl
#align category_theory.Groupoid.id_to_functor CategoryTheory.Grpd.id_to_functor
-/

section Products

attribute [local tidy] tactic.discrete_cases

#print CategoryTheory.Grpd.piLimitFan /-
/-- Construct the product over an indexed family of groupoids, as a fan. -/
def piLimitFan ⦃J : Type u⦄ (F : J → Grpd.{u, u}) : Limits.Fan F :=
  Limits.Fan.mk (@of (∀ j : J, F j) _) fun j => CategoryTheory.Pi.eval _ j
#align category_theory.Groupoid.pi_limit_fan CategoryTheory.Grpd.piLimitFan
-/

#print CategoryTheory.Grpd.piLimitFanIsLimit /-
/-- The product fan over an indexed family of groupoids, is a limit cone. -/
def piLimitFanIsLimit ⦃J : Type u⦄ (F : J → Grpd.{u, u}) : Limits.IsLimit (piLimitFan F) :=
  Limits.mkFanLimit (piLimitFan F) (fun s => Functor.pi' fun j => s.proj j)
    (by intros; dsimp only [pi_limit_fan]; simp [hom_to_functor])
    (by
      intro s m w
      apply functor.pi_ext
      intro j; specialize w j
      simpa)
#align category_theory.Groupoid.pi_limit_fan_is_limit CategoryTheory.Grpd.piLimitFanIsLimit
-/

#print CategoryTheory.Grpd.has_pi /-
instance has_pi : Limits.HasProducts Grpd.{u, u} :=
  Limits.hasProducts_of_limit_fans piLimitFan piLimitFanIsLimit
#align category_theory.Groupoid.has_pi CategoryTheory.Grpd.has_pi
-/

#print CategoryTheory.Grpd.piIsoPi /-
/-- The product of a family of groupoids is isomorphic
to the product object in the category of Groupoids -/
noncomputable def piIsoPi (J : Type u) (f : J → Grpd.{u, u}) : @of (∀ j, f j) _ ≅ ∏ f :=
  Limits.IsLimit.conePointUniqueUpToIso (piLimitFanIsLimit f)
    (Limits.limit.isLimit (Discrete.functor f))
#align category_theory.Groupoid.pi_iso_pi CategoryTheory.Grpd.piIsoPi
-/

#print CategoryTheory.Grpd.piIsoPi_hom_π /-
@[simp]
theorem piIsoPi_hom_π (J : Type u) (f : J → Grpd.{u, u}) (j : J) :
    (piIsoPi J f).Hom ≫ Limits.Pi.π f j = CategoryTheory.Pi.eval _ j := by simp [pi_iso_pi]; rfl
#align category_theory.Groupoid.pi_iso_pi_hom_π CategoryTheory.Grpd.piIsoPi_hom_π
-/

end Products

end Groupoid

end CategoryTheory

