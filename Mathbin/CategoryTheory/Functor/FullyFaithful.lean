/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.functor.fully_faithful
! leanprover-community/mathlib commit 26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.NaturalIsomorphism
import Mathbin.Logic.Equiv.Defs

/-!
# Full and faithful functors

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define typeclasses `full` and `faithful`, decorating functors.

## Main definitions and results
* Use `F.map_injective` to retrieve the fact that `F.map` is injective when `[faithful F]`.
* Similarly, `F.map_surjective` states that `F.map` is surjective when `[full F]`.
* Use `F.preimage` to obtain preimages of morphisms when `[full F]`.
* We prove some basic "cancellation" lemmas for full and/or faithful functors, as well as a
  construction for "dividing" a functor by a faithful functor, see `faithful.div`.
* `full F` carries data, so definitional properties of the preimage can be used when using
  `F.preimage`. To obtain an instance of `full F` non-constructively, you can use `full_of_exists`
  and `full_of_surjective`.

See `category_theory.equivalence.of_fully_faithful_ess_surj` for the fact that a functor is an
equivalence if and only if it is fully faithful and essentially surjective.

-/


-- declare the `v`'s first; see `category_theory.category` for an explanation
universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

#print CategoryTheory.Full /-
/-- A functor `F : C ⥤ D` is full if for each `X Y : C`, `F.map` is surjective.
In fact, we use a constructive definition, so the `full F` typeclass contains data,
specifying a particular preimage of each `f : F.obj X ⟶ F.obj Y`.

See <https://stacks.math.columbia.edu/tag/001C>.
-/
class Full (F : C ⥤ D) where
  preimage : ∀ {X Y : C} (f : F.obj X ⟶ F.obj Y), X ⟶ Y
  witness' : ∀ {X Y : C} (f : F.obj X ⟶ F.obj Y), F.map (preimage f) = f := by obviously
#align category_theory.full CategoryTheory.Full
-/

restate_axiom full.witness'

attribute [simp] full.witness

#print CategoryTheory.Faithful /-
/- ./././Mathport/Syntax/Translate/Command.lean:379:30: infer kinds are unsupported in Lean 4: #[`map_injective'] [] -/
/-- A functor `F : C ⥤ D` is faithful if for each `X Y : C`, `F.map` is injective.

See <https://stacks.math.columbia.edu/tag/001C>.
-/
class Faithful (F : C ⥤ D) : Prop where
  map_injective' : ∀ {X Y : C}, Function.Injective (@Functor.map _ _ _ _ F X Y) := by obviously
#align category_theory.faithful CategoryTheory.Faithful
-/

restate_axiom faithful.map_injective'

namespace Functor

variable {X Y : C}

/- warning: category_theory.functor.map_injective -> CategoryTheory.Functor.map_injective is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] {X : C} {Y : C} (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_3 : CategoryTheory.Faithful.{u1, u2, u3, u4} C _inst_1 D _inst_2 F], Function.Injective.{succ u1, succ u2} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y)) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] {X : C} {Y : C} (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_3 : CategoryTheory.Faithful.{u1, u2, u3, u4} C _inst_1 D _inst_2 F], Function.Injective.{succ u1, succ u2} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y)) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X Y)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_injective CategoryTheory.Functor.map_injectiveₓ'. -/
theorem map_injective (F : C ⥤ D) [Faithful F] : Function.Injective <| @Functor.map _ _ _ _ F X Y :=
  Faithful.map_injective F
#align category_theory.functor.map_injective CategoryTheory.Functor.map_injective

/- warning: category_theory.functor.map_iso_injective -> CategoryTheory.Functor.mapIso_injective is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] {X : C} {Y : C} (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_3 : CategoryTheory.Faithful.{u1, u2, u3, u4} C _inst_1 D _inst_2 F], Function.Injective.{succ u1, succ u2} (CategoryTheory.Iso.{u1, u3} C _inst_1 X Y) (CategoryTheory.Iso.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y)) (CategoryTheory.Functor.mapIso.{u1, u3, u4, u2} C _inst_1 D _inst_2 F X Y)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] {X : C} {Y : C} (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_3 : CategoryTheory.Faithful.{u1, u2, u3, u4} C _inst_1 D _inst_2 F], Function.Injective.{succ u1, succ u2} (CategoryTheory.Iso.{u1, u3} C _inst_1 X Y) (CategoryTheory.Iso.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y)) (CategoryTheory.Functor.mapIso.{u1, u3, u4, u2} C _inst_1 D _inst_2 F X Y)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_iso_injective CategoryTheory.Functor.mapIso_injectiveₓ'. -/
theorem mapIso_injective (F : C ⥤ D) [Faithful F] :
    Function.Injective <| @Functor.mapIso _ _ _ _ F X Y := fun i j h =>
  Iso.ext (map_injective F (congr_arg Iso.hom h : _))
#align category_theory.functor.map_iso_injective CategoryTheory.Functor.mapIso_injective

/- warning: category_theory.functor.preimage -> CategoryTheory.Functor.preimage is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] {X : C} {Y : C} (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_3 : CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F], (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y)) -> (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] {X : C} {Y : C} (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_3 : CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F], (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y)) -> (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.preimage CategoryTheory.Functor.preimageₓ'. -/
/-- The specified preimage of a morphism under a full functor. -/
def preimage (F : C ⥤ D) [Full F] (f : F.obj X ⟶ F.obj Y) : X ⟶ Y :=
  Full.preimage.{v₁, v₂} f
#align category_theory.functor.preimage CategoryTheory.Functor.preimage

/- warning: category_theory.functor.image_preimage -> CategoryTheory.Functor.image_preimage is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_3 : CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] {X : C} {Y : C} (f : Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y)), Eq.{succ u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y)) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y (CategoryTheory.Functor.preimage.{u1, u2, u3, u4} C _inst_1 D _inst_2 X Y F _inst_3 f)) f
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_3 : CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] {X : C} {Y : C} (f : Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y)), Eq.{succ u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y)) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X Y (CategoryTheory.Functor.preimage.{u1, u2, u3, u4} C _inst_1 D _inst_2 X Y F _inst_3 f)) f
Case conversion may be inaccurate. Consider using '#align category_theory.functor.image_preimage CategoryTheory.Functor.image_preimageₓ'. -/
@[simp]
theorem image_preimage (F : C ⥤ D) [Full F] {X Y : C} (f : F.obj X ⟶ F.obj Y) :
    F.map (preimage F f) = f := by unfold preimage <;> obviously
#align category_theory.functor.image_preimage CategoryTheory.Functor.image_preimage

/- warning: category_theory.functor.map_surjective -> CategoryTheory.Functor.map_surjective is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] {X : C} {Y : C} (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_3 : CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F], Function.Surjective.{succ u1, succ u2} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y)) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] {X : C} {Y : C} (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_3 : CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F], Function.Surjective.{succ u1, succ u2} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y)) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X Y)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_surjective CategoryTheory.Functor.map_surjectiveₓ'. -/
theorem map_surjective (F : C ⥤ D) [Full F] : Function.Surjective (@Functor.map _ _ _ _ F X Y) :=
  fun f => ⟨F.preimage f, F.image_preimage f⟩
#align category_theory.functor.map_surjective CategoryTheory.Functor.map_surjective

/- warning: category_theory.functor.full_of_exists -> CategoryTheory.Functor.fullOfExists is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2), (forall (X : C) (Y : C) (f : Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y)), Exists.{succ u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (fun (p : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) => Eq.{succ u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y)) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y p) f)) -> (CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2), (forall (X : C) (Y : C) (f : Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y)), Exists.{succ u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (fun (p : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) => Eq.{succ u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y)) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X Y p) f)) -> (CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.full_of_exists CategoryTheory.Functor.fullOfExistsₓ'. -/
/-- Deduce that `F` is full from the existence of preimages, using choice. -/
noncomputable def fullOfExists (F : C ⥤ D)
    (h : ∀ (X Y : C) (f : F.obj X ⟶ F.obj Y), ∃ p, F.map p = f) : Full F :=
  by
  choose p hp using h
  exact ⟨p, hp⟩
#align category_theory.functor.full_of_exists CategoryTheory.Functor.fullOfExists

/- warning: category_theory.functor.full_of_surjective -> CategoryTheory.Functor.fullOfSurjective is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2), (forall (X : C) (Y : C), Function.Surjective.{succ u1, succ u2} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y)) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y)) -> (CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2), (forall (X : C) (Y : C), Function.Surjective.{succ u1, succ u2} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y)) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X Y)) -> (CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.full_of_surjective CategoryTheory.Functor.fullOfSurjectiveₓ'. -/
/-- Deduce that `F` is full from surjectivity of `F.map`, using choice. -/
noncomputable def fullOfSurjective (F : C ⥤ D)
    (h : ∀ X Y : C, Function.Surjective (@Functor.map _ _ _ _ F X Y)) : Full F :=
  fullOfExists _ h
#align category_theory.functor.full_of_surjective CategoryTheory.Functor.fullOfSurjective

end Functor

section

variable {F : C ⥤ D} [Full F] [Faithful F] {X Y Z : C}

/- warning: category_theory.preimage_id -> CategoryTheory.preimage_id is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] {F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} [_inst_3 : CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] [_inst_4 : CategoryTheory.Faithful.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] {X : C}, Eq.{succ u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X X) (CategoryTheory.Functor.preimage.{u1, u2, u3, u4} C _inst_1 D _inst_2 X X F _inst_3 (CategoryTheory.CategoryStruct.id.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X))) (CategoryTheory.CategoryStruct.id.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1) X)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] {F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} [_inst_3 : CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] [_inst_4 : CategoryTheory.Faithful.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] {X : C}, Eq.{succ u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X X) (CategoryTheory.Functor.preimage.{u1, u2, u3, u4} C _inst_1 D _inst_2 X X F _inst_3 (CategoryTheory.CategoryStruct.id.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X))) (CategoryTheory.CategoryStruct.id.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1) X)
Case conversion may be inaccurate. Consider using '#align category_theory.preimage_id CategoryTheory.preimage_idₓ'. -/
@[simp]
theorem preimage_id : F.preimage (𝟙 (F.obj X)) = 𝟙 X :=
  F.map_injective (by simp)
#align category_theory.preimage_id CategoryTheory.preimage_id

/- warning: category_theory.preimage_comp -> CategoryTheory.preimage_comp is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] {F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} [_inst_3 : CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] [_inst_4 : CategoryTheory.Faithful.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y)) (g : Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Z)), Eq.{succ u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Z) (CategoryTheory.Functor.preimage.{u1, u2, u3, u4} C _inst_1 D _inst_2 X Z F _inst_3 (CategoryTheory.CategoryStruct.comp.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Z) f g)) (CategoryTheory.CategoryStruct.comp.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1) X Y Z (CategoryTheory.Functor.preimage.{u1, u2, u3, u4} C _inst_1 D _inst_2 X Y F _inst_3 f) (CategoryTheory.Functor.preimage.{u1, u2, u3, u4} C _inst_1 D _inst_2 Y Z F _inst_3 g))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] {F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} [_inst_3 : CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] [_inst_4 : CategoryTheory.Faithful.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y)) (g : Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Z)), Eq.{succ u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Z) (CategoryTheory.Functor.preimage.{u1, u2, u3, u4} C _inst_1 D _inst_2 X Z F _inst_3 (CategoryTheory.CategoryStruct.comp.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Z) f g)) (CategoryTheory.CategoryStruct.comp.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1) X Y Z (CategoryTheory.Functor.preimage.{u1, u2, u3, u4} C _inst_1 D _inst_2 X Y F _inst_3 f) (CategoryTheory.Functor.preimage.{u1, u2, u3, u4} C _inst_1 D _inst_2 Y Z F _inst_3 g))
Case conversion may be inaccurate. Consider using '#align category_theory.preimage_comp CategoryTheory.preimage_compₓ'. -/
@[simp]
theorem preimage_comp (f : F.obj X ⟶ F.obj Y) (g : F.obj Y ⟶ F.obj Z) :
    F.preimage (f ≫ g) = F.preimage f ≫ F.preimage g :=
  F.map_injective (by simp)
#align category_theory.preimage_comp CategoryTheory.preimage_comp

/- warning: category_theory.preimage_map -> CategoryTheory.preimage_map is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] {F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} [_inst_3 : CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] [_inst_4 : CategoryTheory.Faithful.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y), Eq.{succ u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (CategoryTheory.Functor.preimage.{u1, u2, u3, u4} C _inst_1 D _inst_2 X Y F _inst_3 (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y f)) f
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] {F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} [_inst_3 : CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] [_inst_4 : CategoryTheory.Faithful.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y), Eq.{succ u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (CategoryTheory.Functor.preimage.{u1, u2, u3, u4} C _inst_1 D _inst_2 X Y F _inst_3 (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X Y f)) f
Case conversion may be inaccurate. Consider using '#align category_theory.preimage_map CategoryTheory.preimage_mapₓ'. -/
@[simp]
theorem preimage_map (f : X ⟶ Y) : F.preimage (F.map f) = f :=
  F.map_injective (by simp)
#align category_theory.preimage_map CategoryTheory.preimage_map

variable (F)

namespace Functor

/- warning: category_theory.functor.preimage_iso -> CategoryTheory.Functor.preimageIso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_3 : CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] [_inst_4 : CategoryTheory.Faithful.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] {X : C} {Y : C}, (CategoryTheory.Iso.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y)) -> (CategoryTheory.Iso.{u1, u3} C _inst_1 X Y)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_3 : CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] [_inst_4 : CategoryTheory.Faithful.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] {X : C} {Y : C}, (CategoryTheory.Iso.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y)) -> (CategoryTheory.Iso.{u1, u3} C _inst_1 X Y)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.preimage_iso CategoryTheory.Functor.preimageIsoₓ'. -/
/-- If `F : C ⥤ D` is fully faithful, every isomorphism `F.obj X ≅ F.obj Y` has a preimage. -/
@[simps]
def preimageIso (f : F.obj X ≅ F.obj Y) : X ≅ Y
    where
  Hom := F.preimage f.Hom
  inv := F.preimage f.inv
  hom_inv_id' := F.map_injective (by simp)
  inv_hom_id' := F.map_injective (by simp)
#align category_theory.functor.preimage_iso CategoryTheory.Functor.preimageIso

#print CategoryTheory.Functor.preimageIso_mapIso /-
@[simp]
theorem preimageIso_mapIso (f : X ≅ Y) : F.preimageIso (F.mapIso f) = f :=
  by
  ext
  simp
#align category_theory.functor.preimage_iso_map_iso CategoryTheory.Functor.preimageIso_mapIso
-/

end Functor

/- warning: category_theory.is_iso_of_fully_faithful -> CategoryTheory.isIso_of_fully_faithful is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_3 : CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] [_inst_4 : CategoryTheory.Faithful.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_5 : CategoryTheory.IsIso.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y f)], CategoryTheory.IsIso.{u1, u3} C _inst_1 X Y f
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_3 : CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] [_inst_4 : CategoryTheory.Faithful.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_5 : CategoryTheory.IsIso.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X Y f)], CategoryTheory.IsIso.{u1, u3} C _inst_1 X Y f
Case conversion may be inaccurate. Consider using '#align category_theory.is_iso_of_fully_faithful CategoryTheory.isIso_of_fully_faithfulₓ'. -/
/-- If the image of a morphism under a fully faithful functor in an isomorphism,
then the original morphisms is also an isomorphism.
-/
theorem isIso_of_fully_faithful (f : X ⟶ Y) [IsIso (F.map f)] : IsIso f :=
  ⟨⟨F.preimage (inv (F.map f)), ⟨F.map_injective (by simp), F.map_injective (by simp)⟩⟩⟩
#align category_theory.is_iso_of_fully_faithful CategoryTheory.isIso_of_fully_faithful

/- warning: category_theory.equiv_of_fully_faithful -> CategoryTheory.equivOfFullyFaithful is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_3 : CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] [_inst_4 : CategoryTheory.Faithful.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] {X : C} {Y : C}, Equiv.{succ u1, succ u2} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_3 : CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] [_inst_4 : CategoryTheory.Faithful.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] {X : C} {Y : C}, Equiv.{succ u1, succ u2} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y))
Case conversion may be inaccurate. Consider using '#align category_theory.equiv_of_fully_faithful CategoryTheory.equivOfFullyFaithfulₓ'. -/
/-- If `F` is fully faithful, we have an equivalence of hom-sets `X ⟶ Y` and `F X ⟶ F Y`. -/
@[simps]
def equivOfFullyFaithful {X Y} : (X ⟶ Y) ≃ (F.obj X ⟶ F.obj Y)
    where
  toFun f := F.map f
  invFun f := F.preimage f
  left_inv f := by simp
  right_inv f := by simp
#align category_theory.equiv_of_fully_faithful CategoryTheory.equivOfFullyFaithful

/- warning: category_theory.iso_equiv_of_fully_faithful -> CategoryTheory.isoEquivOfFullyFaithful is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_3 : CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] [_inst_4 : CategoryTheory.Faithful.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] {X : C} {Y : C}, Equiv.{succ u1, succ u2} (CategoryTheory.Iso.{u1, u3} C _inst_1 X Y) (CategoryTheory.Iso.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_3 : CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] [_inst_4 : CategoryTheory.Faithful.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] {X : C} {Y : C}, Equiv.{succ u1, succ u2} (CategoryTheory.Iso.{u1, u3} C _inst_1 X Y) (CategoryTheory.Iso.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y))
Case conversion may be inaccurate. Consider using '#align category_theory.iso_equiv_of_fully_faithful CategoryTheory.isoEquivOfFullyFaithfulₓ'. -/
/-- If `F` is fully faithful, we have an equivalence of iso-sets `X ≅ Y` and `F X ≅ F Y`. -/
@[simps]
def isoEquivOfFullyFaithful {X Y} : (X ≅ Y) ≃ (F.obj X ≅ F.obj Y)
    where
  toFun f := F.mapIso f
  invFun f := F.preimageIso f
  left_inv f := by simp
  right_inv f := by
    ext
    simp
#align category_theory.iso_equiv_of_fully_faithful CategoryTheory.isoEquivOfFullyFaithful

end

section

variable {E : Type _} [Category E] {F G : C ⥤ D} (H : D ⥤ E) [Full H] [Faithful H]

#print CategoryTheory.natTransOfCompFullyFaithful /-
/-- We can construct a natural transformation between functors by constructing a
natural transformation between those functors composed with a fully faithful functor. -/
@[simps]
def natTransOfCompFullyFaithful (α : F ⋙ H ⟶ G ⋙ H) : F ⟶ G
    where
  app X := (equivOfFullyFaithful H).symm (α.app X)
  naturality' X Y f := by
    dsimp
    apply H.map_injective
    simpa using α.naturality f
#align category_theory.nat_trans_of_comp_fully_faithful CategoryTheory.natTransOfCompFullyFaithful
-/

#print CategoryTheory.natIsoOfCompFullyFaithful /-
/-- We can construct a natural isomorphism between functors by constructing a natural isomorphism
between those functors composed with a fully faithful functor. -/
@[simps]
def natIsoOfCompFullyFaithful (i : F ⋙ H ≅ G ⋙ H) : F ≅ G :=
  NatIso.ofComponents (fun X => (isoEquivOfFullyFaithful H).symm (i.app X)) fun X Y f =>
    by
    dsimp
    apply H.map_injective
    simpa using i.hom.naturality f
#align category_theory.nat_iso_of_comp_fully_faithful CategoryTheory.natIsoOfCompFullyFaithful
-/

/- warning: category_theory.nat_iso_of_comp_fully_faithful_hom -> CategoryTheory.natIsoOfCompFullyFaithful_hom is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] {E : Type.{u5}} [_inst_3 : CategoryTheory.Category.{u6, u5} E] {F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} {G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} (H : CategoryTheory.Functor.{u2, u6, u4, u5} D _inst_2 E _inst_3) [_inst_4 : CategoryTheory.Full.{u2, u6, u4, u5} D _inst_2 E _inst_3 H] [_inst_5 : CategoryTheory.Faithful.{u2, u6, u4, u5} D _inst_2 E _inst_3 H] (i : CategoryTheory.Iso.{max u3 u6, max u1 u6 u3 u5} (CategoryTheory.Functor.{u1, u6, u3, u5} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u1, u6, u3, u5} C _inst_1 E _inst_3) (CategoryTheory.Functor.comp.{u1, u2, u6, u3, u4, u5} C _inst_1 D _inst_2 E _inst_3 F H) (CategoryTheory.Functor.comp.{u1, u2, u6, u3, u4, u5} C _inst_1 D _inst_2 E _inst_3 G H)), Eq.{succ (max u3 u2)} (Quiver.Hom.{succ (max u3 u2), max u1 u2 u3 u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u2, max u1 u2 u3 u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u3 u2, max u1 u2 u3 u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2))) F G) (CategoryTheory.Iso.hom.{max u3 u2, max u1 u2 u3 u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) F G (CategoryTheory.natIsoOfCompFullyFaithful.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F G H _inst_4 _inst_5 i)) (CategoryTheory.natTransOfCompFullyFaithful.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F G H _inst_4 _inst_5 (CategoryTheory.Iso.hom.{max u3 u6, max u1 u6 u3 u5} (CategoryTheory.Functor.{u1, u6, u3, u5} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u1, u6, u3, u5} C _inst_1 E _inst_3) (CategoryTheory.Functor.comp.{u1, u2, u6, u3, u4, u5} C _inst_1 D _inst_2 E _inst_3 F H) (CategoryTheory.Functor.comp.{u1, u2, u6, u3, u4, u5} C _inst_1 D _inst_2 E _inst_3 G H) i))
but is expected to have type
  forall {C : Type.{u5}} [_inst_1 : CategoryTheory.Category.{u3, u5} C] {D : Type.{u6}} [_inst_2 : CategoryTheory.Category.{u4, u6} D] {E : Type.{u1}} [_inst_3 : CategoryTheory.Category.{u2, u1} E] {F : CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2} {G : CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2} (H : CategoryTheory.Functor.{u4, u2, u6, u1} D _inst_2 E _inst_3) [_inst_4 : CategoryTheory.Full.{u4, u2, u6, u1} D _inst_2 E _inst_3 H] [_inst_5 : CategoryTheory.Faithful.{u4, u2, u6, u1} D _inst_2 E _inst_3 H] (i : CategoryTheory.Iso.{max u5 u2, max (max (max u1 u5) u2) u3} (CategoryTheory.Functor.{u3, u2, u5, u1} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u3, u2, u5, u1} C _inst_1 E _inst_3) (CategoryTheory.Functor.comp.{u3, u4, u2, u5, u6, u1} C _inst_1 D _inst_2 E _inst_3 F H) (CategoryTheory.Functor.comp.{u3, u4, u2, u5, u6, u1} C _inst_1 D _inst_2 E _inst_3 G H)), Eq.{max (succ u5) (succ u4)} (Quiver.Hom.{succ (max u5 u4), max (max (max u5 u6) u3) u4} (CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u5 u4, max (max (max u5 u6) u3) u4} (CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u5 u4, max (max (max u5 u6) u3) u4} (CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u3, u4, u5, u6} C _inst_1 D _inst_2))) F G) (CategoryTheory.Iso.hom.{max u5 u4, max (max (max u5 u6) u3) u4} (CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u3, u4, u5, u6} C _inst_1 D _inst_2) F G (CategoryTheory.natIsoOfCompFullyFaithful.{u3, u4, u5, u6, u1, u2} C _inst_1 D _inst_2 E _inst_3 F G H _inst_4 _inst_5 i)) (CategoryTheory.natTransOfCompFullyFaithful.{u3, u4, u5, u6, u1, u2} C _inst_1 D _inst_2 E _inst_3 F G H _inst_4 _inst_5 (CategoryTheory.Iso.hom.{max u5 u2, max (max (max u5 u3) u1) u2} (CategoryTheory.Functor.{u3, u2, u5, u1} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u3, u2, u5, u1} C _inst_1 E _inst_3) (CategoryTheory.Functor.comp.{u3, u4, u2, u5, u6, u1} C _inst_1 D _inst_2 E _inst_3 F H) (CategoryTheory.Functor.comp.{u3, u4, u2, u5, u6, u1} C _inst_1 D _inst_2 E _inst_3 G H) i))
Case conversion may be inaccurate. Consider using '#align category_theory.nat_iso_of_comp_fully_faithful_hom CategoryTheory.natIsoOfCompFullyFaithful_homₓ'. -/
theorem natIsoOfCompFullyFaithful_hom (i : F ⋙ H ≅ G ⋙ H) :
    (natIsoOfCompFullyFaithful H i).Hom = natTransOfCompFullyFaithful H i.Hom :=
  by
  ext
  simp [nat_iso_of_comp_fully_faithful]
#align
  category_theory.nat_iso_of_comp_fully_faithful_hom CategoryTheory.natIsoOfCompFullyFaithful_hom

/- warning: category_theory.nat_iso_of_comp_fully_faithful_inv -> CategoryTheory.natIsoOfCompFullyFaithful_inv is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] {E : Type.{u5}} [_inst_3 : CategoryTheory.Category.{u6, u5} E] {F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} {G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} (H : CategoryTheory.Functor.{u2, u6, u4, u5} D _inst_2 E _inst_3) [_inst_4 : CategoryTheory.Full.{u2, u6, u4, u5} D _inst_2 E _inst_3 H] [_inst_5 : CategoryTheory.Faithful.{u2, u6, u4, u5} D _inst_2 E _inst_3 H] (i : CategoryTheory.Iso.{max u3 u6, max u1 u6 u3 u5} (CategoryTheory.Functor.{u1, u6, u3, u5} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u1, u6, u3, u5} C _inst_1 E _inst_3) (CategoryTheory.Functor.comp.{u1, u2, u6, u3, u4, u5} C _inst_1 D _inst_2 E _inst_3 F H) (CategoryTheory.Functor.comp.{u1, u2, u6, u3, u4, u5} C _inst_1 D _inst_2 E _inst_3 G H)), Eq.{succ (max u3 u2)} (Quiver.Hom.{succ (max u3 u2), max u1 u2 u3 u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u2, max u1 u2 u3 u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u3 u2, max u1 u2 u3 u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2))) G F) (CategoryTheory.Iso.inv.{max u3 u2, max u1 u2 u3 u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) F G (CategoryTheory.natIsoOfCompFullyFaithful.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F G H _inst_4 _inst_5 i)) (CategoryTheory.natTransOfCompFullyFaithful.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 G F H _inst_4 _inst_5 (CategoryTheory.Iso.inv.{max u3 u6, max u1 u6 u3 u5} (CategoryTheory.Functor.{u1, u6, u3, u5} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u1, u6, u3, u5} C _inst_1 E _inst_3) (CategoryTheory.Functor.comp.{u1, u2, u6, u3, u4, u5} C _inst_1 D _inst_2 E _inst_3 F H) (CategoryTheory.Functor.comp.{u1, u2, u6, u3, u4, u5} C _inst_1 D _inst_2 E _inst_3 G H) i))
but is expected to have type
  forall {C : Type.{u5}} [_inst_1 : CategoryTheory.Category.{u3, u5} C] {D : Type.{u6}} [_inst_2 : CategoryTheory.Category.{u4, u6} D] {E : Type.{u1}} [_inst_3 : CategoryTheory.Category.{u2, u1} E] {F : CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2} {G : CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2} (H : CategoryTheory.Functor.{u4, u2, u6, u1} D _inst_2 E _inst_3) [_inst_4 : CategoryTheory.Full.{u4, u2, u6, u1} D _inst_2 E _inst_3 H] [_inst_5 : CategoryTheory.Faithful.{u4, u2, u6, u1} D _inst_2 E _inst_3 H] (i : CategoryTheory.Iso.{max u5 u2, max (max (max u1 u5) u2) u3} (CategoryTheory.Functor.{u3, u2, u5, u1} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u3, u2, u5, u1} C _inst_1 E _inst_3) (CategoryTheory.Functor.comp.{u3, u4, u2, u5, u6, u1} C _inst_1 D _inst_2 E _inst_3 F H) (CategoryTheory.Functor.comp.{u3, u4, u2, u5, u6, u1} C _inst_1 D _inst_2 E _inst_3 G H)), Eq.{max (succ u5) (succ u4)} (Quiver.Hom.{succ (max u5 u4), max (max (max u5 u6) u3) u4} (CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u5 u4, max (max (max u5 u6) u3) u4} (CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u5 u4, max (max (max u5 u6) u3) u4} (CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u3, u4, u5, u6} C _inst_1 D _inst_2))) G F) (CategoryTheory.Iso.inv.{max u5 u4, max (max (max u5 u6) u3) u4} (CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u3, u4, u5, u6} C _inst_1 D _inst_2) F G (CategoryTheory.natIsoOfCompFullyFaithful.{u3, u4, u5, u6, u1, u2} C _inst_1 D _inst_2 E _inst_3 F G H _inst_4 _inst_5 i)) (CategoryTheory.natTransOfCompFullyFaithful.{u3, u4, u5, u6, u1, u2} C _inst_1 D _inst_2 E _inst_3 G F H _inst_4 _inst_5 (CategoryTheory.Iso.inv.{max u5 u2, max (max (max u5 u3) u1) u2} (CategoryTheory.Functor.{u3, u2, u5, u1} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u3, u2, u5, u1} C _inst_1 E _inst_3) (CategoryTheory.Functor.comp.{u3, u4, u2, u5, u6, u1} C _inst_1 D _inst_2 E _inst_3 F H) (CategoryTheory.Functor.comp.{u3, u4, u2, u5, u6, u1} C _inst_1 D _inst_2 E _inst_3 G H) i))
Case conversion may be inaccurate. Consider using '#align category_theory.nat_iso_of_comp_fully_faithful_inv CategoryTheory.natIsoOfCompFullyFaithful_invₓ'. -/
theorem natIsoOfCompFullyFaithful_inv (i : F ⋙ H ≅ G ⋙ H) :
    (natIsoOfCompFullyFaithful H i).inv = natTransOfCompFullyFaithful H i.inv :=
  by
  ext
  simp [← preimage_comp]
  dsimp
  simp
#align
  category_theory.nat_iso_of_comp_fully_faithful_inv CategoryTheory.natIsoOfCompFullyFaithful_inv

#print CategoryTheory.NatTrans.equivOfCompFullyFaithful /-
/-- Horizontal composition with a fully faithful functor induces a bijection on
natural transformations. -/
@[simps]
def NatTrans.equivOfCompFullyFaithful : (F ⟶ G) ≃ (F ⋙ H ⟶ G ⋙ H)
    where
  toFun α := α ◫ 𝟙 H
  invFun := natTransOfCompFullyFaithful H
  left_inv := by tidy
  right_inv := by tidy
#align
  category_theory.nat_trans.equiv_of_comp_fully_faithful CategoryTheory.NatTrans.equivOfCompFullyFaithful
-/

#print CategoryTheory.NatIso.equivOfCompFullyFaithful /-
/-- Horizontal composition with a fully faithful functor induces a bijection on
natural isomorphisms. -/
@[simps]
def NatIso.equivOfCompFullyFaithful : (F ≅ G) ≃ (F ⋙ H ≅ G ⋙ H)
    where
  toFun e := NatIso.hcomp e (Iso.refl H)
  invFun := natIsoOfCompFullyFaithful H
  left_inv := by tidy
  right_inv := by tidy
#align
  category_theory.nat_iso.equiv_of_comp_fully_faithful CategoryTheory.NatIso.equivOfCompFullyFaithful
-/

end

end CategoryTheory

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

#print CategoryTheory.Full.id /-
instance Full.id : Full (𝟭 C) where preimage _ _ f := f
#align category_theory.full.id CategoryTheory.Full.id
-/

#print CategoryTheory.Faithful.id /-
instance Faithful.id : Faithful (𝟭 C) := by obviously
#align category_theory.faithful.id CategoryTheory.Faithful.id
-/

variable {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]

variable (F F' : C ⥤ D) (G : D ⥤ E)

#print CategoryTheory.Faithful.comp /-
instance Faithful.comp [Faithful F] [Faithful G] : Faithful (F ⋙ G)
    where map_injective' _ _ _ _ p := F.map_injective (G.map_injective p)
#align category_theory.faithful.comp CategoryTheory.Faithful.comp
-/

#print CategoryTheory.Faithful.of_comp /-
theorem Faithful.of_comp [faithful <| F ⋙ G] : Faithful F :=
  { map_injective' := fun X Y => (F ⋙ G).map_injective.of_comp }
#align category_theory.faithful.of_comp CategoryTheory.Faithful.of_comp
-/

section

variable {F F'}

#print CategoryTheory.Full.ofIso /-
/-- If `F` is full, and naturally isomorphic to some `F'`, then `F'` is also full. -/
def Full.ofIso [Full F] (α : F ≅ F') : Full F'
    where
  preimage X Y f := F.preimage ((α.app X).Hom ≫ f ≫ (α.app Y).inv)
  witness' X Y f := by simp [← nat_iso.naturality_1 α]
#align category_theory.full.of_iso CategoryTheory.Full.ofIso
-/

#print CategoryTheory.Faithful.of_iso /-
theorem Faithful.of_iso [Faithful F] (α : F ≅ F') : Faithful F' :=
  {
    map_injective' := fun X Y f f' h =>
      F.map_injective (by rw [← nat_iso.naturality_1 α.symm, h, nat_iso.naturality_1 α.symm]) }
#align category_theory.faithful.of_iso CategoryTheory.Faithful.of_iso
-/

end

variable {F G}

#print CategoryTheory.Faithful.of_comp_iso /-
theorem Faithful.of_comp_iso {H : C ⥤ E} [ℋ : Faithful H] (h : F ⋙ G ≅ H) : Faithful F :=
  @Faithful.of_comp _ _ _ _ _ _ F G (Faithful.of_iso h.symm)
#align category_theory.faithful.of_comp_iso CategoryTheory.Faithful.of_comp_iso
-/

alias faithful.of_comp_iso ← _root_.category_theory.iso.faithful_of_comp

#print CategoryTheory.Faithful.of_comp_eq /-
-- We could prove this from `faithful.of_comp_iso` using `eq_to_iso`,
-- but that would introduce a cyclic import.
theorem Faithful.of_comp_eq {H : C ⥤ E} [ℋ : Faithful H] (h : F ⋙ G = H) : Faithful F :=
  @Faithful.of_comp _ _ _ _ _ _ F G (h.symm ▸ ℋ)
#align category_theory.faithful.of_comp_eq CategoryTheory.Faithful.of_comp_eq
-/

alias faithful.of_comp_eq ← _root_.eq.faithful_of_comp

variable (F G)

/- warning: category_theory.faithful.div -> CategoryTheory.Faithful.div is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u4} C] {D : Type.{u5}} [_inst_2 : CategoryTheory.Category.{u2, u5} D] {E : Type.{u6}} [_inst_3 : CategoryTheory.Category.{u3, u6} E] (F : CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_1 E _inst_3) (G : CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_2 E _inst_3) [_inst_4 : CategoryTheory.Faithful.{u2, u3, u5, u6} D _inst_2 E _inst_3 G] (obj : C -> D), (forall (X : C), Eq.{succ u6} E (CategoryTheory.Functor.obj.{u2, u3, u5, u6} D _inst_2 E _inst_3 G (obj X)) (CategoryTheory.Functor.obj.{u1, u3, u4, u6} C _inst_1 E _inst_3 F X)) -> (forall (map : forall {X : C} {Y : C}, (Quiver.Hom.{succ u1, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) X Y) -> (Quiver.Hom.{succ u2, u5} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) (obj X) (obj Y))), (forall {X : C} {Y : C} {f : Quiver.Hom.{succ u1, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) X Y}, HEq.{succ u3} (Quiver.Hom.{succ u3, u6} E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.obj.{u2, u3, u5, u6} D _inst_2 E _inst_3 G (obj X)) (CategoryTheory.Functor.obj.{u2, u3, u5, u6} D _inst_2 E _inst_3 G (obj Y))) (CategoryTheory.Functor.map.{u2, u3, u5, u6} D _inst_2 E _inst_3 G (obj X) (obj Y) (map X Y f)) (Quiver.Hom.{succ u3, u6} E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.obj.{u1, u3, u4, u6} C _inst_1 E _inst_3 F X) (CategoryTheory.Functor.obj.{u1, u3, u4, u6} C _inst_1 E _inst_3 F Y)) (CategoryTheory.Functor.map.{u1, u3, u4, u6} C _inst_1 E _inst_3 F X Y f)) -> (CategoryTheory.Functor.{u1, u2, u4, u5} C _inst_1 D _inst_2))
but is expected to have type
  forall {C : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u4} C] {D : Type.{u5}} [_inst_2 : CategoryTheory.Category.{u2, u5} D] {E : Type.{u6}} [_inst_3 : CategoryTheory.Category.{u3, u6} E] (F : CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_1 E _inst_3) (G : CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_2 E _inst_3) [_inst_4 : CategoryTheory.Faithful.{u2, u3, u5, u6} D _inst_2 E _inst_3 G] (obj : C -> D), (forall (X : C), Eq.{succ u6} E (Prefunctor.obj.{succ u2, succ u3, u5, u6} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u2, u3, u5, u6} D _inst_2 E _inst_3 G) (obj X)) (Prefunctor.obj.{succ u1, succ u3, u4, u6} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u4, u6} C _inst_1 E _inst_3 F) X)) -> (forall (map : forall {X : C} {Y : C}, (Quiver.Hom.{succ u1, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) X Y) -> (Quiver.Hom.{succ u2, u5} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) (obj X) (obj Y))), (forall {X : C} {Y : C} {f : Quiver.Hom.{succ u1, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) X Y}, HEq.{succ u3} (Quiver.Hom.{succ u3, u6} E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (Prefunctor.obj.{succ u2, succ u3, u5, u6} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u2, u3, u5, u6} D _inst_2 E _inst_3 G) (obj X)) (Prefunctor.obj.{succ u2, succ u3, u5, u6} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u2, u3, u5, u6} D _inst_2 E _inst_3 G) (obj Y))) (Prefunctor.map.{succ u2, succ u3, u5, u6} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u2, u3, u5, u6} D _inst_2 E _inst_3 G) (obj X) (obj Y) (map X Y f)) (Quiver.Hom.{succ u3, u6} E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (Prefunctor.obj.{succ u1, succ u3, u4, u6} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u4, u6} C _inst_1 E _inst_3 F) X) (Prefunctor.obj.{succ u1, succ u3, u4, u6} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u4, u6} C _inst_1 E _inst_3 F) Y)) (Prefunctor.map.{succ u1, succ u3, u4, u6} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u4, u6} C _inst_1 E _inst_3 F) X Y f)) -> (CategoryTheory.Functor.{u1, u2, u4, u5} C _inst_1 D _inst_2))
Case conversion may be inaccurate. Consider using '#align category_theory.faithful.div CategoryTheory.Faithful.divₓ'. -/
/-- “Divide” a functor by a faithful functor. -/
protected def Faithful.div (F : C ⥤ E) (G : D ⥤ E) [Faithful G] (obj : C → D)
    (h_obj : ∀ X, G.obj (obj X) = F.obj X) (map : ∀ {X Y}, (X ⟶ Y) → (obj X ⟶ obj Y))
    (h_map : ∀ {X Y} {f : X ⟶ Y}, HEq (G.map (map f)) (F.map f)) : C ⥤ D :=
  { obj
    map := @map
    map_id' := by
      intro X
      apply G.map_injective
      apply eq_of_heq
      trans F.map (𝟙 X); exact h_map
      rw [F.map_id, G.map_id, h_obj X]
    map_comp' := by
      intro X Y Z f g
      apply G.map_injective
      apply eq_of_heq
      trans F.map (f ≫ g); exact h_map
      rw [F.map_comp, G.map_comp]
      congr 1 <;> try exact (h_obj _).symm <;> exact h_map.symm }
#align category_theory.faithful.div CategoryTheory.Faithful.div

/- warning: category_theory.faithful.div_comp -> CategoryTheory.Faithful.div_comp is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u4} C] {D : Type.{u5}} [_inst_2 : CategoryTheory.Category.{u2, u5} D] {E : Type.{u6}} [_inst_3 : CategoryTheory.Category.{u3, u6} E] (F : CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_1 E _inst_3) [_inst_4 : CategoryTheory.Faithful.{u1, u3, u4, u6} C _inst_1 E _inst_3 F] (G : CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_2 E _inst_3) [_inst_5 : CategoryTheory.Faithful.{u2, u3, u5, u6} D _inst_2 E _inst_3 G] (obj : C -> D) (h_obj : forall (X : C), Eq.{succ u6} E (CategoryTheory.Functor.obj.{u2, u3, u5, u6} D _inst_2 E _inst_3 G (obj X)) (CategoryTheory.Functor.obj.{u1, u3, u4, u6} C _inst_1 E _inst_3 F X)) (map : forall {X : C} {Y : C}, (Quiver.Hom.{succ u1, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) X Y) -> (Quiver.Hom.{succ u2, u5} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) (obj X) (obj Y))) (h_map : forall {X : C} {Y : C} {f : Quiver.Hom.{succ u1, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) X Y}, HEq.{succ u3} (Quiver.Hom.{succ u3, u6} E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.obj.{u2, u3, u5, u6} D _inst_2 E _inst_3 G (obj X)) (CategoryTheory.Functor.obj.{u2, u3, u5, u6} D _inst_2 E _inst_3 G (obj Y))) (CategoryTheory.Functor.map.{u2, u3, u5, u6} D _inst_2 E _inst_3 G (obj X) (obj Y) (map X Y f)) (Quiver.Hom.{succ u3, u6} E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.obj.{u1, u3, u4, u6} C _inst_1 E _inst_3 F X) (CategoryTheory.Functor.obj.{u1, u3, u4, u6} C _inst_1 E _inst_3 F Y)) (CategoryTheory.Functor.map.{u1, u3, u4, u6} C _inst_1 E _inst_3 F X Y f)), Eq.{succ (max u1 u3 u4 u6)} (CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_1 E _inst_3) (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 (CategoryTheory.Faithful.div.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F G _inst_5 obj h_obj map h_map) G) F
but is expected to have type
  forall {C : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u4} C] {D : Type.{u5}} [_inst_2 : CategoryTheory.Category.{u2, u5} D] {E : Type.{u6}} [_inst_3 : CategoryTheory.Category.{u3, u6} E] (F : CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_1 E _inst_3) [_inst_4 : CategoryTheory.Faithful.{u1, u3, u4, u6} C _inst_1 E _inst_3 F] (G : CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_2 E _inst_3) [_inst_5 : CategoryTheory.Faithful.{u2, u3, u5, u6} D _inst_2 E _inst_3 G] (obj : C -> D) (h_obj : forall (X : C), Eq.{succ u6} E (Prefunctor.obj.{succ u2, succ u3, u5, u6} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u2, u3, u5, u6} D _inst_2 E _inst_3 G) (obj X)) (Prefunctor.obj.{succ u1, succ u3, u4, u6} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u4, u6} C _inst_1 E _inst_3 F) X)) (map : forall {X : C} {Y : C}, (Quiver.Hom.{succ u1, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) X Y) -> (Quiver.Hom.{succ u2, u5} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) (obj X) (obj Y))) (h_map : forall {X : C} {Y : C} {f : Quiver.Hom.{succ u1, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) X Y}, HEq.{succ u3} (Quiver.Hom.{succ u3, u6} E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (Prefunctor.obj.{succ u2, succ u3, u5, u6} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u2, u3, u5, u6} D _inst_2 E _inst_3 G) (obj X)) (Prefunctor.obj.{succ u2, succ u3, u5, u6} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u2, u3, u5, u6} D _inst_2 E _inst_3 G) (obj Y))) (Prefunctor.map.{succ u2, succ u3, u5, u6} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u2, u3, u5, u6} D _inst_2 E _inst_3 G) (obj X) (obj Y) (map X Y f)) (Quiver.Hom.{succ u3, u6} E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (Prefunctor.obj.{succ u1, succ u3, u4, u6} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u4, u6} C _inst_1 E _inst_3 F) X) (Prefunctor.obj.{succ u1, succ u3, u4, u6} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u4, u6} C _inst_1 E _inst_3 F) Y)) (Prefunctor.map.{succ u1, succ u3, u4, u6} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u4, u6} C _inst_1 E _inst_3 F) X Y f)), Eq.{max (max (max (succ u4) (succ u6)) (succ u1)) (succ u3)} (CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_1 E _inst_3) (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 (CategoryTheory.Faithful.div.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F G _inst_5 obj h_obj map h_map) G) F
Case conversion may be inaccurate. Consider using '#align category_theory.faithful.div_comp CategoryTheory.Faithful.div_compₓ'. -/
-- This follows immediately from `functor.hext` (`functor.hext h_obj @h_map`),
-- but importing `category_theory.eq_to_hom` causes an import loop:
-- category_theory.eq_to_hom → category_theory.opposites →
-- category_theory.equivalence → category_theory.fully_faithful
theorem Faithful.div_comp (F : C ⥤ E) [Faithful F] (G : D ⥤ E) [Faithful G] (obj : C → D)
    (h_obj : ∀ X, G.obj (obj X) = F.obj X) (map : ∀ {X Y}, (X ⟶ Y) → (obj X ⟶ obj Y))
    (h_map : ∀ {X Y} {f : X ⟶ Y}, HEq (G.map (map f)) (F.map f)) :
    Faithful.div F G obj @h_obj @map @h_map ⋙ G = F :=
  by
  cases' F with F_obj _ _ _; cases' G with G_obj _ _ _
  unfold faithful.div Functor.Comp
  unfold_projs  at h_obj
  have : F_obj = G_obj ∘ obj := (funext h_obj).symm
  subst this
  congr
  funext
  exact eq_of_heq h_map
#align category_theory.faithful.div_comp CategoryTheory.Faithful.div_comp

/- warning: category_theory.faithful.div_faithful -> CategoryTheory.Faithful.div_faithful is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u4} C] {D : Type.{u5}} [_inst_2 : CategoryTheory.Category.{u2, u5} D] {E : Type.{u6}} [_inst_3 : CategoryTheory.Category.{u3, u6} E] (F : CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_1 E _inst_3) [_inst_4 : CategoryTheory.Faithful.{u1, u3, u4, u6} C _inst_1 E _inst_3 F] (G : CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_2 E _inst_3) [_inst_5 : CategoryTheory.Faithful.{u2, u3, u5, u6} D _inst_2 E _inst_3 G] (obj : C -> D) (h_obj : forall (X : C), Eq.{succ u6} E (CategoryTheory.Functor.obj.{u2, u3, u5, u6} D _inst_2 E _inst_3 G (obj X)) (CategoryTheory.Functor.obj.{u1, u3, u4, u6} C _inst_1 E _inst_3 F X)) (map : forall {X : C} {Y : C}, (Quiver.Hom.{succ u1, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) X Y) -> (Quiver.Hom.{succ u2, u5} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) (obj X) (obj Y))) (h_map : forall {X : C} {Y : C} {f : Quiver.Hom.{succ u1, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) X Y}, HEq.{succ u3} (Quiver.Hom.{succ u3, u6} E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.obj.{u2, u3, u5, u6} D _inst_2 E _inst_3 G (obj X)) (CategoryTheory.Functor.obj.{u2, u3, u5, u6} D _inst_2 E _inst_3 G (obj Y))) (CategoryTheory.Functor.map.{u2, u3, u5, u6} D _inst_2 E _inst_3 G (obj X) (obj Y) (map X Y f)) (Quiver.Hom.{succ u3, u6} E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.obj.{u1, u3, u4, u6} C _inst_1 E _inst_3 F X) (CategoryTheory.Functor.obj.{u1, u3, u4, u6} C _inst_1 E _inst_3 F Y)) (CategoryTheory.Functor.map.{u1, u3, u4, u6} C _inst_1 E _inst_3 F X Y f)), CategoryTheory.Faithful.{u1, u2, u4, u5} C _inst_1 D _inst_2 (CategoryTheory.Faithful.div.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F G _inst_5 obj h_obj map h_map)
but is expected to have type
  forall {C : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u4} C] {D : Type.{u5}} [_inst_2 : CategoryTheory.Category.{u2, u5} D] {E : Type.{u6}} [_inst_3 : CategoryTheory.Category.{u3, u6} E] (F : CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_1 E _inst_3) [_inst_4 : CategoryTheory.Faithful.{u1, u3, u4, u6} C _inst_1 E _inst_3 F] (G : CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_2 E _inst_3) [_inst_5 : CategoryTheory.Faithful.{u2, u3, u5, u6} D _inst_2 E _inst_3 G] (obj : C -> D) (h_obj : forall (X : C), Eq.{succ u6} E (Prefunctor.obj.{succ u2, succ u3, u5, u6} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u2, u3, u5, u6} D _inst_2 E _inst_3 G) (obj X)) (Prefunctor.obj.{succ u1, succ u3, u4, u6} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u4, u6} C _inst_1 E _inst_3 F) X)) (map : forall {X : C} {Y : C}, (Quiver.Hom.{succ u1, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) X Y) -> (Quiver.Hom.{succ u2, u5} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) (obj X) (obj Y))) (h_map : forall {X : C} {Y : C} {f : Quiver.Hom.{succ u1, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) X Y}, HEq.{succ u3} (Quiver.Hom.{succ u3, u6} E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (Prefunctor.obj.{succ u2, succ u3, u5, u6} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u2, u3, u5, u6} D _inst_2 E _inst_3 G) (obj X)) (Prefunctor.obj.{succ u2, succ u3, u5, u6} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u2, u3, u5, u6} D _inst_2 E _inst_3 G) (obj Y))) (Prefunctor.map.{succ u2, succ u3, u5, u6} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u2, u3, u5, u6} D _inst_2 E _inst_3 G) (obj X) (obj Y) (map X Y f)) (Quiver.Hom.{succ u3, u6} E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (Prefunctor.obj.{succ u1, succ u3, u4, u6} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u4, u6} C _inst_1 E _inst_3 F) X) (Prefunctor.obj.{succ u1, succ u3, u4, u6} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u4, u6} C _inst_1 E _inst_3 F) Y)) (Prefunctor.map.{succ u1, succ u3, u4, u6} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u4, u6} C _inst_1 E _inst_3 F) X Y f)), CategoryTheory.Faithful.{u1, u2, u4, u5} C _inst_1 D _inst_2 (CategoryTheory.Faithful.div.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F G _inst_5 obj h_obj map h_map)
Case conversion may be inaccurate. Consider using '#align category_theory.faithful.div_faithful CategoryTheory.Faithful.div_faithfulₓ'. -/
theorem Faithful.div_faithful (F : C ⥤ E) [Faithful F] (G : D ⥤ E) [Faithful G] (obj : C → D)
    (h_obj : ∀ X, G.obj (obj X) = F.obj X) (map : ∀ {X Y}, (X ⟶ Y) → (obj X ⟶ obj Y))
    (h_map : ∀ {X Y} {f : X ⟶ Y}, HEq (G.map (map f)) (F.map f)) :
    Faithful (Faithful.div F G obj @h_obj @map @h_map) :=
  (Faithful.div_comp F G _ h_obj _ @h_map).faithful_of_comp
#align category_theory.faithful.div_faithful CategoryTheory.Faithful.div_faithful

#print CategoryTheory.Full.comp /-
instance Full.comp [Full F] [Full G] : Full (F ⋙ G)
    where preimage _ _ f := F.preimage (G.preimage f)
#align category_theory.full.comp CategoryTheory.Full.comp
-/

#print CategoryTheory.Full.ofCompFaithful /-
/-- If `F ⋙ G` is full and `G` is faithful, then `F` is full. -/
def Full.ofCompFaithful [full <| F ⋙ G] [Faithful G] : Full F
    where
  preimage X Y f := (F ⋙ G).preimage (G.map f)
  witness' X Y f := G.map_injective ((F ⋙ G).image_preimage _)
#align category_theory.full.of_comp_faithful CategoryTheory.Full.ofCompFaithful
-/

#print CategoryTheory.Full.ofCompFaithfulIso /-
/-- If `F ⋙ G` is full and `G` is faithful, then `F` is full. -/
def Full.ofCompFaithfulIso {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} [Full H] [Faithful G]
    (h : F ⋙ G ≅ H) : Full F :=
  @Full.ofCompFaithful _ _ _ _ _ _ F G (Full.ofIso h.symm) _
#align category_theory.full.of_comp_faithful_iso CategoryTheory.Full.ofCompFaithfulIso
-/

#print CategoryTheory.fullyFaithfulCancelRight /-
/-- Given a natural isomorphism between `F ⋙ H` and `G ⋙ H` for a fully faithful functor `H`, we
can 'cancel' it to give a natural iso between `F` and `G`.
-/
def fullyFaithfulCancelRight {F G : C ⥤ D} (H : D ⥤ E) [Full H] [Faithful H]
    (comp_iso : F ⋙ H ≅ G ⋙ H) : F ≅ G :=
  NatIso.ofComponents (fun X => H.preimageIso (comp_iso.app X)) fun X Y f =>
    H.map_injective (by simpa using comp_iso.hom.naturality f)
#align category_theory.fully_faithful_cancel_right CategoryTheory.fullyFaithfulCancelRight
-/

/- warning: category_theory.fully_faithful_cancel_right_hom_app -> CategoryTheory.fullyFaithfulCancelRight_hom_app is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u4} C] {D : Type.{u5}} [_inst_2 : CategoryTheory.Category.{u2, u5} D] {E : Type.{u6}} [_inst_3 : CategoryTheory.Category.{u3, u6} E] {F : CategoryTheory.Functor.{u1, u2, u4, u5} C _inst_1 D _inst_2} {G : CategoryTheory.Functor.{u1, u2, u4, u5} C _inst_1 D _inst_2} {H : CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_2 E _inst_3} [_inst_4 : CategoryTheory.Full.{u2, u3, u5, u6} D _inst_2 E _inst_3 H] [_inst_5 : CategoryTheory.Faithful.{u2, u3, u5, u6} D _inst_2 E _inst_3 H] (comp_iso : CategoryTheory.Iso.{max u4 u3, max u1 u3 u4 u6} (CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u1, u3, u4, u6} C _inst_1 E _inst_3) (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F H) (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 G H)) (X : C), Eq.{succ u2} (Quiver.Hom.{succ u2, u5} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u2, u4, u5} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u4, u5} C _inst_1 D _inst_2 G X)) (CategoryTheory.NatTrans.app.{u1, u2, u4, u5} C _inst_1 D _inst_2 F G (CategoryTheory.Iso.hom.{max u4 u2, max u1 u2 u4 u5} (CategoryTheory.Functor.{u1, u2, u4, u5} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u4, u5} C _inst_1 D _inst_2) F G (CategoryTheory.fullyFaithfulCancelRight.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F G H _inst_4 _inst_5 comp_iso)) X) (CategoryTheory.Functor.preimage.{u2, u3, u5, u6} D _inst_2 E _inst_3 (CategoryTheory.Functor.obj.{u1, u2, u4, u5} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u4, u5} C _inst_1 D _inst_2 G X) H _inst_4 (CategoryTheory.NatTrans.app.{u1, u3, u4, u6} C _inst_1 E _inst_3 (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F H) (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 G H) (CategoryTheory.Iso.hom.{max u4 u3, max u1 u3 u4 u6} (CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u1, u3, u4, u6} C _inst_1 E _inst_3) (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F H) (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 G H) comp_iso) X))
but is expected to have type
  forall {C : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u4} C] {D : Type.{u5}} [_inst_2 : CategoryTheory.Category.{u2, u5} D] {E : Type.{u6}} [_inst_3 : CategoryTheory.Category.{u3, u6} E] {F : CategoryTheory.Functor.{u1, u2, u4, u5} C _inst_1 D _inst_2} {G : CategoryTheory.Functor.{u1, u2, u4, u5} C _inst_1 D _inst_2} {H : CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_2 E _inst_3} [_inst_4 : CategoryTheory.Full.{u2, u3, u5, u6} D _inst_2 E _inst_3 H] [_inst_5 : CategoryTheory.Faithful.{u2, u3, u5, u6} D _inst_2 E _inst_3 H] (comp_iso : CategoryTheory.Iso.{max u4 u3, max (max (max u6 u4) u3) u1} (CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u1, u3, u4, u6} C _inst_1 E _inst_3) (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F H) (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 G H)) (X : C), Eq.{succ u2} (Quiver.Hom.{succ u2, u5} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) (Prefunctor.obj.{succ u1, succ u2, u4, u5} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u4, u5} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u4, u5} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u4, u5} C _inst_1 D _inst_2 G) X)) (CategoryTheory.NatTrans.app.{u1, u2, u4, u5} C _inst_1 D _inst_2 F G (CategoryTheory.Iso.hom.{max u4 u2, max (max (max u4 u5) u1) u2} (CategoryTheory.Functor.{u1, u2, u4, u5} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u4, u5} C _inst_1 D _inst_2) F G (CategoryTheory.fullyFaithfulCancelRight.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F G H _inst_4 _inst_5 comp_iso)) X) (CategoryTheory.Functor.preimage.{u2, u3, u5, u6} D _inst_2 E _inst_3 (Prefunctor.obj.{succ u1, succ u2, u4, u5} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u4, u5} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u4, u5} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u4, u5} C _inst_1 D _inst_2 G) X) H _inst_4 (CategoryTheory.NatTrans.app.{u1, u3, u4, u6} C _inst_1 E _inst_3 (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F H) (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 G H) (CategoryTheory.Iso.hom.{max u4 u3, max (max (max u4 u6) u1) u3} (CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u1, u3, u4, u6} C _inst_1 E _inst_3) (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F H) (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 G H) comp_iso) X))
Case conversion may be inaccurate. Consider using '#align category_theory.fully_faithful_cancel_right_hom_app CategoryTheory.fullyFaithfulCancelRight_hom_appₓ'. -/
@[simp]
theorem fullyFaithfulCancelRight_hom_app {F G : C ⥤ D} {H : D ⥤ E} [Full H] [Faithful H]
    (comp_iso : F ⋙ H ≅ G ⋙ H) (X : C) :
    (fullyFaithfulCancelRight H comp_iso).Hom.app X = H.preimage (comp_iso.Hom.app X) :=
  rfl
#align
  category_theory.fully_faithful_cancel_right_hom_app CategoryTheory.fullyFaithfulCancelRight_hom_app

/- warning: category_theory.fully_faithful_cancel_right_inv_app -> CategoryTheory.fullyFaithfulCancelRight_inv_app is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u4} C] {D : Type.{u5}} [_inst_2 : CategoryTheory.Category.{u2, u5} D] {E : Type.{u6}} [_inst_3 : CategoryTheory.Category.{u3, u6} E] {F : CategoryTheory.Functor.{u1, u2, u4, u5} C _inst_1 D _inst_2} {G : CategoryTheory.Functor.{u1, u2, u4, u5} C _inst_1 D _inst_2} {H : CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_2 E _inst_3} [_inst_4 : CategoryTheory.Full.{u2, u3, u5, u6} D _inst_2 E _inst_3 H] [_inst_5 : CategoryTheory.Faithful.{u2, u3, u5, u6} D _inst_2 E _inst_3 H] (comp_iso : CategoryTheory.Iso.{max u4 u3, max u1 u3 u4 u6} (CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u1, u3, u4, u6} C _inst_1 E _inst_3) (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F H) (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 G H)) (X : C), Eq.{succ u2} (Quiver.Hom.{succ u2, u5} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u2, u4, u5} C _inst_1 D _inst_2 G X) (CategoryTheory.Functor.obj.{u1, u2, u4, u5} C _inst_1 D _inst_2 F X)) (CategoryTheory.NatTrans.app.{u1, u2, u4, u5} C _inst_1 D _inst_2 G F (CategoryTheory.Iso.inv.{max u4 u2, max u1 u2 u4 u5} (CategoryTheory.Functor.{u1, u2, u4, u5} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u4, u5} C _inst_1 D _inst_2) F G (CategoryTheory.fullyFaithfulCancelRight.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F G H _inst_4 _inst_5 comp_iso)) X) (CategoryTheory.Functor.preimage.{u2, u3, u5, u6} D _inst_2 E _inst_3 (CategoryTheory.Functor.obj.{u1, u2, u4, u5} C _inst_1 D _inst_2 G X) (CategoryTheory.Functor.obj.{u1, u2, u4, u5} C _inst_1 D _inst_2 F X) H _inst_4 (CategoryTheory.NatTrans.app.{u1, u3, u4, u6} C _inst_1 E _inst_3 (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 G H) (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F H) (CategoryTheory.Iso.inv.{max u4 u3, max u1 u3 u4 u6} (CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u1, u3, u4, u6} C _inst_1 E _inst_3) (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F H) (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 G H) comp_iso) X))
but is expected to have type
  forall {C : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u4} C] {D : Type.{u5}} [_inst_2 : CategoryTheory.Category.{u2, u5} D] {E : Type.{u6}} [_inst_3 : CategoryTheory.Category.{u3, u6} E] {F : CategoryTheory.Functor.{u1, u2, u4, u5} C _inst_1 D _inst_2} {G : CategoryTheory.Functor.{u1, u2, u4, u5} C _inst_1 D _inst_2} {H : CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_2 E _inst_3} [_inst_4 : CategoryTheory.Full.{u2, u3, u5, u6} D _inst_2 E _inst_3 H] [_inst_5 : CategoryTheory.Faithful.{u2, u3, u5, u6} D _inst_2 E _inst_3 H] (comp_iso : CategoryTheory.Iso.{max u4 u3, max (max (max u6 u4) u3) u1} (CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u1, u3, u4, u6} C _inst_1 E _inst_3) (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F H) (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 G H)) (X : C), Eq.{succ u2} (Quiver.Hom.{succ u2, u5} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) (Prefunctor.obj.{succ u1, succ u2, u4, u5} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u4, u5} C _inst_1 D _inst_2 G) X) (Prefunctor.obj.{succ u1, succ u2, u4, u5} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u4, u5} C _inst_1 D _inst_2 F) X)) (CategoryTheory.NatTrans.app.{u1, u2, u4, u5} C _inst_1 D _inst_2 G F (CategoryTheory.Iso.inv.{max u4 u2, max (max (max u4 u5) u1) u2} (CategoryTheory.Functor.{u1, u2, u4, u5} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u4, u5} C _inst_1 D _inst_2) F G (CategoryTheory.fullyFaithfulCancelRight.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F G H _inst_4 _inst_5 comp_iso)) X) (CategoryTheory.Functor.preimage.{u2, u3, u5, u6} D _inst_2 E _inst_3 (Prefunctor.obj.{succ u1, succ u2, u4, u5} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u4, u5} C _inst_1 D _inst_2 G) X) (Prefunctor.obj.{succ u1, succ u2, u4, u5} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u4, u5} C _inst_1 D _inst_2 F) X) H _inst_4 (CategoryTheory.NatTrans.app.{u1, u3, u4, u6} C _inst_1 E _inst_3 (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 G H) (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F H) (CategoryTheory.Iso.inv.{max u4 u3, max (max (max u4 u6) u1) u3} (CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u1, u3, u4, u6} C _inst_1 E _inst_3) (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F H) (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 G H) comp_iso) X))
Case conversion may be inaccurate. Consider using '#align category_theory.fully_faithful_cancel_right_inv_app CategoryTheory.fullyFaithfulCancelRight_inv_appₓ'. -/
@[simp]
theorem fullyFaithfulCancelRight_inv_app {F G : C ⥤ D} {H : D ⥤ E} [Full H] [Faithful H]
    (comp_iso : F ⋙ H ≅ G ⋙ H) (X : C) :
    (fullyFaithfulCancelRight H comp_iso).inv.app X = H.preimage (comp_iso.inv.app X) :=
  rfl
#align
  category_theory.fully_faithful_cancel_right_inv_app CategoryTheory.fullyFaithfulCancelRight_inv_app

end CategoryTheory

