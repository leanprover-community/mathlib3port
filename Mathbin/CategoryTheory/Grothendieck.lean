/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.grothendieck
! leanprover-community/mathlib commit 75be6b616681ab6ca66d798ead117e75cd64f125
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Category.Cat
import Mathbin.CategoryTheory.Elements

/-!
# The Grothendieck construction

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given a functor `F : C ⥤ Cat`, the objects of `grothendieck F`
consist of dependent pairs `(b, f)`, where `b : C` and `f : F.obj c`,
and a morphism `(b, f) ⟶ (b', f')` is a pair `β : b ⟶ b'` in `C`, and
`φ : (F.map β).obj f ⟶ f'`

Categories such as `PresheafedSpace` are in fact examples of this construction,
and it may be interesting to try to generalize some of the development there.

## Implementation notes

Really we should treat `Cat` as a 2-category, and allow `F` to be a 2-functor.

There is also a closely related construction starting with `G : Cᵒᵖ ⥤ Cat`,
where morphisms consists again of `β : b ⟶ b'` and `φ : f ⟶ (F.map (op β)).obj f'`.

## References

See also `category_theory.functor.elements` for the category of elements of functor `F : C ⥤ Type`.

* https://stacks.math.columbia.edu/tag/02XV
* https://ncatlab.org/nlab/show/Grothendieck+construction

-/


universe u

namespace CategoryTheory

variable {C D : Type _} [Category C] [Category D]

variable (F : C ⥤ Cat)

/- warning: category_theory.grothendieck -> CategoryTheory.Grothendieck is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C], (CategoryTheory.Functor.{u2, max u3 u4, u1, max (succ u4) u4 (succ u3)} C _inst_1 CategoryTheory.Cat.{u3, u4} CategoryTheory.Cat.category.{u3, u4}) -> Sort.{max (succ u1) (succ u4)}
but is expected to have type
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C], (CategoryTheory.Functor.{u2, max u3 u4, u1, max (succ u3) (succ u4)} C _inst_1 CategoryTheory.Cat.{u4, u3} CategoryTheory.Cat.category.{u4, u3}) -> Sort.{max (succ u1) (succ u3)}
Case conversion may be inaccurate. Consider using '#align category_theory.grothendieck CategoryTheory.Grothendieckₓ'. -/
/--
The Grothendieck construction (often written as `∫ F` in mathematics) for a functor `F : C ⥤ Cat`
gives a category whose
* objects `X` consist of `X.base : C` and `X.fiber : F.obj base`
* morphisms `f : X ⟶ Y` consist of
  `base : X.base ⟶ Y.base` and
  `f.fiber : (F.map base).obj X.fiber ⟶ Y.fiber`
-/
@[nolint has_nonempty_instance]
structure Grothendieck where
  base : C
  fiber : F.obj base
#align category_theory.grothendieck CategoryTheory.Grothendieck

namespace Grothendieck

variable {F}

/- warning: category_theory.grothendieck.hom -> CategoryTheory.Grothendieck.Hom is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] {F : CategoryTheory.Functor.{u2, max u3 u4, u1, max (succ u4) u4 (succ u3)} C _inst_1 CategoryTheory.Cat.{u3, u4} CategoryTheory.Cat.category.{u3, u4}}, (CategoryTheory.Grothendieck.{u1, u2, u3, u4} C _inst_1 F) -> (CategoryTheory.Grothendieck.{u1, u2, u3, u4} C _inst_1 F) -> Sort.{max (succ u2) (succ u3)}
but is expected to have type
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] {F : CategoryTheory.Functor.{u2, max u3 u4, u1, max (succ u3) (succ u4)} C _inst_1 CategoryTheory.Cat.{u4, u3} CategoryTheory.Cat.category.{u4, u3}}, (CategoryTheory.Grothendieck.{u1, u2, u3, u4} C _inst_1 F) -> (CategoryTheory.Grothendieck.{u1, u2, u3, u4} C _inst_1 F) -> Sort.{max (succ u2) (succ u4)}
Case conversion may be inaccurate. Consider using '#align category_theory.grothendieck.hom CategoryTheory.Grothendieck.Homₓ'. -/
/-- A morphism in the Grothendieck category `F : C ⥤ Cat` consists of
`base : X.base ⟶ Y.base` and `f.fiber : (F.map base).obj X.fiber ⟶ Y.fiber`.
-/
structure Hom (X Y : Grothendieck F) where
  base : X.base ⟶ Y.base
  fiber : (F.map base).obj X.fiber ⟶ Y.fiber
#align category_theory.grothendieck.hom CategoryTheory.Grothendieck.Hom

/- warning: category_theory.grothendieck.ext -> CategoryTheory.Grothendieck.ext is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.grothendieck.ext CategoryTheory.Grothendieck.extₓ'. -/
@[ext]
theorem ext {X Y : Grothendieck F} (f g : Hom X Y) (w_base : f.base = g.base)
    (w_fiber : eqToHom (by rw [w_base]) ≫ f.fiber = g.fiber) : f = g :=
  by
  cases f <;> cases g
  congr
  dsimp at w_base
  induction w_base
  rfl
  dsimp at w_base
  induction w_base
  simpa using w_fiber
#align category_theory.grothendieck.ext CategoryTheory.Grothendieck.ext

/- warning: category_theory.grothendieck.id -> CategoryTheory.Grothendieck.id is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] {F : CategoryTheory.Functor.{u2, max u3 u4, u1, max (succ u4) u4 (succ u3)} C _inst_1 CategoryTheory.Cat.{u3, u4} CategoryTheory.Cat.category.{u3, u4}} (X : CategoryTheory.Grothendieck.{u1, u2, u3, u4} C _inst_1 F), CategoryTheory.Grothendieck.Hom.{u1, u2, u3, u4} C _inst_1 F X X
but is expected to have type
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] {F : CategoryTheory.Functor.{u2, max u3 u4, u1, max (succ u3) (succ u4)} C _inst_1 CategoryTheory.Cat.{u4, u3} CategoryTheory.Cat.category.{u4, u3}} (X : CategoryTheory.Grothendieck.{u1, u2, u3, u4} C _inst_1 F), CategoryTheory.Grothendieck.Hom.{u1, u2, u3, u4} C _inst_1 F X X
Case conversion may be inaccurate. Consider using '#align category_theory.grothendieck.id CategoryTheory.Grothendieck.idₓ'. -/
/-- The identity morphism in the Grothendieck category.
-/
@[simps]
def id (X : Grothendieck F) : Hom X X where
  base := 𝟙 X.base
  fiber := eqToHom (by erw [CategoryTheory.Functor.map_id, functor.id_obj X.fiber])
#align category_theory.grothendieck.id CategoryTheory.Grothendieck.id

instance (X : Grothendieck F) : Inhabited (Hom X X) :=
  ⟨id X⟩

/- warning: category_theory.grothendieck.comp -> CategoryTheory.Grothendieck.comp is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] {F : CategoryTheory.Functor.{u2, max u3 u4, u1, max (succ u4) u4 (succ u3)} C _inst_1 CategoryTheory.Cat.{u3, u4} CategoryTheory.Cat.category.{u3, u4}} {X : CategoryTheory.Grothendieck.{u1, u2, u3, u4} C _inst_1 F} {Y : CategoryTheory.Grothendieck.{u1, u2, u3, u4} C _inst_1 F} {Z : CategoryTheory.Grothendieck.{u1, u2, u3, u4} C _inst_1 F}, (CategoryTheory.Grothendieck.Hom.{u1, u2, u3, u4} C _inst_1 F X Y) -> (CategoryTheory.Grothendieck.Hom.{u1, u2, u3, u4} C _inst_1 F Y Z) -> (CategoryTheory.Grothendieck.Hom.{u1, u2, u3, u4} C _inst_1 F X Z)
but is expected to have type
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] {F : CategoryTheory.Functor.{u2, max u3 u4, u1, max (succ u3) (succ u4)} C _inst_1 CategoryTheory.Cat.{u4, u3} CategoryTheory.Cat.category.{u4, u3}} {X : CategoryTheory.Grothendieck.{u1, u2, u3, u4} C _inst_1 F} {Y : CategoryTheory.Grothendieck.{u1, u2, u3, u4} C _inst_1 F} {Z : CategoryTheory.Grothendieck.{u1, u2, u3, u4} C _inst_1 F}, (CategoryTheory.Grothendieck.Hom.{u1, u2, u3, u4} C _inst_1 F X Y) -> (CategoryTheory.Grothendieck.Hom.{u1, u2, u3, u4} C _inst_1 F Y Z) -> (CategoryTheory.Grothendieck.Hom.{u1, u2, u3, u4} C _inst_1 F X Z)
Case conversion may be inaccurate. Consider using '#align category_theory.grothendieck.comp CategoryTheory.Grothendieck.compₓ'. -/
/-- Composition of morphisms in the Grothendieck category.
-/
@[simps]
def comp {X Y Z : Grothendieck F} (f : Hom X Y) (g : Hom Y Z) : Hom X Z
    where
  base := f.base ≫ g.base
  fiber :=
    eqToHom (by erw [functor.map_comp, functor.comp_obj]) ≫ (F.map g.base).map f.fiber ≫ g.fiber
#align category_theory.grothendieck.comp CategoryTheory.Grothendieck.comp

attribute [local simp] eq_to_hom_map

instance : Category (Grothendieck F)
    where
  Hom X Y := Grothendieck.Hom X Y
  id X := Grothendieck.id X
  comp X Y Z f g := Grothendieck.comp f g
  comp_id' X Y f := by
    ext
    · dsimp
      -- We need to turn `F.map_id` (which is an equation between functors)
      -- into a natural isomorphism.
      rw [← nat_iso.naturality_2 (eq_to_iso (F.map_id Y.base)) f.fiber]
      simp
    · simp
  id_comp' X Y f := by ext <;> simp
  assoc' W X Y Z f g h := by
    ext; swap
    · simp
    · dsimp
      rw [← nat_iso.naturality_2 (eq_to_iso (F.map_comp _ _)) f.fiber]
      simp
      rfl

/- warning: category_theory.grothendieck.id_fiber' -> CategoryTheory.Grothendieck.id_fiber' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.grothendieck.id_fiber' CategoryTheory.Grothendieck.id_fiber'ₓ'. -/
@[simp]
theorem id_fiber' (X : Grothendieck F) :
    Hom.fiber (𝟙 X) = eqToHom (by erw [CategoryTheory.Functor.map_id, functor.id_obj X.fiber]) :=
  id_fiber X
#align category_theory.grothendieck.id_fiber' CategoryTheory.Grothendieck.id_fiber'

/- warning: category_theory.grothendieck.congr -> CategoryTheory.Grothendieck.congr is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.grothendieck.congr CategoryTheory.Grothendieck.congrₓ'. -/
theorem congr {X Y : Grothendieck F} {f g : X ⟶ Y} (h : f = g) :
    f.fiber = eqToHom (by subst h) ≫ g.fiber :=
  by
  subst h
  dsimp
  simp
#align category_theory.grothendieck.congr CategoryTheory.Grothendieck.congr

section

variable (F)

/- warning: category_theory.grothendieck.forget -> CategoryTheory.Grothendieck.forget is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] (F : CategoryTheory.Functor.{u2, max u3 u4, u1, max (succ u4) u4 (succ u3)} C _inst_1 CategoryTheory.Cat.{u3, u4} CategoryTheory.Cat.category.{u3, u4}), CategoryTheory.Functor.{max u2 u3, u2, max u1 u4, u1} (CategoryTheory.Grothendieck.{u1, u2, u3, u4} C _inst_1 F) (CategoryTheory.Grothendieck.CategoryTheory.category.{u1, u2, u3, u4} C _inst_1 F) C _inst_1
but is expected to have type
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] (F : CategoryTheory.Functor.{u2, max u3 u4, u1, max (succ u3) (succ u4)} C _inst_1 CategoryTheory.Cat.{u4, u3} CategoryTheory.Cat.category.{u4, u3}), CategoryTheory.Functor.{max u2 u4, u2, max u3 u1, u1} (CategoryTheory.Grothendieck.{u1, u2, u3, u4} C _inst_1 F) (CategoryTheory.Grothendieck.instCategoryGrothendieck.{u1, u2, u3, u4} C _inst_1 F) C _inst_1
Case conversion may be inaccurate. Consider using '#align category_theory.grothendieck.forget CategoryTheory.Grothendieck.forgetₓ'. -/
/-- The forgetful functor from `grothendieck F` to the source category. -/
@[simps]
def forget : Grothendieck F ⥤ C where
  obj X := X.1
  map X Y f := f.1
#align category_theory.grothendieck.forget CategoryTheory.Grothendieck.forget

end

universe w

variable (G : C ⥤ Type w)

/- warning: category_theory.grothendieck.grothendieck_Type_to_Cat_functor -> CategoryTheory.Grothendieck.grothendieckTypeToCatFunctor is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] (G : CategoryTheory.Functor.{u2, u3, u1, succ u3} C _inst_1 Type.{u3} CategoryTheory.types.{u3}), CategoryTheory.Functor.{max u2 u3, u2, max u1 u3, max u1 u3} (CategoryTheory.Grothendieck.{u1, u2, u3, u3} C _inst_1 (CategoryTheory.Functor.comp.{u2, u3, u3, u1, succ u3, succ u3} C _inst_1 Type.{u3} CategoryTheory.types.{u3} CategoryTheory.Cat.{u3, u3} CategoryTheory.Cat.category.{u3, u3} G CategoryTheory.typeToCat.{u3})) (CategoryTheory.Grothendieck.CategoryTheory.category.{u1, u2, u3, u3} C _inst_1 (CategoryTheory.Functor.comp.{u2, u3, u3, u1, succ u3, succ u3} C _inst_1 Type.{u3} CategoryTheory.types.{u3} CategoryTheory.Cat.{u3, u3} CategoryTheory.Cat.category.{u3, u3} G CategoryTheory.typeToCat.{u3})) (CategoryTheory.Functor.Elements.{u3, u2, u1} C _inst_1 G) (CategoryTheory.categoryOfElements.{u3, u2, u1} C _inst_1 G)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u2} C] (G : CategoryTheory.Functor.{u3, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}), CategoryTheory.Functor.{max u1 u3, u3, max u1 u2, max u1 u2} (CategoryTheory.Grothendieck.{u2, u3, u1, u1} C _inst_1 (CategoryTheory.Functor.comp.{u3, u1, u1, u2, succ u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} CategoryTheory.Cat.{u1, u1} CategoryTheory.Cat.category.{u1, u1} G CategoryTheory.typeToCat.{u1})) (CategoryTheory.Grothendieck.instCategoryGrothendieck.{u2, u3, u1, u1} C _inst_1 (CategoryTheory.Functor.comp.{u3, u1, u1, u2, succ u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} CategoryTheory.Cat.{u1, u1} CategoryTheory.Cat.category.{u1, u1} G CategoryTheory.typeToCat.{u1})) (CategoryTheory.Functor.Elements.{u1, u3, u2} C _inst_1 G) (CategoryTheory.categoryOfElements.{u1, u3, u2} C _inst_1 G)
Case conversion may be inaccurate. Consider using '#align category_theory.grothendieck.grothendieck_Type_to_Cat_functor CategoryTheory.Grothendieck.grothendieckTypeToCatFunctorₓ'. -/
/-- Auxiliary definition for `grothendieck_Type_to_Cat`, to speed up elaboration. -/
@[simps]
def grothendieckTypeToCatFunctor : Grothendieck (G ⋙ typeToCat) ⥤ G.Elements
    where
  obj X := ⟨X.1, X.2.as⟩
  map X Y f := ⟨f.1, f.2.1.1⟩
#align category_theory.grothendieck.grothendieck_Type_to_Cat_functor CategoryTheory.Grothendieck.grothendieckTypeToCatFunctor

/- warning: category_theory.grothendieck.grothendieck_Type_to_Cat_inverse -> CategoryTheory.Grothendieck.grothendieckTypeToCatInverse is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] (G : CategoryTheory.Functor.{u2, u3, u1, succ u3} C _inst_1 Type.{u3} CategoryTheory.types.{u3}), CategoryTheory.Functor.{u2, max u2 u3, max u1 u3, max u1 u3} (CategoryTheory.Functor.Elements.{u3, u2, u1} C _inst_1 G) (CategoryTheory.categoryOfElements.{u3, u2, u1} C _inst_1 G) (CategoryTheory.Grothendieck.{u1, u2, u3, u3} C _inst_1 (CategoryTheory.Functor.comp.{u2, u3, u3, u1, succ u3, succ u3} C _inst_1 Type.{u3} CategoryTheory.types.{u3} CategoryTheory.Cat.{u3, u3} CategoryTheory.Cat.category.{u3, u3} G CategoryTheory.typeToCat.{u3})) (CategoryTheory.Grothendieck.CategoryTheory.category.{u1, u2, u3, u3} C _inst_1 (CategoryTheory.Functor.comp.{u2, u3, u3, u1, succ u3, succ u3} C _inst_1 Type.{u3} CategoryTheory.types.{u3} CategoryTheory.Cat.{u3, u3} CategoryTheory.Cat.category.{u3, u3} G CategoryTheory.typeToCat.{u3}))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u2} C] (G : CategoryTheory.Functor.{u3, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}), CategoryTheory.Functor.{u3, max u1 u3, max u1 u2, max u1 u2} (CategoryTheory.Functor.Elements.{u1, u3, u2} C _inst_1 G) (CategoryTheory.categoryOfElements.{u1, u3, u2} C _inst_1 G) (CategoryTheory.Grothendieck.{u2, u3, u1, u1} C _inst_1 (CategoryTheory.Functor.comp.{u3, u1, u1, u2, succ u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} CategoryTheory.Cat.{u1, u1} CategoryTheory.Cat.category.{u1, u1} G CategoryTheory.typeToCat.{u1})) (CategoryTheory.Grothendieck.instCategoryGrothendieck.{u2, u3, u1, u1} C _inst_1 (CategoryTheory.Functor.comp.{u3, u1, u1, u2, succ u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} CategoryTheory.Cat.{u1, u1} CategoryTheory.Cat.category.{u1, u1} G CategoryTheory.typeToCat.{u1}))
Case conversion may be inaccurate. Consider using '#align category_theory.grothendieck.grothendieck_Type_to_Cat_inverse CategoryTheory.Grothendieck.grothendieckTypeToCatInverseₓ'. -/
/-- Auxiliary definition for `grothendieck_Type_to_Cat`, to speed up elaboration. -/
@[simps]
def grothendieckTypeToCatInverse : G.Elements ⥤ Grothendieck (G ⋙ typeToCat)
    where
  obj X := ⟨X.1, ⟨X.2⟩⟩
  map X Y f := ⟨f.1, ⟨⟨f.2⟩⟩⟩
#align category_theory.grothendieck.grothendieck_Type_to_Cat_inverse CategoryTheory.Grothendieck.grothendieckTypeToCatInverse

/- warning: category_theory.grothendieck.grothendieck_Type_to_Cat -> CategoryTheory.Grothendieck.grothendieckTypeToCat is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] (G : CategoryTheory.Functor.{u2, u3, u1, succ u3} C _inst_1 Type.{u3} CategoryTheory.types.{u3}), CategoryTheory.Equivalence.{max u2 u3, u2, max u1 u3, max u1 u3} (CategoryTheory.Grothendieck.{u1, u2, u3, u3} C _inst_1 (CategoryTheory.Functor.comp.{u2, u3, u3, u1, succ u3, succ u3} C _inst_1 Type.{u3} CategoryTheory.types.{u3} CategoryTheory.Cat.{u3, u3} CategoryTheory.Cat.category.{u3, u3} G CategoryTheory.typeToCat.{u3})) (CategoryTheory.Grothendieck.CategoryTheory.category.{u1, u2, u3, u3} C _inst_1 (CategoryTheory.Functor.comp.{u2, u3, u3, u1, succ u3, succ u3} C _inst_1 Type.{u3} CategoryTheory.types.{u3} CategoryTheory.Cat.{u3, u3} CategoryTheory.Cat.category.{u3, u3} G CategoryTheory.typeToCat.{u3})) (CategoryTheory.Functor.Elements.{u3, u2, u1} C _inst_1 G) (CategoryTheory.categoryOfElements.{u3, u2, u1} C _inst_1 G)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u2} C] (G : CategoryTheory.Functor.{u3, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}), CategoryTheory.Equivalence.{max u1 u3, u3, max u1 u2, max u1 u2} (CategoryTheory.Grothendieck.{u2, u3, u1, u1} C _inst_1 (CategoryTheory.Functor.comp.{u3, u1, u1, u2, succ u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} CategoryTheory.Cat.{u1, u1} CategoryTheory.Cat.category.{u1, u1} G CategoryTheory.typeToCat.{u1})) (CategoryTheory.Functor.Elements.{u1, u3, u2} C _inst_1 G) (CategoryTheory.Grothendieck.instCategoryGrothendieck.{u2, u3, u1, u1} C _inst_1 (CategoryTheory.Functor.comp.{u3, u1, u1, u2, succ u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} CategoryTheory.Cat.{u1, u1} CategoryTheory.Cat.category.{u1, u1} G CategoryTheory.typeToCat.{u1})) (CategoryTheory.categoryOfElements.{u1, u3, u2} C _inst_1 G)
Case conversion may be inaccurate. Consider using '#align category_theory.grothendieck.grothendieck_Type_to_Cat CategoryTheory.Grothendieck.grothendieckTypeToCatₓ'. -/
/-- The Grothendieck construction applied to a functor to `Type`
(thought of as a functor to `Cat` by realising a type as a discrete category)
is the same as the 'category of elements' construction.
-/
@[simps]
def grothendieckTypeToCat : Grothendieck (G ⋙ typeToCat) ≌ G.Elements
    where
  Functor := grothendieckTypeToCatFunctor G
  inverse := grothendieckTypeToCatInverse G
  unitIso :=
    NatIso.ofComponents
      (fun X => by
        rcases X with ⟨_, ⟨⟩⟩
        exact iso.refl _)
      (by
        rintro ⟨_, ⟨⟩⟩ ⟨_, ⟨⟩⟩ ⟨base, ⟨⟨f⟩⟩⟩
        dsimp at *
        subst f
        ext
        simp)
  counitIso :=
    NatIso.ofComponents
      (fun X => by
        cases X
        exact iso.refl _)
      (by
        rintro ⟨⟩ ⟨⟩ ⟨f, e⟩
        dsimp at *
        subst e
        ext
        simp)
  functor_unitIso_comp' := by
    rintro ⟨_, ⟨⟩⟩
    dsimp
    simp
    rfl
#align category_theory.grothendieck.grothendieck_Type_to_Cat CategoryTheory.Grothendieck.grothendieckTypeToCat

end Grothendieck

end CategoryTheory

