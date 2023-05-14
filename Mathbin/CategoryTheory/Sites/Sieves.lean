/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, E. W. Ayers

! This file was ported from Lean 3 source module category_theory.sites.sieves
! leanprover-community/mathlib commit f47581155c818e6361af4e4fda60d27d020c226b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.CompleteLattice
import Mathbin.CategoryTheory.Over
import Mathbin.CategoryTheory.Yoneda
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks
import Mathbin.Data.Set.Lattice

/-!
# Theory of sieves

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

- For an object `X` of a category `C`, a `sieve X` is a set of morphisms to `X`
  which is closed under left-composition.
- The complete lattice structure on sieves is given, as well as the Galois insertion
  given by downward-closing.
- A `sieve X` (functorially) induces a presheaf on `C` together with a monomorphism to
  the yoneda embedding of `X`.

## Tags

sieve, pullback
-/


universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

variable {X Y Z : C} (f : Y ⟶ X)

#print CategoryTheory.Presieve /-
/-- A set of arrows all with codomain `X`. -/
def Presieve (X : C) :=
  ∀ ⦃Y⦄, Set (Y ⟶ X)deriving CompleteLattice
#align category_theory.presieve CategoryTheory.Presieve
-/

namespace Presieve

instance : Inhabited (Presieve X) :=
  ⟨⊤⟩

/- warning: category_theory.presieve.diagram -> CategoryTheory.Presieve.diagram is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} (S : CategoryTheory.Presieve.{u1, u2} C _inst_1 X), CategoryTheory.Functor.{u1, u1, max u2 u1, u2} (CategoryTheory.FullSubcategoryₓ.{u1, max u2 u1} (CategoryTheory.Over.{u1, u2} C _inst_1 X) (CategoryTheory.Over.category.{u2, u1} C _inst_1 X) (fun (f : CategoryTheory.Over.{u1, u2} C _inst_1 X) => S (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.Comma.hom.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f))) (CategoryTheory.FullSubcategory.category.{u1, max u2 u1} (CategoryTheory.Over.{u1, u2} C _inst_1 X) (CategoryTheory.Over.category.{u2, u1} C _inst_1 X) (fun (f : CategoryTheory.Over.{u1, u2} C _inst_1 X) => S (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.Comma.hom.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f))) C _inst_1
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} (S : CategoryTheory.Presieve.{u1, u2} C _inst_1 X), CategoryTheory.Functor.{u1, u1, max u2 u1, u2} (CategoryTheory.FullSubcategory.{max u2 u1} (CategoryTheory.Over.{u1, u2} C _inst_1 X) (fun (f : CategoryTheory.Over.{u1, u2} C _inst_1 X) => S (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1)) (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.Comma.hom.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f))) (CategoryTheory.FullSubcategory.category.{u1, max u2 u1} (CategoryTheory.Over.{u1, u2} C _inst_1 X) (CategoryTheory.instCategoryOver.{u1, u2} C _inst_1 X) (fun (f : CategoryTheory.Over.{u1, u2} C _inst_1 X) => S (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1)) (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.Comma.hom.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f))) C _inst_1
Case conversion may be inaccurate. Consider using '#align category_theory.presieve.diagram CategoryTheory.Presieve.diagramₓ'. -/
/-- Given a sieve `S` on `X : C`, its associated diagram `S.diagram` is defined to be
    the natural functor from the full subcategory of the over category `C/X` consisting
    of arrows in `S` to `C`. -/
abbrev diagram (S : Presieve X) : (FullSubcategory fun f : Over X => S f.Hom) ⥤ C :=
  fullSubcategoryInclusion _ ⋙ Over.forget X
#align category_theory.presieve.diagram CategoryTheory.Presieve.diagram

/- warning: category_theory.presieve.cocone -> CategoryTheory.Presieve.cocone is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} (S : CategoryTheory.Presieve.{u1, u2} C _inst_1 X), CategoryTheory.Limits.Cocone.{u1, u1, max u2 u1, u2} (CategoryTheory.FullSubcategoryₓ.{u1, max u2 u1} (CategoryTheory.Over.{u1, u2} C _inst_1 X) (CategoryTheory.Over.category.{u2, u1} C _inst_1 X) (fun (f : CategoryTheory.Over.{u1, u2} C _inst_1 X) => S (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.Comma.hom.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f))) (CategoryTheory.FullSubcategory.category.{u1, max u2 u1} (CategoryTheory.Over.{u1, u2} C _inst_1 X) (CategoryTheory.Over.category.{u2, u1} C _inst_1 X) (fun (f : CategoryTheory.Over.{u1, u2} C _inst_1 X) => S (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.Comma.hom.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f))) C _inst_1 (CategoryTheory.Presieve.diagram.{u1, u2} C _inst_1 X S)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} (S : CategoryTheory.Presieve.{u1, u2} C _inst_1 X), CategoryTheory.Limits.Cocone.{u1, u1, max u2 u1, u2} (CategoryTheory.FullSubcategory.{max u2 u1} (CategoryTheory.Over.{u1, u2} C _inst_1 X) (fun (f : CategoryTheory.Over.{u1, u2} C _inst_1 X) => S (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1)) (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.Comma.hom.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f))) (CategoryTheory.FullSubcategory.category.{u1, max u2 u1} (CategoryTheory.Over.{u1, u2} C _inst_1 X) (CategoryTheory.instCategoryOver.{u1, u2} C _inst_1 X) (fun (f : CategoryTheory.Over.{u1, u2} C _inst_1 X) => S (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1)) (CategoryTheory.Comma.left.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f)) (CategoryTheory.Comma.hom.{u1, u1, u1, u2, u1, u2} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) (CategoryTheory.Functor.fromPUnit.{u1, u2} C _inst_1 X) f))) C _inst_1 (CategoryTheory.Presieve.diagram.{u1, u2} C _inst_1 X S)
Case conversion may be inaccurate. Consider using '#align category_theory.presieve.cocone CategoryTheory.Presieve.coconeₓ'. -/
/-- Given a sieve `S` on `X : C`, its associated cocone `S.cocone` is defined to be
    the natural cocone over the diagram defined above with cocone point `X`. -/
abbrev cocone (S : Presieve X) : Cocone S.diagram :=
  (Over.forgetCocone X).whisker (fullSubcategoryInclusion _)
#align category_theory.presieve.cocone CategoryTheory.Presieve.cocone

#print CategoryTheory.Presieve.bind /-
/-- Given a set of arrows `S` all with codomain `X`, and a set of arrows with codomain `Y` for each
`f : Y ⟶ X` in `S`, produce a set of arrows with codomain `X`:
`{ g ≫ f | (f : Y ⟶ X) ∈ S, (g : Z ⟶ Y) ∈ R f }`.
-/
def bind (S : Presieve X) (R : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → Presieve Y) : Presieve X := fun Z h =>
  ∃ (Y : C)(g : Z ⟶ Y)(f : Y ⟶ X)(H : S f), R H g ∧ g ≫ f = h
#align category_theory.presieve.bind CategoryTheory.Presieve.bind
-/

#print CategoryTheory.Presieve.bind_comp /-
@[simp]
theorem bind_comp {S : Presieve X} {R : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → Presieve Y} {g : Z ⟶ Y}
    (h₁ : S f) (h₂ : R h₁ g) : bind S R (g ≫ f) :=
  ⟨_, _, _, h₁, h₂, rfl⟩
#align category_theory.presieve.bind_comp CategoryTheory.Presieve.bind_comp
-/

-- Note we can't make this into `has_singleton` because of the out-param.
/-- The singleton presieve.  -/
inductive singleton : Presieve X
  | mk : singleton f
#align category_theory.presieve.singleton CategoryTheory.Presieve.singletonₓ

/- warning: category_theory.presieve.singleton_eq_iff_domain -> CategoryTheory.Presieve.singleton_eq_iff_domain is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X) (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X), Iff (CategoryTheory.Presieve.singletonₓ.{u1, u2} C _inst_1 X Y f Y g) (Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X) f g)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X) (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X), Iff (CategoryTheory.Presieve.singleton.{u1, u2} C _inst_1 X Y f Y g) (Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X) f g)
Case conversion may be inaccurate. Consider using '#align category_theory.presieve.singleton_eq_iff_domain CategoryTheory.Presieve.singleton_eq_iff_domainₓ'. -/
@[simp]
theorem singleton_eq_iff_domain (f g : Y ⟶ X) : singleton f g ↔ f = g :=
  by
  constructor
  · rintro ⟨a, rfl⟩
    rfl
  · rintro rfl
    apply singleton.mk
#align category_theory.presieve.singleton_eq_iff_domain CategoryTheory.Presieve.singleton_eq_iff_domain

/- warning: category_theory.presieve.singleton_self -> CategoryTheory.Presieve.singleton_self is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X), CategoryTheory.Presieve.singletonₓ.{u1, u2} C _inst_1 X Y f Y f
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X), CategoryTheory.Presieve.singleton.{u1, u2} C _inst_1 X Y f Y f
Case conversion may be inaccurate. Consider using '#align category_theory.presieve.singleton_self CategoryTheory.Presieve.singleton_selfₓ'. -/
theorem singleton_self : singleton f f :=
  singleton.mk
#align category_theory.presieve.singleton_self CategoryTheory.Presieve.singleton_self

#print CategoryTheory.Presieve.pullbackArrows /-
/-- Pullback a set of arrows with given codomain along a fixed map, by taking the pullback in the
category.
This is not the same as the arrow set of `sieve.pullback`, but there is a relation between them
in `pullback_arrows_comm`.
-/
inductive pullbackArrows [HasPullbacks C] (R : Presieve X) : Presieve Y
  | mk (Z : C) (h : Z ⟶ X) : R h → pullback_arrows (pullback.snd : pullback h f ⟶ Y)
#align category_theory.presieve.pullback_arrows CategoryTheory.Presieve.pullbackArrows
-/

/- warning: category_theory.presieve.pullback_singleton -> CategoryTheory.Presieve.pullback_singleton is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X) [_inst_3 : CategoryTheory.Limits.HasPullbacks.{u1, u2} C _inst_1] (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Z X), Eq.{max (succ u2) (succ u1)} (CategoryTheory.Presieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Presieve.pullbackArrows.{u1, u2} C _inst_1 X Y f _inst_3 (CategoryTheory.Presieve.singletonₓ.{u1, u2} C _inst_1 X Z g)) (CategoryTheory.Presieve.singletonₓ.{u1, u2} C _inst_1 Y (CategoryTheory.Limits.pullback.{u1, u2} C _inst_1 Z Y X g f (CategoryTheory.Limits.hasLimitOfHasLimitsOfShape.{0, 0, u1, u2} C _inst_1 CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) _inst_3 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 Z Y X g f))) (CategoryTheory.Limits.pullback.snd.{u1, u2} C _inst_1 Z Y X g f (CategoryTheory.Limits.hasLimitOfHasLimitsOfShape.{0, 0, u1, u2} C _inst_1 CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) _inst_3 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 Z Y X g f))))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X) [_inst_3 : CategoryTheory.Limits.HasPullbacks.{u1, u2} C _inst_1] (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Z X), Eq.{max (succ u2) (succ u1)} (CategoryTheory.Presieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Presieve.pullbackArrows.{u1, u2} C _inst_1 X Y f _inst_3 (CategoryTheory.Presieve.singleton.{u1, u2} C _inst_1 X Z g)) (CategoryTheory.Presieve.singleton.{u1, u2} C _inst_1 Y (CategoryTheory.Limits.pullback.{u1, u2} C _inst_1 Z Y X g f (CategoryTheory.Limits.hasLimitOfHasLimitsOfShape.{0, 0, u1, u2} C _inst_1 CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) _inst_3 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 Z Y X g f))) (CategoryTheory.Limits.pullback.snd.{u1, u2} C _inst_1 Z Y X g f (CategoryTheory.Limits.hasLimitOfHasLimitsOfShape.{0, 0, u1, u2} C _inst_1 CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) _inst_3 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 Z Y X g f))))
Case conversion may be inaccurate. Consider using '#align category_theory.presieve.pullback_singleton CategoryTheory.Presieve.pullback_singletonₓ'. -/
theorem pullback_singleton [HasPullbacks C] (g : Z ⟶ X) :
    pullbackArrows f (singleton g) = singleton (pullback.snd : pullback g f ⟶ _) :=
  by
  ext (W h)
  constructor
  · rintro ⟨W, _, _, _⟩
    exact singleton.mk
  · rintro ⟨_⟩
    exact pullback_arrows.mk Z g singleton.mk
#align category_theory.presieve.pullback_singleton CategoryTheory.Presieve.pullback_singleton

#print CategoryTheory.Presieve.ofArrows /-
/-- Construct the presieve given by the family of arrows indexed by `ι`. -/
inductive ofArrows {ι : Type _} (Y : ι → C) (f : ∀ i, Y i ⟶ X) : Presieve X
  | mk (i : ι) : of_arrows (f i)
#align category_theory.presieve.of_arrows CategoryTheory.Presieve.ofArrows
-/

/- warning: category_theory.presieve.of_arrows_punit -> CategoryTheory.Presieve.ofArrows_pUnit is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X), Eq.{max (succ u2) (succ u1)} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CategoryTheory.Presieve.ofArrows.{u1, u2, u3} C _inst_1 X PUnit.{succ u3} (fun (_x : PUnit.{succ u3}) => Y) (fun (_x : PUnit.{succ u3}) => f)) (CategoryTheory.Presieve.singletonₓ.{u1, u2} C _inst_1 X Y f)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) Y X), Eq.{max (succ u3) (succ u2)} (CategoryTheory.Presieve.{u2, u3} C _inst_1 X) (CategoryTheory.Presieve.ofArrows.{u2, u3, u1} C _inst_1 X PUnit.{succ u1} (fun (_x : PUnit.{succ u1}) => Y) (fun (_x : PUnit.{succ u1}) => f)) (CategoryTheory.Presieve.singleton.{u2, u3} C _inst_1 X Y f)
Case conversion may be inaccurate. Consider using '#align category_theory.presieve.of_arrows_punit CategoryTheory.Presieve.ofArrows_pUnitₓ'. -/
theorem ofArrows_pUnit : (ofArrows _ fun _ : PUnit => f) = singleton f :=
  by
  ext (Y g)
  constructor
  · rintro ⟨_⟩
    apply singleton.mk
  · rintro ⟨_⟩
    exact of_arrows.mk PUnit.unit
#align category_theory.presieve.of_arrows_punit CategoryTheory.Presieve.ofArrows_pUnit

/- warning: category_theory.presieve.of_arrows_pullback -> CategoryTheory.Presieve.ofArrows_pullback is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X) [_inst_3 : CategoryTheory.Limits.HasPullbacks.{u1, u2} C _inst_1] {ι : Type.{u3}} (Z : ι -> C) (g : forall (i : ι), Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Z i) X), Eq.{max (succ u2) (succ u1)} (CategoryTheory.Presieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Presieve.ofArrows.{u1, u2, u3} C _inst_1 Y ι (fun (i : ι) => CategoryTheory.Limits.pullback.{u1, u2} C _inst_1 (Z i) Y X (g i) f (CategoryTheory.Limits.hasLimitOfHasLimitsOfShape.{0, 0, u1, u2} C _inst_1 CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) _inst_3 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 (Z i) Y X (g i) f))) (fun (i : ι) => CategoryTheory.Limits.pullback.snd.{u1, u2} C _inst_1 (Z i) Y X (g i) f (CategoryTheory.Limits.hasLimitOfHasLimitsOfShape.{0, 0, u1, u2} C _inst_1 CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) _inst_3 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 (Z i) Y X (g i) f)))) (CategoryTheory.Presieve.pullbackArrows.{u1, u2} C _inst_1 X Y f _inst_3 (CategoryTheory.Presieve.ofArrows.{u1, u2, u3} C _inst_1 X ι Z g))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) Y X) [_inst_3 : CategoryTheory.Limits.HasPullbacks.{u2, u3} C _inst_1] {ι : Type.{u1}} (Z : ι -> C) (g : forall (i : ι), Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (Z i) X), Eq.{max (succ u3) (succ u2)} (CategoryTheory.Presieve.{u2, u3} C _inst_1 Y) (CategoryTheory.Presieve.ofArrows.{u2, u3, u1} C _inst_1 Y ι (fun (i : ι) => CategoryTheory.Limits.pullback.{u2, u3} C _inst_1 (Z i) Y X (g i) f (CategoryTheory.Limits.hasLimitOfHasLimitsOfShape.{0, 0, u2, u3} C _inst_1 CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) _inst_3 (CategoryTheory.Limits.cospan.{u2, u3} C _inst_1 (Z i) Y X (g i) f))) (fun (i : ι) => CategoryTheory.Limits.pullback.snd.{u2, u3} C _inst_1 (Z i) Y X (g i) f (CategoryTheory.Limits.hasLimitOfHasLimitsOfShape.{0, 0, u2, u3} C _inst_1 CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) _inst_3 (CategoryTheory.Limits.cospan.{u2, u3} C _inst_1 (Z i) Y X (g i) f)))) (CategoryTheory.Presieve.pullbackArrows.{u2, u3} C _inst_1 X Y f _inst_3 (CategoryTheory.Presieve.ofArrows.{u2, u3, u1} C _inst_1 X ι Z g))
Case conversion may be inaccurate. Consider using '#align category_theory.presieve.of_arrows_pullback CategoryTheory.Presieve.ofArrows_pullbackₓ'. -/
theorem ofArrows_pullback [HasPullbacks C] {ι : Type _} (Z : ι → C) (g : ∀ i : ι, Z i ⟶ X) :
    (ofArrows (fun i => pullback (g i) f) fun i => pullback.snd) =
      pullbackArrows f (ofArrows Z g) :=
  by
  ext (T h)
  constructor
  · rintro ⟨hk⟩
    exact pullback_arrows.mk _ _ (of_arrows.mk hk)
  · rintro ⟨W, k, hk₁⟩
    cases' hk₁ with i hi
    apply of_arrows.mk
#align category_theory.presieve.of_arrows_pullback CategoryTheory.Presieve.ofArrows_pullback

/- warning: category_theory.presieve.of_arrows_bind -> CategoryTheory.Presieve.ofArrows_bind is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {ι : Type.{u3}} (Z : ι -> C) (g : forall (i : ι), Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Z i) X) (j : forall {{Y : C}} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X), (CategoryTheory.Presieve.ofArrows.{u1, u2, u3} C _inst_1 X ι Z g Y f) -> Type.{u4}) (W : forall {{Y : C}} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X) (H : CategoryTheory.Presieve.ofArrows.{u1, u2, u3} C _inst_1 X ι Z g Y f), (j Y f H) -> C) (k : forall {{Y : C}} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X) (H : CategoryTheory.Presieve.ofArrows.{u1, u2, u3} C _inst_1 X ι Z g Y f) (i : j Y f H), Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (W Y f H i) Y), Eq.{max (succ u2) (succ u1)} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CategoryTheory.Presieve.bind.{u1, u2} C _inst_1 X (CategoryTheory.Presieve.ofArrows.{u1, u2, u3} C _inst_1 X ι Z g) (fun (Y : C) (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X) (H : CategoryTheory.Presieve.ofArrows.{u1, u2, u3} C _inst_1 X ι Z g Y f) => CategoryTheory.Presieve.ofArrows.{u1, u2, u4} C _inst_1 Y (j Y f H) (W Y f H) (k Y f H))) (CategoryTheory.Presieve.ofArrows.{u1, u2, max u3 u4} C _inst_1 X (Sigma.{u3, u4} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u1, u2, u3} C _inst_1 X ι Z g i))) (fun (i : Sigma.{u3, u4} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u1, u2, u3} C _inst_1 X ι Z g i))) => W (Z (Sigma.fst.{u3, u4} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u1, u2, u3} C _inst_1 X ι Z g i)) i)) (g (Sigma.fst.{u3, u4} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u1, u2, u3} C _inst_1 X ι Z g i)) i)) (CategoryTheory.Presieve.ofArrows.mk.{u1, u2, u3} C _inst_1 X ι Z g (Sigma.fst.{u3, u4} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u1, u2, u3} C _inst_1 X ι Z g i)) i)) (Sigma.snd.{u3, u4} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u1, u2, u3} C _inst_1 X ι Z g i)) i)) (fun (ij : Sigma.{u3, u4} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u1, u2, u3} C _inst_1 X ι Z g i))) => CategoryTheory.CategoryStruct.comp.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) (W (Z (Sigma.fst.{u3, u4} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u1, u2, u3} C _inst_1 X ι Z g i)) ij)) (g (Sigma.fst.{u3, u4} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u1, u2, u3} C _inst_1 X ι Z g i)) ij)) (CategoryTheory.Presieve.ofArrows.mk.{u1, u2, u3} C _inst_1 X ι Z g (Sigma.fst.{u3, u4} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u1, u2, u3} C _inst_1 X ι Z g i)) ij)) (Sigma.snd.{u3, u4} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u1, u2, u3} C _inst_1 X ι Z g i)) ij)) (Z (Sigma.fst.{u3, u4} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u1, u2, u3} C _inst_1 X ι Z g i)) ij)) X (k (Z (Sigma.fst.{u3, u4} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u1, u2, u3} C _inst_1 X ι Z g i)) ij)) (g (Sigma.fst.{u3, u4} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u1, u2, u3} C _inst_1 X ι Z g i)) ij)) (CategoryTheory.Presieve.ofArrows.mk.{u1, u2, u3} C _inst_1 X ι Z g (Sigma.fst.{u3, u4} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u1, u2, u3} C _inst_1 X ι Z g i)) ij)) (Sigma.snd.{u3, u4} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u1, u2, u3} C _inst_1 X ι Z g i)) ij)) (g (Sigma.fst.{u3, u4} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u1, u2, u3} C _inst_1 X ι Z g i)) ij))))
but is expected to have type
  forall {C : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u3, u4} C] {X : C} {ι : Type.{u2}} (Z : ι -> C) (g : forall (i : ι), Quiver.Hom.{succ u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} C (CategoryTheory.Category.toCategoryStruct.{u3, u4} C _inst_1)) (Z i) X) (j : forall {{Y : C}} (f : Quiver.Hom.{succ u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} C (CategoryTheory.Category.toCategoryStruct.{u3, u4} C _inst_1)) Y X), (CategoryTheory.Presieve.ofArrows.{u3, u4, u2} C _inst_1 X ι Z g Y f) -> Type.{u1}) (W : forall {{Y : C}} (f : Quiver.Hom.{succ u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} C (CategoryTheory.Category.toCategoryStruct.{u3, u4} C _inst_1)) Y X) (H : CategoryTheory.Presieve.ofArrows.{u3, u4, u2} C _inst_1 X ι Z g Y f), (j Y f H) -> C) (k : forall {{Y : C}} (f : Quiver.Hom.{succ u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} C (CategoryTheory.Category.toCategoryStruct.{u3, u4} C _inst_1)) Y X) (H : CategoryTheory.Presieve.ofArrows.{u3, u4, u2} C _inst_1 X ι Z g Y f) (i : j Y f H), Quiver.Hom.{succ u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} C (CategoryTheory.Category.toCategoryStruct.{u3, u4} C _inst_1)) (W Y f H i) Y), Eq.{max (succ u4) (succ u3)} (CategoryTheory.Presieve.{u3, u4} C _inst_1 X) (CategoryTheory.Presieve.bind.{u3, u4} C _inst_1 X (CategoryTheory.Presieve.ofArrows.{u3, u4, u2} C _inst_1 X ι Z g) (fun (Y : C) (f : Quiver.Hom.{succ u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} C (CategoryTheory.Category.toCategoryStruct.{u3, u4} C _inst_1)) Y X) (H : CategoryTheory.Presieve.ofArrows.{u3, u4, u2} C _inst_1 X ι Z g Y f) => CategoryTheory.Presieve.ofArrows.{u3, u4, u1} C _inst_1 Y (j Y f H) (W Y f H) (k Y f H))) (CategoryTheory.Presieve.ofArrows.{u3, u4, max u2 u1} C _inst_1 X (Sigma.{u2, u1} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u3, u4, u2} C _inst_1 X ι Z g i))) (fun (i : Sigma.{u2, u1} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u3, u4, u2} C _inst_1 X ι Z g i))) => W (Z (Sigma.fst.{u2, u1} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u3, u4, u2} C _inst_1 X ι Z g i)) i)) (g (Sigma.fst.{u2, u1} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u3, u4, u2} C _inst_1 X ι Z g i)) i)) (CategoryTheory.Presieve.ofArrows.mk.{u3, u4, u2} C _inst_1 X ι Z g (Sigma.fst.{u2, u1} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u3, u4, u2} C _inst_1 X ι Z g i)) i)) (Sigma.snd.{u2, u1} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u3, u4, u2} C _inst_1 X ι Z g i)) i)) (fun (ij : Sigma.{u2, u1} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u3, u4, u2} C _inst_1 X ι Z g i))) => CategoryTheory.CategoryStruct.comp.{u3, u4} C (CategoryTheory.Category.toCategoryStruct.{u3, u4} C _inst_1) ((fun (i : Sigma.{u2, u1} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u3, u4, u2} C _inst_1 X ι Z g i))) => W (Z (Sigma.fst.{u2, u1} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u3, u4, u2} C _inst_1 X ι Z g i)) i)) (g (Sigma.fst.{u2, u1} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u3, u4, u2} C _inst_1 X ι Z g i)) i)) (CategoryTheory.Presieve.ofArrows.mk.{u3, u4, u2} C _inst_1 X ι Z g (Sigma.fst.{u2, u1} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u3, u4, u2} C _inst_1 X ι Z g i)) i)) (Sigma.snd.{u2, u1} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u3, u4, u2} C _inst_1 X ι Z g i)) i)) ij) (Z (Sigma.fst.{u2, u1} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u3, u4, u2} C _inst_1 X ι Z g i)) ij)) X (k (Z (Sigma.fst.{u2, u1} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u3, u4, u2} C _inst_1 X ι Z g i)) ij)) (g (Sigma.fst.{u2, u1} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u3, u4, u2} C _inst_1 X ι Z g i)) ij)) (CategoryTheory.Presieve.ofArrows.mk.{u3, u4, u2} C _inst_1 X ι Z g (Sigma.fst.{u2, u1} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u3, u4, u2} C _inst_1 X ι Z g i)) ij)) (Sigma.snd.{u2, u1} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u3, u4, u2} C _inst_1 X ι Z g i)) ij)) (g (Sigma.fst.{u2, u1} ι (fun (i : ι) => j (Z i) (g i) (CategoryTheory.Presieve.ofArrows.mk.{u3, u4, u2} C _inst_1 X ι Z g i)) ij))))
Case conversion may be inaccurate. Consider using '#align category_theory.presieve.of_arrows_bind CategoryTheory.Presieve.ofArrows_bindₓ'. -/
theorem ofArrows_bind {ι : Type _} (Z : ι → C) (g : ∀ i : ι, Z i ⟶ X)
    (j : ∀ ⦃Y⦄ (f : Y ⟶ X), ofArrows Z g f → Type _) (W : ∀ ⦃Y⦄ (f : Y ⟶ X) (H), j f H → C)
    (k : ∀ ⦃Y⦄ (f : Y ⟶ X) (H i), W f H i ⟶ Y) :
    ((ofArrows Z g).bind fun Y f H => ofArrows (W f H) (k f H)) =
      ofArrows (fun i : Σi, j _ (ofArrows.mk i) => W (g i.1) _ i.2) fun ij =>
        k (g ij.1) _ ij.2 ≫ g ij.1 :=
  by
  ext (Y f)
  constructor
  · rintro ⟨_, _, _, ⟨i⟩, ⟨i'⟩, rfl⟩
    exact of_arrows.mk (Sigma.mk _ _)
  · rintro ⟨i⟩
    exact bind_comp _ (of_arrows.mk _) (of_arrows.mk _)
#align category_theory.presieve.of_arrows_bind CategoryTheory.Presieve.ofArrows_bind

/- warning: category_theory.presieve.functor_pullback -> CategoryTheory.Presieve.functorPullback is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C}, (CategoryTheory.Presieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) -> (CategoryTheory.Presieve.{u1, u3} C _inst_1 X)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C}, (CategoryTheory.Presieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) -> (CategoryTheory.Presieve.{u1, u3} C _inst_1 X)
Case conversion may be inaccurate. Consider using '#align category_theory.presieve.functor_pullback CategoryTheory.Presieve.functorPullbackₓ'. -/
/-- Given a presieve on `F(X)`, we can define a presieve on `X` by taking the preimage via `F`. -/
def functorPullback (R : Presieve (F.obj X)) : Presieve X := fun _ f => R (F.map f)
#align category_theory.presieve.functor_pullback CategoryTheory.Presieve.functorPullback

/- warning: category_theory.presieve.functor_pullback_mem -> CategoryTheory.Presieve.functorPullback_mem is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} (R : CategoryTheory.Presieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) Y X), Iff (CategoryTheory.Presieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X R Y f) (R (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y X f))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} (R : CategoryTheory.Presieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) Y X), Iff (CategoryTheory.Presieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X R Y f) (R (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y X f))
Case conversion may be inaccurate. Consider using '#align category_theory.presieve.functor_pullback_mem CategoryTheory.Presieve.functorPullback_memₓ'. -/
@[simp]
theorem functorPullback_mem (R : Presieve (F.obj X)) {Y} (f : Y ⟶ X) :
    R.functorPullback F f ↔ R (F.map f) :=
  Iff.rfl
#align category_theory.presieve.functor_pullback_mem CategoryTheory.Presieve.functorPullback_mem

#print CategoryTheory.Presieve.functorPullback_id /-
@[simp]
theorem functorPullback_id (R : Presieve X) : R.functorPullback (𝟭 _) = R :=
  rfl
#align category_theory.presieve.functor_pullback_id CategoryTheory.Presieve.functorPullback_id
-/

section FunctorPushforward

variable {E : Type u₃} [Category.{v₃} E] (G : D ⥤ E)

/- warning: category_theory.presieve.functor_pushforward -> CategoryTheory.Presieve.functorPushforward is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C}, (CategoryTheory.Presieve.{u1, u3} C _inst_1 X) -> (CategoryTheory.Presieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C}, (CategoryTheory.Presieve.{u1, u3} C _inst_1 X) -> (CategoryTheory.Presieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X))
Case conversion may be inaccurate. Consider using '#align category_theory.presieve.functor_pushforward CategoryTheory.Presieve.functorPushforwardₓ'. -/
/-- Given a presieve on `X`, we can define a presieve on `F(X)` (which is actually a sieve)
by taking the sieve generated by the image via `F`.
-/
def functorPushforward (S : Presieve X) : Presieve (F.obj X) := fun Y f =>
  ∃ (Z : C)(g : Z ⟶ X)(h : Y ⟶ F.obj Z), S g ∧ f = h ≫ F.map g
#align category_theory.presieve.functor_pushforward CategoryTheory.Presieve.functorPushforward

/- warning: category_theory.presieve.functor_pushforward_structure -> CategoryTheory.Presieve.FunctorPushforwardStructure is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C}, (CategoryTheory.Presieve.{u1, u3} C _inst_1 X) -> (forall {Y : D}, (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) Y (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) -> Sort.{max (succ u3) (succ u1) (succ u2)})
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C}, (CategoryTheory.Presieve.{u1, u3} C _inst_1 X) -> (forall {Y : D}, (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) Y (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) -> Sort.{max (max (succ u3) (succ u1)) (succ u2)})
Case conversion may be inaccurate. Consider using '#align category_theory.presieve.functor_pushforward_structure CategoryTheory.Presieve.FunctorPushforwardStructureₓ'. -/
/-- An auxillary definition in order to fix the choice of the preimages between various definitions.
-/
@[nolint has_nonempty_instance]
structure FunctorPushforwardStructure (S : Presieve X) {Y} (f : Y ⟶ F.obj X) where
  preobj : C
  premap : preobj ⟶ X
  lift : Y ⟶ F.obj preobj
  cover : S premap
  fac : f = lift ≫ F.map premap
#align category_theory.presieve.functor_pushforward_structure CategoryTheory.Presieve.FunctorPushforwardStructure

/- warning: category_theory.presieve.get_functor_pushforward_structure -> CategoryTheory.Presieve.getFunctorPushforwardStructure is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] {X : C} {F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} {S : CategoryTheory.Presieve.{u1, u3} C _inst_1 X} {Y : D} {f : Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) Y (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)}, (CategoryTheory.Presieve.functorPushforward.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X S Y f) -> (CategoryTheory.Presieve.FunctorPushforwardStructure.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X S Y f)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] {X : C} {F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} {S : CategoryTheory.Presieve.{u1, u3} C _inst_1 X} {Y : D} {f : Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) Y (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)}, (CategoryTheory.Presieve.functorPushforward.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X S Y f) -> (CategoryTheory.Presieve.FunctorPushforwardStructure.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X S Y f)
Case conversion may be inaccurate. Consider using '#align category_theory.presieve.get_functor_pushforward_structure CategoryTheory.Presieve.getFunctorPushforwardStructureₓ'. -/
/-- The fixed choice of a preimage. -/
noncomputable def getFunctorPushforwardStructure {F : C ⥤ D} {S : Presieve X} {Y : D}
    {f : Y ⟶ F.obj X} (h : S.functorPushforward F f) : FunctorPushforwardStructure F S f :=
  by
  choose Z f' g h₁ h using h
  exact ⟨Z, f', g, h₁, h⟩
#align category_theory.presieve.get_functor_pushforward_structure CategoryTheory.Presieve.getFunctorPushforwardStructure

/- warning: category_theory.presieve.functor_pushforward_comp -> CategoryTheory.Presieve.functorPushforward_comp is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u4} C] {D : Type.{u5}} [_inst_2 : CategoryTheory.Category.{u2, u5} D] (F : CategoryTheory.Functor.{u1, u2, u4, u5} C _inst_1 D _inst_2) {X : C} {E : Type.{u6}} [_inst_3 : CategoryTheory.Category.{u3, u6} E] (G : CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_2 E _inst_3) (R : CategoryTheory.Presieve.{u1, u4} C _inst_1 X), Eq.{max (succ u6) (succ u3)} (CategoryTheory.Presieve.{u3, u6} E _inst_3 (CategoryTheory.Functor.obj.{u1, u3, u4, u6} C _inst_1 E _inst_3 (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F G) X)) (CategoryTheory.Presieve.functorPushforward.{u1, u3, u4, u6} C _inst_1 E _inst_3 (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F G) X R) (CategoryTheory.Presieve.functorPushforward.{u2, u3, u5, u6} D _inst_2 E _inst_3 G (CategoryTheory.Functor.obj.{u1, u2, u4, u5} C _inst_1 D _inst_2 F X) (CategoryTheory.Presieve.functorPushforward.{u1, u2, u4, u5} C _inst_1 D _inst_2 F X R))
but is expected to have type
  forall {C : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u4} C] {D : Type.{u5}} [_inst_2 : CategoryTheory.Category.{u2, u5} D] (F : CategoryTheory.Functor.{u1, u2, u4, u5} C _inst_1 D _inst_2) {X : C} {E : Type.{u6}} [_inst_3 : CategoryTheory.Category.{u3, u6} E] (G : CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_2 E _inst_3) (R : CategoryTheory.Presieve.{u1, u4} C _inst_1 X), Eq.{max (succ u6) (succ u3)} (CategoryTheory.Presieve.{u3, u6} E _inst_3 (Prefunctor.obj.{succ u1, succ u3, u4, u6} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u4, u6} C _inst_1 E _inst_3 (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F G)) X)) (CategoryTheory.Presieve.functorPushforward.{u1, u3, u4, u6} C _inst_1 E _inst_3 (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F G) X R) (CategoryTheory.Presieve.functorPushforward.{u2, u3, u5, u6} D _inst_2 E _inst_3 G (Prefunctor.obj.{succ u1, succ u2, u4, u5} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u4, u5} C _inst_1 D _inst_2 F) X) (CategoryTheory.Presieve.functorPushforward.{u1, u2, u4, u5} C _inst_1 D _inst_2 F X R))
Case conversion may be inaccurate. Consider using '#align category_theory.presieve.functor_pushforward_comp CategoryTheory.Presieve.functorPushforward_compₓ'. -/
theorem functorPushforward_comp (R : Presieve X) :
    R.functorPushforward (F ⋙ G) = (R.functorPushforward F).functorPushforward G :=
  by
  ext (x f)
  constructor
  · rintro ⟨X, f₁, g₁, h₁, rfl⟩
    exact ⟨F.obj X, F.map f₁, g₁, ⟨X, f₁, 𝟙 _, h₁, by simp⟩, rfl⟩
  · rintro ⟨X, f₁, g₁, ⟨X', f₂, g₂, h₁, rfl⟩, rfl⟩
    use ⟨X', f₂, g₁ ≫ G.map g₂, h₁, by simp⟩
#align category_theory.presieve.functor_pushforward_comp CategoryTheory.Presieve.functorPushforward_comp

/- warning: category_theory.presieve.image_mem_functor_pushforward -> CategoryTheory.Presieve.image_mem_functorPushforward is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (R : CategoryTheory.Presieve.{u1, u3} C _inst_1 X) {f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) Y X}, (R Y f) -> (CategoryTheory.Presieve.functorPushforward.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X R (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y X f))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (R : CategoryTheory.Presieve.{u1, u3} C _inst_1 X) {f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) Y X}, (R Y f) -> (CategoryTheory.Presieve.functorPushforward.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X R (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y X f))
Case conversion may be inaccurate. Consider using '#align category_theory.presieve.image_mem_functor_pushforward CategoryTheory.Presieve.image_mem_functorPushforwardₓ'. -/
theorem image_mem_functorPushforward (R : Presieve X) {f : Y ⟶ X} (h : R f) :
    R.functorPushforward F (F.map f) :=
  ⟨Y, f, 𝟙 _, h, by simp⟩
#align category_theory.presieve.image_mem_functor_pushforward CategoryTheory.Presieve.image_mem_functorPushforward

end FunctorPushforward

end Presieve

#print CategoryTheory.Sieve /-
/--
For an object `X` of a category `C`, a `sieve X` is a set of morphisms to `X` which is closed under
left-composition.
-/
structure Sieve {C : Type u₁} [Category.{v₁} C] (X : C) where
  arrows : Presieve X
  downward_closed' : ∀ {Y Z f} (hf : arrows f) (g : Z ⟶ Y), arrows (g ≫ f)
#align category_theory.sieve CategoryTheory.Sieve
-/

namespace Sieve

instance : CoeFun (Sieve X) fun _ => Presieve X :=
  ⟨Sieve.arrows⟩

initialize_simps_projections Sieve (arrows → apply)

variable {S R : Sieve X}

/- warning: category_theory.sieve.downward_closed -> CategoryTheory.Sieve.downward_closed is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} (S : CategoryTheory.Sieve.{u1, u2} C _inst_1 X) {f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X}, (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (fun (_x : CategoryTheory.Sieve.{u1, u2} C _inst_1 X) => CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.hasCoeToFun.{u1, u2} C _inst_1 X) S Y f) -> (forall (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Z Y), coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (fun (_x : CategoryTheory.Sieve.{u1, u2} C _inst_1 X) => CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.hasCoeToFun.{u1, u2} C _inst_1 X) S Z (CategoryTheory.CategoryStruct.comp.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Z Y X g f))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} (Y : CategoryTheory.Sieve.{u1, u2} C _inst_1 X) {Z : C} {S : C} {f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Z X}, (CategoryTheory.Sieve.arrows.{u1, u2} C _inst_1 X Y Z f) -> (forall (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) S Z), CategoryTheory.Sieve.arrows.{u1, u2} C _inst_1 X Y S (CategoryTheory.CategoryStruct.comp.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) S Z X g f))
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.downward_closed CategoryTheory.Sieve.downward_closedₓ'. -/
@[simp]
theorem downward_closed (S : Sieve X) {f : Y ⟶ X} (hf : S f) (g : Z ⟶ Y) : S (g ≫ f) :=
  S.downward_closed' hf g
#align category_theory.sieve.downward_closed CategoryTheory.Sieve.downward_closed

#print CategoryTheory.Sieve.arrows_ext /-
theorem arrows_ext : ∀ {R S : Sieve X}, R.arrows = S.arrows → R = S
  | ⟨Ra, _⟩, ⟨Sa, _⟩, rfl => rfl
#align category_theory.sieve.arrows_ext CategoryTheory.Sieve.arrows_ext
-/

#print CategoryTheory.Sieve.ext /-
@[ext]
protected theorem ext {R S : Sieve X} (h : ∀ ⦃Y⦄ (f : Y ⟶ X), R f ↔ S f) : R = S :=
  arrows_ext <| funext fun x => funext fun f => propext <| h f
#align category_theory.sieve.ext CategoryTheory.Sieve.ext
-/

#print CategoryTheory.Sieve.ext_iff /-
protected theorem ext_iff {R S : Sieve X} : R = S ↔ ∀ ⦃Y⦄ (f : Y ⟶ X), R f ↔ S f :=
  ⟨fun h Y f => h ▸ Iff.rfl, Sieve.ext⟩
#align category_theory.sieve.ext_iff CategoryTheory.Sieve.ext_iff
-/

open Lattice

#print CategoryTheory.Sieve.sup /-
/-- The supremum of a collection of sieves: the union of them all. -/
protected def sup (𝒮 : Set (Sieve X)) : Sieve X
    where
  arrows Y := { f | ∃ S ∈ 𝒮, Sieve.arrows S f }
  downward_closed' Y Z f := by
    rintro ⟨S, hS, hf⟩ g
    exact ⟨S, hS, S.downward_closed hf _⟩
#align category_theory.sieve.Sup CategoryTheory.Sieve.sup
-/

#print CategoryTheory.Sieve.inf /-
/-- The infimum of a collection of sieves: the intersection of them all. -/
protected def inf (𝒮 : Set (Sieve X)) : Sieve X
    where
  arrows Y := { f | ∀ S ∈ 𝒮, Sieve.arrows S f }
  downward_closed' Y Z f hf g S H := S.downward_closed (hf S H) g
#align category_theory.sieve.Inf CategoryTheory.Sieve.inf
-/

#print CategoryTheory.Sieve.union /-
/-- The union of two sieves is a sieve. -/
protected def union (S R : Sieve X) : Sieve X
    where
  arrows Y f := S f ∨ R f
  downward_closed' := by rintro Y Z f (h | h) g <;> simp [h]
#align category_theory.sieve.union CategoryTheory.Sieve.union
-/

#print CategoryTheory.Sieve.inter /-
/-- The intersection of two sieves is a sieve. -/
protected def inter (S R : Sieve X) : Sieve X
    where
  arrows Y f := S f ∧ R f
  downward_closed' := by
    rintro Y Z f ⟨h₁, h₂⟩ g
    simp [h₁, h₂]
#align category_theory.sieve.inter CategoryTheory.Sieve.inter
-/

/-- Sieves on an object `X` form a complete lattice.
We generate this directly rather than using the galois insertion for nicer definitional properties.
-/
instance : CompleteLattice (Sieve X)
    where
  le S R := ∀ ⦃Y⦄ (f : Y ⟶ X), S f → R f
  le_refl S f q := id
  le_trans S₁ S₂ S₃ S₁₂ S₂₃ Y f h := S₂₃ _ (S₁₂ _ h)
  le_antisymm S R p q := Sieve.ext fun Y f => ⟨p _, q _⟩
  top :=
    { arrows := fun _ => Set.univ
      downward_closed' := fun Y Z f g h => ⟨⟩ }
  bot :=
    { arrows := fun _ => ∅
      downward_closed' := fun _ _ _ p _ => False.elim p }
  sup := Sieve.union
  inf := Sieve.inter
  sSup := Sieve.sup
  sInf := Sieve.inf
  le_sup 𝒮 S hS Y f hf := ⟨S, hS, hf⟩
  sup_le ℰ S hS Y f := by
    rintro ⟨R, hR, hf⟩
    apply hS R hR _ hf
  inf_le _ _ hS _ _ h := h _ hS
  le_inf _ _ hS _ _ hf _ hR := hS _ hR _ hf
  le_sup_left _ _ _ _ := Or.inl
  le_sup_right _ _ _ _ := Or.inr
  sup_le _ _ _ a b _ _ hf := hf.elim (a _) (b _)
  inf_le_left _ _ _ _ := And.left
  inf_le_right _ _ _ _ := And.right
  le_inf _ _ _ p q _ _ z := ⟨p _ z, q _ z⟩
  le_top _ _ _ _ := trivial
  bot_le _ _ _ := False.elim

#print CategoryTheory.Sieve.sieveInhabited /-
/-- The maximal sieve always exists. -/
instance sieveInhabited : Inhabited (Sieve X) :=
  ⟨⊤⟩
#align category_theory.sieve.sieve_inhabited CategoryTheory.Sieve.sieveInhabited
-/

/- warning: category_theory.sieve.Inf_apply -> CategoryTheory.Sieve.sInf_apply is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Ss : Set.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X)} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X), Iff (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (fun (_x : CategoryTheory.Sieve.{u1, u2} C _inst_1 X) => CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.hasCoeToFun.{u1, u2} C _inst_1 X) (InfSet.sInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteSemilatticeInf.toHasInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 X))) Ss) Y f) (forall (S : CategoryTheory.Sieve.{u1, u2} C _inst_1 X), (Membership.Mem.{max u2 u1, max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (Set.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X)) (Set.hasMem.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X)) S Ss) -> (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (fun (_x : CategoryTheory.Sieve.{u1, u2} C _inst_1 X) => CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.hasCoeToFun.{u1, u2} C _inst_1 X) S Y f))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Ss : Set.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X)} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X), Iff (CategoryTheory.Sieve.arrows.{u1, u2} C _inst_1 X (InfSet.sInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toInfSet.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 X)) Ss) Y f) (forall (S : CategoryTheory.Sieve.{u1, u2} C _inst_1 X), (Membership.mem.{max u2 u1, max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (Set.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X)) (Set.instMembershipSet.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X)) S Ss) -> (CategoryTheory.Sieve.arrows.{u1, u2} C _inst_1 X S Y f))
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.Inf_apply CategoryTheory.Sieve.sInf_applyₓ'. -/
@[simp]
theorem sInf_apply {Ss : Set (Sieve X)} {Y} (f : Y ⟶ X) :
    sInf Ss f ↔ ∀ (S : Sieve X) (H : S ∈ Ss), S f :=
  Iff.rfl
#align category_theory.sieve.Inf_apply CategoryTheory.Sieve.sInf_apply

/- warning: category_theory.sieve.Sup_apply -> CategoryTheory.Sieve.sSup_apply is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Ss : Set.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X)} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X), Iff (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (fun (_x : CategoryTheory.Sieve.{u1, u2} C _inst_1 X) => CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.hasCoeToFun.{u1, u2} C _inst_1 X) (SupSet.sSup.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteSemilatticeSup.toHasSup.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeSup.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 X))) Ss) Y f) (Exists.{max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (fun (S : CategoryTheory.Sieve.{u1, u2} C _inst_1 X) => Exists.{0} (Membership.Mem.{max u2 u1, max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (Set.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X)) (Set.hasMem.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X)) S Ss) (fun (H : Membership.Mem.{max u2 u1, max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (Set.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X)) (Set.hasMem.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X)) S Ss) => coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (fun (_x : CategoryTheory.Sieve.{u1, u2} C _inst_1 X) => CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.hasCoeToFun.{u1, u2} C _inst_1 X) S Y f)))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Ss : Set.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X)} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X), Iff (CategoryTheory.Sieve.arrows.{u1, u2} C _inst_1 X (SupSet.sSup.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toSupSet.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 X)) Ss) Y f) (Exists.{max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (fun (S : CategoryTheory.Sieve.{u1, u2} C _inst_1 X) => Exists.{0} (Membership.mem.{max u2 u1, max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (Set.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X)) (Set.instMembershipSet.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X)) S Ss) (fun (H : Membership.mem.{max u2 u1, max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (Set.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X)) (Set.instMembershipSet.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X)) S Ss) => CategoryTheory.Sieve.arrows.{u1, u2} C _inst_1 X S Y f)))
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.Sup_apply CategoryTheory.Sieve.sSup_applyₓ'. -/
@[simp]
theorem sSup_apply {Ss : Set (Sieve X)} {Y} (f : Y ⟶ X) :
    sSup Ss f ↔ ∃ (S : Sieve X)(H : S ∈ Ss), S f :=
  Iff.rfl
#align category_theory.sieve.Sup_apply CategoryTheory.Sieve.sSup_apply

/- warning: category_theory.sieve.inter_apply -> CategoryTheory.Sieve.inter_apply is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {R : CategoryTheory.Sieve.{u1, u2} C _inst_1 X} {S : CategoryTheory.Sieve.{u1, u2} C _inst_1 X} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X), Iff (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (fun (_x : CategoryTheory.Sieve.{u1, u2} C _inst_1 X) => CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.hasCoeToFun.{u1, u2} C _inst_1 X) (Inf.inf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (SemilatticeInf.toHasInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (Lattice.toSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toLattice.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 X)))) R S) Y f) (And (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (fun (_x : CategoryTheory.Sieve.{u1, u2} C _inst_1 X) => CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.hasCoeToFun.{u1, u2} C _inst_1 X) R Y f) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (fun (_x : CategoryTheory.Sieve.{u1, u2} C _inst_1 X) => CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.hasCoeToFun.{u1, u2} C _inst_1 X) S Y f))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {R : CategoryTheory.Sieve.{u1, u2} C _inst_1 X} {S : CategoryTheory.Sieve.{u1, u2} C _inst_1 X} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X), Iff (CategoryTheory.Sieve.arrows.{u1, u2} C _inst_1 X (Inf.inf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (Lattice.toInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toLattice.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 X))) R S) Y f) (And (CategoryTheory.Sieve.arrows.{u1, u2} C _inst_1 X R Y f) (CategoryTheory.Sieve.arrows.{u1, u2} C _inst_1 X S Y f))
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.inter_apply CategoryTheory.Sieve.inter_applyₓ'. -/
@[simp]
theorem inter_apply {R S : Sieve X} {Y} (f : Y ⟶ X) : (R ⊓ S) f ↔ R f ∧ S f :=
  Iff.rfl
#align category_theory.sieve.inter_apply CategoryTheory.Sieve.inter_apply

/- warning: category_theory.sieve.union_apply -> CategoryTheory.Sieve.union_apply is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {R : CategoryTheory.Sieve.{u1, u2} C _inst_1 X} {S : CategoryTheory.Sieve.{u1, u2} C _inst_1 X} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X), Iff (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (fun (_x : CategoryTheory.Sieve.{u1, u2} C _inst_1 X) => CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.hasCoeToFun.{u1, u2} C _inst_1 X) (Sup.sup.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (SemilatticeSup.toHasSup.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (Lattice.toSemilatticeSup.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toLattice.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 X)))) R S) Y f) (Or (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (fun (_x : CategoryTheory.Sieve.{u1, u2} C _inst_1 X) => CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.hasCoeToFun.{u1, u2} C _inst_1 X) R Y f) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (fun (_x : CategoryTheory.Sieve.{u1, u2} C _inst_1 X) => CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.hasCoeToFun.{u1, u2} C _inst_1 X) S Y f))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {R : CategoryTheory.Sieve.{u1, u2} C _inst_1 X} {S : CategoryTheory.Sieve.{u1, u2} C _inst_1 X} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X), Iff (CategoryTheory.Sieve.arrows.{u1, u2} C _inst_1 X (Sup.sup.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (SemilatticeSup.toSup.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (Lattice.toSemilatticeSup.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toLattice.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 X)))) R S) Y f) (Or (CategoryTheory.Sieve.arrows.{u1, u2} C _inst_1 X R Y f) (CategoryTheory.Sieve.arrows.{u1, u2} C _inst_1 X S Y f))
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.union_apply CategoryTheory.Sieve.union_applyₓ'. -/
@[simp]
theorem union_apply {R S : Sieve X} {Y} (f : Y ⟶ X) : (R ⊔ S) f ↔ R f ∨ S f :=
  Iff.rfl
#align category_theory.sieve.union_apply CategoryTheory.Sieve.union_apply

/- warning: category_theory.sieve.top_apply -> CategoryTheory.Sieve.top_apply is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X), coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (fun (_x : CategoryTheory.Sieve.{u1, u2} C _inst_1 X) => CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.hasCoeToFun.{u1, u2} C _inst_1 X) (Top.top.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toHasTop.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 X))) Y f
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X), CategoryTheory.Sieve.arrows.{u1, u2} C _inst_1 X (Top.top.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toTop.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 X))) Y f
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.top_apply CategoryTheory.Sieve.top_applyₓ'. -/
@[simp]
theorem top_apply (f : Y ⟶ X) : (⊤ : Sieve X) f :=
  trivial
#align category_theory.sieve.top_apply CategoryTheory.Sieve.top_apply

#print CategoryTheory.Sieve.generate /-
/-- Generate the smallest sieve containing the given set of arrows. -/
@[simps]
def generate (R : Presieve X) : Sieve X
    where
  arrows Z f := ∃ (Y : _)(h : Z ⟶ Y)(g : Y ⟶ X), R g ∧ h ≫ g = f
  downward_closed' := by
    rintro Y Z _ ⟨W, g, f, hf, rfl⟩ h
    exact ⟨_, h ≫ g, _, hf, by simp⟩
#align category_theory.sieve.generate CategoryTheory.Sieve.generate
-/

#print CategoryTheory.Sieve.bind /-
/-- Given a presieve on `X`, and a sieve on each domain of an arrow in the presieve, we can bind to
produce a sieve on `X`.
-/
@[simps]
def bind (S : Presieve X) (R : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → Sieve Y) : Sieve X
    where
  arrows := S.bind fun Y f h => R h
  downward_closed' := by
    rintro Y Z f ⟨W, f, h, hh, hf, rfl⟩ g
    exact ⟨_, g ≫ f, _, hh, by simp [hf]⟩
#align category_theory.sieve.bind CategoryTheory.Sieve.bind
-/

open Order Lattice

/- warning: category_theory.sieve.sets_iff_generate -> CategoryTheory.Sieve.sets_iff_generate is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} (R : CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (S : CategoryTheory.Sieve.{u1, u2} C _inst_1 X), Iff (LE.le.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (Preorder.toLE.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 X))))) (CategoryTheory.Sieve.generate.{u1, u2} C _inst_1 X R) S) (LE.le.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (Preorder.toLE.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CategoryTheory.Presieve.completeLattice.{u2, u1} C _inst_1 X))))) R (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (fun (_x : CategoryTheory.Sieve.{u1, u2} C _inst_1 X) => CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.hasCoeToFun.{u1, u2} C _inst_1 X) S))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} (R : CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (S : CategoryTheory.Sieve.{u1, u2} C _inst_1 X), Iff (LE.le.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (Preorder.toLE.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 X))))) (CategoryTheory.Sieve.generate.{u1, u2} C _inst_1 X R) S) (LE.le.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (Preorder.toLE.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CategoryTheory.instCompleteLatticePresieve.{u1, u2} C _inst_1 X))))) R (CategoryTheory.Sieve.arrows.{u1, u2} C _inst_1 X S))
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.sets_iff_generate CategoryTheory.Sieve.sets_iff_generateₓ'. -/
theorem sets_iff_generate (R : Presieve X) (S : Sieve X) : generate R ≤ S ↔ R ≤ S :=
  ⟨fun H Y g hg => H _ ⟨_, 𝟙 _, _, hg, id_comp _⟩, fun ss Y f =>
    by
    rintro ⟨Z, f, g, hg, rfl⟩
    exact S.downward_closed (ss Z hg) f⟩
#align category_theory.sieve.sets_iff_generate CategoryTheory.Sieve.sets_iff_generate

/- warning: category_theory.sieve.gi_generate -> CategoryTheory.Sieve.giGenerate is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C}, GaloisInsertion.{max u2 u1, max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CategoryTheory.Presieve.completeLattice.{u2, u1} C _inst_1 X)))) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 X)))) (CategoryTheory.Sieve.generate.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.arrows.{u1, u2} C _inst_1 X)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C}, GaloisInsertion.{max u2 u1, max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CategoryTheory.instCompleteLatticePresieve.{u1, u2} C _inst_1 X)))) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 X)))) (CategoryTheory.Sieve.generate.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.arrows.{u1, u2} C _inst_1 X)
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.gi_generate CategoryTheory.Sieve.giGenerateₓ'. -/
/-- Show that there is a galois insertion (generate, set_over). -/
def giGenerate : GaloisInsertion (generate : Presieve X → Sieve X) arrows
    where
  gc := sets_iff_generate
  choice 𝒢 _ := generate 𝒢
  choice_eq _ _ := rfl
  le_l_u S Y f hf := ⟨_, 𝟙 _, _, hf, id_comp _⟩
#align category_theory.sieve.gi_generate CategoryTheory.Sieve.giGenerate

/- warning: category_theory.sieve.le_generate -> CategoryTheory.Sieve.le_generate is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} (R : CategoryTheory.Presieve.{u1, u2} C _inst_1 X), LE.le.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (Preorder.toLE.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CategoryTheory.Presieve.completeLattice.{u2, u1} C _inst_1 X))))) R (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (fun (_x : CategoryTheory.Sieve.{u1, u2} C _inst_1 X) => CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.hasCoeToFun.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.generate.{u1, u2} C _inst_1 X R))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} (R : CategoryTheory.Presieve.{u1, u2} C _inst_1 X), LE.le.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (Preorder.toLE.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CategoryTheory.instCompleteLatticePresieve.{u1, u2} C _inst_1 X))))) R (CategoryTheory.Sieve.arrows.{u1, u2} C _inst_1 X (CategoryTheory.Sieve.generate.{u1, u2} C _inst_1 X R))
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.le_generate CategoryTheory.Sieve.le_generateₓ'. -/
theorem le_generate (R : Presieve X) : R ≤ generate R :=
  giGenerate.gc.le_u_l R
#align category_theory.sieve.le_generate CategoryTheory.Sieve.le_generate

#print CategoryTheory.Sieve.generate_sieve /-
@[simp]
theorem generate_sieve (S : Sieve X) : generate S = S :=
  giGenerate.l_u_eq S
#align category_theory.sieve.generate_sieve CategoryTheory.Sieve.generate_sieve
-/

/- warning: category_theory.sieve.id_mem_iff_eq_top -> CategoryTheory.Sieve.id_mem_iff_eq_top is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {S : CategoryTheory.Sieve.{u1, u2} C _inst_1 X}, Iff (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (fun (_x : CategoryTheory.Sieve.{u1, u2} C _inst_1 X) => CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.hasCoeToFun.{u1, u2} C _inst_1 X) S X (CategoryTheory.CategoryStruct.id.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X)) (Eq.{max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) S (Top.top.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toHasTop.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 X))))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {S : CategoryTheory.Sieve.{u1, u2} C _inst_1 X}, Iff (CategoryTheory.Sieve.arrows.{u1, u2} C _inst_1 X S X (CategoryTheory.CategoryStruct.id.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X)) (Eq.{max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) S (Top.top.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toTop.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 X))))
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.id_mem_iff_eq_top CategoryTheory.Sieve.id_mem_iff_eq_topₓ'. -/
/-- If the identity arrow is in a sieve, the sieve is maximal. -/
theorem id_mem_iff_eq_top : S (𝟙 X) ↔ S = ⊤ :=
  ⟨fun h => top_unique fun Y f _ => by simpa using downward_closed _ h f, fun h => h.symm ▸ trivial⟩
#align category_theory.sieve.id_mem_iff_eq_top CategoryTheory.Sieve.id_mem_iff_eq_top

/- warning: category_theory.sieve.generate_of_contains_is_split_epi -> CategoryTheory.Sieve.generate_of_contains_isSplitEpi is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {R : CategoryTheory.Presieve.{u1, u2} C _inst_1 X} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X) [_inst_3 : CategoryTheory.IsSplitEpi.{u1, u2} C _inst_1 Y X f], (R Y f) -> (Eq.{max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.generate.{u1, u2} C _inst_1 X R) (Top.top.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toHasTop.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 X))))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {R : CategoryTheory.Presieve.{u1, u2} C _inst_1 X} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X) [_inst_3 : CategoryTheory.IsSplitEpi.{u1, u2} C _inst_1 Y X f], (R Y f) -> (Eq.{max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.generate.{u1, u2} C _inst_1 X R) (Top.top.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toTop.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 X))))
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.generate_of_contains_is_split_epi CategoryTheory.Sieve.generate_of_contains_isSplitEpiₓ'. -/
/-- If an arrow set contains a split epi, it generates the maximal sieve. -/
theorem generate_of_contains_isSplitEpi {R : Presieve X} (f : Y ⟶ X) [IsSplitEpi f] (hf : R f) :
    generate R = ⊤ := by
  rw [← id_mem_iff_eq_top]
  exact ⟨_, section_ f, f, hf, by simp⟩
#align category_theory.sieve.generate_of_contains_is_split_epi CategoryTheory.Sieve.generate_of_contains_isSplitEpi

/- warning: category_theory.sieve.generate_of_singleton_is_split_epi -> CategoryTheory.Sieve.generate_of_singleton_isSplitEpi is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X) [_inst_3 : CategoryTheory.IsSplitEpi.{u1, u2} C _inst_1 Y X f], Eq.{max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.generate.{u1, u2} C _inst_1 X (CategoryTheory.Presieve.singletonₓ.{u1, u2} C _inst_1 X Y f)) (Top.top.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toHasTop.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 X)))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X) [_inst_3 : CategoryTheory.IsSplitEpi.{u1, u2} C _inst_1 Y X f], Eq.{max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.generate.{u1, u2} C _inst_1 X (CategoryTheory.Presieve.singleton.{u1, u2} C _inst_1 X Y f)) (Top.top.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toTop.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 X)))
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.generate_of_singleton_is_split_epi CategoryTheory.Sieve.generate_of_singleton_isSplitEpiₓ'. -/
@[simp]
theorem generate_of_singleton_isSplitEpi (f : Y ⟶ X) [IsSplitEpi f] :
    generate (Presieve.singleton f) = ⊤ :=
  generate_of_contains_isSplitEpi f (Presieve.singleton_self _)
#align category_theory.sieve.generate_of_singleton_is_split_epi CategoryTheory.Sieve.generate_of_singleton_isSplitEpi

/- warning: category_theory.sieve.generate_top -> CategoryTheory.Sieve.generate_top is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C}, Eq.{max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.generate.{u1, u2} C _inst_1 X (Top.top.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CompleteLattice.toHasTop.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CategoryTheory.Presieve.completeLattice.{u2, u1} C _inst_1 X)))) (Top.top.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toHasTop.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 X)))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C}, Eq.{max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.generate.{u1, u2} C _inst_1 X (Top.top.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CompleteLattice.toTop.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CategoryTheory.instCompleteLatticePresieve.{u1, u2} C _inst_1 X)))) (Top.top.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toTop.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 X)))
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.generate_top CategoryTheory.Sieve.generate_topₓ'. -/
@[simp]
theorem generate_top : generate (⊤ : Presieve X) = ⊤ :=
  generate_of_contains_isSplitEpi (𝟙 _) ⟨⟩
#align category_theory.sieve.generate_top CategoryTheory.Sieve.generate_top

#print CategoryTheory.Sieve.pullback /-
/-- Given a morphism `h : Y ⟶ X`, send a sieve S on X to a sieve on Y
    as the inverse image of S with `_ ≫ h`.
    That is, `sieve.pullback S h := (≫ h) '⁻¹ S`. -/
@[simps]
def pullback (h : Y ⟶ X) (S : Sieve X) : Sieve Y
    where
  arrows Y sl := S (sl ≫ h)
  downward_closed' Z W f g h := by simp [g]
#align category_theory.sieve.pullback CategoryTheory.Sieve.pullback
-/

#print CategoryTheory.Sieve.pullback_id /-
@[simp]
theorem pullback_id : S.pullback (𝟙 _) = S := by simp [sieve.ext_iff]
#align category_theory.sieve.pullback_id CategoryTheory.Sieve.pullback_id
-/

/- warning: category_theory.sieve.pullback_top -> CategoryTheory.Sieve.pullback_top is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X}, Eq.{max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.pullback.{u1, u2} C _inst_1 X Y f (Top.top.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toHasTop.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 X)))) (Top.top.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteLattice.toHasTop.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 Y)))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X}, Eq.{max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.pullback.{u1, u2} C _inst_1 X Y f (Top.top.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toTop.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 X)))) (Top.top.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteLattice.toTop.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 Y)))
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.pullback_top CategoryTheory.Sieve.pullback_topₓ'. -/
@[simp]
theorem pullback_top {f : Y ⟶ X} : (⊤ : Sieve X).pullback f = ⊤ :=
  top_unique fun _ g => id
#align category_theory.sieve.pullback_top CategoryTheory.Sieve.pullback_top

#print CategoryTheory.Sieve.pullback_comp /-
theorem pullback_comp {f : Y ⟶ X} {g : Z ⟶ Y} (S : Sieve X) :
    S.pullback (g ≫ f) = (S.pullback f).pullback g := by simp [sieve.ext_iff]
#align category_theory.sieve.pullback_comp CategoryTheory.Sieve.pullback_comp
-/

/- warning: category_theory.sieve.pullback_inter -> CategoryTheory.Sieve.pullback_inter is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X} (S : CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (R : CategoryTheory.Sieve.{u1, u2} C _inst_1 X), Eq.{max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.pullback.{u1, u2} C _inst_1 X Y f (Inf.inf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (SemilatticeInf.toHasInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (Lattice.toSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toLattice.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 X)))) S R)) (Inf.inf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (SemilatticeInf.toHasInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (Lattice.toSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteLattice.toLattice.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 Y)))) (CategoryTheory.Sieve.pullback.{u1, u2} C _inst_1 X Y f S) (CategoryTheory.Sieve.pullback.{u1, u2} C _inst_1 X Y f R))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X} (S : CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (R : CategoryTheory.Sieve.{u1, u2} C _inst_1 X), Eq.{max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.pullback.{u1, u2} C _inst_1 X Y f (Inf.inf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (Lattice.toInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toLattice.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 X))) S R)) (Inf.inf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (Lattice.toInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteLattice.toLattice.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 Y))) (CategoryTheory.Sieve.pullback.{u1, u2} C _inst_1 X Y f S) (CategoryTheory.Sieve.pullback.{u1, u2} C _inst_1 X Y f R))
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.pullback_inter CategoryTheory.Sieve.pullback_interₓ'. -/
@[simp]
theorem pullback_inter {f : Y ⟶ X} (S R : Sieve X) :
    (S ⊓ R).pullback f = S.pullback f ⊓ R.pullback f := by simp [sieve.ext_iff]
#align category_theory.sieve.pullback_inter CategoryTheory.Sieve.pullback_inter

/- warning: category_theory.sieve.pullback_eq_top_iff_mem -> CategoryTheory.Sieve.pullback_eq_top_iff_mem is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {S : CategoryTheory.Sieve.{u1, u2} C _inst_1 X} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X), Iff (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (fun (_x : CategoryTheory.Sieve.{u1, u2} C _inst_1 X) => CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.hasCoeToFun.{u1, u2} C _inst_1 X) S Y f) (Eq.{max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.pullback.{u1, u2} C _inst_1 X Y f S) (Top.top.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteLattice.toHasTop.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 Y))))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {S : CategoryTheory.Sieve.{u1, u2} C _inst_1 X} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X), Iff (CategoryTheory.Sieve.arrows.{u1, u2} C _inst_1 X S Y f) (Eq.{max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.pullback.{u1, u2} C _inst_1 X Y f S) (Top.top.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteLattice.toTop.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 Y))))
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.pullback_eq_top_iff_mem CategoryTheory.Sieve.pullback_eq_top_iff_memₓ'. -/
theorem pullback_eq_top_iff_mem (f : Y ⟶ X) : S f ↔ S.pullback f = ⊤ := by
  rw [← id_mem_iff_eq_top, pullback_apply, id_comp]
#align category_theory.sieve.pullback_eq_top_iff_mem CategoryTheory.Sieve.pullback_eq_top_iff_mem

/- warning: category_theory.sieve.pullback_eq_top_of_mem -> CategoryTheory.Sieve.pullback_eq_top_of_mem is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (S : CategoryTheory.Sieve.{u1, u2} C _inst_1 X) {f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X}, (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (fun (_x : CategoryTheory.Sieve.{u1, u2} C _inst_1 X) => CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.hasCoeToFun.{u1, u2} C _inst_1 X) S Y f) -> (Eq.{max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.pullback.{u1, u2} C _inst_1 X Y f S) (Top.top.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteLattice.toHasTop.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 Y))))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (S : CategoryTheory.Sieve.{u1, u2} C _inst_1 X) {f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X}, (CategoryTheory.Sieve.arrows.{u1, u2} C _inst_1 X S Y f) -> (Eq.{max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.pullback.{u1, u2} C _inst_1 X Y f S) (Top.top.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteLattice.toTop.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 Y))))
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.pullback_eq_top_of_mem CategoryTheory.Sieve.pullback_eq_top_of_memₓ'. -/
theorem pullback_eq_top_of_mem (S : Sieve X) {f : Y ⟶ X} : S f → S.pullback f = ⊤ :=
  (pullback_eq_top_iff_mem f).1
#align category_theory.sieve.pullback_eq_top_of_mem CategoryTheory.Sieve.pullback_eq_top_of_mem

#print CategoryTheory.Sieve.pushforward /-
/-- Push a sieve `R` on `Y` forward along an arrow `f : Y ⟶ X`: `gf : Z ⟶ X` is in the sieve if `gf`
factors through some `g : Z ⟶ Y` which is in `R`.
-/
@[simps]
def pushforward (f : Y ⟶ X) (R : Sieve Y) : Sieve X
    where
  arrows Z gf := ∃ g, g ≫ f = gf ∧ R g
  downward_closed' := fun Z₁ Z₂ g ⟨j, k, z⟩ h => ⟨h ≫ j, by simp [k], by simp [z]⟩
#align category_theory.sieve.pushforward CategoryTheory.Sieve.pushforward
-/

#print CategoryTheory.Sieve.pushforward_apply_comp /-
theorem pushforward_apply_comp {R : Sieve Y} {Z : C} {g : Z ⟶ Y} (hg : R g) (f : Y ⟶ X) :
    R.pushforward f (g ≫ f) :=
  ⟨g, rfl, hg⟩
#align category_theory.sieve.pushforward_apply_comp CategoryTheory.Sieve.pushforward_apply_comp
-/

#print CategoryTheory.Sieve.pushforward_comp /-
theorem pushforward_comp {f : Y ⟶ X} {g : Z ⟶ Y} (R : Sieve Z) :
    R.pushforward (g ≫ f) = (R.pushforward g).pushforward f :=
  Sieve.ext fun W h =>
    ⟨fun ⟨f₁, hq, hf₁⟩ => ⟨f₁ ≫ g, by simpa, f₁, rfl, hf₁⟩, fun ⟨y, hy, z, hR, hz⟩ =>
      ⟨z, by rwa [reassoc_of hR], hz⟩⟩
#align category_theory.sieve.pushforward_comp CategoryTheory.Sieve.pushforward_comp
-/

/- warning: category_theory.sieve.galois_connection -> CategoryTheory.Sieve.galoisConnection is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X), GaloisConnection.{max u2 u1, max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 Y)))) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 X)))) (CategoryTheory.Sieve.pushforward.{u1, u2} C _inst_1 X Y f) (CategoryTheory.Sieve.pullback.{u1, u2} C _inst_1 X Y f)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X), GaloisConnection.{max u2 u1, max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 Y)))) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 X)))) (CategoryTheory.Sieve.pushforward.{u1, u2} C _inst_1 X Y f) (CategoryTheory.Sieve.pullback.{u1, u2} C _inst_1 X Y f)
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.galois_connection CategoryTheory.Sieve.galoisConnectionₓ'. -/
theorem galoisConnection (f : Y ⟶ X) : GaloisConnection (Sieve.pushforward f) (Sieve.pullback f) :=
  fun S R => ⟨fun hR Z g hg => hR _ ⟨g, rfl, hg⟩, fun hS Z g ⟨h, hg, hh⟩ => hg ▸ hS h hh⟩
#align category_theory.sieve.galois_connection CategoryTheory.Sieve.galoisConnection

/- warning: category_theory.sieve.pullback_monotone -> CategoryTheory.Sieve.pullback_monotone is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X), Monotone.{max u2 u1, max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 X)))) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 Y)))) (CategoryTheory.Sieve.pullback.{u1, u2} C _inst_1 X Y f)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X), Monotone.{max u2 u1, max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 X)))) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 Y)))) (CategoryTheory.Sieve.pullback.{u1, u2} C _inst_1 X Y f)
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.pullback_monotone CategoryTheory.Sieve.pullback_monotoneₓ'. -/
theorem pullback_monotone (f : Y ⟶ X) : Monotone (Sieve.pullback f) :=
  (galoisConnection f).monotone_u
#align category_theory.sieve.pullback_monotone CategoryTheory.Sieve.pullback_monotone

/- warning: category_theory.sieve.pushforward_monotone -> CategoryTheory.Sieve.pushforward_monotone is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X), Monotone.{max u2 u1, max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 Y)))) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 X)))) (CategoryTheory.Sieve.pushforward.{u1, u2} C _inst_1 X Y f)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X), Monotone.{max u2 u1, max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 Y)))) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 X)))) (CategoryTheory.Sieve.pushforward.{u1, u2} C _inst_1 X Y f)
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.pushforward_monotone CategoryTheory.Sieve.pushforward_monotoneₓ'. -/
theorem pushforward_monotone (f : Y ⟶ X) : Monotone (Sieve.pushforward f) :=
  (galoisConnection f).monotone_l
#align category_theory.sieve.pushforward_monotone CategoryTheory.Sieve.pushforward_monotone

/- warning: category_theory.sieve.le_pushforward_pullback -> CategoryTheory.Sieve.le_pushforward_pullback is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X) (R : CategoryTheory.Sieve.{u1, u2} C _inst_1 Y), LE.le.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (Preorder.toLE.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 Y))))) R (CategoryTheory.Sieve.pullback.{u1, u2} C _inst_1 X Y f (CategoryTheory.Sieve.pushforward.{u1, u2} C _inst_1 X Y f R))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X) (R : CategoryTheory.Sieve.{u1, u2} C _inst_1 Y), LE.le.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (Preorder.toLE.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 Y))))) R (CategoryTheory.Sieve.pullback.{u1, u2} C _inst_1 X Y f (CategoryTheory.Sieve.pushforward.{u1, u2} C _inst_1 X Y f R))
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.le_pushforward_pullback CategoryTheory.Sieve.le_pushforward_pullbackₓ'. -/
theorem le_pushforward_pullback (f : Y ⟶ X) (R : Sieve Y) : R ≤ (R.pushforward f).pullback f :=
  (galoisConnection f).le_u_l _
#align category_theory.sieve.le_pushforward_pullback CategoryTheory.Sieve.le_pushforward_pullback

/- warning: category_theory.sieve.pullback_pushforward_le -> CategoryTheory.Sieve.pullback_pushforward_le is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X) (R : CategoryTheory.Sieve.{u1, u2} C _inst_1 X), LE.le.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (Preorder.toLE.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 X))))) (CategoryTheory.Sieve.pushforward.{u1, u2} C _inst_1 X Y f (CategoryTheory.Sieve.pullback.{u1, u2} C _inst_1 X Y f R)) R
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X) (R : CategoryTheory.Sieve.{u1, u2} C _inst_1 X), LE.le.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (Preorder.toLE.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 X))))) (CategoryTheory.Sieve.pushforward.{u1, u2} C _inst_1 X Y f (CategoryTheory.Sieve.pullback.{u1, u2} C _inst_1 X Y f R)) R
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.pullback_pushforward_le CategoryTheory.Sieve.pullback_pushforward_leₓ'. -/
theorem pullback_pushforward_le (f : Y ⟶ X) (R : Sieve X) : (R.pullback f).pushforward f ≤ R :=
  (galoisConnection f).l_u_le _
#align category_theory.sieve.pullback_pushforward_le CategoryTheory.Sieve.pullback_pushforward_le

/- warning: category_theory.sieve.pushforward_union -> CategoryTheory.Sieve.pushforward_union is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X} (S : CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (R : CategoryTheory.Sieve.{u1, u2} C _inst_1 Y), Eq.{max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.pushforward.{u1, u2} C _inst_1 X Y f (Sup.sup.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (SemilatticeSup.toHasSup.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (Lattice.toSemilatticeSup.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteLattice.toLattice.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 Y)))) S R)) (Sup.sup.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (SemilatticeSup.toHasSup.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (Lattice.toSemilatticeSup.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toLattice.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 X)))) (CategoryTheory.Sieve.pushforward.{u1, u2} C _inst_1 X Y f S) (CategoryTheory.Sieve.pushforward.{u1, u2} C _inst_1 X Y f R))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X} (S : CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (R : CategoryTheory.Sieve.{u1, u2} C _inst_1 Y), Eq.{max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.pushforward.{u1, u2} C _inst_1 X Y f (Sup.sup.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (SemilatticeSup.toSup.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (Lattice.toSemilatticeSup.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteLattice.toLattice.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 Y)))) S R)) (Sup.sup.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (SemilatticeSup.toSup.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (Lattice.toSemilatticeSup.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toLattice.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 X)))) (CategoryTheory.Sieve.pushforward.{u1, u2} C _inst_1 X Y f S) (CategoryTheory.Sieve.pushforward.{u1, u2} C _inst_1 X Y f R))
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.pushforward_union CategoryTheory.Sieve.pushforward_unionₓ'. -/
theorem pushforward_union {f : Y ⟶ X} (S R : Sieve Y) :
    (S ⊔ R).pushforward f = S.pushforward f ⊔ R.pushforward f :=
  (galoisConnection f).l_sup
#align category_theory.sieve.pushforward_union CategoryTheory.Sieve.pushforward_union

/- warning: category_theory.sieve.pushforward_le_bind_of_mem -> CategoryTheory.Sieve.pushforward_le_bind_of_mem is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (S : CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (R : forall {{Y : C}} {{f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X}}, (S Y f) -> (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y)) (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X) (h : S Y f), LE.le.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (Preorder.toLE.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 X))))) (CategoryTheory.Sieve.pushforward.{u1, u2} C _inst_1 X Y f (R Y f h)) (CategoryTheory.Sieve.bind.{u1, u2} C _inst_1 X S R)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (S : CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (R : forall {{Y : C}} {{f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X}}, (S Y f) -> (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y)) (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X) (h : S Y f), LE.le.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (Preorder.toLE.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 X))))) (CategoryTheory.Sieve.pushforward.{u1, u2} C _inst_1 X Y f (R Y f h)) (CategoryTheory.Sieve.bind.{u1, u2} C _inst_1 X S R)
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.pushforward_le_bind_of_mem CategoryTheory.Sieve.pushforward_le_bind_of_memₓ'. -/
theorem pushforward_le_bind_of_mem (S : Presieve X) (R : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → Sieve Y)
    (f : Y ⟶ X) (h : S f) : (R h).pushforward f ≤ bind S R :=
  by
  rintro Z _ ⟨g, rfl, hg⟩
  exact ⟨_, g, f, h, hg, rfl⟩
#align category_theory.sieve.pushforward_le_bind_of_mem CategoryTheory.Sieve.pushforward_le_bind_of_mem

/- warning: category_theory.sieve.le_pullback_bind -> CategoryTheory.Sieve.le_pullback_bind is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (S : CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (R : forall {{Y : C}} {{f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X}}, (S Y f) -> (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y)) (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X) (h : S Y f), LE.le.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (Preorder.toLE.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 Y))))) (R Y f h) (CategoryTheory.Sieve.pullback.{u1, u2} C _inst_1 X Y f (CategoryTheory.Sieve.bind.{u1, u2} C _inst_1 X S R))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (S : CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (R : forall {{Y : C}} {{f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X}}, (S Y f) -> (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y)) (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X) (h : S Y f), LE.le.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (Preorder.toLE.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 Y))))) (R Y f h) (CategoryTheory.Sieve.pullback.{u1, u2} C _inst_1 X Y f (CategoryTheory.Sieve.bind.{u1, u2} C _inst_1 X S R))
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.le_pullback_bind CategoryTheory.Sieve.le_pullback_bindₓ'. -/
theorem le_pullback_bind (S : Presieve X) (R : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → Sieve Y) (f : Y ⟶ X)
    (h : S f) : R h ≤ (bind S R).pullback f :=
  by
  rw [← GaloisConnection f]
  apply pushforward_le_bind_of_mem
#align category_theory.sieve.le_pullback_bind CategoryTheory.Sieve.le_pullback_bind

/- warning: category_theory.sieve.galois_coinsertion_of_mono -> CategoryTheory.Sieve.galoisCoinsertionOfMono is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X) [_inst_3 : CategoryTheory.Mono.{u1, u2} C _inst_1 Y X f], GaloisCoinsertion.{max u2 u1, max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 Y)))) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 X)))) (CategoryTheory.Sieve.pushforward.{u1, u2} C _inst_1 X Y f) (CategoryTheory.Sieve.pullback.{u1, u2} C _inst_1 X Y f)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X) [_inst_3 : CategoryTheory.Mono.{u1, u2} C _inst_1 Y X f], GaloisCoinsertion.{max u2 u1, max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 Y)))) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 X)))) (CategoryTheory.Sieve.pushforward.{u1, u2} C _inst_1 X Y f) (CategoryTheory.Sieve.pullback.{u1, u2} C _inst_1 X Y f)
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.galois_coinsertion_of_mono CategoryTheory.Sieve.galoisCoinsertionOfMonoₓ'. -/
/-- If `f` is a monomorphism, the pushforward-pullback adjunction on sieves is coreflective. -/
def galoisCoinsertionOfMono (f : Y ⟶ X) [Mono f] :
    GaloisCoinsertion (Sieve.pushforward f) (Sieve.pullback f) :=
  by
  apply (GaloisConnection f).toGaloisCoinsertion
  rintro S Z g ⟨g₁, hf, hg₁⟩
  rw [cancel_mono f] at hf
  rwa [← hf]
#align category_theory.sieve.galois_coinsertion_of_mono CategoryTheory.Sieve.galoisCoinsertionOfMono

/- warning: category_theory.sieve.galois_insertion_of_is_split_epi -> CategoryTheory.Sieve.galoisInsertionOfIsSplitEpi is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X) [_inst_3 : CategoryTheory.IsSplitEpi.{u1, u2} C _inst_1 Y X f], GaloisInsertion.{max u2 u1, max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 Y)))) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 X)))) (CategoryTheory.Sieve.pushforward.{u1, u2} C _inst_1 X Y f) (CategoryTheory.Sieve.pullback.{u1, u2} C _inst_1 X Y f)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y X) [_inst_3 : CategoryTheory.IsSplitEpi.{u1, u2} C _inst_1 Y X f], GaloisInsertion.{max u2 u1, max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 Y) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 Y)))) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 X)))) (CategoryTheory.Sieve.pushforward.{u1, u2} C _inst_1 X Y f) (CategoryTheory.Sieve.pullback.{u1, u2} C _inst_1 X Y f)
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.galois_insertion_of_is_split_epi CategoryTheory.Sieve.galoisInsertionOfIsSplitEpiₓ'. -/
/-- If `f` is a split epi, the pushforward-pullback adjunction on sieves is reflective. -/
def galoisInsertionOfIsSplitEpi (f : Y ⟶ X) [IsSplitEpi f] :
    GaloisInsertion (Sieve.pushforward f) (Sieve.pullback f) :=
  by
  apply (GaloisConnection f).toGaloisInsertion
  intro S Z g hg
  refine' ⟨g ≫ section_ f, by simpa⟩
#align category_theory.sieve.galois_insertion_of_is_split_epi CategoryTheory.Sieve.galoisInsertionOfIsSplitEpi

#print CategoryTheory.Sieve.pullbackArrows_comm /-
theorem pullbackArrows_comm [HasPullbacks C] {X Y : C} (f : Y ⟶ X) (R : Presieve X) :
    Sieve.generate (R.pullbackArrows f) = (Sieve.generate R).pullback f :=
  by
  ext (Z g)
  constructor
  · rintro ⟨_, h, k, hk, rfl⟩
    cases' hk with W g hg
    change (sieve.generate R).pullback f (h ≫ pullback.snd)
    rw [sieve.pullback_apply, assoc, ← pullback.condition, ← assoc]
    exact sieve.downward_closed _ (sieve.le_generate R W hg) (h ≫ pullback.fst)
  · rintro ⟨W, h, k, hk, comm⟩
    exact ⟨_, _, _, presieve.pullback_arrows.mk _ _ hk, pullback.lift_snd _ _ comm⟩
#align category_theory.sieve.pullback_arrows_comm CategoryTheory.Sieve.pullbackArrows_comm
-/

section Functor

variable {E : Type u₃} [Category.{v₃} E] (G : D ⥤ E)

/- warning: category_theory.sieve.functor_pullback -> CategoryTheory.Sieve.functorPullback is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C}, (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) -> (CategoryTheory.Sieve.{u1, u3} C _inst_1 X)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C}, (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) -> (CategoryTheory.Sieve.{u1, u3} C _inst_1 X)
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.functor_pullback CategoryTheory.Sieve.functorPullbackₓ'. -/
/--
If `R` is a sieve, then the `category_theory.presieve.functor_pullback` of `R` is actually a sieve.
-/
@[simps]
def functorPullback (R : Sieve (F.obj X)) : Sieve X
    where
  arrows := Presieve.functorPullback F R
  downward_closed' _ _ f hf g := by
    unfold presieve.functor_pullback
    rw [F.map_comp]
    exact R.downward_closed hf (F.map g)
#align category_theory.sieve.functor_pullback CategoryTheory.Sieve.functorPullback

/- warning: category_theory.sieve.functor_pullback_arrows -> CategoryTheory.Sieve.functorPullback_arrows is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} (R : CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)), Eq.{max (succ u3) (succ u1)} (CategoryTheory.Presieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.arrows.{u1, u3} C _inst_1 X (CategoryTheory.Sieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X R)) (CategoryTheory.Presieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X (CategoryTheory.Sieve.arrows.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) R))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} (R : CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)), Eq.{max (succ u3) (succ u1)} (CategoryTheory.Presieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.arrows.{u1, u3} C _inst_1 X (CategoryTheory.Sieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X R)) (CategoryTheory.Presieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X (CategoryTheory.Sieve.arrows.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) R))
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.functor_pullback_arrows CategoryTheory.Sieve.functorPullback_arrowsₓ'. -/
@[simp]
theorem functorPullback_arrows (R : Sieve (F.obj X)) :
    (R.functorPullback F).arrows = R.arrows.functorPullback F :=
  rfl
#align category_theory.sieve.functor_pullback_arrows CategoryTheory.Sieve.functorPullback_arrows

#print CategoryTheory.Sieve.functorPullback_id /-
@[simp]
theorem functorPullback_id (R : Sieve X) : R.functorPullback (𝟭 _) = R :=
  by
  ext
  rfl
#align category_theory.sieve.functor_pullback_id CategoryTheory.Sieve.functorPullback_id
-/

/- warning: category_theory.sieve.functor_pullback_comp -> CategoryTheory.Sieve.functorPullback_comp is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u4} C] {D : Type.{u5}} [_inst_2 : CategoryTheory.Category.{u2, u5} D] (F : CategoryTheory.Functor.{u1, u2, u4, u5} C _inst_1 D _inst_2) {X : C} {E : Type.{u6}} [_inst_3 : CategoryTheory.Category.{u3, u6} E] (G : CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_2 E _inst_3) (R : CategoryTheory.Sieve.{u3, u6} E _inst_3 (CategoryTheory.Functor.obj.{u1, u3, u4, u6} C _inst_1 E _inst_3 (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F G) X)), Eq.{max (succ u4) (succ u1)} (CategoryTheory.Sieve.{u1, u4} C _inst_1 X) (CategoryTheory.Sieve.functorPullback.{u1, u3, u4, u6} C _inst_1 E _inst_3 (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F G) X R) (CategoryTheory.Sieve.functorPullback.{u1, u2, u4, u5} C _inst_1 D _inst_2 F X (CategoryTheory.Sieve.functorPullback.{u2, u3, u5, u6} D _inst_2 E _inst_3 G (CategoryTheory.Functor.obj.{u1, u2, u4, u5} C _inst_1 D _inst_2 F X) R))
but is expected to have type
  forall {C : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u4} C] {D : Type.{u5}} [_inst_2 : CategoryTheory.Category.{u2, u5} D] (F : CategoryTheory.Functor.{u1, u2, u4, u5} C _inst_1 D _inst_2) {X : C} {E : Type.{u6}} [_inst_3 : CategoryTheory.Category.{u3, u6} E] (G : CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_2 E _inst_3) (R : CategoryTheory.Sieve.{u3, u6} E _inst_3 (Prefunctor.obj.{succ u1, succ u3, u4, u6} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u4, u6} C _inst_1 E _inst_3 (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F G)) X)), Eq.{max (succ u4) (succ u1)} (CategoryTheory.Sieve.{u1, u4} C _inst_1 X) (CategoryTheory.Sieve.functorPullback.{u1, u3, u4, u6} C _inst_1 E _inst_3 (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F G) X R) (CategoryTheory.Sieve.functorPullback.{u1, u2, u4, u5} C _inst_1 D _inst_2 F X (CategoryTheory.Sieve.functorPullback.{u2, u3, u5, u6} D _inst_2 E _inst_3 G (Prefunctor.obj.{succ u1, succ u2, u4, u5} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u4, u5} C _inst_1 D _inst_2 F) X) R))
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.functor_pullback_comp CategoryTheory.Sieve.functorPullback_compₓ'. -/
theorem functorPullback_comp (R : Sieve ((F ⋙ G).obj X)) :
    R.functorPullback (F ⋙ G) = (R.functorPullback G).functorPullback F :=
  by
  ext
  rfl
#align category_theory.sieve.functor_pullback_comp CategoryTheory.Sieve.functorPullback_comp

/- warning: category_theory.sieve.functor_pushforward_extend_eq -> CategoryTheory.Sieve.functorPushforward_extend_eq is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {R : CategoryTheory.Presieve.{u1, u3} C _inst_1 X}, Eq.{max (succ u4) (succ u2)} (CategoryTheory.Presieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CategoryTheory.Presieve.functorPushforward.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X (CategoryTheory.Sieve.arrows.{u1, u3} C _inst_1 X (CategoryTheory.Sieve.generate.{u1, u3} C _inst_1 X R))) (CategoryTheory.Presieve.functorPushforward.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X R)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {R : CategoryTheory.Presieve.{u1, u3} C _inst_1 X}, Eq.{max (succ u4) (succ u2)} (CategoryTheory.Presieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CategoryTheory.Presieve.functorPushforward.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X (CategoryTheory.Sieve.arrows.{u1, u3} C _inst_1 X (CategoryTheory.Sieve.generate.{u1, u3} C _inst_1 X R))) (CategoryTheory.Presieve.functorPushforward.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X R)
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.functor_pushforward_extend_eq CategoryTheory.Sieve.functorPushforward_extend_eqₓ'. -/
theorem functorPushforward_extend_eq {R : Presieve X} :
    (generate R).arrows.functorPushforward F = R.functorPushforward F :=
  by
  ext (Y f); constructor
  · rintro ⟨X', g, f', ⟨X'', g', f'', h₁, rfl⟩, rfl⟩
    exact ⟨X'', f'', f' ≫ F.map g', h₁, by simp⟩
  · rintro ⟨X', g, f', h₁, h₂⟩
    exact ⟨X', g, f', le_generate R _ h₁, h₂⟩
#align category_theory.sieve.functor_pushforward_extend_eq CategoryTheory.Sieve.functorPushforward_extend_eq

/- warning: category_theory.sieve.functor_pushforward -> CategoryTheory.Sieve.functorPushforward is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C}, (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) -> (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C}, (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) -> (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X))
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.functor_pushforward CategoryTheory.Sieve.functorPushforwardₓ'. -/
/-- The sieve generated by the image of `R` under `F`. -/
@[simps]
def functorPushforward (R : Sieve X) : Sieve (F.obj X)
    where
  arrows := R.arrows.functorPushforward F
  downward_closed' Y Z f h g := by
    obtain ⟨X, α, β, hα, rfl⟩ := h
    exact ⟨X, α, g ≫ β, hα, by simp⟩
#align category_theory.sieve.functor_pushforward CategoryTheory.Sieve.functorPushforward

/- warning: category_theory.sieve.functor_pushforward_id -> CategoryTheory.Sieve.functorPushforward_id is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} (R : CategoryTheory.Sieve.{u1, u2} C _inst_1 X), Eq.{max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) X)) (CategoryTheory.Sieve.functorPushforward.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) X R) R
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} (R : CategoryTheory.Sieve.{u1, u2} C _inst_1 X), Eq.{max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1)) X)) (CategoryTheory.Sieve.functorPushforward.{u1, u1, u2, u2} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u2} C _inst_1) X R) R
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.functor_pushforward_id CategoryTheory.Sieve.functorPushforward_idₓ'. -/
@[simp]
theorem functorPushforward_id (R : Sieve X) : R.functorPushforward (𝟭 _) = R :=
  by
  ext (X f)
  constructor
  · intro hf
    obtain ⟨X, g, h, hg, rfl⟩ := hf
    exact R.downward_closed hg h
  · intro hf
    exact ⟨X, f, 𝟙 _, hf, by simp⟩
#align category_theory.sieve.functor_pushforward_id CategoryTheory.Sieve.functorPushforward_id

/- warning: category_theory.sieve.functor_pushforward_comp -> CategoryTheory.Sieve.functorPushforward_comp is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u4} C] {D : Type.{u5}} [_inst_2 : CategoryTheory.Category.{u2, u5} D] (F : CategoryTheory.Functor.{u1, u2, u4, u5} C _inst_1 D _inst_2) {X : C} {E : Type.{u6}} [_inst_3 : CategoryTheory.Category.{u3, u6} E] (G : CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_2 E _inst_3) (R : CategoryTheory.Sieve.{u1, u4} C _inst_1 X), Eq.{max (succ u6) (succ u3)} (CategoryTheory.Sieve.{u3, u6} E _inst_3 (CategoryTheory.Functor.obj.{u1, u3, u4, u6} C _inst_1 E _inst_3 (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F G) X)) (CategoryTheory.Sieve.functorPushforward.{u1, u3, u4, u6} C _inst_1 E _inst_3 (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F G) X R) (CategoryTheory.Sieve.functorPushforward.{u2, u3, u5, u6} D _inst_2 E _inst_3 G (CategoryTheory.Functor.obj.{u1, u2, u4, u5} C _inst_1 D _inst_2 F X) (CategoryTheory.Sieve.functorPushforward.{u1, u2, u4, u5} C _inst_1 D _inst_2 F X R))
but is expected to have type
  forall {C : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u4} C] {D : Type.{u5}} [_inst_2 : CategoryTheory.Category.{u2, u5} D] (F : CategoryTheory.Functor.{u1, u2, u4, u5} C _inst_1 D _inst_2) {X : C} {E : Type.{u6}} [_inst_3 : CategoryTheory.Category.{u3, u6} E] (G : CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_2 E _inst_3) (R : CategoryTheory.Sieve.{u1, u4} C _inst_1 X), Eq.{max (succ u6) (succ u3)} (CategoryTheory.Sieve.{u3, u6} E _inst_3 (Prefunctor.obj.{succ u1, succ u3, u4, u6} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) E (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} E (CategoryTheory.Category.toCategoryStruct.{u3, u6} E _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u4, u6} C _inst_1 E _inst_3 (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F G)) X)) (CategoryTheory.Sieve.functorPushforward.{u1, u3, u4, u6} C _inst_1 E _inst_3 (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 E _inst_3 F G) X R) (CategoryTheory.Sieve.functorPushforward.{u2, u3, u5, u6} D _inst_2 E _inst_3 G (Prefunctor.obj.{succ u1, succ u2, u4, u5} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} C (CategoryTheory.Category.toCategoryStruct.{u1, u4} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} D (CategoryTheory.Category.toCategoryStruct.{u2, u5} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u4, u5} C _inst_1 D _inst_2 F) X) (CategoryTheory.Sieve.functorPushforward.{u1, u2, u4, u5} C _inst_1 D _inst_2 F X R))
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.functor_pushforward_comp CategoryTheory.Sieve.functorPushforward_compₓ'. -/
theorem functorPushforward_comp (R : Sieve X) :
    R.functorPushforward (F ⋙ G) = (R.functorPushforward F).functorPushforward G :=
  by
  ext
  simpa [R.arrows.functor_pushforward_comp F G]
#align category_theory.sieve.functor_pushforward_comp CategoryTheory.Sieve.functorPushforward_comp

/- warning: category_theory.sieve.functor_galois_connection -> CategoryTheory.Sieve.functor_galoisConnection is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (X : C), GaloisConnection.{max u3 u1, max u4 u2} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (PartialOrder.toPreorder.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u3} C _inst_1 X)))) (PartialOrder.toPreorder.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CompleteSemilatticeInf.toPartialOrder.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CompleteLattice.toCompleteSemilatticeInf.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CategoryTheory.Sieve.completeLattice.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X))))) (CategoryTheory.Sieve.functorPushforward.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Sieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (X : C), GaloisConnection.{max u3 u1, max u4 u2} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (PartialOrder.toPreorder.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u3} C _inst_1 X)))) (PartialOrder.toPreorder.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CompleteSemilatticeInf.toPartialOrder.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CompleteLattice.toCompleteSemilatticeInf.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X))))) (CategoryTheory.Sieve.functorPushforward.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Sieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.functor_galois_connection CategoryTheory.Sieve.functor_galoisConnectionₓ'. -/
theorem functor_galoisConnection (X : C) :
    GaloisConnection (Sieve.functorPushforward F : Sieve X → Sieve (F.obj X))
      (Sieve.functorPullback F) :=
  by
  intro R S
  constructor
  · intro hle X f hf
    apply hle
    refine' ⟨X, f, 𝟙 _, hf, _⟩
    rw [id_comp]
  · rintro hle Y f ⟨X, g, h, hg, rfl⟩
    apply sieve.downward_closed S
    exact hle g hg
#align category_theory.sieve.functor_galois_connection CategoryTheory.Sieve.functor_galoisConnection

/- warning: category_theory.sieve.functor_pullback_monotone -> CategoryTheory.Sieve.functorPullback_monotone is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (X : C), Monotone.{max u4 u2, max u3 u1} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (PartialOrder.toPreorder.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CompleteSemilatticeInf.toPartialOrder.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CompleteLattice.toCompleteSemilatticeInf.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CategoryTheory.Sieve.completeLattice.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X))))) (PartialOrder.toPreorder.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u3} C _inst_1 X)))) (CategoryTheory.Sieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (X : C), Monotone.{max u4 u2, max u3 u1} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (PartialOrder.toPreorder.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CompleteSemilatticeInf.toPartialOrder.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CompleteLattice.toCompleteSemilatticeInf.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X))))) (PartialOrder.toPreorder.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u3} C _inst_1 X)))) (CategoryTheory.Sieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.functor_pullback_monotone CategoryTheory.Sieve.functorPullback_monotoneₓ'. -/
theorem functorPullback_monotone (X : C) :
    Monotone (Sieve.functorPullback F : Sieve (F.obj X) → Sieve X) :=
  (functor_galoisConnection F X).monotone_u
#align category_theory.sieve.functor_pullback_monotone CategoryTheory.Sieve.functorPullback_monotone

/- warning: category_theory.sieve.functor_pushforward_monotone -> CategoryTheory.Sieve.functorPushforward_monotone is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (X : C), Monotone.{max u3 u1, max u4 u2} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (PartialOrder.toPreorder.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u3} C _inst_1 X)))) (PartialOrder.toPreorder.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CompleteSemilatticeInf.toPartialOrder.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CompleteLattice.toCompleteSemilatticeInf.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CategoryTheory.Sieve.completeLattice.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X))))) (CategoryTheory.Sieve.functorPushforward.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (X : C), Monotone.{max u3 u1, max u4 u2} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (PartialOrder.toPreorder.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u3} C _inst_1 X)))) (PartialOrder.toPreorder.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CompleteSemilatticeInf.toPartialOrder.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CompleteLattice.toCompleteSemilatticeInf.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X))))) (CategoryTheory.Sieve.functorPushforward.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.functor_pushforward_monotone CategoryTheory.Sieve.functorPushforward_monotoneₓ'. -/
theorem functorPushforward_monotone (X : C) :
    Monotone (Sieve.functorPushforward F : Sieve X → Sieve (F.obj X)) :=
  (functor_galoisConnection F X).monotone_l
#align category_theory.sieve.functor_pushforward_monotone CategoryTheory.Sieve.functorPushforward_monotone

/- warning: category_theory.sieve.le_functor_pushforward_pullback -> CategoryTheory.Sieve.le_functorPushforward_pullback is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} (R : CategoryTheory.Sieve.{u1, u3} C _inst_1 X), LE.le.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (Preorder.toLE.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (PartialOrder.toPreorder.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u3} C _inst_1 X))))) R (CategoryTheory.Sieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X (CategoryTheory.Sieve.functorPushforward.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X R))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} (R : CategoryTheory.Sieve.{u1, u3} C _inst_1 X), LE.le.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (Preorder.toLE.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (PartialOrder.toPreorder.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u3} C _inst_1 X))))) R (CategoryTheory.Sieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X (CategoryTheory.Sieve.functorPushforward.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X R))
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.le_functor_pushforward_pullback CategoryTheory.Sieve.le_functorPushforward_pullbackₓ'. -/
theorem le_functorPushforward_pullback (R : Sieve X) :
    R ≤ (R.functorPushforward F).functorPullback F :=
  (functor_galoisConnection F X).le_u_l _
#align category_theory.sieve.le_functor_pushforward_pullback CategoryTheory.Sieve.le_functorPushforward_pullback

/- warning: category_theory.sieve.functor_pullback_pushforward_le -> CategoryTheory.Sieve.functorPullback_pushforward_le is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} (R : CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)), LE.le.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (Preorder.toLE.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (PartialOrder.toPreorder.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CompleteSemilatticeInf.toPartialOrder.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CompleteLattice.toCompleteSemilatticeInf.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CategoryTheory.Sieve.completeLattice.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)))))) (CategoryTheory.Sieve.functorPushforward.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X (CategoryTheory.Sieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X R)) R
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} (R : CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)), LE.le.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (Preorder.toLE.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (PartialOrder.toPreorder.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CompleteSemilatticeInf.toPartialOrder.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CompleteLattice.toCompleteSemilatticeInf.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)))))) (CategoryTheory.Sieve.functorPushforward.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X (CategoryTheory.Sieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X R)) R
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.functor_pullback_pushforward_le CategoryTheory.Sieve.functorPullback_pushforward_leₓ'. -/
theorem functorPullback_pushforward_le (R : Sieve (F.obj X)) :
    (R.functorPullback F).functorPushforward F ≤ R :=
  (functor_galoisConnection F X).l_u_le _
#align category_theory.sieve.functor_pullback_pushforward_le CategoryTheory.Sieve.functorPullback_pushforward_le

/- warning: category_theory.sieve.functor_pushforward_union -> CategoryTheory.Sieve.functorPushforward_union is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} (S : CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (R : CategoryTheory.Sieve.{u1, u3} C _inst_1 X), Eq.{max (succ u4) (succ u2)} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CategoryTheory.Sieve.functorPushforward.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X (Sup.sup.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (SemilatticeSup.toHasSup.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (Lattice.toSemilatticeSup.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteLattice.toLattice.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u3} C _inst_1 X)))) S R)) (Sup.sup.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (SemilatticeSup.toHasSup.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (Lattice.toSemilatticeSup.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CompleteLattice.toLattice.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CategoryTheory.Sieve.completeLattice.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X))))) (CategoryTheory.Sieve.functorPushforward.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X S) (CategoryTheory.Sieve.functorPushforward.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X R))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} (S : CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (R : CategoryTheory.Sieve.{u1, u3} C _inst_1 X), Eq.{max (succ u4) (succ u2)} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CategoryTheory.Sieve.functorPushforward.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X (Sup.sup.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (SemilatticeSup.toSup.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (Lattice.toSemilatticeSup.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteLattice.toLattice.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u3} C _inst_1 X)))) S R)) (Sup.sup.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (SemilatticeSup.toSup.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (Lattice.toSemilatticeSup.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CompleteLattice.toLattice.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X))))) (CategoryTheory.Sieve.functorPushforward.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X S) (CategoryTheory.Sieve.functorPushforward.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X R))
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.functor_pushforward_union CategoryTheory.Sieve.functorPushforward_unionₓ'. -/
theorem functorPushforward_union (S R : Sieve X) :
    (S ⊔ R).functorPushforward F = S.functorPushforward F ⊔ R.functorPushforward F :=
  (functor_galoisConnection F X).l_sup
#align category_theory.sieve.functor_pushforward_union CategoryTheory.Sieve.functorPushforward_union

/- warning: category_theory.sieve.functor_pullback_union -> CategoryTheory.Sieve.functorPullback_union is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} (S : CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (R : CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)), Eq.{max (succ u3) (succ u1)} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X (Sup.sup.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (SemilatticeSup.toHasSup.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (Lattice.toSemilatticeSup.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CompleteLattice.toLattice.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CategoryTheory.Sieve.completeLattice.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X))))) S R)) (Sup.sup.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (SemilatticeSup.toHasSup.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (Lattice.toSemilatticeSup.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteLattice.toLattice.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u3} C _inst_1 X)))) (CategoryTheory.Sieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X S) (CategoryTheory.Sieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X R))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} (S : CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (R : CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)), Eq.{max (succ u3) (succ u1)} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X (Sup.sup.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (SemilatticeSup.toSup.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (Lattice.toSemilatticeSup.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CompleteLattice.toLattice.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X))))) S R)) (Sup.sup.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (SemilatticeSup.toSup.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (Lattice.toSemilatticeSup.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteLattice.toLattice.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u3} C _inst_1 X)))) (CategoryTheory.Sieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X S) (CategoryTheory.Sieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X R))
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.functor_pullback_union CategoryTheory.Sieve.functorPullback_unionₓ'. -/
theorem functorPullback_union (S R : Sieve (F.obj X)) :
    (S ⊔ R).functorPullback F = S.functorPullback F ⊔ R.functorPullback F :=
  rfl
#align category_theory.sieve.functor_pullback_union CategoryTheory.Sieve.functorPullback_union

/- warning: category_theory.sieve.functor_pullback_inter -> CategoryTheory.Sieve.functorPullback_inter is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} (S : CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (R : CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)), Eq.{max (succ u3) (succ u1)} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X (Inf.inf.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (SemilatticeInf.toHasInf.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (Lattice.toSemilatticeInf.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CompleteLattice.toLattice.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CategoryTheory.Sieve.completeLattice.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X))))) S R)) (Inf.inf.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (SemilatticeInf.toHasInf.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (Lattice.toSemilatticeInf.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteLattice.toLattice.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u3} C _inst_1 X)))) (CategoryTheory.Sieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X S) (CategoryTheory.Sieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X R))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} (S : CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (R : CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)), Eq.{max (succ u3) (succ u1)} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X (Inf.inf.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (Lattice.toInf.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CompleteLattice.toLattice.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)))) S R)) (Inf.inf.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (Lattice.toInf.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteLattice.toLattice.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u3} C _inst_1 X))) (CategoryTheory.Sieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X S) (CategoryTheory.Sieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X R))
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.functor_pullback_inter CategoryTheory.Sieve.functorPullback_interₓ'. -/
theorem functorPullback_inter (S R : Sieve (F.obj X)) :
    (S ⊓ R).functorPullback F = S.functorPullback F ⊓ R.functorPullback F :=
  rfl
#align category_theory.sieve.functor_pullback_inter CategoryTheory.Sieve.functorPullback_inter

/- warning: category_theory.sieve.functor_pushforward_bot -> CategoryTheory.Sieve.functorPushforward_bot is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (X : C), Eq.{max (succ u4) (succ u2)} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CategoryTheory.Sieve.functorPushforward.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X (Bot.bot.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteLattice.toHasBot.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u3} C _inst_1 X)))) (Bot.bot.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CompleteLattice.toHasBot.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CategoryTheory.Sieve.completeLattice.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X))))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (X : C), Eq.{max (succ u4) (succ u2)} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CategoryTheory.Sieve.functorPushforward.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X (Bot.bot.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteLattice.toBot.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u3} C _inst_1 X)))) (Bot.bot.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CompleteLattice.toBot.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X))))
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.functor_pushforward_bot CategoryTheory.Sieve.functorPushforward_botₓ'. -/
@[simp]
theorem functorPushforward_bot (F : C ⥤ D) (X : C) : (⊥ : Sieve X).functorPushforward F = ⊥ :=
  (functor_galoisConnection F X).l_bot
#align category_theory.sieve.functor_pushforward_bot CategoryTheory.Sieve.functorPushforward_bot

/- warning: category_theory.sieve.functor_pushforward_top -> CategoryTheory.Sieve.functorPushforward_top is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (X : C), Eq.{max (succ u4) (succ u2)} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CategoryTheory.Sieve.functorPushforward.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X (Top.top.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteLattice.toHasTop.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u3} C _inst_1 X)))) (Top.top.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CompleteLattice.toHasTop.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CategoryTheory.Sieve.completeLattice.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X))))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (X : C), Eq.{max (succ u4) (succ u2)} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CategoryTheory.Sieve.functorPushforward.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X (Top.top.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteLattice.toTop.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u3} C _inst_1 X)))) (Top.top.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CompleteLattice.toTop.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X))))
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.functor_pushforward_top CategoryTheory.Sieve.functorPushforward_topₓ'. -/
@[simp]
theorem functorPushforward_top (F : C ⥤ D) (X : C) : (⊤ : Sieve X).functorPushforward F = ⊤ :=
  by
  refine' (generate_sieve _).symm.trans _
  apply generate_of_contains_is_split_epi (𝟙 (F.obj X))
  refine' ⟨X, 𝟙 _, 𝟙 _, trivial, by simp⟩
#align category_theory.sieve.functor_pushforward_top CategoryTheory.Sieve.functorPushforward_top

/- warning: category_theory.sieve.functor_pullback_bot -> CategoryTheory.Sieve.functorPullback_bot is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (X : C), Eq.{max (succ u3) (succ u1)} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X (Bot.bot.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CompleteLattice.toHasBot.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CategoryTheory.Sieve.completeLattice.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X))))) (Bot.bot.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteLattice.toHasBot.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u3} C _inst_1 X)))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (X : C), Eq.{max (succ u3) (succ u1)} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X (Bot.bot.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CompleteLattice.toBot.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X))))) (Bot.bot.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteLattice.toBot.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u3} C _inst_1 X)))
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.functor_pullback_bot CategoryTheory.Sieve.functorPullback_botₓ'. -/
@[simp]
theorem functorPullback_bot (F : C ⥤ D) (X : C) : (⊥ : Sieve (F.obj X)).functorPullback F = ⊥ :=
  rfl
#align category_theory.sieve.functor_pullback_bot CategoryTheory.Sieve.functorPullback_bot

/- warning: category_theory.sieve.functor_pullback_top -> CategoryTheory.Sieve.functorPullback_top is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (X : C), Eq.{max (succ u3) (succ u1)} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X (Top.top.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CompleteLattice.toHasTop.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CategoryTheory.Sieve.completeLattice.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X))))) (Top.top.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteLattice.toHasTop.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u3} C _inst_1 X)))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (X : C), Eq.{max (succ u3) (succ u1)} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X (Top.top.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CompleteLattice.toTop.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X))))) (Top.top.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteLattice.toTop.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u3} C _inst_1 X)))
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.functor_pullback_top CategoryTheory.Sieve.functorPullback_topₓ'. -/
@[simp]
theorem functorPullback_top (F : C ⥤ D) (X : C) : (⊤ : Sieve (F.obj X)).functorPullback F = ⊤ :=
  rfl
#align category_theory.sieve.functor_pullback_top CategoryTheory.Sieve.functorPullback_top

/- warning: category_theory.sieve.image_mem_functor_pushforward -> CategoryTheory.Sieve.image_mem_functorPushforward is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} (R : CategoryTheory.Sieve.{u1, u3} C _inst_1 X) {V : C} {f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) V X}, (coeFn.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (fun (_x : CategoryTheory.Sieve.{u1, u3} C _inst_1 X) => CategoryTheory.Presieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.hasCoeToFun.{u1, u3} C _inst_1 X) R V f) -> (coeFn.{max (succ u4) (succ u2), max (succ u4) (succ u2)} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (fun (_x : CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) => CategoryTheory.Presieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CategoryTheory.Sieve.hasCoeToFun.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CategoryTheory.Sieve.functorPushforward.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X R) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F V) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F V X f))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} (R : CategoryTheory.Sieve.{u1, u3} C _inst_1 X) {V : C} {f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) V X}, (CategoryTheory.Sieve.arrows.{u1, u3} C _inst_1 X R V f) -> (CategoryTheory.Sieve.arrows.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (CategoryTheory.Sieve.functorPushforward.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X R) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) V) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) V X f))
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.image_mem_functor_pushforward CategoryTheory.Sieve.image_mem_functorPushforwardₓ'. -/
theorem image_mem_functorPushforward (R : Sieve X) {V} {f : V ⟶ X} (h : R f) :
    R.functorPushforward F (F.map f) :=
  ⟨V, f, 𝟙 _, h, by simp⟩
#align category_theory.sieve.image_mem_functor_pushforward CategoryTheory.Sieve.image_mem_functorPushforward

/- warning: category_theory.sieve.ess_surj_full_functor_galois_insertion -> CategoryTheory.Sieve.essSurjFullFunctorGaloisInsertion is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_4 : CategoryTheory.EssSurj.{u1, u2, u3, u4} C D _inst_1 _inst_2 F] [_inst_5 : CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] (X : C), GaloisInsertion.{max u3 u1, max u4 u2} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (PartialOrder.toPreorder.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u3} C _inst_1 X)))) (PartialOrder.toPreorder.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CompleteSemilatticeInf.toPartialOrder.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CompleteLattice.toCompleteSemilatticeInf.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CategoryTheory.Sieve.completeLattice.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X))))) (CategoryTheory.Sieve.functorPushforward.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Sieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_4 : CategoryTheory.EssSurj.{u1, u2, u3, u4} C D _inst_1 _inst_2 F] [_inst_5 : CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] (X : C), GaloisInsertion.{max u3 u1, max u4 u2} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (PartialOrder.toPreorder.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u3} C _inst_1 X)))) (PartialOrder.toPreorder.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CompleteSemilatticeInf.toPartialOrder.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CompleteLattice.toCompleteSemilatticeInf.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X))))) (CategoryTheory.Sieve.functorPushforward.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Sieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.ess_surj_full_functor_galois_insertion CategoryTheory.Sieve.essSurjFullFunctorGaloisInsertionₓ'. -/
/-- When `F` is essentially surjective and full, the galois connection is a galois insertion. -/
def essSurjFullFunctorGaloisInsertion [EssSurj F] [Full F] (X : C) :
    GaloisInsertion (Sieve.functorPushforward F : Sieve X → Sieve (F.obj X))
      (Sieve.functorPullback F) :=
  by
  apply (functor_galois_connection F X).toGaloisInsertion
  intro S Y f hf
  refine' ⟨_, F.preimage ((F.obj_obj_preimage_iso Y).Hom ≫ f), (F.obj_obj_preimage_iso Y).inv, _⟩
  simpa using S.downward_closed hf _
#align category_theory.sieve.ess_surj_full_functor_galois_insertion CategoryTheory.Sieve.essSurjFullFunctorGaloisInsertion

/- warning: category_theory.sieve.fully_faithful_functor_galois_coinsertion -> CategoryTheory.Sieve.fullyFaithfulFunctorGaloisCoinsertion is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_4 : CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] [_inst_5 : CategoryTheory.Faithful.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] (X : C), GaloisCoinsertion.{max u3 u1, max u4 u2} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (PartialOrder.toPreorder.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u3} C _inst_1 X)))) (PartialOrder.toPreorder.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CompleteSemilatticeInf.toPartialOrder.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CompleteLattice.toCompleteSemilatticeInf.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CategoryTheory.Sieve.completeLattice.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X))))) (CategoryTheory.Sieve.functorPushforward.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Sieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_4 : CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] [_inst_5 : CategoryTheory.Faithful.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] (X : C), GaloisCoinsertion.{max u3 u1, max u4 u2} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (PartialOrder.toPreorder.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u3 u1} (CategoryTheory.Sieve.{u1, u3} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u3} C _inst_1 X)))) (PartialOrder.toPreorder.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CompleteSemilatticeInf.toPartialOrder.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CompleteLattice.toCompleteSemilatticeInf.{max u4 u2} (CategoryTheory.Sieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X))))) (CategoryTheory.Sieve.functorPushforward.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Sieve.functorPullback.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.fully_faithful_functor_galois_coinsertion CategoryTheory.Sieve.fullyFaithfulFunctorGaloisCoinsertionₓ'. -/
/-- When `F` is fully faithful, the galois connection is a galois coinsertion. -/
def fullyFaithfulFunctorGaloisCoinsertion [Full F] [Faithful F] (X : C) :
    GaloisCoinsertion (Sieve.functorPushforward F : Sieve X → Sieve (F.obj X))
      (Sieve.functorPullback F) :=
  by
  apply (functor_galois_connection F X).toGaloisCoinsertion
  rintro S Y f ⟨Z, g, h, h₁, h₂⟩
  rw [← F.image_preimage h, ← F.map_comp] at h₂
  rw [F.map_injective h₂]
  exact S.downward_closed h₁ _
#align category_theory.sieve.fully_faithful_functor_galois_coinsertion CategoryTheory.Sieve.fullyFaithfulFunctorGaloisCoinsertion

end Functor

#print CategoryTheory.Sieve.functor /-
/-- A sieve induces a presheaf. -/
@[simps]
def functor (S : Sieve X) : Cᵒᵖ ⥤ Type v₁
    where
  obj Y := { g : Y.unop ⟶ X // S g }
  map Y Z f g := ⟨f.unop ≫ g.1, downward_closed _ g.2 _⟩
#align category_theory.sieve.functor CategoryTheory.Sieve.functor
-/

/- warning: category_theory.sieve.nat_trans_of_le -> CategoryTheory.Sieve.natTransOfLe is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {S : CategoryTheory.Sieve.{u1, u2} C _inst_1 X} {T : CategoryTheory.Sieve.{u1, u2} C _inst_1 X}, (LE.le.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (Preorder.toLE.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 X))))) S T) -> (Quiver.Hom.{succ (max u2 u1), max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Sieve.functor.{u1, u2} C _inst_1 X S) (CategoryTheory.Sieve.functor.{u1, u2} C _inst_1 X T))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {S : CategoryTheory.Sieve.{u1, u2} C _inst_1 X} {T : CategoryTheory.Sieve.{u1, u2} C _inst_1 X}, (LE.le.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (Preorder.toLE.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 X))))) S T) -> (Quiver.Hom.{max (succ u2) (succ u1), max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Sieve.functor.{u1, u2} C _inst_1 X S) (CategoryTheory.Sieve.functor.{u1, u2} C _inst_1 X T))
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.nat_trans_of_le CategoryTheory.Sieve.natTransOfLeₓ'. -/
/-- If a sieve S is contained in a sieve T, then we have a morphism of presheaves on their induced
presheaves.
-/
@[simps]
def natTransOfLe {S T : Sieve X} (h : S ≤ T) : S.Functor ⟶ T.Functor where app Y f := ⟨f.1, h _ f.2⟩
#align category_theory.sieve.nat_trans_of_le CategoryTheory.Sieve.natTransOfLe

/- warning: category_theory.sieve.functor_inclusion -> CategoryTheory.Sieve.functorInclusion is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} (S : CategoryTheory.Sieve.{u1, u2} C _inst_1 X), Quiver.Hom.{succ (max u2 u1), max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Sieve.functor.{u1, u2} C _inst_1 X S) (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1) X)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} (S : CategoryTheory.Sieve.{u1, u2} C _inst_1 X), Quiver.Hom.{max (succ u2) (succ u1), max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Sieve.functor.{u1, u2} C _inst_1 X S) (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u2, max (succ u1) u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1)) X)
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.functor_inclusion CategoryTheory.Sieve.functorInclusionₓ'. -/
/-- The natural inclusion from the functor induced by a sieve to the yoneda embedding. -/
@[simps]
def functorInclusion (S : Sieve X) : S.Functor ⟶ yoneda.obj X where app Y f := f.1
#align category_theory.sieve.functor_inclusion CategoryTheory.Sieve.functorInclusion

/- warning: category_theory.sieve.nat_trans_of_le_comm -> CategoryTheory.Sieve.natTransOfLe_comm is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {S : CategoryTheory.Sieve.{u1, u2} C _inst_1 X} {T : CategoryTheory.Sieve.{u1, u2} C _inst_1 X} (h : LE.le.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (Preorder.toLE.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 X))))) S T), Eq.{succ (max u2 u1)} (Quiver.Hom.{succ (max u2 u1), max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Sieve.functor.{u1, u2} C _inst_1 X S) (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1) X)) (CategoryTheory.CategoryStruct.comp.{max u2 u1, max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Sieve.functor.{u1, u2} C _inst_1 X S) (CategoryTheory.Sieve.functor.{u1, u2} C _inst_1 X T) (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1) X) (CategoryTheory.Sieve.natTransOfLe.{u1, u2} C _inst_1 X S T h) (CategoryTheory.Sieve.functorInclusion.{u1, u2} C _inst_1 X T)) (CategoryTheory.Sieve.functorInclusion.{u1, u2} C _inst_1 X S)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {S : CategoryTheory.Sieve.{u1, u2} C _inst_1 X} {T : CategoryTheory.Sieve.{u1, u2} C _inst_1 X} (h : LE.le.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (Preorder.toLE.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 X))))) S T), Eq.{max (succ u2) (succ u1)} (Quiver.Hom.{succ (max u2 u1), max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Sieve.functor.{u1, u2} C _inst_1 X S) (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u2, max (succ u1) u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1)) X)) (CategoryTheory.CategoryStruct.comp.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Sieve.functor.{u1, u2} C _inst_1 X S) (CategoryTheory.Sieve.functor.{u1, u2} C _inst_1 X T) (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u2, max (succ u1) u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1)) X) (CategoryTheory.Sieve.natTransOfLe.{u1, u2} C _inst_1 X S T h) (CategoryTheory.Sieve.functorInclusion.{u1, u2} C _inst_1 X T)) (CategoryTheory.Sieve.functorInclusion.{u1, u2} C _inst_1 X S)
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.nat_trans_of_le_comm CategoryTheory.Sieve.natTransOfLe_commₓ'. -/
theorem natTransOfLe_comm {S T : Sieve X} (h : S ≤ T) :
    natTransOfLe h ≫ functorInclusion _ = functorInclusion _ :=
  rfl
#align category_theory.sieve.nat_trans_of_le_comm CategoryTheory.Sieve.natTransOfLe_comm

/- warning: category_theory.sieve.functor_inclusion_is_mono -> CategoryTheory.Sieve.functorInclusion_is_mono is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {S : CategoryTheory.Sieve.{u1, u2} C _inst_1 X}, CategoryTheory.Mono.{max u2 u1, max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Sieve.functor.{u1, u2} C _inst_1 X S) (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1) X) (CategoryTheory.Sieve.functorInclusion.{u1, u2} C _inst_1 X S)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {S : CategoryTheory.Sieve.{u1, u2} C _inst_1 X}, CategoryTheory.Mono.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Sieve.functor.{u1, u2} C _inst_1 X S) (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u2, max (succ u1) u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1)) X) (CategoryTheory.Sieve.functorInclusion.{u1, u2} C _inst_1 X S)
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.functor_inclusion_is_mono CategoryTheory.Sieve.functorInclusion_is_monoₓ'. -/
/-- The presheaf induced by a sieve is a subobject of the yoneda embedding. -/
instance functorInclusion_is_mono : Mono S.functorInclusion :=
  ⟨fun Z f g h => by
    ext (Y y)
    apply congr_fun (nat_trans.congr_app h Y) y⟩
#align category_theory.sieve.functor_inclusion_is_mono CategoryTheory.Sieve.functorInclusion_is_mono

/- warning: category_theory.sieve.sieve_of_subfunctor -> CategoryTheory.Sieve.sieveOfSubfunctor is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {R : CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}}, (Quiver.Hom.{succ (max u2 u1), max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) R (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1) X)) -> (CategoryTheory.Sieve.{u1, u2} C _inst_1 X)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {R : CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}}, (Quiver.Hom.{max (succ u2) (succ u1), max (succ u1) u2} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) R (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u2, max (succ u1) u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1)) X)) -> (CategoryTheory.Sieve.{u1, u2} C _inst_1 X)
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.sieve_of_subfunctor CategoryTheory.Sieve.sieveOfSubfunctorₓ'. -/
-- TODO: Show that when `f` is mono, this is right inverse to `functor_inclusion` up to isomorphism.
/-- A natural transformation to a representable functor induces a sieve. This is the left inverse of
`functor_inclusion`, shown in `sieve_of_functor_inclusion`.
-/
@[simps]
def sieveOfSubfunctor {R} (f : R ⟶ yoneda.obj X) : Sieve X
    where
  arrows Y g := ∃ t, f.app (Opposite.op Y) t = g
  downward_closed' Y Z _ := by
    rintro ⟨t, rfl⟩ g
    refine' ⟨R.map g.op t, _⟩
    rw [functor_to_types.naturality _ _ f]
    simp
#align category_theory.sieve.sieve_of_subfunctor CategoryTheory.Sieve.sieveOfSubfunctor

#print CategoryTheory.Sieve.sieveOfSubfunctor_functorInclusion /-
theorem sieveOfSubfunctor_functorInclusion : sieveOfSubfunctor S.functorInclusion = S :=
  by
  ext
  simp only [functor_inclusion_app, sieve_of_subfunctor_apply, Subtype.val_eq_coe]
  constructor
  · rintro ⟨⟨f, hf⟩, rfl⟩
    exact hf
  · intro hf
    exact ⟨⟨_, hf⟩, rfl⟩
#align category_theory.sieve.sieve_of_subfunctor_functor_inclusion CategoryTheory.Sieve.sieveOfSubfunctor_functorInclusion
-/

/- warning: category_theory.sieve.functor_inclusion_top_is_iso -> CategoryTheory.Sieve.functorInclusion_top_isIso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C}, CategoryTheory.IsIso.{max u2 u1, max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Sieve.functor.{u1, u2} C _inst_1 X (Top.top.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toHasTop.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 X)))) (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1) X) (CategoryTheory.Sieve.functorInclusion.{u1, u2} C _inst_1 X (Top.top.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toHasTop.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.completeLattice.{u1, u2} C _inst_1 X))))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C}, CategoryTheory.IsIso.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Sieve.functor.{u1, u2} C _inst_1 X (Top.top.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toTop.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 X)))) (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u2, max (succ u1) u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1)) X) (CategoryTheory.Sieve.functorInclusion.{u1, u2} C _inst_1 X (Top.top.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CompleteLattice.toTop.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.instCompleteLatticeSieve.{u1, u2} C _inst_1 X))))
Case conversion may be inaccurate. Consider using '#align category_theory.sieve.functor_inclusion_top_is_iso CategoryTheory.Sieve.functorInclusion_top_isIsoₓ'. -/
instance functorInclusion_top_isIso : IsIso (⊤ : Sieve X).functorInclusion :=
  ⟨⟨{ app := fun Y a => ⟨a, ⟨⟩⟩ }, by tidy⟩⟩
#align category_theory.sieve.functor_inclusion_top_is_iso CategoryTheory.Sieve.functorInclusion_top_isIso

end Sieve

end CategoryTheory

