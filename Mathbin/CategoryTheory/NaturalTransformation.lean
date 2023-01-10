/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Scott Morrison, Floris van Doorn

! This file was ported from Lean 3 source module category_theory.natural_transformation
! leanprover-community/mathlib commit 7b78d1776212a91ecc94cf601f83bdcc46b04213
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Functor.Basic

/-!
# Natural transformations

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Defines natural transformations between functors.

A natural transformation `α : nat_trans F G` consists of morphisms `α.app X : F.obj X ⟶ G.obj X`,
and the naturality squares `α.naturality f : F.map f ≫ α.app Y = α.app X ≫ G.map f`,
where `f : X ⟶ Y`.

Note that we make `nat_trans.naturality` a simp lemma, with the preferred simp normal form
pushing components of natural transformations to the left.

See also `category_theory.functor_category`, where we provide the category structure on
functors and natural transformations.

Introduces notations
* `τ.app X` for the components of natural transformations,
* `F ⟶ G` for the type of natural transformations between functors `F` and `G`
  (this and the next require `category_theory.functor_category`),
* `σ ≫ τ` for vertical compositions, and
* `σ ◫ τ` for horizontal compositions.

-/


namespace CategoryTheory

-- declare the `v`'s first; see `category_theory.category` for an explanation
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

#print CategoryTheory.NatTrans /-
/-- `nat_trans F G` represents a natural transformation between functors `F` and `G`.

The field `app` provides the components of the natural transformation.

Naturality is expressed by `α.naturality_lemma`.
-/
@[ext]
structure NatTrans (F G : C ⥤ D) : Type max u₁ v₂ where
  app : ∀ X : C, F.obj X ⟶ G.obj X
  naturality' : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), F.map f ≫ app Y = app X ≫ G.map f := by obviously
#align category_theory.nat_trans CategoryTheory.NatTrans
-/

restate_axiom nat_trans.naturality'

-- Rather arbitrarily, we say that the 'simpler' form is
-- components of natural transfomations moving earlier.
attribute [simp, reassoc.1] nat_trans.naturality

/- warning: category_theory.congr_app -> CategoryTheory.congr_app is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] {F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} {G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} {α : CategoryTheory.NatTrans.{u1, u2, u3, u4} C _inst_1 D _inst_2 F G} {β : CategoryTheory.NatTrans.{u1, u2, u3, u4} C _inst_1 D _inst_2 F G}, (Eq.{succ (max u3 u2)} (CategoryTheory.NatTrans.{u1, u2, u3, u4} C _inst_1 D _inst_2 F G) α β) -> (forall (X : C), Eq.{succ u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X)) (CategoryTheory.NatTrans.app.{u1, u2, u3, u4} C _inst_1 D _inst_2 F G α X) (CategoryTheory.NatTrans.app.{u1, u2, u3, u4} C _inst_1 D _inst_2 F G β X))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] {F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} {G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} {α : CategoryTheory.NatTrans.{u1, u2, u3, u4} C _inst_1 D _inst_2 F G} {β : CategoryTheory.NatTrans.{u1, u2, u3, u4} C _inst_1 D _inst_2 F G}, (Eq.{max (succ u3) (succ u2)} (CategoryTheory.NatTrans.{u1, u2, u3, u4} C _inst_1 D _inst_2 F G) α β) -> (forall (X : C), Eq.{succ u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X)) (CategoryTheory.NatTrans.app.{u1, u2, u3, u4} C _inst_1 D _inst_2 F G α X) (CategoryTheory.NatTrans.app.{u1, u2, u3, u4} C _inst_1 D _inst_2 F G β X))
Case conversion may be inaccurate. Consider using '#align category_theory.congr_app CategoryTheory.congr_appₓ'. -/
theorem congr_app {F G : C ⥤ D} {α β : NatTrans F G} (h : α = β) (X : C) : α.app X = β.app X :=
  congr_fun (congr_arg NatTrans.app h) X
#align category_theory.congr_app CategoryTheory.congr_app

namespace NatTrans

#print CategoryTheory.NatTrans.id /-
/-- `nat_trans.id F` is the identity natural transformation on a functor `F`. -/
protected def id (F : C ⥤ D) : NatTrans F F where app X := 𝟙 (F.obj X)
#align category_theory.nat_trans.id CategoryTheory.NatTrans.id
-/

/- warning: category_theory.nat_trans.id_app' -> CategoryTheory.NatTrans.id_app' is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (X : C), Eq.{succ u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X)) (CategoryTheory.NatTrans.app.{u1, u2, u3, u4} C _inst_1 D _inst_2 F F (CategoryTheory.NatTrans.id.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (CategoryTheory.CategoryStruct.id.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (X : C), Eq.{succ u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X)) (CategoryTheory.NatTrans.app.{u1, u2, u3, u4} C _inst_1 D _inst_2 F F (CategoryTheory.NatTrans.id.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (CategoryTheory.CategoryStruct.id.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X))
Case conversion may be inaccurate. Consider using '#align category_theory.nat_trans.id_app' CategoryTheory.NatTrans.id_app'ₓ'. -/
@[simp]
theorem id_app' (F : C ⥤ D) (X : C) : (NatTrans.id F).app X = 𝟙 (F.obj X) :=
  rfl
#align category_theory.nat_trans.id_app' CategoryTheory.NatTrans.id_app'

instance (F : C ⥤ D) : Inhabited (NatTrans F F) :=
  ⟨NatTrans.id F⟩

open Category

open CategoryTheory.Functor

section

variable {F G H I : C ⥤ D}

#print CategoryTheory.NatTrans.vcomp /-
/-- `vcomp α β` is the vertical compositions of natural transformations. -/
def vcomp (α : NatTrans F G) (β : NatTrans G H) : NatTrans F H where app X := α.app X ≫ β.app X
#align category_theory.nat_trans.vcomp CategoryTheory.NatTrans.vcomp
-/

/- warning: category_theory.nat_trans.vcomp_app -> CategoryTheory.NatTrans.vcomp_app is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] {F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} {G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} {H : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} (α : CategoryTheory.NatTrans.{u1, u2, u3, u4} C _inst_1 D _inst_2 F G) (β : CategoryTheory.NatTrans.{u1, u2, u3, u4} C _inst_1 D _inst_2 G H) (X : C), Eq.{succ u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 H X)) (CategoryTheory.NatTrans.app.{u1, u2, u3, u4} C _inst_1 D _inst_2 F H (CategoryTheory.NatTrans.vcomp.{u1, u2, u3, u4} C _inst_1 D _inst_2 F G H α β) X) (CategoryTheory.CategoryStruct.comp.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 H X) (CategoryTheory.NatTrans.app.{u1, u2, u3, u4} C _inst_1 D _inst_2 F G α X) (CategoryTheory.NatTrans.app.{u1, u2, u3, u4} C _inst_1 D _inst_2 G H β X))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] {F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} {G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} {H : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} (α : CategoryTheory.NatTrans.{u1, u2, u3, u4} C _inst_1 D _inst_2 F G) (β : CategoryTheory.NatTrans.{u1, u2, u3, u4} C _inst_1 D _inst_2 G H) (X : C), Eq.{succ u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 H) X)) (CategoryTheory.NatTrans.app.{u1, u2, u3, u4} C _inst_1 D _inst_2 F H (CategoryTheory.NatTrans.vcomp.{u1, u2, u3, u4} C _inst_1 D _inst_2 F G H α β) X) (CategoryTheory.CategoryStruct.comp.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 H) X) (CategoryTheory.NatTrans.app.{u1, u2, u3, u4} C _inst_1 D _inst_2 F G α X) (CategoryTheory.NatTrans.app.{u1, u2, u3, u4} C _inst_1 D _inst_2 G H β X))
Case conversion may be inaccurate. Consider using '#align category_theory.nat_trans.vcomp_app CategoryTheory.NatTrans.vcomp_appₓ'. -/
-- functor_category will rewrite (vcomp α β) to (α ≫ β), so this is not a
-- suitable simp lemma.  We will declare the variant vcomp_app' there.
theorem vcomp_app (α : NatTrans F G) (β : NatTrans G H) (X : C) :
    (vcomp α β).app X = α.app X ≫ β.app X :=
  rfl
#align category_theory.nat_trans.vcomp_app CategoryTheory.NatTrans.vcomp_app

end

/-- The diagram
    F(f)      F(g)      F(h)
F X ----> F Y ----> F U ----> F U
 |         |         |         |
 | α(X)    | α(Y)    | α(U)    | α(V)
 v         v         v         v
G X ----> G Y ----> G U ----> G V
    G(f)      G(g)      G(h)
commutes.
-/
example {F G : C ⥤ D} (α : NatTrans F G) {X Y U V : C} (f : X ⟶ Y) (g : Y ⟶ U) (h : U ⟶ V) :
    α.app X ≫ G.map f ≫ G.map g ≫ G.map h = F.map f ≫ F.map g ≫ F.map h ≫ α.app V := by simp

end NatTrans

end CategoryTheory

