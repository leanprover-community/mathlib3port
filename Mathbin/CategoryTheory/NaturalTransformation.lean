/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Scott Morrison, Floris van Doorn
-/
import CategoryTheory.Functor.Basic

#align_import category_theory.natural_transformation from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

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

-- Rather arbitrarily, we say that the 'simpler' form is
-- components of natural transfomations moving earlier.
attribute [simp, reassoc] nat_trans.naturality

#print CategoryTheory.congr_app /-
theorem congr_app {F G : C ⥤ D} {α β : NatTrans F G} (h : α = β) (X : C) : α.app X = β.app X :=
  congr_fun (congr_arg NatTrans.app h) X
#align category_theory.congr_app CategoryTheory.congr_app
-/

namespace NatTrans

#print CategoryTheory.NatTrans.id /-
/-- `nat_trans.id F` is the identity natural transformation on a functor `F`. -/
protected def id (F : C ⥤ D) : NatTrans F F where app X := 𝟙 (F.obj X)
#align category_theory.nat_trans.id CategoryTheory.NatTrans.id
-/

#print CategoryTheory.NatTrans.id_app' /-
@[simp]
theorem id_app' (F : C ⥤ D) (X : C) : (NatTrans.id F).app X = 𝟙 (F.obj X) :=
  rfl
#align category_theory.nat_trans.id_app' CategoryTheory.NatTrans.id_app'
-/

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

#print CategoryTheory.NatTrans.vcomp_app /-
-- functor_category will rewrite (vcomp α β) to (α ≫ β), so this is not a
-- suitable simp lemma.  We will declare the variant vcomp_app' there.
theorem vcomp_app (α : NatTrans F G) (β : NatTrans G H) (X : C) :
    (vcomp α β).app X = α.app X ≫ β.app X :=
  rfl
#align category_theory.nat_trans.vcomp_app CategoryTheory.NatTrans.vcomp_app
-/

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

