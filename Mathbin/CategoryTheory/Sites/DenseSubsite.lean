/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module category_theory.sites.dense_subsite
! leanprover-community/mathlib commit 2ed2c6310e6f1c5562bdf6bfbda55ebbf6891abe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Sites.Sheaf
import Mathbin.CategoryTheory.Sites.CoverLifting
import Mathbin.CategoryTheory.Adjunction.FullyFaithful

/-!
# Dense subsites

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define `cover_dense` functors into sites as functors such that there exists a covering sieve
that factors through images of the functor for each object in `D`.

We will primarily consider cover-dense functors that are also full, since this notion is in general
not well-behaved otherwise. Note that https://ncatlab.org/nlab/show/dense+sub-site indeed has a
weaker notion of cover-dense that loosens this requirement, but it would not have all the properties
we would need, and some sheafification would be needed for here and there.

## Main results

- `category_theory.cover_dense.presheaf_hom`: If `G : C ⥤ (D, K)` is full and cover-dense,
  then given any presheaf `ℱ` and sheaf `ℱ'` on `D`, and a morphism `α : G ⋙ ℱ ⟶ G ⋙ ℱ'`,
  we may glue them together to obtain a morphism of presheaves `ℱ ⟶ ℱ'`.
- `category_theory.cover_dense.sheaf_iso`: If `ℱ` above is a sheaf and `α` is an iso,
  then the result is also an iso.
- `category_theory.cover_dense.iso_of_restrict_iso`: If `G : C ⥤ (D, K)` is full and cover-dense,
  then given any sheaves `ℱ, ℱ'` on `D`, and a morphism `α : ℱ ⟶ ℱ'`, then `α` is an iso if
  `G ⋙ ℱ ⟶ G ⋙ ℱ'` is iso.
- `category_theory.cover_dense.Sheaf_equiv_of_cover_preserving_cover_lifting`:
  If `G : (C, J) ⥤ (D, K)` is fully-faithful, cover-lifting, cover-preserving, and cover-dense,
  then it will induce an equivalence of categories of sheaves valued in a complete category.

## References

* [Elephant]: *Sketches of an Elephant*, ℱ. T. Johnstone: C2.2.
* https://ncatlab.org/nlab/show/dense+sub-site
* https://ncatlab.org/nlab/show/comparison+lemma

-/


universe w v u

namespace CategoryTheory

variable {C : Type _} [Category C] {D : Type _} [Category D] {E : Type _} [Category E]

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)

variable {L : GrothendieckTopology E}

#print CategoryTheory.Presieve.CoverByImageStructure /-
/-- An auxiliary structure that witnesses the fact that `f` factors through an image object of `G`.
-/
@[nolint has_nonempty_instance]
structure Presieve.CoverByImageStructure (G : C ⥤ D) {V U : D} (f : V ⟶ U) where
  obj : C
  lift : V ⟶ G.obj obj
  map : G.obj obj ⟶ U
  fac : lift ≫ map = f := by obviously
#align category_theory.presieve.cover_by_image_structure CategoryTheory.Presieve.CoverByImageStructure
-/

restate_axiom presieve.cover_by_image_structure.fac'

attribute [simp, reassoc] presieve.cover_by_image_structure.fac

#print CategoryTheory.Presieve.coverByImage /-
/-- For a functor `G : C ⥤ D`, and an object `U : D`, `presieve.cover_by_image G U` is the presieve
of `U` consisting of those arrows that factor through images of `G`.
-/
def Presieve.coverByImage (G : C ⥤ D) (U : D) : Presieve U := fun Y f =>
  Nonempty (Presieve.CoverByImageStructure G f)
#align category_theory.presieve.cover_by_image CategoryTheory.Presieve.coverByImage
-/

#print CategoryTheory.Sieve.coverByImage /-
/-- For a functor `G : C ⥤ D`, and an object `U : D`, `sieve.cover_by_image G U` is the sieve of `U`
consisting of those arrows that factor through images of `G`.
-/
def Sieve.coverByImage (G : C ⥤ D) (U : D) : Sieve U :=
  ⟨Presieve.coverByImage G U, fun X Y f ⟨⟨Z, f₁, f₂, (e : _ = _)⟩⟩ g =>
    ⟨⟨Z, g ≫ f₁, f₂, show (g ≫ f₁) ≫ f₂ = g ≫ f by rw [category.assoc, ← e]⟩⟩⟩
#align category_theory.sieve.cover_by_image CategoryTheory.Sieve.coverByImage
-/

/- warning: category_theory.presieve.in_cover_by_image -> CategoryTheory.Presieve.in_coverByImage is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} D] (G : CategoryTheory.Functor.{u2, u4, u1, u3} C _inst_1 D _inst_2) {X : D} {Y : C} (f : Quiver.Hom.{succ u4, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.obj.{u2, u4, u1, u3} C _inst_1 D _inst_2 G Y) X), CategoryTheory.Presieve.coverByImage.{u1, u2, u3, u4} C _inst_1 D _inst_2 G X (CategoryTheory.Functor.obj.{u2, u4, u1, u3} C _inst_1 D _inst_2 G Y) f
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u4, u2} C] {D : Type.{u1}} [_inst_2 : CategoryTheory.Category.{u3, u1} D] (G : CategoryTheory.Functor.{u4, u3, u2, u1} C _inst_1 D _inst_2) {X : D} {Y : C} (f : Quiver.Hom.{succ u3, u1} D (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} D (CategoryTheory.Category.toCategoryStruct.{u3, u1} D _inst_2)) (Prefunctor.obj.{succ u4, succ u3, u2, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} C (CategoryTheory.Category.toCategoryStruct.{u4, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} D (CategoryTheory.Category.toCategoryStruct.{u3, u1} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u4, u3, u2, u1} C _inst_1 D _inst_2 G) Y) X), CategoryTheory.Presieve.coverByImage.{u2, u4, u1, u3} C _inst_1 D _inst_2 G X (Prefunctor.obj.{succ u4, succ u3, u2, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} C (CategoryTheory.Category.toCategoryStruct.{u4, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} D (CategoryTheory.Category.toCategoryStruct.{u3, u1} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u4, u3, u2, u1} C _inst_1 D _inst_2 G) Y) f
Case conversion may be inaccurate. Consider using '#align category_theory.presieve.in_cover_by_image CategoryTheory.Presieve.in_coverByImageₓ'. -/
theorem Presieve.in_coverByImage (G : C ⥤ D) {X : D} {Y : C} (f : G.obj Y ⟶ X) :
    Presieve.coverByImage G X f :=
  ⟨⟨Y, 𝟙 _, f, by simp⟩⟩
#align category_theory.presieve.in_cover_by_image CategoryTheory.Presieve.in_coverByImage

#print CategoryTheory.CoverDense /-
/-- A functor `G : (C, J) ⥤ (D, K)` is called `cover_dense` if for each object in `D`,
  there exists a covering sieve in `D` that factors through images of `G`.

This definition can be found in https://ncatlab.org/nlab/show/dense+sub-site Definition 2.2.
-/
structure CoverDense (K : GrothendieckTopology D) (G : C ⥤ D) : Prop where
  is_cover : ∀ U : D, Sieve.coverByImage G U ∈ K U
#align category_theory.cover_dense CategoryTheory.CoverDense
-/

open Presieve Opposite

namespace CoverDense

variable {K}

variable {A : Type _} [Category A] {G : C ⥤ D} (H : CoverDense K G)

/- warning: category_theory.cover_dense.ext -> CategoryTheory.CoverDense.ext is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.cover_dense.ext CategoryTheory.CoverDense.extₓ'. -/
-- this is not marked with `@[ext]` because `H` can not be inferred from the type
theorem ext (H : CoverDense K G) (ℱ : SheafOfTypes K) (X : D) {s t : ℱ.val.obj (op X)}
    (h : ∀ ⦃Y : C⦄ (f : G.obj Y ⟶ X), ℱ.val.map f.op s = ℱ.val.map f.op t) : s = t :=
  by
  apply (ℱ.cond (sieve.cover_by_image G X) (H.is_cover X)).IsSeparatedFor.ext
  rintro Y _ ⟨Z, f₁, f₂, ⟨rfl⟩⟩
  simp [h f₂]
#align category_theory.cover_dense.ext CategoryTheory.CoverDense.ext

/- warning: category_theory.cover_dense.functor_pullback_pushforward_covering -> CategoryTheory.CoverDense.functorPullback_pushforward_covering is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.cover_dense.functor_pullback_pushforward_covering CategoryTheory.CoverDense.functorPullback_pushforward_coveringₓ'. -/
theorem functorPullback_pushforward_covering [Full G] (H : CoverDense K G) {X : C}
    (T : K (G.obj X)) : (T.val.functorPullback G).functorPushforward G ∈ K (G.obj X) :=
  by
  refine' K.superset_covering _ (K.bind_covering T.property fun Y f Hf => H.is_cover Y)
  rintro Y _ ⟨Z, _, f, hf, ⟨W, g, f', ⟨rfl⟩⟩, rfl⟩
  use W; use G.preimage (f' ≫ f); use g
  constructor
  · simpa using T.val.downward_closed hf f'
  · simp
#align category_theory.cover_dense.functor_pullback_pushforward_covering CategoryTheory.CoverDense.functorPullback_pushforward_covering

/- warning: category_theory.cover_dense.hom_over -> CategoryTheory.CoverDense.homOver is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} D] {K : CategoryTheory.GrothendieckTopology.{u4, u3} D _inst_2} {A : Type.{u5}} [_inst_4 : CategoryTheory.Category.{u6, u5} A] {G : CategoryTheory.Functor.{u2, u4, u1, u3} C _inst_1 D _inst_2} {ℱ : CategoryTheory.Functor.{u4, u6, u3, u5} (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) A _inst_4} {ℱ' : CategoryTheory.Sheaf.{u4, u6, u3, u5} D _inst_2 K A _inst_4}, (Quiver.Hom.{succ (max u1 u6), max u2 u6 u1 u5} (CategoryTheory.Functor.{u2, u6, u1, u5} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) A _inst_4) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u6, max u2 u6 u1 u5} (CategoryTheory.Functor.{u2, u6, u1, u5} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) A _inst_4) (CategoryTheory.Category.toCategoryStruct.{max u1 u6, max u2 u6 u1 u5} (CategoryTheory.Functor.{u2, u6, u1, u5} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) A _inst_4) (CategoryTheory.Functor.category.{u2, u6, u1, u5} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) A _inst_4))) (CategoryTheory.Functor.comp.{u2, u4, u6, u1, u3, u5} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) A _inst_4 (CategoryTheory.Functor.op.{u2, u4, u1, u3} C _inst_1 D _inst_2 G) ℱ) (CategoryTheory.Functor.comp.{u2, u4, u6, u1, u3, u5} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) A _inst_4 (CategoryTheory.Functor.op.{u2, u4, u1, u3} C _inst_1 D _inst_2 G) (CategoryTheory.Sheaf.val.{u4, u6, u3, u5} D _inst_2 K A _inst_4 ℱ'))) -> (forall (X : A), Quiver.Hom.{succ (max u1 u6), max u2 u6 u1 (succ u6)} (CategoryTheory.Functor.{u2, u6, u1, succ u6} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) Type.{u6} CategoryTheory.types.{u6}) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u6, max u2 u6 u1 (succ u6)} (CategoryTheory.Functor.{u2, u6, u1, succ u6} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) Type.{u6} CategoryTheory.types.{u6}) (CategoryTheory.Category.toCategoryStruct.{max u1 u6, max u2 u6 u1 (succ u6)} (CategoryTheory.Functor.{u2, u6, u1, succ u6} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) Type.{u6} CategoryTheory.types.{u6}) (CategoryTheory.Functor.category.{u2, u6, u1, succ u6} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) Type.{u6} CategoryTheory.types.{u6}))) (CategoryTheory.Functor.comp.{u2, u4, u6, u1, u3, succ u6} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) Type.{u6} CategoryTheory.types.{u6} (CategoryTheory.Functor.op.{u2, u4, u1, u3} C _inst_1 D _inst_2 G) (CategoryTheory.Functor.comp.{u4, u6, u6, u3, u5, succ u6} (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) A _inst_4 Type.{u6} CategoryTheory.types.{u6} ℱ (CategoryTheory.Functor.obj.{u6, max u5 u6, u5, max u6 u5 (succ u6)} (Opposite.{succ u5} A) (CategoryTheory.Category.opposite.{u6, u5} A _inst_4) (CategoryTheory.Functor.{u6, u6, u5, succ u6} A _inst_4 Type.{u6} CategoryTheory.types.{u6}) (CategoryTheory.Functor.category.{u6, u6, u5, succ u6} A _inst_4 Type.{u6} CategoryTheory.types.{u6}) (CategoryTheory.coyoneda.{u6, u5} A _inst_4) (Opposite.op.{succ u5} A X)))) (CategoryTheory.Functor.comp.{u2, u4, u6, u1, u3, succ u6} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) Type.{u6} CategoryTheory.types.{u6} (CategoryTheory.Functor.op.{u2, u4, u1, u3} C _inst_1 D _inst_2 G) (CategoryTheory.SheafOfTypes.val.{u6, u4, u3} D _inst_2 K (CategoryTheory.sheafOver.{u4, u6, u3, u5} D _inst_2 A _inst_4 K ℱ' X))))
but is expected to have type
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} D] {K : CategoryTheory.GrothendieckTopology.{u4, u3} D _inst_2} {A : Type.{u5}} [_inst_4 : CategoryTheory.Category.{u6, u5} A] {G : CategoryTheory.Functor.{u2, u4, u1, u3} C _inst_1 D _inst_2} {ℱ : CategoryTheory.Functor.{u4, u6, u3, u5} (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) A _inst_4} {ℱ' : CategoryTheory.Sheaf.{u4, u6, u3, u5} D _inst_2 K A _inst_4}, (Quiver.Hom.{max (succ u1) (succ u6), max (max (max u5 u1) u6) u2} (CategoryTheory.Functor.{u2, u6, u1, u5} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) A _inst_4) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u6, max (max (max u1 u2) u5) u6} (CategoryTheory.Functor.{u2, u6, u1, u5} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) A _inst_4) (CategoryTheory.Category.toCategoryStruct.{max u1 u6, max (max (max u1 u2) u5) u6} (CategoryTheory.Functor.{u2, u6, u1, u5} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) A _inst_4) (CategoryTheory.Functor.category.{u2, u6, u1, u5} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) A _inst_4))) (CategoryTheory.Functor.comp.{u2, u4, u6, u1, u3, u5} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) A _inst_4 (CategoryTheory.Functor.op.{u2, u4, u1, u3} C _inst_1 D _inst_2 G) ℱ) (CategoryTheory.Functor.comp.{u2, u4, u6, u1, u3, u5} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) A _inst_4 (CategoryTheory.Functor.op.{u2, u4, u1, u3} C _inst_1 D _inst_2 G) (CategoryTheory.Sheaf.val.{u4, u6, u3, u5} D _inst_2 K A _inst_4 ℱ'))) -> (forall (X : A), Quiver.Hom.{max (succ u1) (succ u6), max (max (max (succ u6) u1) u6) u2} (CategoryTheory.Functor.{u2, u6, u1, succ u6} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) Type.{u6} CategoryTheory.types.{u6}) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u6, max (max u1 u2) (succ u6)} (CategoryTheory.Functor.{u2, u6, u1, succ u6} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) Type.{u6} CategoryTheory.types.{u6}) (CategoryTheory.Category.toCategoryStruct.{max u1 u6, max (max u1 u2) (succ u6)} (CategoryTheory.Functor.{u2, u6, u1, succ u6} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) Type.{u6} CategoryTheory.types.{u6}) (CategoryTheory.Functor.category.{u2, u6, u1, succ u6} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) Type.{u6} CategoryTheory.types.{u6}))) (CategoryTheory.Functor.comp.{u2, u4, u6, u1, u3, succ u6} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) Type.{u6} CategoryTheory.types.{u6} (CategoryTheory.Functor.op.{u2, u4, u1, u3} C _inst_1 D _inst_2 G) (CategoryTheory.Functor.comp.{u4, u6, u6, u3, u5, succ u6} (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) A _inst_4 Type.{u6} CategoryTheory.types.{u6} ℱ (Prefunctor.obj.{succ u6, max (succ u5) (succ u6), u5, max u5 (succ u6)} (Opposite.{succ u5} A) (CategoryTheory.CategoryStruct.toQuiver.{u6, u5} (Opposite.{succ u5} A) (CategoryTheory.Category.toCategoryStruct.{u6, u5} (Opposite.{succ u5} A) (CategoryTheory.Category.opposite.{u6, u5} A _inst_4))) (CategoryTheory.Functor.{u6, u6, u5, succ u6} A _inst_4 Type.{u6} CategoryTheory.types.{u6}) (CategoryTheory.CategoryStruct.toQuiver.{max u5 u6, max u5 (succ u6)} (CategoryTheory.Functor.{u6, u6, u5, succ u6} A _inst_4 Type.{u6} CategoryTheory.types.{u6}) (CategoryTheory.Category.toCategoryStruct.{max u5 u6, max u5 (succ u6)} (CategoryTheory.Functor.{u6, u6, u5, succ u6} A _inst_4 Type.{u6} CategoryTheory.types.{u6}) (CategoryTheory.Functor.category.{u6, u6, u5, succ u6} A _inst_4 Type.{u6} CategoryTheory.types.{u6}))) (CategoryTheory.Functor.toPrefunctor.{u6, max u5 u6, u5, max u5 (succ u6)} (Opposite.{succ u5} A) (CategoryTheory.Category.opposite.{u6, u5} A _inst_4) (CategoryTheory.Functor.{u6, u6, u5, succ u6} A _inst_4 Type.{u6} CategoryTheory.types.{u6}) (CategoryTheory.Functor.category.{u6, u6, u5, succ u6} A _inst_4 Type.{u6} CategoryTheory.types.{u6}) (CategoryTheory.coyoneda.{u6, u5} A _inst_4)) (Opposite.op.{succ u5} A X)))) (CategoryTheory.Functor.comp.{u2, u4, u6, u1, u3, succ u6} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) Type.{u6} CategoryTheory.types.{u6} (CategoryTheory.Functor.op.{u2, u4, u1, u3} C _inst_1 D _inst_2 G) (CategoryTheory.SheafOfTypes.val.{u6, u4, u3} D _inst_2 K (CategoryTheory.sheafOver.{u4, u6, u3, u5} D _inst_2 A _inst_4 K ℱ' X))))
Case conversion may be inaccurate. Consider using '#align category_theory.cover_dense.hom_over CategoryTheory.CoverDense.homOverₓ'. -/
/-- (Implementation). Given an hom between the pullbacks of two sheaves, we can whisker it with
`coyoneda` to obtain an hom between the pullbacks of the sheaves of maps from `X`.
-/
@[simps]
def homOver {ℱ : Dᵒᵖ ⥤ A} {ℱ' : Sheaf K A} (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) (X : A) :
    G.op ⋙ ℱ ⋙ coyoneda.obj (op X) ⟶ G.op ⋙ (sheafOver ℱ' X).val :=
  whiskerRight α (coyoneda.obj (op X))
#align category_theory.cover_dense.hom_over CategoryTheory.CoverDense.homOver

#print CategoryTheory.CoverDense.isoOver /-
/-- (Implementation). Given an iso between the pullbacks of two sheaves, we can whisker it with
`coyoneda` to obtain an iso between the pullbacks of the sheaves of maps from `X`.
-/
@[simps]
def isoOver {ℱ ℱ' : Sheaf K A} (α : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) (X : A) :
    G.op ⋙ (sheafOver ℱ X).val ≅ G.op ⋙ (sheafOver ℱ' X).val :=
  isoWhiskerRight α (coyoneda.obj (op X))
#align category_theory.cover_dense.iso_over CategoryTheory.CoverDense.isoOver
-/

/- warning: category_theory.cover_dense.sheaf_eq_amalgamation -> CategoryTheory.CoverDense.sheaf_eq_amalgamation is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.cover_dense.sheaf_eq_amalgamation CategoryTheory.CoverDense.sheaf_eq_amalgamationₓ'. -/
theorem sheaf_eq_amalgamation (ℱ : Sheaf K A) {X : A} {U : D} {T : Sieve U} (hT)
    (x : FamilyOfElements _ T) (hx) (t) (h : x.IsAmalgamation t) :
    t = (ℱ.cond X T hT).amalgamate x hx :=
  (ℱ.cond X T hT).IsSeparatedFor x t _ h ((ℱ.cond X T hT).IsAmalgamation hx)
#align category_theory.cover_dense.sheaf_eq_amalgamation CategoryTheory.CoverDense.sheaf_eq_amalgamation

variable [Full G]

namespace Types

variable {ℱ : Dᵒᵖ ⥤ Type v} {ℱ' : SheafOfTypes.{v} K} (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val)

/- warning: category_theory.cover_dense.types.pushforward_family -> CategoryTheory.CoverDense.Types.pushforwardFamily is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u2} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u5, u4} D] {K : CategoryTheory.GrothendieckTopology.{u5, u4} D _inst_2} {G : CategoryTheory.Functor.{u3, u5, u2, u4} C _inst_1 D _inst_2} [_inst_5 : CategoryTheory.Full.{u3, u5, u2, u4} C _inst_1 D _inst_2 G] {ℱ : CategoryTheory.Functor.{u5, u1, u4, succ u1} (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2) Type.{u1} CategoryTheory.types.{u1}} {ℱ' : CategoryTheory.SheafOfTypes.{u1, u5, u4} D _inst_2 K}, (Quiver.Hom.{succ (max u2 u1), max u3 u1 u2 (succ u1)} (CategoryTheory.Functor.{u3, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u3 u1 u2 (succ u1)} (CategoryTheory.Functor.{u3, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u3 u1 u2 (succ u1)} (CategoryTheory.Functor.{u3, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u3, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.comp.{u3, u5, u1, u2, u4, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2) Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.op.{u3, u5, u2, u4} C _inst_1 D _inst_2 G) ℱ) (CategoryTheory.Functor.comp.{u3, u5, u1, u2, u4, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2) Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.op.{u3, u5, u2, u4} C _inst_1 D _inst_2 G) (CategoryTheory.SheafOfTypes.val.{u1, u5, u4} D _inst_2 K ℱ'))) -> (forall {X : D}, (CategoryTheory.Functor.obj.{u5, u1, u4, succ u1} (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2) Type.{u1} CategoryTheory.types.{u1} ℱ (Opposite.op.{succ u4} D X)) -> (CategoryTheory.Presieve.FamilyOfElements.{u1, u5, u4} D _inst_2 X (CategoryTheory.SheafOfTypes.val.{u1, u5, u4} D _inst_2 K ℱ') (CategoryTheory.Presieve.coverByImage.{u2, u3, u4, u5} C _inst_1 D _inst_2 G X)))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u2} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u5, u4} D] {K : CategoryTheory.GrothendieckTopology.{u5, u4} D _inst_2} {G : CategoryTheory.Functor.{u3, u5, u2, u4} C _inst_1 D _inst_2} {_inst_5 : CategoryTheory.Functor.{u5, u1, u4, succ u1} (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2) Type.{u1} CategoryTheory.types.{u1}} {ℱ : CategoryTheory.SheafOfTypes.{u1, u5, u4} D _inst_2 K}, (Quiver.Hom.{max (succ u1) (succ u2), max (max (max (succ u1) u2) u1) u3} (CategoryTheory.Functor.{u3, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, max (max (succ u1) u2) u3} (CategoryTheory.Functor.{u3, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u1 u2, max (max (succ u1) u2) u3} (CategoryTheory.Functor.{u3, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u3, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.comp.{u3, u5, u1, u2, u4, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2) Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.op.{u3, u5, u2, u4} C _inst_1 D _inst_2 G) _inst_5) (CategoryTheory.Functor.comp.{u3, u5, u1, u2, u4, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2) Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.op.{u3, u5, u2, u4} C _inst_1 D _inst_2 G) (CategoryTheory.SheafOfTypes.val.{u1, u5, u4} D _inst_2 K ℱ))) -> (forall {α : D}, (Prefunctor.obj.{succ u5, succ u1, u4, succ u1} (Opposite.{succ u4} D) (CategoryTheory.CategoryStruct.toQuiver.{u5, u4} (Opposite.{succ u4} D) (CategoryTheory.Category.toCategoryStruct.{u5, u4} (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u5, u1, u4, succ u1} (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2) Type.{u1} CategoryTheory.types.{u1} _inst_5) (Opposite.op.{succ u4} D α)) -> (CategoryTheory.Presieve.FamilyOfElements.{u1, u5, u4} D _inst_2 α (CategoryTheory.SheafOfTypes.val.{u1, u5, u4} D _inst_2 K ℱ) (CategoryTheory.Presieve.coverByImage.{u2, u3, u4, u5} C _inst_1 D _inst_2 G α)))
Case conversion may be inaccurate. Consider using '#align category_theory.cover_dense.types.pushforward_family CategoryTheory.CoverDense.Types.pushforwardFamilyₓ'. -/
/--
(Implementation). Given a section of `ℱ` on `X`, we can obtain a family of elements valued in `ℱ'`
that is defined on a cover generated by the images of `G`. -/
@[simp, nolint unused_arguments]
noncomputable def pushforwardFamily {X} (x : ℱ.obj (op X)) :
    FamilyOfElements ℱ'.val (coverByImage G X) := fun Y f hf =>
  ℱ'.val.map hf.some.lift.op <| α.app (op _) (ℱ.map hf.some.map.op x : _)
#align category_theory.cover_dense.types.pushforward_family CategoryTheory.CoverDense.Types.pushforwardFamily

include H

/- warning: category_theory.cover_dense.types.pushforward_family_compatible -> CategoryTheory.CoverDense.Types.pushforwardFamily_compatible is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u2} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u5, u4} D] {K : CategoryTheory.GrothendieckTopology.{u5, u4} D _inst_2} {G : CategoryTheory.Functor.{u3, u5, u2, u4} C _inst_1 D _inst_2}, (CategoryTheory.CoverDense.{u2, u3, u4, u5} C _inst_1 D _inst_2 K G) -> (forall [_inst_5 : CategoryTheory.Full.{u3, u5, u2, u4} C _inst_1 D _inst_2 G] {ℱ : CategoryTheory.Functor.{u5, u1, u4, succ u1} (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2) Type.{u1} CategoryTheory.types.{u1}} {ℱ' : CategoryTheory.SheafOfTypes.{u1, u5, u4} D _inst_2 K} (α : Quiver.Hom.{succ (max u2 u1), max u3 u1 u2 (succ u1)} (CategoryTheory.Functor.{u3, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u3 u1 u2 (succ u1)} (CategoryTheory.Functor.{u3, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u3 u1 u2 (succ u1)} (CategoryTheory.Functor.{u3, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u3, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.comp.{u3, u5, u1, u2, u4, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2) Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.op.{u3, u5, u2, u4} C _inst_1 D _inst_2 G) ℱ) (CategoryTheory.Functor.comp.{u3, u5, u1, u2, u4, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2) Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.op.{u3, u5, u2, u4} C _inst_1 D _inst_2 G) (CategoryTheory.SheafOfTypes.val.{u1, u5, u4} D _inst_2 K ℱ'))) {X : D} (x : CategoryTheory.Functor.obj.{u5, u1, u4, succ u1} (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2) Type.{u1} CategoryTheory.types.{u1} ℱ (Opposite.op.{succ u4} D X)), CategoryTheory.Presieve.FamilyOfElements.Compatible.{u1, u5, u4} D _inst_2 (CategoryTheory.SheafOfTypes.val.{u1, u5, u4} D _inst_2 K ℱ') X (CategoryTheory.Presieve.coverByImage.{u2, u3, u4, u5} C _inst_1 D _inst_2 G X) (CategoryTheory.CoverDense.Types.pushforwardFamily.{u1, u2, u3, u4, u5} C _inst_1 D _inst_2 K G _inst_5 ℱ ℱ' α X x))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} D] {K : CategoryTheory.GrothendieckTopology.{u4, u3} D _inst_2} {G : CategoryTheory.Functor.{u1, u4, u2, u3} C _inst_1 D _inst_2}, (CategoryTheory.CoverDense.{u2, u1, u3, u4} C _inst_1 D _inst_2 K G) -> (forall [_inst_5 : CategoryTheory.Full.{u1, u4, u2, u3} C _inst_1 D _inst_2 G] {ℱ : CategoryTheory.Functor.{u4, u5, u3, succ u5} (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) Type.{u5} CategoryTheory.types.{u5}} {ℱ' : CategoryTheory.SheafOfTypes.{u5, u4, u3} D _inst_2 K} (α : Quiver.Hom.{max (succ u5) (succ u2), max (max (max (succ u5) u2) u5) u1} (CategoryTheory.Functor.{u1, u5, u2, succ u5} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u5} CategoryTheory.types.{u5}) (CategoryTheory.CategoryStruct.toQuiver.{max u5 u2, max (max (succ u5) u2) u1} (CategoryTheory.Functor.{u1, u5, u2, succ u5} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u5} CategoryTheory.types.{u5}) (CategoryTheory.Category.toCategoryStruct.{max u5 u2, max (max (succ u5) u2) u1} (CategoryTheory.Functor.{u1, u5, u2, succ u5} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u5} CategoryTheory.types.{u5}) (CategoryTheory.Functor.category.{u1, u5, u2, succ u5} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u5} CategoryTheory.types.{u5}))) (CategoryTheory.Functor.comp.{u1, u4, u5, u2, u3, succ u5} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) Type.{u5} CategoryTheory.types.{u5} (CategoryTheory.Functor.op.{u1, u4, u2, u3} C _inst_1 D _inst_2 G) ℱ) (CategoryTheory.Functor.comp.{u1, u4, u5, u2, u3, succ u5} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) Type.{u5} CategoryTheory.types.{u5} (CategoryTheory.Functor.op.{u1, u4, u2, u3} C _inst_1 D _inst_2 G) (CategoryTheory.SheafOfTypes.val.{u5, u4, u3} D _inst_2 K ℱ'))) {X : D} (x : Prefunctor.obj.{succ u4, succ u5, u3, succ u5} (Opposite.{succ u3} D) (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} (Opposite.{succ u3} D) (CategoryTheory.Category.toCategoryStruct.{u4, u3} (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2))) Type.{u5} (CategoryTheory.CategoryStruct.toQuiver.{u5, succ u5} Type.{u5} (CategoryTheory.Category.toCategoryStruct.{u5, succ u5} Type.{u5} CategoryTheory.types.{u5})) (CategoryTheory.Functor.toPrefunctor.{u4, u5, u3, succ u5} (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) Type.{u5} CategoryTheory.types.{u5} ℱ) (Opposite.op.{succ u3} D X)), CategoryTheory.Presieve.FamilyOfElements.Compatible.{u5, u4, u3} D _inst_2 (CategoryTheory.SheafOfTypes.val.{u5, u4, u3} D _inst_2 K ℱ') X (CategoryTheory.Presieve.coverByImage.{u2, u1, u3, u4} C _inst_1 D _inst_2 G X) (CategoryTheory.CoverDense.Types.pushforwardFamily.{u5, u2, u1, u3, u4} C _inst_1 D _inst_2 K G ℱ ℱ' α X x))
Case conversion may be inaccurate. Consider using '#align category_theory.cover_dense.types.pushforward_family_compatible CategoryTheory.CoverDense.Types.pushforwardFamily_compatibleₓ'. -/
/-- (Implementation). The `pushforward_family` defined is compatible. -/
theorem pushforwardFamily_compatible {X} (x : ℱ.obj (op X)) : (pushforwardFamily α x).Compatible :=
  by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e
  apply H.ext
  intro Y f
  simp only [pushforward_family, ← functor_to_types.map_comp_apply, ← op_comp]
  change (ℱ.map _ ≫ α.app (op _) ≫ ℱ'.val.map _) _ = (ℱ.map _ ≫ α.app (op _) ≫ ℱ'.val.map _) _
  rw [← G.image_preimage (f ≫ g₁ ≫ _)]
  rw [← G.image_preimage (f ≫ g₂ ≫ _)]
  erw [← α.naturality (G.preimage _).op]
  erw [← α.naturality (G.preimage _).op]
  refine' congr_fun _ x
  simp only [Quiver.Hom.unop_op, functor.comp_map, ← op_comp, ← category.assoc, functor.op_map, ←
    ℱ.map_comp, G.image_preimage]
  congr 3
  simp [e]
#align category_theory.cover_dense.types.pushforward_family_compatible CategoryTheory.CoverDense.Types.pushforwardFamily_compatible

omit H

/- warning: category_theory.cover_dense.types.app_hom -> CategoryTheory.CoverDense.Types.appHom is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u2} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u5, u4} D] {K : CategoryTheory.GrothendieckTopology.{u5, u4} D _inst_2} {G : CategoryTheory.Functor.{u3, u5, u2, u4} C _inst_1 D _inst_2}, (CategoryTheory.CoverDense.{u2, u3, u4, u5} C _inst_1 D _inst_2 K G) -> (forall [_inst_5 : CategoryTheory.Full.{u3, u5, u2, u4} C _inst_1 D _inst_2 G] {ℱ : CategoryTheory.Functor.{u5, u1, u4, succ u1} (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2) Type.{u1} CategoryTheory.types.{u1}} {ℱ' : CategoryTheory.SheafOfTypes.{u1, u5, u4} D _inst_2 K}, (Quiver.Hom.{succ (max u2 u1), max u3 u1 u2 (succ u1)} (CategoryTheory.Functor.{u3, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u3 u1 u2 (succ u1)} (CategoryTheory.Functor.{u3, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u3 u1 u2 (succ u1)} (CategoryTheory.Functor.{u3, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u3, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.comp.{u3, u5, u1, u2, u4, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2) Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.op.{u3, u5, u2, u4} C _inst_1 D _inst_2 G) ℱ) (CategoryTheory.Functor.comp.{u3, u5, u1, u2, u4, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2) Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.op.{u3, u5, u2, u4} C _inst_1 D _inst_2 G) (CategoryTheory.SheafOfTypes.val.{u1, u5, u4} D _inst_2 K ℱ'))) -> (forall (X : D), Quiver.Hom.{succ u1, succ u1} Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.obj.{u5, u1, u4, succ u1} (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2) Type.{u1} CategoryTheory.types.{u1} ℱ (Opposite.op.{succ u4} D X)) (CategoryTheory.Functor.obj.{u5, u1, u4, succ u1} (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2) Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.SheafOfTypes.val.{u1, u5, u4} D _inst_2 K ℱ') (Opposite.op.{succ u4} D X))))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u2} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u5, u4} D] {K : CategoryTheory.GrothendieckTopology.{u5, u4} D _inst_2} {G : CategoryTheory.Functor.{u3, u5, u2, u4} C _inst_1 D _inst_2}, (CategoryTheory.CoverDense.{u2, u3, u4, u5} C _inst_1 D _inst_2 K G) -> (forall [_inst_5 : CategoryTheory.Full.{u3, u5, u2, u4} C _inst_1 D _inst_2 G] {ℱ : CategoryTheory.Functor.{u5, u1, u4, succ u1} (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2) Type.{u1} CategoryTheory.types.{u1}} {ℱ' : CategoryTheory.SheafOfTypes.{u1, u5, u4} D _inst_2 K}, (Quiver.Hom.{max (succ u1) (succ u2), max (max (max (succ u1) u2) u1) u3} (CategoryTheory.Functor.{u3, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, max (max (succ u1) u2) u3} (CategoryTheory.Functor.{u3, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u1 u2, max (max (succ u1) u2) u3} (CategoryTheory.Functor.{u3, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u3, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.comp.{u3, u5, u1, u2, u4, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2) Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.op.{u3, u5, u2, u4} C _inst_1 D _inst_2 G) ℱ) (CategoryTheory.Functor.comp.{u3, u5, u1, u2, u4, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2) Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.op.{u3, u5, u2, u4} C _inst_1 D _inst_2 G) (CategoryTheory.SheafOfTypes.val.{u1, u5, u4} D _inst_2 K ℱ'))) -> (forall (X : D), Quiver.Hom.{succ u1, succ u1} Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (Prefunctor.obj.{succ u5, succ u1, u4, succ u1} (Opposite.{succ u4} D) (CategoryTheory.CategoryStruct.toQuiver.{u5, u4} (Opposite.{succ u4} D) (CategoryTheory.Category.toCategoryStruct.{u5, u4} (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u5, u1, u4, succ u1} (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2) Type.{u1} CategoryTheory.types.{u1} ℱ) (Opposite.op.{succ u4} D X)) (Prefunctor.obj.{succ u5, succ u1, u4, succ u1} (Opposite.{succ u4} D) (CategoryTheory.CategoryStruct.toQuiver.{u5, u4} (Opposite.{succ u4} D) (CategoryTheory.Category.toCategoryStruct.{u5, u4} (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u5, u1, u4, succ u1} (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2) Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.SheafOfTypes.val.{u1, u5, u4} D _inst_2 K ℱ')) (Opposite.op.{succ u4} D X))))
Case conversion may be inaccurate. Consider using '#align category_theory.cover_dense.types.app_hom CategoryTheory.CoverDense.Types.appHomₓ'. -/
/-- (Implementation). The morphism `ℱ(X) ⟶ ℱ'(X)` given by gluing the `pushforward_family`. -/
noncomputable def appHom (X : D) : ℱ.obj (op X) ⟶ ℱ'.val.obj (op X) := fun x =>
  (ℱ'.cond _ (H.is_cover X)).amalgamate (pushforwardFamily α x) (pushforwardFamily_compatible H α x)
#align category_theory.cover_dense.types.app_hom CategoryTheory.CoverDense.Types.appHom

/- warning: category_theory.cover_dense.types.pushforward_family_apply -> CategoryTheory.CoverDense.Types.pushforwardFamily_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.cover_dense.types.pushforward_family_apply CategoryTheory.CoverDense.Types.pushforwardFamily_applyₓ'. -/
@[simp]
theorem pushforwardFamily_apply {X} (x : ℱ.obj (op X)) {Y : C} (f : G.obj Y ⟶ X) :
    pushforwardFamily α x f (Presieve.in_coverByImage G f) = α.app (op Y) (ℱ.map f.op x) :=
  by
  unfold pushforward_family
  refine' congr_fun _ x
  rw [← G.image_preimage (Nonempty.some _ : presieve.cover_by_image_structure _ _).lift]
  change ℱ.map _ ≫ α.app (op _) ≫ ℱ'.val.map _ = ℱ.map f.op ≫ α.app (op Y)
  erw [← α.naturality (G.preimage _).op]
  simp only [← functor.map_comp, ← category.assoc, functor.comp_map, G.image_preimage, G.op_map,
    Quiver.Hom.unop_op, ← op_comp, presieve.cover_by_image_structure.fac]
#align category_theory.cover_dense.types.pushforward_family_apply CategoryTheory.CoverDense.Types.pushforwardFamily_apply

/- warning: category_theory.cover_dense.types.app_hom_restrict -> CategoryTheory.CoverDense.Types.appHom_restrict is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.cover_dense.types.app_hom_restrict CategoryTheory.CoverDense.Types.appHom_restrictₓ'. -/
@[simp]
theorem appHom_restrict {X : D} {Y : C} (f : op X ⟶ op (G.obj Y)) (x) :
    ℱ'.val.map f (appHom H α X x) = α.app (op Y) (ℱ.map f x) :=
  by
  refine'
    ((ℱ'.cond _ (H.is_cover X)).valid_glue (pushforward_family_compatible H α x) f.unop
          (presieve.in_cover_by_image G f.unop)).trans
      _
  apply pushforward_family_apply
#align category_theory.cover_dense.types.app_hom_restrict CategoryTheory.CoverDense.Types.appHom_restrict

/- warning: category_theory.cover_dense.types.app_hom_valid_glue -> CategoryTheory.CoverDense.Types.appHom_valid_glue is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.cover_dense.types.app_hom_valid_glue CategoryTheory.CoverDense.Types.appHom_valid_glueₓ'. -/
@[simp]
theorem appHom_valid_glue {X : D} {Y : C} (f : op X ⟶ op (G.obj Y)) :
    appHom H α X ≫ ℱ'.val.map f = ℱ.map f ≫ α.app (op Y) :=
  by
  ext
  apply app_hom_restrict
#align category_theory.cover_dense.types.app_hom_valid_glue CategoryTheory.CoverDense.Types.appHom_valid_glue

/- warning: category_theory.cover_dense.types.app_iso -> CategoryTheory.CoverDense.Types.appIso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u2} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u5, u4} D] {K : CategoryTheory.GrothendieckTopology.{u5, u4} D _inst_2} {G : CategoryTheory.Functor.{u3, u5, u2, u4} C _inst_1 D _inst_2}, (CategoryTheory.CoverDense.{u2, u3, u4, u5} C _inst_1 D _inst_2 K G) -> (forall [_inst_5 : CategoryTheory.Full.{u3, u5, u2, u4} C _inst_1 D _inst_2 G] {ℱ : CategoryTheory.SheafOfTypes.{u1, u5, u4} D _inst_2 K} {ℱ' : CategoryTheory.SheafOfTypes.{u1, u5, u4} D _inst_2 K}, (CategoryTheory.Iso.{max u2 u1, max u3 u1 u2 (succ u1)} (CategoryTheory.Functor.{u3, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u3, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.comp.{u3, u5, u1, u2, u4, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2) Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.op.{u3, u5, u2, u4} C _inst_1 D _inst_2 G) (CategoryTheory.SheafOfTypes.val.{u1, u5, u4} D _inst_2 K ℱ)) (CategoryTheory.Functor.comp.{u3, u5, u1, u2, u4, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2) Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.op.{u3, u5, u2, u4} C _inst_1 D _inst_2 G) (CategoryTheory.SheafOfTypes.val.{u1, u5, u4} D _inst_2 K ℱ'))) -> (forall (X : D), CategoryTheory.Iso.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.obj.{u5, u1, u4, succ u1} (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2) Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.SheafOfTypes.val.{u1, u5, u4} D _inst_2 K ℱ) (Opposite.op.{succ u4} D X)) (CategoryTheory.Functor.obj.{u5, u1, u4, succ u1} (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2) Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.SheafOfTypes.val.{u1, u5, u4} D _inst_2 K ℱ') (Opposite.op.{succ u4} D X))))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u2} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u5, u4} D] {K : CategoryTheory.GrothendieckTopology.{u5, u4} D _inst_2} {G : CategoryTheory.Functor.{u3, u5, u2, u4} C _inst_1 D _inst_2}, (CategoryTheory.CoverDense.{u2, u3, u4, u5} C _inst_1 D _inst_2 K G) -> (forall [_inst_5 : CategoryTheory.Full.{u3, u5, u2, u4} C _inst_1 D _inst_2 G] {ℱ : CategoryTheory.SheafOfTypes.{u1, u5, u4} D _inst_2 K} {ℱ' : CategoryTheory.SheafOfTypes.{u1, u5, u4} D _inst_2 K}, (CategoryTheory.Iso.{max u1 u2, max (max (max (succ u1) u2) u1) u3} (CategoryTheory.Functor.{u3, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u3, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.comp.{u3, u5, u1, u2, u4, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2) Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.op.{u3, u5, u2, u4} C _inst_1 D _inst_2 G) (CategoryTheory.SheafOfTypes.val.{u1, u5, u4} D _inst_2 K ℱ)) (CategoryTheory.Functor.comp.{u3, u5, u1, u2, u4, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u3, u2} C _inst_1) (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2) Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.op.{u3, u5, u2, u4} C _inst_1 D _inst_2 G) (CategoryTheory.SheafOfTypes.val.{u1, u5, u4} D _inst_2 K ℱ'))) -> (forall (X : D), CategoryTheory.Iso.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} (Prefunctor.obj.{succ u5, succ u1, u4, succ u1} (Opposite.{succ u4} D) (CategoryTheory.CategoryStruct.toQuiver.{u5, u4} (Opposite.{succ u4} D) (CategoryTheory.Category.toCategoryStruct.{u5, u4} (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u5, u1, u4, succ u1} (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2) Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.SheafOfTypes.val.{u1, u5, u4} D _inst_2 K ℱ)) (Opposite.op.{succ u4} D X)) (Prefunctor.obj.{succ u5, succ u1, u4, succ u1} (Opposite.{succ u4} D) (CategoryTheory.CategoryStruct.toQuiver.{u5, u4} (Opposite.{succ u4} D) (CategoryTheory.Category.toCategoryStruct.{u5, u4} (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u5, u1, u4, succ u1} (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u5, u4} D _inst_2) Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.SheafOfTypes.val.{u1, u5, u4} D _inst_2 K ℱ')) (Opposite.op.{succ u4} D X))))
Case conversion may be inaccurate. Consider using '#align category_theory.cover_dense.types.app_iso CategoryTheory.CoverDense.Types.appIsoₓ'. -/
/--
(Implementation). The maps given in `app_iso` is inverse to each other and gives a `ℱ(X) ≅ ℱ'(X)`.
-/
@[simps]
noncomputable def appIso {ℱ ℱ' : SheafOfTypes.{v} K} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) (X : D) :
    ℱ.val.obj (op X) ≅ ℱ'.val.obj (op X)
    where
  Hom := appHom H i.Hom X
  inv := appHom H i.inv X
  hom_inv_id' := by
    ext x
    apply H.ext
    intro Y f
    simp
  inv_hom_id' := by
    ext x
    apply H.ext
    intro Y f
    simp
#align category_theory.cover_dense.types.app_iso CategoryTheory.CoverDense.Types.appIso

#print CategoryTheory.CoverDense.Types.presheafHom /-
/-- Given an natural transformation `G ⋙ ℱ ⟶ G ⋙ ℱ'` between presheaves of types, where `G` is full
and cover-dense, and `ℱ'` is a sheaf, we may obtain a natural transformation between sheaves.
-/
@[simps]
noncomputable def presheafHom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) : ℱ ⟶ ℱ'.val
    where
  app X := appHom H α (unop X)
  naturality' X Y f := by
    ext x
    apply H.ext ℱ' (unop Y)
    intro Y' f'
    simp only [app_hom_restrict, types_comp_apply, ← functor_to_types.map_comp_apply]
    rw [app_hom_restrict H α (f ≫ f'.op : op (unop X) ⟶ _)]
#align category_theory.cover_dense.types.presheaf_hom CategoryTheory.CoverDense.Types.presheafHom
-/

#print CategoryTheory.CoverDense.Types.presheafIso /-
/-- Given an natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of types, where `G` is full and
cover-dense, and `ℱ, ℱ'` are sheaves, we may obtain a natural isomorphism between presheaves.
-/
@[simps]
noncomputable def presheafIso {ℱ ℱ' : SheafOfTypes.{v} K} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) :
    ℱ.val ≅ ℱ'.val :=
  NatIso.ofComponents (fun X => appIso H i (unop X)) (presheafHom H i.Hom).naturality
#align category_theory.cover_dense.types.presheaf_iso CategoryTheory.CoverDense.Types.presheafIso
-/

#print CategoryTheory.CoverDense.Types.sheafIso /-
/-- Given an natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of types, where `G` is full and
cover-dense, and `ℱ, ℱ'` are sheaves, we may obtain a natural isomorphism between sheaves.
-/
@[simps]
noncomputable def sheafIso {ℱ ℱ' : SheafOfTypes.{v} K} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) : ℱ ≅ ℱ'
    where
  Hom := ⟨(presheafIso H i).Hom⟩
  inv := ⟨(presheafIso H i).inv⟩
  hom_inv_id' := by
    ext1
    apply (presheaf_iso H i).hom_inv_id
  inv_hom_id' := by
    ext1
    apply (presheaf_iso H i).inv_hom_id
#align category_theory.cover_dense.types.sheaf_iso CategoryTheory.CoverDense.Types.sheafIso
-/

end Types

open Types

variable {ℱ : Dᵒᵖ ⥤ A} {ℱ' : Sheaf K A}

/- warning: category_theory.cover_dense.sheaf_coyoneda_hom -> CategoryTheory.CoverDense.sheafCoyonedaHom is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.cover_dense.sheaf_coyoneda_hom CategoryTheory.CoverDense.sheafCoyonedaHomₓ'. -/
/-- (Implementation). The sheaf map given in `types.sheaf_hom` is natural in terms of `X`. -/
@[simps]
noncomputable def sheafCoyonedaHom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) :
    coyoneda ⋙ (whiskeringLeft Dᵒᵖ A (Type _)).obj ℱ ⟶
      coyoneda ⋙ (whiskeringLeft Dᵒᵖ A (Type _)).obj ℱ'.val
    where
  app X := presheafHom H (homOver α (unop X))
  naturality' X Y f := by
    ext (U x)
    change
      app_hom H (hom_over α (unop Y)) (unop U) (f.unop ≫ x) =
        f.unop ≫ app_hom H (hom_over α (unop X)) (unop U) x
    symm
    apply sheaf_eq_amalgamation
    apply H.is_cover
    intro Y' f' hf'
    change unop X ⟶ ℱ.obj (op (unop _)) at x
    dsimp
    simp only [pushforward_family, functor.comp_map, coyoneda_obj_map, hom_over_app, category.assoc]
    congr 1
    conv_lhs => rw [← hf'.some.fac]
    simp only [← category.assoc, op_comp, functor.map_comp]
    congr 1
    refine' (app_hom_restrict H (hom_over α (unop X)) hf'.some.map.op x).trans _
    simp
#align category_theory.cover_dense.sheaf_coyoneda_hom CategoryTheory.CoverDense.sheafCoyonedaHom

include H

#print CategoryTheory.CoverDense.sheafYonedaHom /-
/--
(Implementation). `sheaf_coyoneda_hom` but the order of the arguments of the functor are swapped.
-/
noncomputable def sheafYonedaHom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) : ℱ ⋙ yoneda ⟶ ℱ'.val ⋙ yoneda :=
  by
  let α := sheaf_coyoneda_hom H α
  refine'
    { app := _
      naturality' := _ }
  · intro U
    refine'
      { app := fun X => (α.app X).app U
        naturality' := fun X Y f => by simpa using congr_app (α.naturality f) U }
  · intro U V i
    ext (X x)
    exact congr_fun ((α.app X).naturality i) x
#align category_theory.cover_dense.sheaf_yoneda_hom CategoryTheory.CoverDense.sheafYonedaHom
-/

omit H

#print CategoryTheory.CoverDense.sheafHom /-
/-- Given an natural transformation `G ⋙ ℱ ⟶ G ⋙ ℱ'` between presheaves of arbitrary category,
where `G` is full and cover-dense, and `ℱ'` is a sheaf, we may obtain a natural transformation
between presheaves.
-/
noncomputable def sheafHom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) : ℱ ⟶ ℱ'.val :=
  let α' := sheafYonedaHom H α
  { app := fun X => yoneda.preimage (α'.app X)
    naturality' := fun X Y f => yoneda.map_injective (by simpa using α'.naturality f) }
#align category_theory.cover_dense.sheaf_hom CategoryTheory.CoverDense.sheafHom
-/

include H

#print CategoryTheory.CoverDense.presheafIso /-
/-- Given an natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of arbitrary category,
where `G` is full and cover-dense, and `ℱ', ℱ` are sheaves,
we may obtain a natural isomorphism between presheaves.
-/
@[simps]
noncomputable def presheafIso {ℱ ℱ' : Sheaf K A} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) :
    ℱ.val ≅ ℱ'.val :=
  by
  have : ∀ X : Dᵒᵖ, is_iso ((sheaf_hom H i.hom).app X) :=
    by
    intro X
    apply is_iso_of_reflects_iso _ yoneda
    use (sheaf_yoneda_hom H i.inv).app X
    constructor <;> ext x : 2 <;>
      simp only [sheaf_hom, nat_trans.comp_app, nat_trans.id_app, functor.image_preimage]
    exact ((presheaf_iso H (iso_over i (unop x))).app X).hom_inv_id
    exact ((presheaf_iso H (iso_over i (unop x))).app X).inv_hom_id
    infer_instance
  haveI : is_iso (sheaf_hom H i.hom) := by apply nat_iso.is_iso_of_is_iso_app
  apply as_iso (sheaf_hom H i.hom)
#align category_theory.cover_dense.presheaf_iso CategoryTheory.CoverDense.presheafIso
-/

omit H

#print CategoryTheory.CoverDense.sheafIso /-
/-- Given an natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of arbitrary category,
where `G` is full and cover-dense, and `ℱ', ℱ` are sheaves,
we may obtain a natural isomorphism between presheaves.
-/
@[simps]
noncomputable def sheafIso {ℱ ℱ' : Sheaf K A} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) : ℱ ≅ ℱ'
    where
  Hom := ⟨(presheafIso H i).Hom⟩
  inv := ⟨(presheafIso H i).inv⟩
  hom_inv_id' := by
    ext1
    apply (presheaf_iso H i).hom_inv_id
  inv_hom_id' := by
    ext1
    apply (presheaf_iso H i).inv_hom_id
#align category_theory.cover_dense.sheaf_iso CategoryTheory.CoverDense.sheafIso
-/

/- warning: category_theory.cover_dense.sheaf_hom_restrict_eq -> CategoryTheory.CoverDense.sheafHom_restrict_eq is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} D] {K : CategoryTheory.GrothendieckTopology.{u4, u3} D _inst_2} {A : Type.{u5}} [_inst_4 : CategoryTheory.Category.{u6, u5} A] {G : CategoryTheory.Functor.{u2, u4, u1, u3} C _inst_1 D _inst_2} (H : CategoryTheory.CoverDense.{u1, u2, u3, u4} C _inst_1 D _inst_2 K G) [_inst_5 : CategoryTheory.Full.{u2, u4, u1, u3} C _inst_1 D _inst_2 G] {ℱ : CategoryTheory.Functor.{u4, u6, u3, u5} (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) A _inst_4} {ℱ' : CategoryTheory.Sheaf.{u4, u6, u3, u5} D _inst_2 K A _inst_4} (α : Quiver.Hom.{succ (max u1 u6), max u2 u6 u1 u5} (CategoryTheory.Functor.{u2, u6, u1, u5} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) A _inst_4) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u6, max u2 u6 u1 u5} (CategoryTheory.Functor.{u2, u6, u1, u5} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) A _inst_4) (CategoryTheory.Category.toCategoryStruct.{max u1 u6, max u2 u6 u1 u5} (CategoryTheory.Functor.{u2, u6, u1, u5} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) A _inst_4) (CategoryTheory.Functor.category.{u2, u6, u1, u5} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) A _inst_4))) (CategoryTheory.Functor.comp.{u2, u4, u6, u1, u3, u5} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) A _inst_4 (CategoryTheory.Functor.op.{u2, u4, u1, u3} C _inst_1 D _inst_2 G) ℱ) (CategoryTheory.Functor.comp.{u2, u4, u6, u1, u3, u5} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) A _inst_4 (CategoryTheory.Functor.op.{u2, u4, u1, u3} C _inst_1 D _inst_2 G) (CategoryTheory.Sheaf.val.{u4, u6, u3, u5} D _inst_2 K A _inst_4 ℱ'))), Eq.{succ (max u1 u6)} (Quiver.Hom.{succ (max u1 u6), max u2 u6 u1 u5} (CategoryTheory.Functor.{u2, u6, u1, u5} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) A _inst_4) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u6, max u2 u6 u1 u5} (CategoryTheory.Functor.{u2, u6, u1, u5} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) A _inst_4) (CategoryTheory.Category.toCategoryStruct.{max u1 u6, max u2 u6 u1 u5} (CategoryTheory.Functor.{u2, u6, u1, u5} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) A _inst_4) (CategoryTheory.Functor.category.{u2, u6, u1, u5} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) A _inst_4))) (CategoryTheory.Functor.comp.{u2, u4, u6, u1, u3, u5} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) A _inst_4 (CategoryTheory.Functor.op.{u2, u4, u1, u3} C _inst_1 D _inst_2 G) ℱ) (CategoryTheory.Functor.comp.{u2, u4, u6, u1, u3, u5} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) A _inst_4 (CategoryTheory.Functor.op.{u2, u4, u1, u3} C _inst_1 D _inst_2 G) (CategoryTheory.Sheaf.val.{u4, u6, u3, u5} D _inst_2 K A _inst_4 ℱ'))) (CategoryTheory.whiskerLeft.{u1, u2, u3, u4, u5, u6} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) A _inst_4 (CategoryTheory.Functor.op.{u2, u4, u1, u3} C _inst_1 D _inst_2 G) ℱ (CategoryTheory.Sheaf.val.{u4, u6, u3, u5} D _inst_2 K A _inst_4 ℱ') (CategoryTheory.CoverDense.sheafHom.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 K A _inst_4 G H _inst_5 ℱ ℱ' α)) α
but is expected to have type
  forall {C : Type.{u6}} [_inst_1 : CategoryTheory.Category.{u3, u6} C] {D : Type.{u1}} [_inst_2 : CategoryTheory.Category.{u2, u1} D] {K : CategoryTheory.GrothendieckTopology.{u2, u1} D _inst_2} {A : Type.{u4}} [_inst_4 : CategoryTheory.Category.{u5, u4} A] {G : CategoryTheory.Functor.{u3, u2, u6, u1} C _inst_1 D _inst_2} (H : CategoryTheory.CoverDense.{u6, u3, u1, u2} C _inst_1 D _inst_2 K G) [_inst_5 : CategoryTheory.Full.{u3, u2, u6, u1} C _inst_1 D _inst_2 G] {ℱ : CategoryTheory.Functor.{u2, u5, u1, u4} (Opposite.{succ u1} D) (CategoryTheory.Category.opposite.{u2, u1} D _inst_2) A _inst_4} {ℱ' : CategoryTheory.Sheaf.{u2, u5, u1, u4} D _inst_2 K A _inst_4} (α : Quiver.Hom.{max (succ u6) (succ u5), max (max (max u4 u6) u5) u3} (CategoryTheory.Functor.{u3, u5, u6, u4} (Opposite.{succ u6} C) (CategoryTheory.Category.opposite.{u3, u6} C _inst_1) A _inst_4) (CategoryTheory.CategoryStruct.toQuiver.{max u6 u5, max (max (max u6 u3) u4) u5} (CategoryTheory.Functor.{u3, u5, u6, u4} (Opposite.{succ u6} C) (CategoryTheory.Category.opposite.{u3, u6} C _inst_1) A _inst_4) (CategoryTheory.Category.toCategoryStruct.{max u6 u5, max (max (max u6 u3) u4) u5} (CategoryTheory.Functor.{u3, u5, u6, u4} (Opposite.{succ u6} C) (CategoryTheory.Category.opposite.{u3, u6} C _inst_1) A _inst_4) (CategoryTheory.Functor.category.{u3, u5, u6, u4} (Opposite.{succ u6} C) (CategoryTheory.Category.opposite.{u3, u6} C _inst_1) A _inst_4))) (CategoryTheory.Functor.comp.{u3, u2, u5, u6, u1, u4} (Opposite.{succ u6} C) (CategoryTheory.Category.opposite.{u3, u6} C _inst_1) (Opposite.{succ u1} D) (CategoryTheory.Category.opposite.{u2, u1} D _inst_2) A _inst_4 (CategoryTheory.Functor.op.{u3, u2, u6, u1} C _inst_1 D _inst_2 G) ℱ) (CategoryTheory.Functor.comp.{u3, u2, u5, u6, u1, u4} (Opposite.{succ u6} C) (CategoryTheory.Category.opposite.{u3, u6} C _inst_1) (Opposite.{succ u1} D) (CategoryTheory.Category.opposite.{u2, u1} D _inst_2) A _inst_4 (CategoryTheory.Functor.op.{u3, u2, u6, u1} C _inst_1 D _inst_2 G) (CategoryTheory.Sheaf.val.{u2, u5, u1, u4} D _inst_2 K A _inst_4 ℱ'))), Eq.{max (succ u6) (succ u5)} (Quiver.Hom.{max (succ u6) (succ u5), max (max (max u4 u6) u5) u3} (CategoryTheory.Functor.{u3, u5, u6, u4} (Opposite.{succ u6} C) (CategoryTheory.Category.opposite.{u3, u6} C _inst_1) A _inst_4) (CategoryTheory.CategoryStruct.toQuiver.{max u6 u5, max (max (max u6 u4) u3) u5} (CategoryTheory.Functor.{u3, u5, u6, u4} (Opposite.{succ u6} C) (CategoryTheory.Category.opposite.{u3, u6} C _inst_1) A _inst_4) (CategoryTheory.Category.toCategoryStruct.{max u6 u5, max (max (max u6 u4) u3) u5} (CategoryTheory.Functor.{u3, u5, u6, u4} (Opposite.{succ u6} C) (CategoryTheory.Category.opposite.{u3, u6} C _inst_1) A _inst_4) (CategoryTheory.Functor.category.{u3, u5, u6, u4} (Opposite.{succ u6} C) (CategoryTheory.Category.opposite.{u3, u6} C _inst_1) A _inst_4))) (CategoryTheory.Functor.comp.{u3, u2, u5, u6, u1, u4} (Opposite.{succ u6} C) (CategoryTheory.Category.opposite.{u3, u6} C _inst_1) (Opposite.{succ u1} D) (CategoryTheory.Category.opposite.{u2, u1} D _inst_2) A _inst_4 (CategoryTheory.Functor.op.{u3, u2, u6, u1} C _inst_1 D _inst_2 G) ℱ) (CategoryTheory.Functor.comp.{u3, u2, u5, u6, u1, u4} (Opposite.{succ u6} C) (CategoryTheory.Category.opposite.{u3, u6} C _inst_1) (Opposite.{succ u1} D) (CategoryTheory.Category.opposite.{u2, u1} D _inst_2) A _inst_4 (CategoryTheory.Functor.op.{u3, u2, u6, u1} C _inst_1 D _inst_2 G) (CategoryTheory.Sheaf.val.{u2, u5, u1, u4} D _inst_2 K A _inst_4 ℱ'))) (CategoryTheory.whiskerLeft.{u6, u3, u1, u2, u4, u5} (Opposite.{succ u6} C) (CategoryTheory.Category.opposite.{u3, u6} C _inst_1) (Opposite.{succ u1} D) (CategoryTheory.Category.opposite.{u2, u1} D _inst_2) A _inst_4 (CategoryTheory.Functor.op.{u3, u2, u6, u1} C _inst_1 D _inst_2 G) ℱ (CategoryTheory.Sheaf.val.{u2, u5, u1, u4} D _inst_2 K A _inst_4 ℱ') (CategoryTheory.CoverDense.sheafHom.{u6, u3, u1, u2, u4, u5} C _inst_1 D _inst_2 K A _inst_4 G H _inst_5 ℱ ℱ' α)) α
Case conversion may be inaccurate. Consider using '#align category_theory.cover_dense.sheaf_hom_restrict_eq CategoryTheory.CoverDense.sheafHom_restrict_eqₓ'. -/
/-- The constructed `sheaf_hom α` is equal to `α` when restricted onto `C`.
-/
theorem sheafHom_restrict_eq (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) : whiskerLeft G.op (sheafHom H α) = α :=
  by
  ext X
  apply yoneda.map_injective
  ext U
  erw [yoneda.image_preimage]
  symm
  change (show (ℱ'.val ⋙ coyoneda.obj (op (unop U))).obj (op (G.obj (unop X))) from _) = _
  apply sheaf_eq_amalgamation ℱ' (H.is_cover _)
  intro Y f hf
  conv_lhs => rw [← hf.some.fac]
  simp only [pushforward_family, functor.comp_map, yoneda_map_app, coyoneda_obj_map, op_comp,
    functor_to_types.map_comp_apply, hom_over_app, ← category.assoc]
  congr 1
  simp only [category.assoc]
  congr 1
  rw [← G.image_preimage hf.some.map]
  symm
  apply α.naturality (G.preimage hf.some.map).op
  infer_instance
#align category_theory.cover_dense.sheaf_hom_restrict_eq CategoryTheory.CoverDense.sheafHom_restrict_eq

/- warning: category_theory.cover_dense.sheaf_hom_eq -> CategoryTheory.CoverDense.sheafHom_eq is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} D] {K : CategoryTheory.GrothendieckTopology.{u4, u3} D _inst_2} {A : Type.{u5}} [_inst_4 : CategoryTheory.Category.{u6, u5} A] {G : CategoryTheory.Functor.{u2, u4, u1, u3} C _inst_1 D _inst_2} (H : CategoryTheory.CoverDense.{u1, u2, u3, u4} C _inst_1 D _inst_2 K G) [_inst_5 : CategoryTheory.Full.{u2, u4, u1, u3} C _inst_1 D _inst_2 G] {ℱ : CategoryTheory.Functor.{u4, u6, u3, u5} (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) A _inst_4} {ℱ' : CategoryTheory.Sheaf.{u4, u6, u3, u5} D _inst_2 K A _inst_4} (α : Quiver.Hom.{succ (max u3 u6), max u4 u6 u3 u5} (CategoryTheory.Functor.{u4, u6, u3, u5} (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) A _inst_4) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u6, max u4 u6 u3 u5} (CategoryTheory.Functor.{u4, u6, u3, u5} (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) A _inst_4) (CategoryTheory.Category.toCategoryStruct.{max u3 u6, max u4 u6 u3 u5} (CategoryTheory.Functor.{u4, u6, u3, u5} (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) A _inst_4) (CategoryTheory.Functor.category.{u4, u6, u3, u5} (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) A _inst_4))) ℱ (CategoryTheory.Sheaf.val.{u4, u6, u3, u5} D _inst_2 K A _inst_4 ℱ')), Eq.{succ (max u3 u6)} (Quiver.Hom.{succ (max u3 u6), max u4 u6 u3 u5} (CategoryTheory.Functor.{u4, u6, u3, u5} (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) A _inst_4) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u6, max u4 u6 u3 u5} (CategoryTheory.Functor.{u4, u6, u3, u5} (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) A _inst_4) (CategoryTheory.Category.toCategoryStruct.{max u3 u6, max u4 u6 u3 u5} (CategoryTheory.Functor.{u4, u6, u3, u5} (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) A _inst_4) (CategoryTheory.Functor.category.{u4, u6, u3, u5} (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) A _inst_4))) ℱ (CategoryTheory.Sheaf.val.{u4, u6, u3, u5} D _inst_2 K A _inst_4 ℱ')) (CategoryTheory.CoverDense.sheafHom.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 K A _inst_4 G H _inst_5 ℱ ℱ' (CategoryTheory.whiskerLeft.{u1, u2, u3, u4, u5, u6} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) A _inst_4 (CategoryTheory.Functor.op.{u2, u4, u1, u3} C _inst_1 D _inst_2 G) ℱ (CategoryTheory.Sheaf.val.{u4, u6, u3, u5} D _inst_2 K A _inst_4 ℱ') α)) α
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u6}} [_inst_2 : CategoryTheory.Category.{u4, u6} D] {K : CategoryTheory.GrothendieckTopology.{u4, u6} D _inst_2} {A : Type.{u3}} [_inst_4 : CategoryTheory.Category.{u5, u3} A] {G : CategoryTheory.Functor.{u1, u4, u2, u6} C _inst_1 D _inst_2} (H : CategoryTheory.CoverDense.{u2, u1, u6, u4} C _inst_1 D _inst_2 K G) [_inst_5 : CategoryTheory.Full.{u1, u4, u2, u6} C _inst_1 D _inst_2 G] {ℱ : CategoryTheory.Functor.{u4, u5, u6, u3} (Opposite.{succ u6} D) (CategoryTheory.Category.opposite.{u4, u6} D _inst_2) A _inst_4} {ℱ' : CategoryTheory.Sheaf.{u4, u5, u6, u3} D _inst_2 K A _inst_4} (α : Quiver.Hom.{max (succ u6) (succ u5), max (max (max u6 u4) u3) u5} (CategoryTheory.Functor.{u4, u5, u6, u3} (Opposite.{succ u6} D) (CategoryTheory.Category.opposite.{u4, u6} D _inst_2) A _inst_4) (CategoryTheory.CategoryStruct.toQuiver.{max u6 u5, max (max (max u6 u4) u3) u5} (CategoryTheory.Functor.{u4, u5, u6, u3} (Opposite.{succ u6} D) (CategoryTheory.Category.opposite.{u4, u6} D _inst_2) A _inst_4) (CategoryTheory.Category.toCategoryStruct.{max u6 u5, max (max (max u6 u4) u3) u5} (CategoryTheory.Functor.{u4, u5, u6, u3} (Opposite.{succ u6} D) (CategoryTheory.Category.opposite.{u4, u6} D _inst_2) A _inst_4) (CategoryTheory.Functor.category.{u4, u5, u6, u3} (Opposite.{succ u6} D) (CategoryTheory.Category.opposite.{u4, u6} D _inst_2) A _inst_4))) ℱ (CategoryTheory.Sheaf.val.{u4, u5, u6, u3} D _inst_2 K A _inst_4 ℱ')), Eq.{max (succ u6) (succ u5)} (Quiver.Hom.{max (succ u6) (succ u5), max (max (max u6 u4) u3) u5} (CategoryTheory.Functor.{u4, u5, u6, u3} (Opposite.{succ u6} D) (CategoryTheory.Category.opposite.{u4, u6} D _inst_2) A _inst_4) (CategoryTheory.CategoryStruct.toQuiver.{max u6 u5, max (max (max u6 u4) u3) u5} (CategoryTheory.Functor.{u4, u5, u6, u3} (Opposite.{succ u6} D) (CategoryTheory.Category.opposite.{u4, u6} D _inst_2) A _inst_4) (CategoryTheory.Category.toCategoryStruct.{max u6 u5, max (max (max u6 u4) u3) u5} (CategoryTheory.Functor.{u4, u5, u6, u3} (Opposite.{succ u6} D) (CategoryTheory.Category.opposite.{u4, u6} D _inst_2) A _inst_4) (CategoryTheory.Functor.category.{u4, u5, u6, u3} (Opposite.{succ u6} D) (CategoryTheory.Category.opposite.{u4, u6} D _inst_2) A _inst_4))) ℱ (CategoryTheory.Sheaf.val.{u4, u5, u6, u3} D _inst_2 K A _inst_4 ℱ')) (CategoryTheory.CoverDense.sheafHom.{u2, u1, u6, u4, u3, u5} C _inst_1 D _inst_2 K A _inst_4 G H _inst_5 ℱ ℱ' (CategoryTheory.whiskerLeft.{u2, u1, u6, u4, u3, u5} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (Opposite.{succ u6} D) (CategoryTheory.Category.opposite.{u4, u6} D _inst_2) A _inst_4 (CategoryTheory.Functor.op.{u1, u4, u2, u6} C _inst_1 D _inst_2 G) ℱ (CategoryTheory.Sheaf.val.{u4, u5, u6, u3} D _inst_2 K A _inst_4 ℱ') α)) α
Case conversion may be inaccurate. Consider using '#align category_theory.cover_dense.sheaf_hom_eq CategoryTheory.CoverDense.sheafHom_eqₓ'. -/
/-- If the pullback map is obtained via whiskering,
then the result `sheaf_hom (whisker_left G.op α)` is equal to `α`.
-/
theorem sheafHom_eq (α : ℱ ⟶ ℱ'.val) : sheafHom H (whiskerLeft G.op α) = α :=
  by
  ext X
  apply yoneda.map_injective
  swap; · infer_instance
  ext U
  erw [yoneda.image_preimage]
  symm
  change (show (ℱ'.val ⋙ coyoneda.obj (op (unop U))).obj (op (unop X)) from _) = _
  apply sheaf_eq_amalgamation ℱ' (H.is_cover _)
  intro Y f hf
  conv_lhs => rw [← hf.some.fac]
  dsimp
  simp
#align category_theory.cover_dense.sheaf_hom_eq CategoryTheory.CoverDense.sheafHom_eq

#print CategoryTheory.CoverDense.restrictHomEquivHom /-
/-- A full and cover-dense functor `G` induces an equivalence between morphisms into a sheaf and
morphisms over the restrictions via `G`.
-/
noncomputable def restrictHomEquivHom : (G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) ≃ (ℱ ⟶ ℱ'.val)
    where
  toFun := sheafHom H
  invFun := whiskerLeft G.op
  left_inv := sheafHom_restrict_eq H
  right_inv := sheafHom_eq H
#align category_theory.cover_dense.restrict_hom_equiv_hom CategoryTheory.CoverDense.restrictHomEquivHom
-/

include H

/- warning: category_theory.cover_dense.iso_of_restrict_iso -> CategoryTheory.CoverDense.iso_of_restrict_iso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} D] {K : CategoryTheory.GrothendieckTopology.{u4, u3} D _inst_2} {A : Type.{u5}} [_inst_4 : CategoryTheory.Category.{u6, u5} A] {G : CategoryTheory.Functor.{u2, u4, u1, u3} C _inst_1 D _inst_2}, (CategoryTheory.CoverDense.{u1, u2, u3, u4} C _inst_1 D _inst_2 K G) -> (forall [_inst_5 : CategoryTheory.Full.{u2, u4, u1, u3} C _inst_1 D _inst_2 G] {ℱ : CategoryTheory.Sheaf.{u4, u6, u3, u5} D _inst_2 K A _inst_4} {ℱ' : CategoryTheory.Sheaf.{u4, u6, u3, u5} D _inst_2 K A _inst_4} (α : Quiver.Hom.{succ (max u3 u6), max u3 u5 u4 u6} (CategoryTheory.Sheaf.{u4, u6, u3, u5} D _inst_2 K A _inst_4) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u6, max u3 u5 u4 u6} (CategoryTheory.Sheaf.{u4, u6, u3, u5} D _inst_2 K A _inst_4) (CategoryTheory.Category.toCategoryStruct.{max u3 u6, max u3 u5 u4 u6} (CategoryTheory.Sheaf.{u4, u6, u3, u5} D _inst_2 K A _inst_4) (CategoryTheory.Sheaf.CategoryTheory.category.{u4, u6, u3, u5} D _inst_2 K A _inst_4))) ℱ ℱ'), (CategoryTheory.IsIso.{max u1 u6, max u2 u6 u1 u5} (CategoryTheory.Functor.{u2, u6, u1, u5} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) A _inst_4) (CategoryTheory.Functor.category.{u2, u6, u1, u5} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) A _inst_4) (CategoryTheory.Functor.comp.{u2, u4, u6, u1, u3, u5} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) A _inst_4 (CategoryTheory.Functor.op.{u2, u4, u1, u3} C _inst_1 D _inst_2 G) (CategoryTheory.Sheaf.val.{u4, u6, u3, u5} D _inst_2 K A _inst_4 ℱ)) (CategoryTheory.Functor.comp.{u2, u4, u6, u1, u3, u5} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) A _inst_4 (CategoryTheory.Functor.op.{u2, u4, u1, u3} C _inst_1 D _inst_2 G) (CategoryTheory.Sheaf.val.{u4, u6, u3, u5} D _inst_2 K A _inst_4 ℱ')) (CategoryTheory.whiskerLeft.{u1, u2, u3, u4, u5, u6} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) (Opposite.{succ u3} D) (CategoryTheory.Category.opposite.{u4, u3} D _inst_2) A _inst_4 (CategoryTheory.Functor.op.{u2, u4, u1, u3} C _inst_1 D _inst_2 G) (CategoryTheory.Sheaf.val.{u4, u6, u3, u5} D _inst_2 K A _inst_4 ℱ) (CategoryTheory.Sheaf.val.{u4, u6, u3, u5} D _inst_2 K A _inst_4 ℱ') (CategoryTheory.Sheaf.Hom.val.{u4, u6, u3, u5} D _inst_2 K A _inst_4 ℱ ℱ' α))) -> (CategoryTheory.IsIso.{max u3 u6, max u3 u5 u4 u6} (CategoryTheory.Sheaf.{u4, u6, u3, u5} D _inst_2 K A _inst_4) (CategoryTheory.Sheaf.CategoryTheory.category.{u4, u6, u3, u5} D _inst_2 K A _inst_4) ℱ ℱ' α))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u6, u4} D] {K : CategoryTheory.GrothendieckTopology.{u6, u4} D _inst_2} {A : Type.{u3}} [_inst_4 : CategoryTheory.Category.{u5, u3} A] {G : CategoryTheory.Functor.{u1, u6, u2, u4} C _inst_1 D _inst_2}, (CategoryTheory.CoverDense.{u2, u1, u4, u6} C _inst_1 D _inst_2 K G) -> (forall [_inst_5 : CategoryTheory.Full.{u1, u6, u2, u4} C _inst_1 D _inst_2 G] {ℱ : CategoryTheory.Sheaf.{u6, u5, u4, u3} D _inst_2 K A _inst_4} {ℱ' : CategoryTheory.Sheaf.{u6, u5, u4, u3} D _inst_2 K A _inst_4} (α : Quiver.Hom.{max (succ u4) (succ u5), max (max (max u4 u6) u3) u5} (CategoryTheory.Sheaf.{u6, u5, u4, u3} D _inst_2 K A _inst_4) (CategoryTheory.CategoryStruct.toQuiver.{max u4 u5, max (max (max u4 u6) u3) u5} (CategoryTheory.Sheaf.{u6, u5, u4, u3} D _inst_2 K A _inst_4) (CategoryTheory.Category.toCategoryStruct.{max u4 u5, max (max (max u4 u6) u3) u5} (CategoryTheory.Sheaf.{u6, u5, u4, u3} D _inst_2 K A _inst_4) (CategoryTheory.Sheaf.instCategorySheaf.{u6, u5, u4, u3} D _inst_2 K A _inst_4))) ℱ ℱ'), (CategoryTheory.IsIso.{max u2 u5, max (max (max u2 u1) u3) u5} (CategoryTheory.Functor.{u1, u5, u2, u3} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) A _inst_4) (CategoryTheory.Functor.category.{u1, u5, u2, u3} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) A _inst_4) (CategoryTheory.Functor.comp.{u1, u6, u5, u2, u4, u3} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u6, u4} D _inst_2) A _inst_4 (CategoryTheory.Functor.op.{u1, u6, u2, u4} C _inst_1 D _inst_2 G) (CategoryTheory.Sheaf.val.{u6, u5, u4, u3} D _inst_2 K A _inst_4 ℱ)) (CategoryTheory.Functor.comp.{u1, u6, u5, u2, u4, u3} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u6, u4} D _inst_2) A _inst_4 (CategoryTheory.Functor.op.{u1, u6, u2, u4} C _inst_1 D _inst_2 G) (CategoryTheory.Sheaf.val.{u6, u5, u4, u3} D _inst_2 K A _inst_4 ℱ')) (CategoryTheory.whiskerLeft.{u2, u1, u4, u6, u3, u5} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (Opposite.{succ u4} D) (CategoryTheory.Category.opposite.{u6, u4} D _inst_2) A _inst_4 (CategoryTheory.Functor.op.{u1, u6, u2, u4} C _inst_1 D _inst_2 G) (CategoryTheory.Sheaf.val.{u6, u5, u4, u3} D _inst_2 K A _inst_4 ℱ) (CategoryTheory.Sheaf.val.{u6, u5, u4, u3} D _inst_2 K A _inst_4 ℱ') (CategoryTheory.Sheaf.Hom.val.{u6, u5, u4, u3} D _inst_2 K A _inst_4 ℱ ℱ' α))) -> (CategoryTheory.IsIso.{max u4 u5, max (max (max u4 u6) u3) u5} (CategoryTheory.Sheaf.{u6, u5, u4, u3} D _inst_2 K A _inst_4) (CategoryTheory.Sheaf.instCategorySheaf.{u6, u5, u4, u3} D _inst_2 K A _inst_4) ℱ ℱ' α))
Case conversion may be inaccurate. Consider using '#align category_theory.cover_dense.iso_of_restrict_iso CategoryTheory.CoverDense.iso_of_restrict_isoₓ'. -/
/-- Given a full and cover-dense functor `G` and a natural transformation of sheaves `α : ℱ ⟶ ℱ'`,
if the pullback of `α` along `G` is iso, then `α` is also iso.
-/
theorem iso_of_restrict_iso {ℱ ℱ' : Sheaf K A} (α : ℱ ⟶ ℱ') (i : IsIso (whiskerLeft G.op α.val)) :
    IsIso α :=
  by
  convert is_iso.of_iso (sheaf_iso H (as_iso (whisker_left G.op α.val))) using 1
  ext1
  apply (sheaf_hom_eq _ _).symm
#align category_theory.cover_dense.iso_of_restrict_iso CategoryTheory.CoverDense.iso_of_restrict_iso

/- warning: category_theory.cover_dense.compatible_preserving -> CategoryTheory.CoverDense.compatiblePreserving is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} D] {K : CategoryTheory.GrothendieckTopology.{u4, u3} D _inst_2} {G : CategoryTheory.Functor.{u2, u4, u1, u3} C _inst_1 D _inst_2}, (CategoryTheory.CoverDense.{u1, u2, u3, u4} C _inst_1 D _inst_2 K G) -> (forall [_inst_5 : CategoryTheory.Full.{u2, u4, u1, u3} C _inst_1 D _inst_2 G] [_inst_6 : CategoryTheory.Faithful.{u2, u4, u1, u3} C _inst_1 D _inst_2 G], CategoryTheory.CompatiblePreserving.{u5, u2, u4, u1, u3} C _inst_1 D _inst_2 K G)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u5, u3} C] {D : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u4, u2} D] {K : CategoryTheory.GrothendieckTopology.{u4, u2} D _inst_2} {G : CategoryTheory.Functor.{u5, u4, u3, u2} C _inst_1 D _inst_2}, (CategoryTheory.CoverDense.{u3, u5, u2, u4} C _inst_1 D _inst_2 K G) -> (forall [_inst_5 : CategoryTheory.Full.{u5, u4, u3, u2} C _inst_1 D _inst_2 G] [_inst_6 : CategoryTheory.Faithful.{u5, u4, u3, u2} C _inst_1 D _inst_2 G], CategoryTheory.CompatiblePreserving.{u1, u5, u4, u3, u2} C _inst_1 D _inst_2 K G)
Case conversion may be inaccurate. Consider using '#align category_theory.cover_dense.compatible_preserving CategoryTheory.CoverDense.compatiblePreservingₓ'. -/
/-- A fully faithful cover-dense functor preserves compatible families. -/
theorem compatiblePreserving [Faithful G] : CompatiblePreserving K G :=
  by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ eq
  apply H.ext
  intro W i
  simp only [← functor_to_types.map_comp_apply, ← op_comp]
  rw [← G.image_preimage (i ≫ f₁)]
  rw [← G.image_preimage (i ≫ f₂)]
  apply hx
  apply G.map_injective
  simp [Eq]
#align category_theory.cover_dense.compatible_preserving CategoryTheory.CoverDense.compatiblePreserving

omit H

#print CategoryTheory.CoverDense.Sites.Pullback.full /-
noncomputable instance Sites.Pullback.full [Faithful G] (Hp : CoverPreserving J K G) :
    Full (Sites.pullback A H.CompatiblePreserving Hp)
    where
  preimage ℱ ℱ' α := ⟨H.sheafHom α.val⟩
  witness' ℱ ℱ' α := Sheaf.Hom.ext _ _ <| H.sheafHom_restrict_eq α.val
#align category_theory.cover_dense.sites.pullback.full CategoryTheory.CoverDense.Sites.Pullback.full
-/

#print CategoryTheory.CoverDense.Sites.Pullback.faithful /-
instance Sites.Pullback.faithful [Faithful G] (Hp : CoverPreserving J K G) :
    Faithful (Sites.pullback A H.CompatiblePreserving Hp)
    where map_injective' := by
    intro ℱ ℱ' α β e
    ext1
    apply_fun fun e => e.val  at e
    dsimp at e
    rw [← H.sheaf_hom_eq α.val, ← H.sheaf_hom_eq β.val, e]
#align category_theory.cover_dense.sites.pullback.faithful CategoryTheory.CoverDense.Sites.Pullback.faithful
-/

end CoverDense

end CategoryTheory

namespace CategoryTheory.CoverDense

open CategoryTheory

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

variable {G : C ⥤ D} [Full G] [Faithful G]

variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

variable {A : Type w} [Category.{max u v} A] [Limits.HasLimits A]

variable (Hd : CoverDense K G) (Hp : CoverPreserving J K G) (Hl : CoverLifting J K G)

include Hd Hp Hl

/- warning: category_theory.cover_dense.Sheaf_equiv_of_cover_preserving_cover_lifting -> CategoryTheory.CoverDense.sheafEquivOfCoverPreservingCoverLifting is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} {D : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] [_inst_2 : CategoryTheory.Category.{u2, u3} D] {G : CategoryTheory.Functor.{u2, u2, u3, u3} C _inst_1 D _inst_2} [_inst_3 : CategoryTheory.Full.{u2, u2, u3, u3} C _inst_1 D _inst_2 G] [_inst_4 : CategoryTheory.Faithful.{u2, u2, u3, u3} C _inst_1 D _inst_2 G] {J : CategoryTheory.GrothendieckTopology.{u2, u3} C _inst_1} {K : CategoryTheory.GrothendieckTopology.{u2, u3} D _inst_2} {A : Type.{u1}} [_inst_5 : CategoryTheory.Category.{max u3 u2, u1} A] [_inst_6 : CategoryTheory.Limits.HasLimits.{max u3 u2, u1} A _inst_5], (CategoryTheory.CoverDense.{u3, u2, u3, u2} C _inst_1 D _inst_2 K G) -> (CategoryTheory.CoverPreserving.{u2, u2, u3, u3} C _inst_1 D _inst_2 J K G) -> (CategoryTheory.CoverLifting.{u3, u2, u3, u2} C _inst_1 D _inst_2 J K G) -> (CategoryTheory.Equivalence.{max u3 u2, max u3 u2, max u3 u1 u3 u2, max u3 u1 u3 u2} (CategoryTheory.Sheaf.{u2, max u3 u2, u3, u1} C _inst_1 J A _inst_5) (CategoryTheory.Sheaf.CategoryTheory.category.{u2, max u3 u2, u3, u1} C _inst_1 J A _inst_5) (CategoryTheory.Sheaf.{u2, max u3 u2, u3, u1} D _inst_2 K A _inst_5) (CategoryTheory.Sheaf.CategoryTheory.category.{u2, max u3 u2, u3, u1} D _inst_2 K A _inst_5))
but is expected to have type
  forall {C : Type.{u3}} {D : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] [_inst_2 : CategoryTheory.Category.{u2, u3} D] {G : CategoryTheory.Functor.{u2, u2, u3, u3} C _inst_1 D _inst_2} [_inst_3 : CategoryTheory.Full.{u2, u2, u3, u3} C _inst_1 D _inst_2 G] [_inst_4 : CategoryTheory.Faithful.{u2, u2, u3, u3} C _inst_1 D _inst_2 G] {J : CategoryTheory.GrothendieckTopology.{u2, u3} C _inst_1} {K : CategoryTheory.GrothendieckTopology.{u2, u3} D _inst_2} {A : Type.{u1}} [_inst_5 : CategoryTheory.Category.{max u3 u2, u1} A] [_inst_6 : CategoryTheory.Limits.HasLimits.{max u3 u2, u1} A _inst_5], (CategoryTheory.CoverDense.{u3, u2, u3, u2} C _inst_1 D _inst_2 K G) -> (CategoryTheory.CoverPreserving.{u2, u2, u3, u3} C _inst_1 D _inst_2 J K G) -> (CategoryTheory.CoverLifting.{u3, u2, u3, u2} C _inst_1 D _inst_2 J K G) -> (CategoryTheory.Equivalence.{max u3 u2, max u3 u2, max (max (max u1 u3) u3 u2) u2, max (max (max u1 u3) u3 u2) u2} (CategoryTheory.Sheaf.{u2, max u3 u2, u3, u1} C _inst_1 J A _inst_5) (CategoryTheory.Sheaf.{u2, max u3 u2, u3, u1} D _inst_2 K A _inst_5) (CategoryTheory.Sheaf.instCategorySheaf.{u2, max u3 u2, u3, u1} C _inst_1 J A _inst_5) (CategoryTheory.Sheaf.instCategorySheaf.{u2, max u3 u2, u3, u1} D _inst_2 K A _inst_5))
Case conversion may be inaccurate. Consider using '#align category_theory.cover_dense.Sheaf_equiv_of_cover_preserving_cover_lifting CategoryTheory.CoverDense.sheafEquivOfCoverPreservingCoverLiftingₓ'. -/
/-- Given a functor between small sites that is cover-dense, cover-preserving, and cover-lifting,
it induces an equivalence of category of sheaves valued in a complete category.
-/
@[simps Functor inverse]
noncomputable def sheafEquivOfCoverPreservingCoverLifting : Sheaf J A ≌ Sheaf K A :=
  by
  symm
  let α := Sites.pullbackCopullbackAdjunction.{w, v, u} A Hp Hl Hd.compatible_preserving
  have : ∀ X : Sheaf J A, is_iso (α.counit.app X) :=
    by
    intro ℱ
    apply (config := { instances := false }) reflects_isomorphisms.reflects (Sheaf_to_presheaf J A)
    exact is_iso.of_iso ((@as_iso _ _ _ _ _ (Ran.reflective A G.op)).app ℱ.val)
  haveI : is_iso α.counit := nat_iso.is_iso_of_is_iso_app _
  exact
    { Functor := sites.pullback A Hd.compatible_preserving Hp
      inverse := sites.copullback A Hl
      unitIso := as_iso α.unit
      counitIso := as_iso α.counit
      functor_unitIso_comp' := fun ℱ => by convert α.left_triangle_components }
#align category_theory.cover_dense.Sheaf_equiv_of_cover_preserving_cover_lifting CategoryTheory.CoverDense.sheafEquivOfCoverPreservingCoverLifting

end CategoryTheory.CoverDense

